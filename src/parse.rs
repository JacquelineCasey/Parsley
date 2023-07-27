
use crate::define::RuleExpression;

use std::collections::HashMap;
use std::rc::Rc;


/* Public Interface */

pub struct Parser<T: Token> {
    pub(crate) rules: HashMap<String, RuleExpression<T>>
}

pub enum SyntaxTree<T: Token> {
    RuleNode {rule_name: String, subexpressions: Vec<SyntaxTree<T>>},
    TokenNode (T)
}

#[derive(Debug)]
pub struct ParseError (String);

/* Represents a token, namely a type (used for parsing) and content (used after parsing). 
 *
 * This is a trait so that users can define parsers over specific alphabets beyond
 * what we support out of the box. It can also be useful to allow a language to
 * provide detailed error messages, or simply to run faster (tokenization is often O(n),
 * and most parsing algorithms are O(n^3) worst case, so preprocessing to shorten the
 * list of tokens can be useful).
 * 
 * Tokens need not track their own location in the source file, that will eventually
 * be done by the parser. */
pub trait Token : Sized + Clone + std::fmt::Debug {
    /* Returns the type of a token e.g. 'identifier' */
    fn get_type(&self) -> &str;

    /* Returns the actual matched contents of a token, e.g. 'foo' */
    fn get_contents(&self) -> &str;

    /* Converts a literal string in the definition language into a sequence of
     * tokens. Escape sequences are built in as part of the definition language,
     * so the escape sequences need not be processed here.
     * 
     * Most user defined token types will not have this capability. If this returns
     * null, then define_parser() will return an error if you use a literal.
     * 
     * Notably, the predefined CharToken does support this feature. */
    fn token_sequence_from_literal(_literal: &str) -> Option<Vec<Self>> {
        None
    }
}

/* A token that represents  */
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CharToken {
    /* Unlike most tokens, a single field is sufficient, as all token_types have
     * a single possible value (the character). */
    token_type: String,  // String for annoying ownership reasons. Will validate that its a single character.
}

impl Token for CharToken {
    fn get_type(&self) -> &str {
        &self.token_type
    }

    fn get_contents(&self) -> &str {
        &self.token_type
    }

    fn token_sequence_from_literal(literal: &str) -> Option<Vec<Self>> {
        return Some(literal.chars().map(|c| CharToken {token_type: c.to_string()}).collect())
    }
}

impl<T: Token> Parser<T> {
    pub fn parse_tokens(&self, tokens: Vec<T>, start_rule: &str) -> Result<SyntaxTree<T>, ParseError> {
        let root_expr = RuleExpression::RuleName(start_rule.to_string());
        let root_node = Rc::new(GSSNode {expr: &root_expr, parent: None, parent_data: GSSParentData::NoData});
        
        /* gss[i] holds all terminals that are set to try to match tokens[i].
         * When the algorithm is finished, the last layer (gss[tokens.len()])
         * holds nodes representing parser processes that have consumed all tokens. */
        let mut gss: Vec<Vec<Rc<GSSNode<T>>>> = vec![GSSNode::resolve_to_terminals(root_node, &self)?];

        for token in tokens {
            let mut next_layer = vec![];
            
            for node in gss.last().expect("gss initialized") {
                next_layer.extend(GSSNode::advance_token(node.clone(), &token, &self)?);
            }

            // TODO: Implement merging.

            gss.push(next_layer);
        }

        println!("Final Layer: {:?}", gss.last().expect("gss initialized"));

        todo!() // Work backwards to identify successful parse tree. 
    }
}

impl Parser<CharToken> {
    pub fn parse_string(&self, input: String, start_rule: &str) -> Result<SyntaxTree<CharToken>, ParseError> {
        let tokens = CharToken::token_sequence_from_literal(&input)
            .expect("CharToken returns Some(...)");
        self.parse_tokens(tokens, start_rule)
    }
}


/* Private Implementation */

/* Graph Structured Stack! Models a current position in the parsing process. */
struct GSSNode<'a, T: Token> {
    expr: &'a RuleExpression<T>,
    parent: Option<Rc<GSSNode<'a, T>>>,
    parent_data: GSSParentData
}

#[derive(Debug, Clone, Copy)]
enum GSSParentData {
    Index (usize),
    NoData,
    Done
}

impl<T: Token> std::fmt::Debug for GSSNode<'_, T> {
    // Required method
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let mut temp = f.debug_struct("GSSNode");
        let res = temp.field("expr", self.expr);

        let res = match self.parent.clone() {
            Some(parent) => res.field("parent.expr", parent.expr),
            None => res.field("parent.expr", &"None"),
        };

        res.field("parent_data", &self.parent_data)
            .finish()

    }
}


impl<'a, T: Token> GSSNode<'a, T> {
    /* Returns a set of all next terminal expressions to parse, modelling the next
     * step after consuming a token in a given state. */
    fn advance_token(node: Rc<GSSNode<'a, T>>, token: &T, parser: &'a Parser<T>) -> Result<Vec<Rc<GSSNode<'a, T>>>, ParseError> {
        if let GSSParentData::Done = node.parent_data {
            Ok(vec![])
        }
        else {
            match node.expr {
                RuleExpression::Terminal(required_token) if required_token.get_type() == token.get_type() => {
                    if let Some(parent) = node.parent.clone() {
                        Self::advance_auto(parent, parser, node.parent_data)
                    }
                    else {
                        Err(ParseError("Terminal Expression has no parent".to_string()))
                    }
                }
                RuleExpression::Terminal(_) => Ok(vec![]),
                _ => Err(ParseError("Tried to feed token to non terminal expresison".to_string()))
            }
        }
    } 

    /* In this case, there is no token to consume. */
    fn advance_auto(node: Rc<GSSNode<'a, T>>, parser: &'a Parser<T>, caller_parent_data: GSSParentData) -> Result<Vec<Rc<GSSNode<'a, T>>>, ParseError> {
        match node.expr {
            RuleExpression::Terminal(_) => Err(ParseError("Tried to advance terminal without token".to_owned())),
            RuleExpression::RuleName(_) => {
                match node.parent.clone() {
                    Some(parent) => Self::advance_auto(parent, parser, node.parent_data),
                    None => Ok(vec![GSSNode {expr: node.expr, parent: None, parent_data: GSSParentData::Done}.into()])
                }
            } 
            RuleExpression::Concatenation(sub_exprs) => {
                if let GSSParentData::Index(i) = caller_parent_data {
                    if i+1 >= sub_exprs.len() {
                        Self::advance_auto(
                            node.parent.clone().ok_or(ParseError("Concatenation without parent".to_owned()))?, 
                            parser,
                            node.parent_data
                        )
                    } 
                    else {
                        Self::resolve_to_terminals(Rc::new(GSSNode {
                            expr: &sub_exprs[i+1], 
                            parent: Some(node.clone()),
                            parent_data: GSSParentData::Index(i+1)
                        }), parser)
                    }
                }
                else {
                    Err(ParseError("Tried to advance Concatenation without index".to_owned()))
                }
            }
            RuleExpression::Alternatives(_) | RuleExpression::Optional(_) => {
                match node.parent.clone() {
                    Some(parent) => Self::advance_auto(parent, parser, node.parent_data),
                    None => Err(ParseError("Alternatives or Optional lack parent".to_string()))
                }
            }
            RuleExpression::OneOrMore(sub_expr) | RuleExpression::Many(sub_expr) => {
                match node.parent.clone() {
                    Some(parent) => Ok(
                        Self::resolve_to_terminals(Rc::new(GSSNode { 
                            expr: sub_expr, 
                            parent: Some(node.clone()), 
                            parent_data: GSSParentData::NoData 
                        }), parser)?.into_iter()
                            .chain(Self::advance_auto(parent, parser, node.parent_data)?.into_iter())
                            .collect::<Vec<_>>()
                    ),
                    None => Err(ParseError("OneOrMore or Many lack parent".to_string()))
                }
            }
        }
    }

    /* Recursively substitute while building a GSSTree, until leaves are terminals  */
    fn resolve_to_terminals(node: Rc<GSSNode<'a, T>>, parser: &'a Parser<T>) -> Result<Vec<Rc<GSSNode<'a, T>>>, ParseError> {
        match node.expr {
            RuleExpression::Terminal(_) => Ok(vec![node]),
            RuleExpression::RuleName(name) => {
                Self::resolve_to_terminals(Rc::new(GSSNode {
                    expr: &parser.rules[name], 
                    parent: Some(node), 
                    parent_data: GSSParentData::NoData
                }), parser)
            }
            RuleExpression::Concatenation(sub_exprs) => {
                Self::resolve_to_terminals(Rc::new(GSSNode {
                    expr: &sub_exprs[0],
                    parent: Some(node), 
                    parent_data: GSSParentData::Index(0),
                }), parser)
            }
            RuleExpression::Alternatives(sub_exprs) => {
                Ok(sub_exprs.iter()
                    .map(|expr| 
                        Self::resolve_to_terminals(Rc::new(GSSNode {
                            expr,
                            parent: Some(node.clone()),
                            parent_data: GSSParentData::NoData
                        }), parser)
                    )
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .flatten()
                    .collect()
                )
            }
            RuleExpression::Optional(sub_expr) | RuleExpression::Many(sub_expr) => {
                Ok(
                    Self::resolve_to_terminals(Rc::new(GSSNode {
                        expr: sub_expr,
                        parent: Some(node.clone()),
                        parent_data: GSSParentData::NoData
                    }), parser)?.into_iter()
                        .chain(Self::advance_auto(node, parser, GSSParentData::NoData)?.into_iter())
                        .collect()
                )
            },
            RuleExpression::OneOrMore(sub_expr) => {
                Self::resolve_to_terminals(Rc::new(GSSNode {
                    expr: sub_expr,
                    parent: Some(node),
                    parent_data: GSSParentData::NoData,
                }), parser)
            }
        }
    }
}


/* Tests */

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parsing_does_not_explode_color() {
        let parser: Parser<CharToken> = crate::define::define_parser(r##"
            Color: RGB | Hex ;
            RGB: "Color"  " "  "(" Num " " Num " " Num ")" ;
            Hex: "#" HexNum ;
            Num: "0" | "1" | "2" | "3" ; # Proof of concept
            HexNum: Num | "A" | "B" | "C" ; # Proof of concept
        "##.to_string()).expect("Parser definition ok");

        parser
            .parse_string("Color (1 3 0)".to_string(), "Color")
            .expect("No error");
    }

    #[test]
    fn parsing_does_not_explode_optional() {
        let parser: Parser<CharToken> = crate::define::define_parser(r##"
            Num : "1" | "2" | "3" | "4" ; # Incomplete ofc
            AddExpr: Num ("+" AddExpr)? ;
        "##.to_string()).expect("Parser definition ok");

        parser
            .parse_string("1+2+3+4".to_string(), "AddExpr")
            .expect("No error");
    }

    #[test]
    fn parsing_does_not_explode_many() {
        let parser: Parser<CharToken> = crate::define::define_parser(r##"
            Rule : "a"* "b"+ "c"* "d"+; 
        "##.to_string()).expect("Parser definition ok");

        parser
            .parse_string("aaabbbddd".to_string(), "Rule")
            .expect("No error");
    }   
}
