
use crate::define::RuleExpression;

use hashable_rc::HashableRc;

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;


/* Public Interface */

pub struct Parser<T: Token> {
    pub(crate) rules: HashMap<String, RuleExpression<T>>
}

#[derive(Debug)]
pub enum SyntaxTree<T: Token> {
    RuleNode {rule_name: String, subexpressions: Vec<SyntaxTree<T>>},
    TokenNode (T)
}

impl<T: Token> std::fmt::Display for SyntaxTree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Syntax Tree {")?;
        self.helper_fmt(1, f)?;
        f.write_str("\n}")
    }
}

impl<T: Token> SyntaxTree<T> {
    fn helper_fmt(&self, level: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("\n")?;
        f.write_str(&std::iter::repeat(' ').take(level * 4).collect::<String>())?;
        match self {
            SyntaxTree::RuleNode {rule_name, subexpressions} => {
                f.write_str(&rule_name)?;
                for expr in subexpressions {
                    expr.helper_fmt(level + 1, f)?;
                    // f.write_str("\n")?
                }
                Ok(())
            },
            SyntaxTree::TokenNode(token) => {
                f.write_str(&format!("token ({})", token.get_contents()))
            }
        }

    }
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
pub trait Token : Sized + Clone + std::fmt::Debug + Eq {
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
        let root_link = Rc::new(GSSLink {
            node: Rc::new(GSSNode {expr: &root_expr, parent: None, parent_data: GSSParentData::NoData}),
            prev: vec![]
        });
        
        /* gss[i] holds all terminals that are set to try to match tokens[i].
         * When the algorithm is finished, the last layer (gss[tokens.len()])
         * holds nodes representing parser processes that have consumed all tokens. */
        let mut gss: Vec<Vec<Rc<GSSLink<T>>>> = vec![
            GSSNode::resolve_to_terminals(Rc::clone(&root_link.node), &self)?.into_iter()
                .map(|node| Rc::new(GSSLink {node: node, prev: vec![Rc::clone(&root_link)]}))
                .collect()
        ];

        for token in tokens.clone() {
            let mut next_layer = vec![];

            for link in gss.last().ok_or(ParseError("gss uninitialized".to_string()))? {
                next_layer.extend(
                    GSSNode::advance_token(Rc::clone(&link.node), &token, &self)?.into_iter()
                        .map(|node| Rc::new(GSSLink {node: Rc::clone(&node), prev: vec![Rc::clone(&link)]}))
                        .collect::<Vec<_>>()
                );
            }

            // TODO: Implement merging.

            gss.push(next_layer);
        }
        
        /* Backtracks from the final node to the first. Final and first are removed, since they are the root rule. 
         * All other nodes correspond to tokens. */
        let backtrace = Parser::<T>::get_backtrace(&gss)?;

        /* Uses the backtrace to determine the hierarchy of rules and tokens, i.e.
         * the final syntax tree */
        Parser::<T>::backtrace_to_tree(backtrace)
    }

    fn get_backtrace<'a>(gss: &'a Vec<Vec<Rc<GSSLink<T>>>>) -> Result<Vec<Rc<GSSNode<'a, T>>>, ParseError> {
        let final_links = gss.get(gss.len() - 1)
        .ok_or(ParseError("gss initialized".to_string()))?
        .iter()
        .filter(|link| matches!(link.node.parent_data, GSSParentData::Done))
        .collect::<Vec<_>>();

        let final_link = match final_links.len() {
            0 => Err(ParseError("Unsuccessful Parse...".to_string())),
            1 => {
                Ok(final_links[0])
            },
            _ => Err(ParseError("Ambiguous Parse...".to_string())),
        }?;

        let backtrace = std::iter::successors(Some(final_link), |link|
            match link.prev.len() {
                0 => None,
                _ => Some(&link.prev[0])
            }
        ).map(|link| Rc::clone(&link.node))
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect::<Vec<_>>();

        let backtrace = backtrace[1..backtrace.len()-1].to_vec();  // Drop ends, they are the root rule. 

        Ok(backtrace)
    }

    fn backtrace_to_tree(backtrace: Vec<Rc<GSSNode<'_, T>>>) -> Result<SyntaxTree<T>, ParseError> {
        /* Theory: this can be way way way simplified. I think I got really confused
         * before I decided to use HashableRc. Keep only the following loop. If you
         * can get rid of the intermediate tree, great, but I kinda doubt thats possible. 
         * 
         * The key: A singular hashtable, from HashableRc::<GSSNode> to Rc<RefCell<IntermediateSyntaxTree>> */

        let mut subtrees: HashMap<HashableRc::<GSSNode<T>>, Rc<RefCell<IntermediateSyntaxTree<T>>>> = HashMap::new();
        let mut root: Option<Rc<RefCell<IntermediateSyntaxTree<T>>>> = None;

        for node in backtrace.into_iter() {
            if let RuleExpression::Terminal(tok) = node.expr {
                let mut curr_node = node;
                let mut curr_subtree = Rc::new(RefCell::new(IntermediateSyntaxTree::TokenNode(tok.clone())));

                while let Some(parent) = &curr_node.parent {
                    if let RuleExpression::RuleName(name) = parent.expr {
                        let parent_unprocessed = !subtrees.contains_key(&HashableRc::new(Rc::clone(parent)));

                        if parent_unprocessed {
                            subtrees.insert(HashableRc::new(Rc::clone(parent)), Rc::new(RefCell::new(IntermediateSyntaxTree::RuleNode { rule_name: name.clone(), subexpressions: vec![] })));
                        }
 
                        let parent_tree = subtrees.get(&HashableRc::new(Rc::clone(parent))).expect("Known to contain node");
                        if let IntermediateSyntaxTree::RuleNode { rule_name: _, subexpressions } = &mut *(parent_tree.borrow_mut()) {  // I hate this &mut *(...) thing.
                            subexpressions.push(curr_subtree);
                        }
                        else {
                            panic!("Known to be RuleNode variant");
                        }

                        curr_subtree = Rc::clone(parent_tree);

                        if !parent_unprocessed {
                            break;
                        }
                    } 

                    curr_node = Rc::clone(&curr_node.parent.clone().expect("Known to be Some ()"));

                    if curr_node.parent == None {
                        root = Some(Rc::clone(subtrees.get(&HashableRc::new(Rc::clone(&curr_node))).expect("Known to contain node")));
                    }
                }
            }
            else {
                return Err(ParseError("Non Terminal in backtrace".to_owned()));
            }
        }

        /* Final conversion to tree. */
        Ok(intermediate_to_final(
            root.ok_or(ParseError("No root found at end of parsing".to_string()))?
        ))
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

#[derive(Clone, Debug)]
enum IntermediateSyntaxTree<T: Token> { // Vec contains Rc's, to be removed later.
    RuleNode {rule_name: String, subexpressions: Vec<Rc<RefCell<IntermediateSyntaxTree<T>>>>},
    TokenNode (T)
}

fn intermediate_to_final<T: Token>(root: Rc<RefCell<IntermediateSyntaxTree<T>>>) -> SyntaxTree<T> {
    match root.borrow().clone() {
        IntermediateSyntaxTree::RuleNode {rule_name, subexpressions} => 
            SyntaxTree::RuleNode {
                rule_name, 
                subexpressions: subexpressions.into_iter()
                    .map(|rc_refcell_tree| intermediate_to_final(rc_refcell_tree))
                    .collect()
            },
        IntermediateSyntaxTree::TokenNode(token) => SyntaxTree::TokenNode(token),
    }
}

/* Graph Structured Stack! A node models a current position in the parsing process. */
#[derive(PartialEq, Eq)]
// Eq *should* only be needed for use in a HashableRc hashtable, where equality is by reference.
struct GSSNode<'a, T: Token> {
    expr: &'a RuleExpression<T>,
    parent: Option<Rc<GSSNode<'a, T>>>, // Corresponds to the parent expression.
    parent_data: GSSParentData // Corresponds to the data regarding this node's relationship to its parent. i.e. which index of the concatenation.
}

// Represents a link between two GSSNodes, where `node` is the current node and `prev` is a node whose continuation
// leads to `node`.
#[derive(Debug)]
struct GSSLink<'a, T: Token> {
    node: Rc<GSSNode<'a, T>>,
    prev: Vec<Rc<GSSLink<'a, T>>>,  // Note: When merging is implemeneted, we will need multiple prev nodes.
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
        if caller_parent_data == GSSParentData::Done {
            return Ok(vec![]);
        }

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
                            parent: Some(Rc::clone(&node)),
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
                            parent: Some(Rc::clone(&node)), 
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
                            parent: Some(Rc::clone(&node)),
                            parent_data: GSSParentData::NoData
                        }), parser)
                    )
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .flatten()
                    .collect()
                )
            },
            RuleExpression::Many(_) => {
                Self::advance_auto(node, parser, GSSParentData::NoData)
            },
            RuleExpression::Optional(sub_expr) => {
                Ok(
                    Self::resolve_to_terminals(Rc::new(GSSNode {
                        expr: sub_expr,
                        parent: Some(Rc::clone(&node)),
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

    use indoc::indoc;

    
    #[test]
    fn parsing_does_not_explode_color() {
        let parser: Parser<CharToken> = crate::define::define_parser(r##"
            Color: RGB | Hex ;
            RGB: "Color"  " "  "(" Num " " Num " " Num ")" ;
            Hex: "#" HexNum ;
            Num: "0" | "1" | "2" | "3" ; # Proof of concept
            HexNum: Num | "A" | "B" | "C" ; # Proof of concept
        "##.to_string()).expect("Parser definition ok");

        let tree = parser
            .parse_string("Color (1 3 0)".to_string(), "Color")
            .expect("No error");

        println!("{}", tree);

        assert_eq!(tree.to_string(), indoc! {"
        Syntax Tree {
            Color
                RGB
                    token (C)
                    token (o)
                    token (l)
                    token (o)
                    token (r)
                    token ( )
                    token (()
                    Num
                        token (1)
                    token ( )
                    Num
                        token (3)
                    token ( )
                    Num
                        token (0)
                    token ())
        }"}
        );
    }

    #[test]
    fn parsing_does_not_explode_optional() {
        let parser: Parser<CharToken> = crate::define::define_parser(r##"
            Num : "1" | "2" | "3" | "4" ; # Incomplete ofc
            AddExpr: Num ("+" AddExpr)? ;
        "##.to_string()).expect("Parser definition ok");

        let tree = parser
            .parse_string("1+2+3+4".to_string(), "AddExpr")
            .expect("No error");

        assert_eq!(tree.to_string(), indoc! {"
            Syntax Tree {
                AddExpr
                    Num
                        token (1)
                    token (+)
                    AddExpr
                        Num
                            token (2)
                        token (+)
                        AddExpr
                            Num
                                token (3)
                            token (+)
                            AddExpr
                                Num
                                    token (4)
            }"}
        );
    }

    #[test]
    fn parsing_does_not_explode_many() {
        let parser: Parser<CharToken> = crate::define::define_parser(r##"
            Rule : ManyA "b"+ ManyC "d"+;
            ManyA: "a"*;
            ManyC: "c"*; 
        "##.to_string()).expect("Parser definition ok");

        let tree = parser
            .parse_string("abbdddd".to_string(), "Rule")
            .expect("No error");

        assert_eq!(tree.to_string(), indoc! {"
            Syntax Tree {
                Rule
                    ManyA
                        token (a)
                    token (b)
                    token (b)
                    token (d)
                    token (d)
                    token (d)
                    token (d)
            }"} // Note that ManyC is not shown at all... We kinda have to accept this
            // since otherwise we would have to figure out after the fact where ManyC
            // fits in, which could be hard if for example it were surrounded by
            // other ManyC's that did parse (especially if they had quantifiers).
            // Basically, we would have to rethink what data ends up in the GSS,
            // and that sounds really unpleasant.
        );
    }   
}
