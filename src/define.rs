/* Allows creation of a parser object from a string definition. Projects will
 * likely want to give that definition in a file, but we accept it as a string. */

use super::Parser;
use super::Token;

use itertools::Itertools;

use std::collections::HashMap;


/* Public Interface */

pub fn define_parser<T: Token>(definition: String) -> Result<Parser<T>, DefinitionError> {
    let tokens = tokenize(definition)?;
    let rule_token_slices = tokens.split(|t| t == &DefinitionToken::Operator(Operator::Semicolon));

    match rule_token_slices.clone().last() {
        None => return Err(DefinitionError("No rules defined".to_string())),
        Some(slice) if slice != vec![] => return Err(DefinitionError("Missing final semicolon".to_string())),
        _ => ()
    }

    // TODO: Better error reporting - report all errors, and allow for diagnostics that
    // print the line or at least the rule name.

    let rules_map = rule_token_slices
        .dropping_back(1)
        .map(|slice| parse_rule(slice))
        .collect::<Result<HashMap<String, RuleExpression<T>>, DefinitionError>>()?;

    let parser = Parser::<T> {rules: rules_map};
        
    validate_parser(parser)
}

#[derive(PartialEq, Eq, Debug)]
pub struct DefinitionError (String);


/* Private Implementation */

/* This is a token for the parser definition language. This is completely unrelated
 * to the tokens consumed by the parser (i.e. the parse::Token trait) */
#[derive(PartialEq, Eq, Debug, Clone, PartialOrd, Ord)]
enum DefinitionToken {
    Operator (Operator),
    Identifier (String),
    StringLiteral (String), // This holds the string that appears in the source, escape sequences are not proccessed.
    LeftParenthesis,
    RightParenthesis,
}
// Note: Ord definition reflects precedence, so Operator has highest precedence


#[derive(PartialEq, Eq, Debug, Clone, Copy, PartialOrd, Ord)]
enum Operator {
    Colon,
    Semicolon,
    Bar,
    Plus,
    Star,
    QuestionMark
    // possibly more to come as the language gets more interesting
}
// Note: Ord definition reflects precedence, so Bar has least precedence.

/* Describes the rules for what matches a specific rule. The name of the associated
 * rule is stored externally (i.e. as a hash map key) */
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuleExpression<T: Token> {
    Terminal (T),
    RuleName (String),
    Concatenation (Vec<RuleExpression<T>>),
    Alternatives (Vec<RuleExpression<T>>),
    Optional (Box<RuleExpression<T>>),
    OneOrMore (Box<RuleExpression<T>>),
    Many (Box<RuleExpression<T>>)
}

/* Converts a string into tokens. Whitespace is removed, but considered in order
 * to differentiate adjacent identifiers. Also strips comments */
fn tokenize(definition: String) -> Result<Vec<DefinitionToken>, DefinitionError> {
    let mut tokens = Vec::new();
    let mut curr_token = String::new();
    let mut quote_mode = false;
    let mut comment_mode = false;
    let mut slash_mode = false;

    let push_curr_token = |curr_token: &mut String, tokens: &mut Vec<DefinitionToken>| -> Result<(), DefinitionError>{
        if !curr_token.is_empty() {
            tokens.push(string_to_token(curr_token.clone())?);
            curr_token.clear();
        }    
        Ok(())
    };

    for char in definition.chars() {
        if comment_mode && char == '\n' {
            comment_mode = false;
        }
        else if comment_mode {
            continue;
        }
        else if slash_mode {
            slash_mode = false;
            curr_token.push(char);
        }
        else if char == '"' && !quote_mode {
            quote_mode = true;
            push_curr_token(&mut curr_token, &mut tokens)?;
            curr_token.push('"');
        }
        else if char == '"' && quote_mode {
            quote_mode = false;
            curr_token.push('"');
            push_curr_token(&mut curr_token, &mut tokens)?;
        }
        else if quote_mode && char == '\\' {
            slash_mode = true;
            curr_token.push('\\');
        }
        else if quote_mode {
            curr_token.push(char);
        }
        else if char == '#' {
            comment_mode = true;
            push_curr_token(&mut curr_token, &mut tokens)?;
        }
        else if char.is_whitespace() {
            push_curr_token(&mut curr_token, &mut tokens)?;
        }
        else if is_identifier_char(char) {
            curr_token.push(char);
        }
        else {
            push_curr_token(&mut curr_token, &mut tokens)?;

            tokens.push(string_to_token(char.to_string())?);
        }
    }

    push_curr_token(&mut curr_token, &mut tokens)?;

    Ok(tokens)
}

// Weird semantics for efficiency within above algorithm
fn string_to_token(mut string: String) -> Result<DefinitionToken, DefinitionError> {
    match string.as_str() {
        ";" => Ok(DefinitionToken::Operator(Operator::Semicolon)),
        ":" => Ok(DefinitionToken::Operator(Operator::Colon)),
        "|" => Ok(DefinitionToken::Operator(Operator::Bar)),
        "+" => Ok(DefinitionToken::Operator(Operator::Plus)),
        "*" => Ok(DefinitionToken::Operator(Operator::Star)),
        "?" => Ok(DefinitionToken::Operator(Operator::QuestionMark)),
        "(" => Ok(DefinitionToken::LeftParenthesis),
        ")" => Ok(DefinitionToken::RightParenthesis),
        _ if string.chars().nth(0) == Some('"') && string.chars().last() == Some('"') 
            => {
                string.remove(string.len() - 1);
                string.remove(0);
                Ok(DefinitionToken::StringLiteral(deliteralize(string)?))
            }
        _ if string.chars().all(|ch| is_identifier_char(ch))
            => Ok(DefinitionToken::Identifier(string)),
        _ => Err(DefinitionError(format!("Unrecognized token in parser definition: \"{}\"", string)))
    }
}

fn is_identifier_char(char: char) -> bool {
    char.is_ascii_alphanumeric() || char == '_'
}

/* Given a string that may have escape sequences, substitutes those escape sequences with 
 * the characters they represent. 
 * 
 * Currently supports all single character escape sequences supported by Rust, 
 * i.e. those that can be typed written as a backslash followed by a single character.
 * There are other escape sequences that could be supported, but I would need to
 * rewrite tokenize() above to be smarter. */
fn deliteralize(string: String) -> Result<String, DefinitionError> {
    let mut result = String::new();

    let mut slash_mode = false;
    for ch in string.chars() {
        if slash_mode {
            match ch {
                '\\' => result.push('\\'),
                'n' => result.push('\n'),
                'r' => result.push('\r'),
                't' => result.push('\t'),
                '0' => result.push('\0'),
                '\'' => result.push('\''),
                '"' => result.push('"'),
                _ => return Err(DefinitionError("Bad escape sequence".to_owned())),
            }

            slash_mode = false;
        }
        else {
            if ch == '\\' {
                slash_mode = true;
            }
            else {
                result.push(ch);
            }
        }
    }

    return Ok(result);
}

fn parse_rule<T: Token>(tokens: &[DefinitionToken]) -> Result<(String, RuleExpression<T>), DefinitionError> {
    let tokens = tokens.to_vec();

    if tokens.get(1).ok_or(DefinitionError("Not enough tokens in rule".to_owned()))? != &DefinitionToken::Operator(Operator::Colon) {
        return Err(DefinitionError("Second token in rule is not ':'. Syntax: <Rule> : <Rule Expression> ;".to_owned()));
    }

    let rule_name = match &tokens[0] {
        DefinitionToken::Identifier(str) => str.clone(),
        _ => Err(DefinitionError("First token of rule must be an identifier. Syntax: <Rule> : <Rule Expression> ;".to_owned()))?
    };

    return Ok((rule_name, parse_expression(tokens[2..].to_vec())?));
}

fn parse_expression<T: Token>(tokens: Vec<DefinitionToken>) -> Result<RuleExpression<T>, DefinitionError> {
    if tokens.len() == 0 {
        return Err(DefinitionError("Encountered empty subexpression".to_string()));
    }

    if tokens[0] == DefinitionToken::RightParenthesis {
        return Err(DefinitionError("Encountered right parenthesis at left of subexpression".to_string()));
    }

    if tokens[tokens.len() - 1] == DefinitionToken::LeftParenthesis {
        return Err(DefinitionError("Encountered left parenthesis at left of subexpression".to_string()));
    }

    /* Scan and determine most relevant operator (least precedence!). */

    let mut min_precedence_indices = vec![];
    let mut paren_nesting = 0;
    for i in 0..tokens.len() {
        if tokens[i] == DefinitionToken::LeftParenthesis {
            paren_nesting += 1;
        }
        else if tokens[i] == DefinitionToken::RightParenthesis {
            paren_nesting -= 1;
        }
        else if paren_nesting == 0 {
            /* The operator evaluated precedence as defined in the enum ordering. Technically,
             * all tokens have a precedence, though we really only care about certain operator */
            if min_precedence_indices.is_empty() || tokens[i] < tokens[min_precedence_indices[0]] {
                min_precedence_indices = vec![i];
            }
            else if tokens[i] == tokens[min_precedence_indices[0]] {
                min_precedence_indices.push(i);
            }
        }
        else if paren_nesting < 0 {
            return Err(DefinitionError("Too many right parentheses in subexpression!".to_owned()));
        }
    }

    if paren_nesting > 0 {
        return Err(DefinitionError("Too many left parentheses in subexpression!".to_owned()));
    }

    if min_precedence_indices.is_empty() {
        return parse_expression(tokens[1..tokens.len()-1].to_vec());
    }

    match tokens[min_precedence_indices[0]] {
        DefinitionToken::Operator(Operator::Bar) => {
            let delimiters = std::iter::once(-1)
                .chain(min_precedence_indices.into_iter().map(|u| u as i32))
                .chain(std::iter::once(tokens.len() as i32));

            let sub_expressions = delimiters.clone()
                .zip(delimiters.skip(1))
                .map(|(left, right)| parse_expression(tokens[((left+1) as usize)..(right as usize)].to_vec()))
                .collect::<Result<Vec<RuleExpression<T>>, DefinitionError>>()?;
            Ok(RuleExpression::Alternatives(sub_expressions))
        }

        DefinitionToken::Identifier(_) | DefinitionToken::StringLiteral(_) 
        | DefinitionToken::Operator(Operator::Plus | Operator::Star | Operator::QuestionMark) => {
            let mut paren_nesting = 0;
            let mut curr_left_paren = 0;

            let mut sub_expressions = vec![];

            for i in 0..tokens.len() {
                if tokens[i] == DefinitionToken::LeftParenthesis {
                    paren_nesting += 1;
                    if paren_nesting == 1 {
                        curr_left_paren = i;
                    }
                }
                else if tokens[i] == DefinitionToken::RightParenthesis {
                    paren_nesting -= 1;
                    if paren_nesting == 0 {
                        sub_expressions.push(parse_expression(tokens[curr_left_paren + 1..i].to_vec())?);
                    }
                }
                else if paren_nesting == 0 {
                    match &tokens[i] {
                        DefinitionToken::Identifier(rule_name)
                            => sub_expressions.push(RuleExpression::RuleName(rule_name.clone())),
                        DefinitionToken::StringLiteral(literal)
                            => sub_expressions.push(literal_to_combination(literal.clone())?),
                        DefinitionToken::Operator(Operator::Plus) => {
                            let len = sub_expressions.len();  // appease borrow checker
                            sub_expressions[len - 1] = RuleExpression::OneOrMore(Box::new(sub_expressions[sub_expressions.len() - 1].clone()))
                        }
                        DefinitionToken::Operator(Operator::Star) => {
                            let len = sub_expressions.len();  
                            sub_expressions[len - 1] = RuleExpression::Many(Box::new(sub_expressions[sub_expressions.len() - 1].clone()))
                        }
                        DefinitionToken::Operator(Operator::QuestionMark) => {
                            let len = sub_expressions.len();  
                            sub_expressions[len - 1] = RuleExpression::Optional(Box::new(sub_expressions[sub_expressions.len() - 1].clone()))
                        }
                        _ => ()
                    }
                }
            }

            if sub_expressions.len() == 1 {
                return Ok(sub_expressions[0].clone());
            }
            
            Ok(RuleExpression::Concatenation(sub_expressions))
        }

        DefinitionToken::Operator(a) => Err(DefinitionError(format!("Bad operator {:?}", a))),

        DefinitionToken::LeftParenthesis => Err(DefinitionError("Subexpression is only parentheses".to_string())),

        DefinitionToken::RightParenthesis => Err(DefinitionError("Subexpression is only parentheses".to_string())),
    }
}

fn literal_to_combination<T: Token>(literal: String) -> Result<RuleExpression<T>, DefinitionError> {
    match T::token_sequence_from_literal(&literal) {
        Some(sequence) if sequence.len() == 0 => Err(DefinitionError("Matching no tokens is forbidden".to_string())),
        Some(sequence) if sequence.len() == 1 => Ok(RuleExpression::Terminal(sequence[0].clone())),
        Some(sequence) if sequence.len() > 1
            => Ok(RuleExpression::Concatenation(sequence.into_iter().map(|t| RuleExpression::Terminal(t)).collect())),
        Some(_) => Err(DefinitionError("Something went horribly wrong".to_owned())),
        None => Err(DefinitionError("Token type does not support converting string literals".to_owned())),
    }
}
fn validate_parser<T: Token>(parser: Parser<T>) -> Result<Parser<T>, DefinitionError> {
    // TODO!

    // Ensure all rules are spelled correctly
    // Ensure at most one modifier per literal (basically, ensure Definition Language Grammar)
    // Ensure no left recursion
    Ok(parser)
}


/* Tests */

#[cfg(test)]
mod tests {
    use super::*;

    use super::DefinitionToken::*;
    use super::Operator::*;
    use super::RuleExpression::*;

    #[test]
    fn test_tokenize() {
        assert_eq!(
            tokenize("foo : abc (Foo_bAr ham)   \t \n\n | (  egg|(cheese)) ;".to_string()),
            Ok(vec![
                Identifier("foo".to_string()),
                Operator(Colon),
                Identifier("abc".to_string()),
                LeftParenthesis,
                Identifier("Foo_bAr".to_string()),
                Identifier("ham".to_string()),
                RightParenthesis,
                Operator(Bar),
                LeftParenthesis,
                Identifier("egg".to_string()),
                Operator(Bar),
                LeftParenthesis,
                Identifier("cheese".to_string()),
                RightParenthesis,
                RightParenthesis,
                Operator(Semicolon)
            ])
        );
    }


    #[test]
    fn test_parse_rule() {
        // And also tokenize

        assert_eq!(
            parse_rule::<crate::CharToken>(&tokenize("Color : Number Number Number | HexString | ColorName".to_string()).unwrap()),
            Ok(("Color".to_string(), Alternatives(vec![
                Concatenation(vec![
                    RuleName("Number".to_string()),
                    RuleName("Number".to_string()),
                    RuleName("Number".to_string()),
                ]),
                RuleName("HexString".to_string()),
                RuleName("ColorName".to_string()),
            ])))
        );

        assert_eq!(
            parse_rule::<crate::CharToken>(&tokenize("Rule: (A | (B | (C) D) | ((E)))".to_string()).unwrap()),
            Ok(("Rule".to_string(), Alternatives(vec![
                RuleName("A".to_string()),
                Alternatives(vec![
                    RuleName("B".to_string()),
                    Concatenation(vec![
                        RuleName("C".to_string()),
                        RuleName("D".to_string()),
                    ])
                ]),
                RuleName("E".to_string()),
            ])))
        );

        assert_eq!(
            parse_rule::<crate::CharToken>(&tokenize(r#"Coordinate: ("A" | "B" | "C") " " ("1" | "2" | "3")"#.to_string()).unwrap()),
            Ok(("Coordinate".to_string(), Concatenation(vec![
                Alternatives(vec![
                    literal_to_combination("A".to_string()).unwrap(), // Actually not combinations btw
                    literal_to_combination("B".to_string()).unwrap(),
                    literal_to_combination("C".to_string()).unwrap(),
                ]),
                literal_to_combination(" ".to_string()).unwrap(),
                Alternatives(vec![
                    literal_to_combination("1".to_string()).unwrap(),
                    literal_to_combination("2".to_string()).unwrap(),
                    literal_to_combination("3".to_string()).unwrap(),
                ]),
            ])))
        );
    }

    #[test]
    fn test_define_parser() {
        /* Taken from https://en.wikipedia.org/wiki/Extended_Backus%E2%80%93Naur_form,
         * a simple Pascal like langauge. */

        let def = r#"
        # This is a comment!
        program : "PROGRAM" white_space identifier white_space 
                   "BEGIN" white_space 
                   (assignment ";" white_space)*
                   "END." ;
        identifier : alphabetic_character (alphabetic_character | digit)* ;
        number : "-"? digit+  ;
        string : "\"" (all_characters_no_quote)* "\"" ;
        assignment : identifier ":=" ( number | identifier | string ) ;
        alphabetic_character : "A" | "B" | "C" | "D" | "E" | "F" | "G"
                             | "H" | "I" | "J" | "K" | "L" | "M" | "N"
                             | "O" | "P" | "Q" | "R" | "S" | "T" | "U"
                             | "V" | "W" | "X" | "Y" | "Z" ;
        digit : "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
        white_space : " " | "\r\n" | "\n" | "\t";
        all_characters_no_quote : (alphabetic_character | white_space | digit) ; # Definitely incomplete...
        "#.to_string();

        let parser : Parser<crate::CharToken> = define_parser(def).expect("ok");

        ["program", "identifier", "number", "string", "assignment", "alphabetic_character", "digit", "white_space", "all_characters_no_quote"]
            .map(|name| {
                assert!(parser.rules.contains_key(name));
            });
    }
}
