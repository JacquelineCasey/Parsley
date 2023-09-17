
mod gss_parser;

#[cfg(test)]
mod tests;


use gss_parser::gss_parse_tokens;

use crate::define::RuleExpression;

use std::collections::HashMap;


/* Public Interface */

pub struct Parser<T: Token> {
    pub(crate) phantom: std::marker::PhantomData<T>,  // Act like we own a T
    pub(crate) rules: HashMap<String, RuleExpression>
}

#[derive(Debug)]
pub enum SyntaxTree<T: Token> {
    RuleNode {rule_name: String, subexpressions: Vec<SyntaxTree<T>>},
    TokenNode (T)
}

impl<T: Token + std::fmt::Display> std::fmt::Display for SyntaxTree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Syntax Tree {")?;
        self.helper_fmt(1, f)?;
        f.write_str("\n}")
    }
}

impl<T: Token + std::fmt::Display> SyntaxTree<T> {
    fn helper_fmt(&self, level: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("\n")?;
        f.write_str(&" ".repeat(level * 4))?;
        match self {
            SyntaxTree::RuleNode {rule_name, subexpressions} => {
                f.write_str(rule_name)?;
                for expr in subexpressions {
                    expr.helper_fmt(level + 1, f)?;
                    // f.write_str("\n")?
                }
                Ok(())
            },
            SyntaxTree::TokenNode(token) => {
                f.write_str(&format!("token ({token})"))
            }
        }

    }
}

#[derive(Debug)]
pub struct ParseError (pub String);

/* Represents a token.
 *
 * This is a trait so that users can define parsers over specific alphabets beyond
 * what we support out of the box. It can also be useful to allow a language to
 * provide detailed error messages, or simply to run faster (tokenization is often O(n),
 * and most parsing algorithms are O(n^3) worst case, so preprocessing to shorten the
 * list of tokens can be useful).
 * 
 * Tokens need not track their own location in the source file, that will eventually
 * be done by the parser. */
pub trait Token : Sized + std::fmt::Debug {
    /* If the parser definition contains a rule with a name starting with an underscore,
     * e.g. "_ascii_lower", then instead of acting as a normal rule, it will act
     * as a special rule that dispatches to this function.
     * 
     * This function receives the token type (e.g. "ascii_lower") without the leading
     * underscore. It should return true if the parser accepts the current token.
     * 
     * It is permitted to return ParseError if something goes wrong. For example, 
     * receiving an unknown token_type. 
     * 
     * Note: if you also override type_sequence_from_literal, then you define which
     * token_types are fed into this function. */
    fn matches(token_type: &str, token: &Self) -> Result<bool, ParseError>;

    /* Converts a literal string in the definition language into a sequence of
     * strings that are later fed into match() as token_type, one by one.
     * 
     * Notably, CharToken provides this feature as the main way to match terminals. 
     * Most custom token types will not need to provide this. */
     fn type_sequence_from_literal(_literal: &str) -> Option<Vec<String>> {
        None
    }
}

/* A token that represents  */
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CharToken {
    /* Unlike most tokens, a single field is sufficient, as all token_types have
     * a single possible value (the character). */
    pub token_type: String,  // String for annoying ownership reasons. Will validate that its a single character.
}

impl Token for CharToken {
    fn type_sequence_from_literal(literal: &str) -> Option<Vec<String>> {
        return Some(literal.chars().map(|c| c.to_string()).collect())
    }

    /* Simplest possible match behavior */
    fn matches(token_type: &str, token: &Self) -> Result<bool, ParseError> {
        Ok(token_type == token.token_type)
    }
}

impl std::fmt::Display for CharToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.token_type)
    }
}

impl<T: Token> Parser<T> {
    pub fn parse_tokens(&self, tokens: Vec<T>, start_rule: &str) -> Result<SyntaxTree<T>, ParseError> {
        gss_parse_tokens(self, tokens, start_rule)

        // recursive_parse_tokens();
    }
}

impl Parser<CharToken> {
    pub fn parse_string(&self, input: &str, start_rule: &str) -> Result<SyntaxTree<CharToken>, ParseError> {
        let tokens = input.chars()
            .map(|ch| CharToken { token_type: ch.to_string() })
            .collect();
        self.parse_tokens(tokens, start_rule)
    }
}

