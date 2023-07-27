
use crate::define::RuleExpression;

use std::collections::HashMap;

pub struct Parser<T: Token> {
    pub(crate) rules: HashMap<String, RuleExpression<T>>
}

pub struct SyntaxTree<T: Token> {
    pub first: T
    // TODO!
}

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
    token_type: char,  
}

impl Token for CharToken {
    fn token_sequence_from_literal(literal: &str) -> Option<Vec<Self>> {
        return Some(literal.chars().map(|c| CharToken {token_type: c}).collect())
    }
}

impl<T: Token> Parser<T> {
    pub fn parse_tokens(&self, _tokens: Vec<T>) -> SyntaxTree<T> {
        todo!();
    }
}

impl Parser<CharToken> {
    pub fn parse_string(&self, _input: String) -> SyntaxTree<CharToken> {
        let _char_token_vec: Vec<CharToken> = todo!();  // using _input
        //  self.parse_tokens(char_token_vec)
    }
}
