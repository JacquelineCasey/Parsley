
use std::marker::PhantomData;


pub struct Parser<T: Token> {
    pub(crate) _phantom: PhantomData<T>  // appease compiler by telling it we actually use T

    // TODO!
}

impl<T: Token> Parser<T> {
    pub(crate) fn new() -> Parser<T> {
        Parser { _phantom: std::marker::PhantomData }
    }
}

pub struct SyntaxTree<T: Token> {
    pub first: T
    // TODO!
}

pub trait Token {
    // TODO!
}

//

pub struct CharToken {
    pub num: i32
    // TODO!   
}

impl Token for CharToken {
    // TODO!
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
