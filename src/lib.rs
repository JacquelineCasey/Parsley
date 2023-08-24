// I use `cargo clippy -- -D clippy::pedantic`
#![allow(
    clippy::missing_errors_doc,  // Docs? Lol.
    clippy::must_use_candidate,  // What?
    clippy::module_name_repetitions,  // Maybe a little weird but I'm bad at naming things.
    clippy::cast_sign_loss,  // Allow by default, not with -D clippy::pedantic
    clippy::cast_possible_truncation,  // I know
    clippy::cast_possible_wrap,  // I know
)]

mod define;

pub use define::define_parser;


mod parse;

pub use parse::Parser;
pub use parse::ParseError;
pub use parse::SyntaxTree;
pub use parse::Token;
pub use parse::CharToken;


mod utils;
