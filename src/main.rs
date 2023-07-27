
fn main() {
    let p : parsley::Parser<parsley::CharToken> = parsley::define_parser("abcd".to_owned()).expect("Not an error?");
    let _syntax_tree = p.parse_string("my custom language!".to_owned(), "plink"); // Concrete Syntax Tree

    // Code to specialize concrete syntax tree into AST.

    // Code to turn AST into bytecode / assembly / behavior / etc.
}
