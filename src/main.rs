
fn main() {
    let parser : parsley::Parser<parsley::CharToken> = parsley::define_parser(r#"
        PlusMinusExpr :  MultDivExpr  (("+" | "-") MultDivExpr)* ;
        MultDivExpr : AtomicExpr (("*" | "/") AtomicExpr)* ;
        AtomicExpr : OptWhitespace (Literal | "(" PlusMinusExpr ")" ) OptWhitespace;
        Literal : "a" | "b" | "c" | "d" ;
        OptWhitespace : (" " | "\t" | "\n" | "\r\n" | "\'" | "\"" )* ; # Yeah the quotes are kinda weird
    "#).expect("Not an error?");
    
    let tree = parser.parse_string("   ( a + b)*( c +  a  * \n\n\n\t\t '''\"\"\" (  d )+ c  )", "PlusMinusExpr")
        .expect("Good parse");
    println!("{tree}");

    /* Nota Bene: The syntax tree this produces is pretty heinous, but I expect that
     * in a real language the compiler would come along and specialize the syntax tree
     * (concrete syntax tree) into an abstract syntax tree, removing unnecessary
     * layers and preparing for analysis and compilation.
     */
}
