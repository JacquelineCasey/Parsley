use super::*;

use indoc::indoc;


#[test]
fn concatenation() {
    let parser: Parser<CharToken> = crate::define::define_parser(r##"
        Start: A B C ;
        A: "a" ;
        B: "b" ;
        C: "c" ;
    "##).expect("Parser definition ok");

    let tree = parser
        .parse_string("abc", "Start")
        .expect("No error");

    assert_eq!(tree.to_string(), indoc! {"
    Syntax Tree {
        Start
            A
                token (a)
            B
                token (b)
            C
                token (c)
    }"});
}

#[test]
fn color() {
    let parser: Parser<CharToken> = crate::define::define_parser(r##"
        Color: RGB | Hex ;
        RGB: "Color"  " "  "(" Num " " Num " " Num ")" ;
        Hex: "#" HexNum HexNum HexNum HexNum HexNum HexNum ;
        Num: "0" | "1" | "2" | "3" ; # Proof of concept
        HexNum: Num | "A" | "B" | "C" ; # Proof of concept
    "##).expect("Parser definition ok");

    let tree = parser
        .parse_string("Color (1 3 0)", "Color")
        .expect("No error");

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

    let tree = parser
        .parse_string("#ABC012", "Color")
        .expect("No error");

    println!("{}", tree);

    assert_eq!(tree.to_string(), indoc! {"
        Syntax Tree {
            Color
                Hex
                    token (#)
                    HexNum
                        token (A)
                    HexNum
                        token (B)
                    HexNum
                        token (C)
                    HexNum
                        Num
                            token (0)
                    HexNum
                        Num
                            token (1)
                    HexNum
                        Num
                            token (2)
        }"}
    );
}

#[test]
fn optional() {
    let parser: Parser<CharToken> = crate::define::define_parser(r##"
        Num : "1" | "2" | "3" | "4" ; # Incomplete ofc
        AddExpr: Num ("+" AddExpr)? ;
    "##).expect("Parser definition ok");

    // Modifiers bind tightly, so this should fial
    parser.parse_string("12", "AddExpr").expect_err("Should fail");

    let tree = parser
        .parse_string("1+2+3+4", "AddExpr")
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
fn many() {
    let parser: Parser<CharToken> = crate::define::define_parser(r##"
        Rule : ManyA "b"+ ManyC "d"+;
        ManyA: "a"*;
        ManyC: "c"*; 
    "##).expect("Parser definition ok");

    let tree = parser
        .parse_string("abbdddd", "Rule")
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
