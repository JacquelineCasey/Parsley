use parsley::Token;


#[derive(Debug)]
struct CustomToken (String);

impl Token for CustomToken {
    fn matches(token_type: &str, token: &Self) -> Result<bool, parsley::ParseError> {
        match token_type {
            "NonKeyword" => 
                Ok(token.0 != "for" && token.0 != "while"),
            "KeywordFor" => 
                Ok(token.0 == "for"),
            "KeywordWhile" => 
                Ok(token.0 == "while"),
            _ => 
                Err(parsley::ParseError("Bad token type".to_string()))
        }
    }
}

impl std::fmt::Display for CustomToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}


#[test]
fn tests_work() {
    let parser = parsley::define_parser::<CustomToken>(r#"
        Program : Loop Loop Loop ;

        Loop : (_KeywordFor | _KeywordWhile) _NonKeyword+ ;
    "#.to_string()).expect("Defined successfully");

    let tokens = vec![
        CustomToken("for".to_string()),
        CustomToken("foo".to_string()),
        CustomToken("bar".to_string()),
        CustomToken("while".to_string()),
        CustomToken("baz".to_string()),
        CustomToken("for".to_string()),
        CustomToken("42".to_string()),
        CustomToken("123".to_string()),
    ];

    let tree = parser.parse_tokens(tokens, "Program").expect("Parsed successfully");

    assert_eq!(indoc::indoc!{"
    Syntax Tree {
        Program
            Loop
                token (for)
                token (foo)
                token (bar)
            Loop
                token (while)
                token (baz)
            Loop
                token (for)
                token (42)
                token (123)
    }"}, tree.to_string());

    let tokens = vec![
        CustomToken("for".to_string()),
        CustomToken("foo".to_string()),
        CustomToken("bar".to_string()),
        CustomToken("while".to_string()),
        CustomToken("baz".to_string()),
        CustomToken("for".to_string()),
        CustomToken("42".to_string()),
        CustomToken("123".to_string()),
        CustomToken("while".to_string()), // 4th while should fail
    ];

    parser.parse_tokens(tokens, "Program").expect_err("Parse should fail");
}