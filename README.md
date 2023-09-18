
Parsers are a perennial interest of mine, so I wrote one!

---

Look, realistically, I can't be trusted to keep the below documentation up to date.
However, I can be trusted to keep writing tests as I add and tweak features, so
consider poking around in the code to see how the tests work.

---

Feed in the definition of a parser using the "Parsley Definition Language", which
I made to look mostly like Backus-Naur form with some conveniences from Regex.

Here is an example definition. Pass this in as a string to `parsley::define_parser()`.

```text
# We've got comments!

# A definition is a series of rules. The left side is the name of a rule, and the
# right side defines what matches this rule. Rules end in a semicolon, so feel
# free to split rules across multiple lines

Rule : SubRule1 SubRule2 SubRule3;

# At some point, your rules should parse literal tokens. For now, the tokens are
# assumed to be characters, but I plan to extend the system to work on user defined
# tokens. For character tokens, you use string literals

SubRule1 : "Hello";

# Any rule can contains subrules. You can just put a literal next to anything else.
SubRule2 : Whitespace "World";

SubRule3 : "!\n#;  # We even have (simple) escapes! "\n\r\0\t\"\'\\" all work.

# Importantly, there can be many ways to match a rule, so we can write alternatives

Color : HexColor | RGBTriple ;

# Any element can be modified with a quantifier. ? means 0 or 1, * means 0 or more, + means 1 or more.
# The quantifiers bind tightly. Use as many parentheses as you need for grouping.

Whitespace : (" " | "\t" | "\n" | "\r\n")+ ;
OptWhitespace : Whitespace? ; 

# Here's another example

AddExpr : Term (("+" | "-") Term)* ;

# Recursion is allowed, so you can also do this
AddExpr2 : Term (("+" | "-") AddExpr2)? ;

# Unfortunately, left recursion is not allowed, it breaks the algorithm. This does not work:
AddExprBad : AddExprBad ("+" | "-") Term | Term ;

# It needs to be gauranteed that you consume some token before you get to a recursive rule.
# This means if you want to model left associative operations like '-', you are going
# to have to settle for one of the two other methods, and adjust the resultant syntax
# tree yourself.
```

I'm proud to say that I've designed the parser for this parser definition langauge
myself, and I've designed the actual parsing process mostly myself. I've taken
inspiration from various articles on Wikipedia, where I learned about the idea
of using a Graph Structured Stack to model multiple parsing processes at once. 
However, I did not read up on the actual algorithms that uses the GSS, I just 
cooked up my own.

**Update**: I've swapped out the GSS algorithm with a much prettier and demonstrably
more efficient recursive algorithm. It memoizes a lot, so it resembles a dynamic
programming approach, though the table is very jagged so I don't know if it technically
qualifies as DP.

I am unsure about the runtime - I haven't tried to determine this yet since I know
I still want to make some optimizations. Technically, its not gauranteed to terminate,
since left recursive formulae lead to infinite loops. These could be detected in 
the future though.

My main real concern is formula like "Rule*********". A preprocessor could help, but
you get the point - the parser will try to understand all the "paths" through this
formula, so long as it continues to see things that match "Rule".

However, for most sane formulas, it seems to run pretty fast.

One more thing - parsers are defined generically with respect to a token type. Lexerless
parsing is possible if you use the provided `CharToken` type. This allows you to match
strings of tokens using string literals in the definition language.

If you want to use your own token type, you need to implement the `Token` trait.
The main feature is the function `matches()` which takes a string token_type and a
token, and declares whether or not the token matches the token_type. Then, in the
parser definition, you can write the token type prefixed with an underscore in order
to match any token that passes the check. For example, if you write `matches()` so that
"any_lowercase_ascii" accepts a string token if it is all lowercase ascii, then you
have access to the special Terminal `_any_lowercase_ascii` that has this behavior.
Note that this is not treated as a Rule in the Syntax Tree, it is directly replaced
by the token it matches.

`CharToken` provides the useful behavior with string literals, which you can also
get for your custom tokens if you override `type_sequence_from_literal()`, which
returns a sequence of "token types" that will be passed into `matches()` later.
I suspect this will be of limited utility to authors of custom token types, but it
makes lexerless parsing with `CharToken` pleasant.

Parsing a sequence of tokens returns a syntax tree, which is also generic over the
token type.

```rust
pub enum SyntaxTree<T: Token> {
    RuleNode {rule_name: String, subexpressions: Vec<SyntaxTree<T>>},
    TokenNode (T)
}
```

The syntax tree only contains rule nodes and terminals (tokens), it does not contain
any other features corresponding to alternatives or quantifiers or so on. Also, due
to a quirk in the current algorithm, if a rule is processed but parses no tokens, it
is not included in the final syntax tree.

**Update**: This behavior has changed recently. Now, if a rule is satisfied despite
parsing no tokens, it will still be included in the final tree. This means there is
a difference between `Outer: Inner?; Inner: A;` and `Outer: Inner;  Inner: A?`. They
recognize the same language, but in the first case the Inner rule will not appear in
the output if it didn't get to parse an `A`, where as in the second case it will appear
in the output either way. The Many operator `*` behaves similarly.

It is intended for users to write code that transforms this concrete syntax tree
into an abstract syntax tree. This may require some careful consideration in cases
where subrules can parse no tokens, and so may or may not be in the final tree. Additionally,
if a subrule or a group it is contained in was quantified, it may appear 0 or many times
in the final tree. The point of the parser is to organize the tokens in a hierarchy,
anything more would require me to make significant assumptions on the end user's
use case.

Happy parsing!

---

To see Parsley at scale, see the programming language I've been writing here:
https://github.com/jackcasey067/nom/.

