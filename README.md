
Parsers are a perennial interest of mine, so I wrote one!

Feed in the definition of a parser using the "Parsley Definition Language", which
I made to look mostly like Backus-Naur form with some conveniences from Regex.

Here is an example definition. Pass this in as a string to `parsley::define_parser()`.

```text
# We've got comments!

# A definition is a series of rules. The left side is the name of a rule, and the
# right side defines what matches this rule. Rules end in a semicolon, so feel
# free to split rules across multiple lines

Rule := SubRule1 SubRule2 SubRule3;

# At some point, your rules should parse literal tokens. For now, the tokens are
# assumed to be characters, but I plan to extend the system to work on user defined
# tokens. For character tokens, you use string literals

SubRule1 := "Hello";

# Any rule can contains subrules. You can just put a literal next to anything else.
SubRule2 := OptWhitespace "World";

SubRule3 := "!\n#;  # We even have (simple) escapes! "\n\r\0\t\"\'\\" all work.

# Importantly, there can be many ways to match a rule, so we can write alternatives

Color := HexColor | RGBTriple ;

# Any element can be modified with a quantifier. ? means 0 or 1, * means 0 or more, + means 1 or more.
# The quantifiers bind tightly. Use as many parentheses as you need for grouping.
AddExpr := Term (("+" | "-") Term)* ;

# Recursion is allowed, so you can also do this
AddExpr2 := Term (("+" | "-") AddExpr2)? ;

# Unfortunately, left recursion is not allowed, it breaks the algorithm. This does not work:
AddExprBad := AddExprBad ("+" | "-") Term | Term ;

# This means if you want to model left associative operations like '-', you are going
# to have to settle for one of the two other methods, and adjust the resultant syntax
# tree yourself.
```



