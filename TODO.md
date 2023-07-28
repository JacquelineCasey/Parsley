
- Add support for escapes in parser definition string literals.
- Improve definition parse efficiency by using slices more than vectors.
- Add useful builtins (especially whitespace, lowercase, uppercase, numbers).
- Actually do parser validation.
- Improve actual parse efficiency by using slices more than vectors
- Handle ambiguous parse

- Nota Bene: With current algorithm, rules can be skipped in final parse tree
  if surrounding Optional or Many operators consume no tokens. I guess this is 
  ultimately fine, afterall the alternative seems to be letting certain recursive 
  formulae have infinite parse trees: " Expr : Term Expr? "