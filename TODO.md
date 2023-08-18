
- Add support for escapes in parser definition string literals.
- Improve definition parse efficiency by using slices more than vectors.
- Add useful builtins (especially whitespace, lowercase, uppercase, numbers).
- Actually do parser validation.
- Improve actual parse efficiency by using slices more than vectors
- Handle ambiguous parse

- Maybe we should seperate Tokens from Token recognizers, and recognizers could
  accept or reject tokens arbitrarily. This makes something like "all unicode 
  codepoints except '\' and '"' feasible to write and run. 

- Nota Bene: With current algorithm, rules can be skipped in final parse tree
  if surrounding Optional or Many operators consume no tokens. I guess this is 
  ultimately fine, afterall the alternative seems to be letting certain recursive 
  formulae have infinite parse trees: " Expr : Term Expr? "

PS: Here is a C grammar for when we really want to stress test:
- https://cs.wmich.edu/~gupta/teaching/cs4850/sumII06/The%20syntax%20of%20C%20in%20Backus-Naur%20form.htm