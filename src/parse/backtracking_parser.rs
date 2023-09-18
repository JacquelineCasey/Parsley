
use crate::{Token, define::RuleExpression};
use super::{Parser, ParseError, SyntaxTree};

use std::collections::HashMap;
use std::rc::Rc;

use by_address::ByAddress;


#[derive(Clone, Debug)]
struct Continuation<'a, T: Token>(usize, Vec<Rc<IntermediateSyntaxTree<'a, T>>>); // usize is the next token to parse

impl<'a, T: Token> PartialEq for Continuation<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1.iter().zip(other.1.iter()).all(|(a, b)| Rc::ptr_eq(a, b))
    }
}

impl<'a, T: Token> PartialOrd for Continuation<'a, T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<'a, T: Token> Eq for Continuation<'a, T> {}
impl<'a, T: Token> Ord for Continuation<'a, T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

// Wrapper around the stacker library to ensure the stack keeps growing.
// It will eventually move onto the heap.
pub fn stack_safe<R, F: FnOnce() -> R>(callback: F) -> R {
    stacker::maybe_grow(32 * 1024, 1024 * 1024, || {
        callback()
    })
}

pub fn backtracking_parse<T: Token>(parser: &Parser<T>, tokens: &[T], start_rule: &str) -> Result<SyntaxTree<T>, ParseError> {
    let start_expr = RuleExpression::RuleName(start_rule.to_string());

    let mut memo_map: HashMap<(ByAddress<&RuleExpression>, usize), Vec<Continuation<T>>> = HashMap::new();

    parse_expr(parser, tokens, 0, &start_expr, &mut memo_map)?;

    if let Some(Continuation (_, trees)) = memo_map[&(ByAddress(&start_expr), 0)].clone().into_iter()
        .filter(|Continuation (i, _)| *i == tokens.len())
        .next() {
        
        Ok(intermediate_to_final(Rc::clone(&trees[0])))
    }
    // TODO - also handle ambiguous parse. (?)
    else {
        Err(ParseError("Failed to parse".into()))
    }
}

fn parse_expr<'a, T: Token>(
    parser: &'a Parser<T>, 
    tokens: &[T], 
    token_index: usize, 
    expr: &'a RuleExpression,
    memo_map: &mut HashMap<(ByAddress<&'a RuleExpression>, usize), Vec<Continuation<'a, T>>>
) -> Result<(), ParseError> {

    if memo_map.contains_key(&(ByAddress(expr), token_index)) {
        return Ok(());
    }

    let mut continuations = vec![];

    match expr {
        RuleExpression::Terminal(term) => {
            if token_index < tokens.len() && T::matches(term, &tokens[token_index])? {
                continuations.push(Continuation (
                    token_index + 1,
                    vec![Rc::new(IntermediateSyntaxTree::TokenNode(tokens[token_index].clone()))]
                ));
            }
        },
        RuleExpression::RuleName(rule_name) => {
            match parser.rules.get(rule_name) {
                Some(rule_expr) => {
                    stack_safe(|| parse_expr(parser, tokens, token_index, rule_expr, memo_map))?;
                    continuations = memo_map[&(ByAddress(rule_expr), token_index)].clone().into_iter()
                        .map(|Continuation (a, subtrees)| 
                            Continuation (a, vec![Rc::new(IntermediateSyntaxTree::RuleNode { rule_name, subexpressions: subtrees })])
                        )
                        .collect()
                }
                None => return Err(ParseError("Rule not found".to_string())),
            }
        },
        RuleExpression::Concatenation(exprs) => {
            let mut curr_pass = Vec::new();  // This needs some work
            curr_pass.push(Continuation (token_index, vec![]));

            // This is the computational bottleneck I think...
            for expr in exprs {
                let mut next_pass = Vec::new();
                for Continuation (index, old_trees) in curr_pass.iter() {
                    stack_safe(|| parse_expr(parser, tokens, *index, expr, memo_map))?;
                    next_pass.append(&mut memo_map[&(ByAddress(expr), *index)].clone().into_iter()
                        .map(|Continuation (i, subtrees)| {
                            let mut final_trees = old_trees.clone();
                            final_trees.append(&mut subtrees.clone());

                            Continuation (i, final_trees)
                        })
                        .collect()
                    );
                }

                curr_pass = next_pass;
            }

            continuations = curr_pass.into_iter().collect();
        },
        RuleExpression::Alternatives(exprs) => {
            for expr in exprs {
                stack_safe(|| parse_expr(parser, tokens, token_index, expr, memo_map))?;

                continuations.append(&mut memo_map[&(ByAddress(expr), token_index)].clone());
            }
        },
        RuleExpression::Optional(expr) => {
            continuations.push(Continuation (token_index, vec![]));

            stack_safe(|| parse_expr(parser, tokens, token_index, expr, memo_map))?;
            continuations.append(&mut memo_map[&(ByAddress(&**expr), token_index)].clone());
        },
        RuleExpression::Many(expr) => {
            continuations.push(Continuation(token_index, vec![]));

            let mut curr_pass = Vec::new();  // This needs some work
            curr_pass.push(Continuation (token_index, vec![]));

            // Another bottleneck
            loop {
                let mut next_pass = Vec::new();
                for Continuation (index, old_trees) in curr_pass.iter() {
                    stack_safe(|| parse_expr(parser, tokens, *index, expr, memo_map))?;
                    next_pass.append(&mut memo_map[&(ByAddress(&**expr), *index)].clone().into_iter()
                        .map(|Continuation (i, subtrees)| {
                            let mut final_trees = old_trees.clone();
                            final_trees.append(&mut subtrees.clone());

                            Continuation (i, final_trees)
                        })
                        .collect()
                    );

                    continuations.append(&mut next_pass.clone());
                }

                if next_pass.is_empty() {
                    break;
                }

                curr_pass = next_pass;
            }
        },
        RuleExpression::OneOrMore(expr) => {
            let mut curr_pass = Vec::new();  // This needs some work
            curr_pass.push(Continuation (token_index, vec![]));

            // Another bottleneck
            loop {
                let mut next_pass = Vec::new();
                for Continuation (index, old_trees) in curr_pass.iter() {
                    stack_safe(|| parse_expr(parser, tokens, *index, expr, memo_map))?;
                    next_pass.append(&mut memo_map[&(ByAddress(&**expr), *index)].clone().into_iter()
                        .map(|Continuation (i, subtrees)| {
                            let mut final_trees = old_trees.clone();
                            final_trees.append(&mut subtrees.clone());

                            Continuation (i, final_trees)
                        })
                        .collect()
                    );

                    continuations.append(&mut next_pass.clone());
                }

                if next_pass.is_empty() {
                    break;
                }

                curr_pass = next_pass;
            }
        }
    }

    memo_map.insert((ByAddress(expr), token_index), continuations);
    Ok(())
}


#[derive(Clone, Debug)]
enum IntermediateSyntaxTree<'a, T: Token> { // Vec contains Rc's, to be removed later.
    RuleNode {rule_name: &'a str, subexpressions: Vec<Rc<IntermediateSyntaxTree<'a, T>>>},
    TokenNode (T)
}

fn intermediate_to_final<T: Token>(root: Rc<IntermediateSyntaxTree<T>>) -> SyntaxTree<T> {
    match (*root).clone() {
        IntermediateSyntaxTree::RuleNode {rule_name, subexpressions} => 
            SyntaxTree::RuleNode {
                rule_name: rule_name.to_string(), 
                subexpressions: subexpressions.into_iter()
                    .map(|rc_refcell_tree| intermediate_to_final(rc_refcell_tree))
                    .collect()
            },
        IntermediateSyntaxTree::TokenNode(token) => SyntaxTree::TokenNode(token),
    }
}
