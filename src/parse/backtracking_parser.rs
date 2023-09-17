
use crate::{Token, define::RuleExpression};
use super::{Parser, ParseError, SyntaxTree};

use std::collections::{HashMap, BTreeSet};

use by_address::ByAddress;

#[derive(Clone, Debug, PartialEq, PartialOrd, Eq, Ord)]
struct Continuation (usize); // usize is the next token to parse


pub fn backtracking_parse<T: Token>(parser: &Parser<T>, tokens: &[T], start_rule: &str) -> Result<SyntaxTree<T>, ParseError> {
    let start_expr = RuleExpression::RuleName(start_rule.to_string());

    let mut memo_map: HashMap<(ByAddress<&RuleExpression>, usize), Vec<Continuation>> = HashMap::new();

    parse_expr(parser, tokens, 0, &start_expr, &mut memo_map)?;

    if memo_map[&(ByAddress(&start_expr), 0)].contains(&Continuation (tokens.len())) {
        dbg!("Success. Now we must build the tree");
        todo!()
    }
    else {
        return Err(ParseError("Failed to parse".into()));
    }
}

fn parse_expr<'a, T: Token>(
    parser: &'a Parser<T>, 
    tokens: &[T], 
    token_index: usize, 
    expr: &'a RuleExpression,
    memo_map: &mut HashMap<(ByAddress<&'a RuleExpression>, usize), Vec<Continuation>>
) -> Result<(), ParseError> {

    if memo_map.contains_key(&(ByAddress(expr), token_index)) {
        return Ok(());
    }

    let mut continuations = vec![];

    match expr {
        RuleExpression::Terminal(term) => {
            if token_index < tokens.len() && T::matches(term, &tokens[token_index])? {
                continuations.push(Continuation (token_index + 1));
            }
        },
        RuleExpression::RuleName(rule_name) => {
            match parser.rules.get(rule_name) {
                Some(rule_expr) => {
                    parse_expr(parser, tokens, token_index, rule_expr, memo_map)?;
                    continuations = memo_map[&(ByAddress(rule_expr), token_index)].clone();
                }
                None => return Err(ParseError("Rule not found".to_string())),
            }
        },
        RuleExpression::Concatenation(exprs) => {
            let mut curr_pass = BTreeSet::new();  // This needs some work
            curr_pass.insert(Continuation (token_index));

            for expr in exprs {
                let mut next_pass = BTreeSet::new();
                for Continuation (index) in curr_pass.iter() {
                    parse_expr(parser, tokens, *index, expr, memo_map)?;
                    next_pass.append(&mut memo_map[&(ByAddress(expr), *index)].clone().into_iter().collect());
                }

                curr_pass = next_pass;
            }

            continuations = curr_pass.into_iter().collect();
        },
        RuleExpression::Alternatives(exprs) => {
            for expr in exprs {
                parse_expr(parser, tokens, token_index, expr, memo_map)?;

                continuations.append(&mut memo_map[&(ByAddress(expr), token_index)].clone());
            }
        },
        RuleExpression::Optional(expr) => {
            continuations.push(Continuation (token_index));

            parse_expr(parser, tokens, token_index, expr, memo_map)?;
            continuations.append(&mut memo_map[&(ByAddress(&**expr), token_index)].clone());
        },
        RuleExpression::Many(expr) => {
            continuations.push(Continuation (token_index));

            let mut curr_pass = BTreeSet::new();  // This needs some work
            curr_pass.insert(Continuation (token_index));

            loop {
                let mut next_pass = BTreeSet::new();
                for Continuation (index) in curr_pass.iter() {
                    if *index == tokens.len() {
                        continue;
                    }

                    parse_expr(parser, tokens, *index, expr, memo_map)?;

                    next_pass.append(&mut memo_map[&(ByAddress(&**expr), *index)].clone().into_iter().collect());
                }

                for cont in next_pass.clone() {
                    continuations.push(cont);
                }

                if curr_pass.len() == 0 {
                    break;
                }

                curr_pass = next_pass;
            };
        },
        RuleExpression::OneOrMore(expr) => {
            let mut curr_pass = BTreeSet::new();  // This needs some work
            curr_pass.insert(Continuation (token_index));

            loop {
                let mut next_pass = BTreeSet::new();
                for Continuation (index) in curr_pass.iter() {
                    if *index == tokens.len() {
                        continue;
                    }

                    parse_expr(parser, tokens, *index, expr, memo_map)?;

                    next_pass.append(&mut memo_map[&(ByAddress(&**expr), *index)].clone().into_iter().collect()
                    );
                }

                for cont in next_pass.clone() {
                    continuations.push(cont);
                }

                if curr_pass.len() == 0 {
                    break;
                }

                curr_pass = next_pass;
            };
        }
    }

    memo_map.insert((ByAddress(expr), token_index), continuations);
    Ok(())
}
