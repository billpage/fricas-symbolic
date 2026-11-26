# 0002. Presentation axioms for `SymbolicPair`

- Status: Accepted (default axiom set); associative flattening left open
- Date: 2026-11-25
- Decided by: Bill Page
- Spec: §4.1, §5, §7 (items 2 and 3)

## Context

Results built by FriCAS's algorithms carry untidy written forms, e.g. the closed form of $`\sum_{x=1}^{10} x`$ built from `(1+10-1)*(...)`. Which rewrites may the pair domain apply automatically without losing what the user wrote (G1)?

## Options

1. No axioms: forms exactly as built.
2. Identities only (Id): remove $`0+x`$, $`1\cdot x`$, $`x^1`$, …; numerals are not folded, so `1+2` stays.
3. $`A_P`$ = Id ∪ Ann ∪ Inv ∪ Num: also $`0\cdot x \to 0`$, $`-(-x)\to x`$, $`1/(1/x)\to x`$, and evaluation of operations on numerals.
4. Larger sets (commutativity, collecting like terms): reorder or merge what was written, and need AC rewriting (spec §4.2).

## Decision

The axiom set is a parameter, `SymbolicPair(R, A)`, so every option above except 4 is available. **`SymbolicExpression(R)` uses $`A_P`$ = Id ∪ Ann ∪ Inv ∪ Num (option 3).** Theorem 3 shows it sound, terminating and confluent.

The deciding comparison (run `ASUS-20261125-221244-numerals-default-compare`, FriCAS 1.4.0): with $`A_P`$, `sum(x, 'x=1..10)` displays `55`; with `[identities]` only it displays `(1+10-1)*(1/2+1/2*(1+10-1))-(1-1)*(1/2+1/2*(1-1))`. The values are equal either way. Num cannot tell numerals typed by the user from numerals built inside an algorithm, so a default must favour one; algorithm-built numeral arithmetic is far more common, and `SymbolicPair(R, [identities])` keeps typed arithmetic such as `1+2` for the cases where it matters (G3).

Considered and not chosen: a default without Num plus an on-request `tidy` operation (closer to the 2016 "no automatic simplifications", one more step after every algorithm call).

Still open: whether associative chains are flattened for display (spec §7, item 3).

## Consequences

- `SymbolicExpression(R)` displays `1+2` as `3`; `SymbolicPair(R, [identities])` keeps `1+2` for G3-style use.
- No rule reorders or regroups user input.
