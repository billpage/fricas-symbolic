# 0002. Presentation axioms for `SymbolicPair`

- Status: Proposed
- Date: 2026-11-25
- Spec: §4.1, §5, §7 (items 2 and 3)

## Context

Results built by FriCAS's algorithms carry untidy written forms, e.g. the closed form of $`\sum_{x=1}^{10} x`$ built from `(1+10-1)*(...)`. Which rewrites may the pair domain apply automatically without losing what the user wrote (G1)?

## Options

1. No axioms: forms exactly as built.
2. Identities only (Id): remove $`0+x`$, $`1\cdot x`$, $`x^1`$, …; numerals are not folded, so `1+2` stays.
3. $`A_P`$ = Id ∪ Ann ∪ Inv ∪ Num: also $`0\cdot x \to 0`$, $`-(-x)\to x`$, $`1/(1/x)\to x`$, and evaluation of operations on numerals.
4. Larger sets (commutativity, collecting like terms): reorder or merge what was written, and need AC rewriting (spec §4.2).

## Proposal

The axiom set is a parameter, `SymbolicPair(R, A)`, so every option above except 4 is available. $`A_P`$ is the proposed default for `SymbolicExpression(R)`: Theorem 3 shows it sound, terminating and confluent, and it gives `55` for the sum. Open for decision: whether the default folds numerals (option 3) or not (option 2), and whether associative chains are flattened for display (spec §7, item 3).

## Consequences (if accepted)

- `SymbolicExpression(R)` displays `1+2` as `3`; `SymbolicPair(R, [identities])` keeps `1+2` for G3-style use.
- No rule reorders or regroups user input.
