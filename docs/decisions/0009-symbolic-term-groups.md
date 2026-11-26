# 0009. `SymbolicTerm(R, A)`, with axiom groups named in a list

- Status: Accepted (amended 2026-11-26, see admissibility below)
- Date: 2026-11-26
- Decided by: Bill Page
- Spec: §3.2, §3.4 (axiom groups and admissible sets)

## Context

Plan step 2 (decision 0008) makes design (II) reject axiom sets that are not admissible on the ladder. The 2017 `Symbolic(R, A)` names its axioms by domains combined with `join`. Most single-axiom domains (Cancels, Doubles, Squares, …) are parts of a rung, not admissible alone. Yet each checks itself on instantiation in `Symbolic(Integer, <itself>)`, and tests use such sets. Rejecting them in place would break the 2017 machinery before plan step 6 replaces it. Domain parameters are also hit by the FriCAS 1.4.0 `)lib` signature-ordering bug (the reason for loading the libraries twice).

## Options

1. Keep the 2017 axiom domains and `join` as the parameter, and map each combination to rungs by its categories.
2. A new constructor for design (II) whose parameter is a list of group names, `List Symbol`, as for `GeneralSymbolicExpression`, built alongside the old `Symbolic` until step 6.

## Decision

Option 2.

- **Name:** `SymbolicTerm(R, A)`, abbreviation `SYMTERM` (both free in FriCAS 1.4.0). "Term", equality modulo axioms, contrasts with "Expression", equality of value, in `GeneralSymbolicExpression(R, A)`.
- **One vocabulary of groups for both constructors** (spec §3.4):
  - from $`A_P`$ and §4.1.1: `identities`, `annihilation`, `involutions`, `numerals`, `associativity`;
  - new: `commutativity`, `linear` (P4), `powers` (M4), `quotients` (M5), `ring`, `field`.
- **Admissible:** every name known, and every required group present. Requirements are listed, not implied.
  *Amended 2026-11-26, when `ring` was implemented:* `ring` and `quotients` together also require `field`. Without it the normal forms are not canonical: under M5, $`(y+1)^{-1}`$ is a factor whose base is a sum, and distributivity rewrites $`(y+1)^{-1}(y+1)`$ to $`(y+1)^{-1}y + (y+1)^{-1}`$ instead of $`1`$.
- **Rejection:** both constructors reject inadmissible lists at instantiation, naming the problem. `GeneralSymbolicExpression` also rejects groups it does not implement yet; until now it silently ignored unknown names.

## Consequences

- No `join`, no axiom domains as parameters, and no `)lib` double loading for the new constructor.
- The 2017 `Symbolic(R, A)`, its axiom domains and `sexpr2.input` stay as they are until plan step 6, which retires them and ports the tests to `SymbolicTerm`.
- The vocabulary has no group for the 2017 AntiCommutative axiom, which is unsound for `Expression` and has no rung.
- Open for later: which FriCAS categories `SymbolicTerm(R, A)` claims for each admissible $`A`$ (plan §4).
