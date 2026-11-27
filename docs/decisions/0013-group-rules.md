# 0013. The rules of each axiom group are listed in the spec

- Status: Accepted
- Date: 2026-11-27
- Decided by: Bill Page
- Spec: §3.4 (axiom groups and admissible sets)

## Context

Spec §3.4 listed the rules of the groups of $`A_P`$ and of `associativity` (§4.1, §4.1.1), but named the axioms of `commutativity`, `linear`, `powers`, `quotients`, `ring` and `field` only by the 2017 names (Doubles, Cancels, Squares, Divides) or by their normal forms. E1 of the Lean plan (soundness of every group) needs the rules themselves, so `lean/FricasSymbolic/Groups.lean` wrote them out (`Ladder`), read from the spec's tables and checked against the clauses of `src/algebra/gsexpr.spad` that each group enables (plan §6.1).

FriCAS agrees with that reading (run `20261127-153137-group-rules-probe`, `main` at `847db6d`, `GeneralSymbolicExpression(Integer, A)`):

| $`A`$ contains | Terms | Forms |
|---|---|---|
| `linear` | $`x/2`$, $`2x+3x`$, $`x-x`$, $`2(x+y)`$, $`0\cdot x`$, $`2(3x)`$ | `x/2`, `5*x`, `0`, `2*x+2*y`, `0`, `6*x` |
| `powers` | $`x\cdot x`$, $`x^2 x^3`$, $`(x^2)^3`$, $`(xy)^2`$, $`x^{-1}x^{-1}`$, $`x/x`$ | `x^2`, `x^5`, `x^6`, `x^2*y^2`, `(x^(-1))^2`, `x/x` |
| `quotients` | $`x/x`$, $`x^{-1}x^{-1}`$, $`(xy)^{-1}`$, $`x^2 x^{-3}`$ | `1`, `1/(x^2)`, `1/(x*y)`, `1/x` |
| `ring` | $`x(y+1)`$, $`x/2`$, $`(x+1)^2`$, $`x/y`$ | `x+x*y`, `(1/2)*x`, `2*x+x^2+1`, `x/y` |
| `field` | $`(x^2-1)/(x-1)`$, $`x/y+1/x`$ | `x+1`, `(y+x^2)/(x*y)` |

## Decision

Spec §3.4 lists the rules of every group, in the table "Axiom groups and admissible sets", so that the spec, the Spad code and Lean list the same rules. For the six groups above ($`n, m`$ numerals):

- `commutativity`: $`x+y \to y+x`$, $`x\cdot y \to y\cdot x`$.
- `linear`: $`x-y \to x+(-1)\cdot y`$, $`-x \to (-1)\cdot x`$, $`n\cdot x+m\cdot x \to (n+m)\cdot x`$, $`n\cdot(m\cdot x) \to (nm)\cdot x`$, $`n\cdot(x+y) \to n\cdot x+n\cdot y`$, $`0\cdot x \to 0`$.
- `powers`: $`x^m x^n \to x^{m+n}`$, $`(x^m)^n \to x^{mn}`$, $`(xy)^n \to x^n y^n`$, for $`m, n \ge 0`$.
- `quotients`: $`x/y \to x\cdot y^{-1}`$, and the rules of `powers` for all $`m, n \in \mathbb{Z}`$.
- `ring`: $`x\cdot(y+z) \to x\cdot y+x\cdot z`$, and $`x/q \to q^{-1}\cdot x`$ for a numeral $`q \ne 0`$.
- `field`: no rule of its own.

## Consequences

- The table states what the constructors promise; the code already does this (the run above), so no code changes.
- Lean's `Ladder` is the table, and E1 (`E1_ladder`) proves each rule sound where its left side is defined. R1–R3 and R5 of the plan prove that the rules of each rung generate exactly its free algebra.
- A change to a group's rules now changes the spec table, the Spad code and `Ladder` together.
