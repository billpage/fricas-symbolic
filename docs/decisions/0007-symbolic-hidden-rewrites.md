# 0007. `SymbolicExpression` is rebuilt; `Symbolic` rewrites only by its axioms

- Status: Accepted
- Date: 2026-11-26
- Decided by: Bill Page
- Spec: §4.2, §5; note [2026-11-26-commutativity-and-hidden-rewrites](../notes/2026-11-26-commutativity-and-hidden-rewrites.md) §3–4 (step 1)

## Context

Two things were left from the 2017 code. `SymbolicExpression(R)` was `Symbolic(R, <axiom set>)` with a semantic `=` grafted on, the mixed equality that decision 0001 rejects. And `Symbolic(R, A)` applied nine rewrites even with no axioms (spec §4.2), against G3.

## Decision

1. `SymbolicExpression(R)` is `GeneralSymbolicExpression(R, A_P)`, defined in `src/algebra/gsexpr.spad` (decisions 0002, 0006). The 2017 domain of that name is removed; its axiom set stays available as `Symbolic(R, join(...))` (written out in `src/input/sexpr2.input`).
2. In `Symbolic(R, A)`:
   - **removed:** repeated doubling and repeated squaring for `PositiveInteger` arguments, $`x^{-n} \to 1/x^n`$ and $`x^{p/q} \to \mathrm{nthRoot}(x,q)^p`$; multiples and powers build their node;
   - **tied to axioms:** $`0\cdot x \to 0`$ to a new axiom `Annihilation`; $`0-y \to -y`$ to `LeftIdentity`; $`x^1 \to x`$ and $`x^0 \to 1`$ (found hidden in the old power code) to `RightIdentity`; $`-(x-y) \to y-x`$, $`-(x+y) \to (-x)+(-y)`$ and $`1/(x/y) \to y/x`$ to `Inverse`, as an interim home until the ladder of the note (§2.2) replaces the 2017 axiom categories.
3. The exponent and coefficient arithmetic inside the Divides, Squares, Cancels and Doubles rules writes $`x^1, x^0, x\cdot 1, x\cdot 0`$ as $`x, 1, x, 0`$. These are part of those rules' results, not separate rewrites.

## Consequences

- `Symbolic(Integer, None)` keeps all nine inputs of spec §4.2 as written (test case "G3" in `sexpr2.input`).
- Kurt Pagani's suite now runs on `Symbolic` with the 2017 axiom set plus `Annihilation`, with `Symbolic`'s own syntactic `=`. Its tests that meant equality of value compare in `Expression`.
- **Finding:** with that syntactic `=`, applying the rule set of the trigonometric example (`rc rs expr`) does not terminate, on `main` before these changes as well. The old `SymbolicExpression` avoided it only through its semantic `=`. Rewrite rules over `Symbolic` need the AC matcher of the note (§2.3, item 5); on `SymbolicExpression` the example works (`gsexpr.input`).
