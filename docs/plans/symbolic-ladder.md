# Plan: design (II) on the ladder of normalisers: `SymbolicTerm(R, A)`

*2026-11-26. Planning document; implements decision [0008](../decisions/0008-ladder-of-normalisers.md) and spec §3.4–3.5. Status: steps 1–5 and 7 done; step 6 remains.*

## 1. Goal

Build `SymbolicTerm(R, A)` (decision [0009](../decisions/0009-symbolic-term-groups.md)) from normalisers that build the canonical forms of spec §3.4, one rung at a time, and then retire the 2017 `Symbolic(R, A)` in `src/algebra/sexpr.spad`. At every step `make check` passes, and each landed rung has tests of (N1) and (N2).

## 2. Read first

Spec §2–3 (especially §3.4, §3.5), §4.2; decisions 0001, 0007, 0008; the note [2026-11-26-commutativity-and-hidden-rewrites](../notes/2026-11-26-commutativity-and-hidden-rewrites.md); `src/algebra/sexpr.spad` (`Symbolic`, `SINFunctions`, the axiom categories); `src/input/sexpr2.input`.

## 3. Steps

Each step is one pull request: code, tests named by spec label, and the status updated in `docs/INDEX.md`.

1. **Done 2026-11-26.** **The term order (Ord).** A package with `smaller?` implementing §3.5 on `InputForm` normal forms. Tests: irreflexive, antisymmetric, transitive and total on all pairs and triples drawn from a list of about 30 varied terms, compared exhaustively. It is not yet wired in.
2. **Done 2026-11-26.** **`SymbolicTerm(R, A)` with `A : List Symbol`.** Admissibility check at instantiation (spec §3.4), also added to `GeneralSymbolicExpression`, which today ignores unknown names. Rungs P0/M0 (`[]`) and the $`A_P`$ groups, with `associativity`, through the normaliser code `GeneralSymbolicExpression` already has. Equality is identity of normal forms; display and (Disp) as for `GeneralSymbolicExpression`. A new file `src/algebra/symterm.spad` and tests `src/input/symterm.input`, added to `make check`.
3. **Done 2026-11-26** (in the shared normaliser of `gsexpr.spad`, so both constructors have them). **P1–P3 and M1–M3** (C, A, AC): sorted binary nodes, flat words, flat sorted lists. Tests: for every small term, all permutations and regroupings allowed by the rung give one normal form (N2), with the bracketing test of `gsexpr.input` as the model; and terms that are different under the rung keep different forms.
4. **Done 2026-11-26** (in the shared normaliser, groups `linear`, `powers`, `quotients`). **P4 and M4–M5** (linear combinations; power products), signed sums and quotients as powers. The canonical elements are sorted lists of (atom, coefficient) and (atom, exponent) records, the representation `FreeModule` would use, built into `InputForm` trees as in spec §3.4. Tests: random linear combinations and power products, each written in many ways, have one normal form, and different ones keep different forms (150 trials each, with a mutation check); (N3) by `check` on 300 random terms; (Disp) on the new forms.
5. **Done 2026-11-26** (groups `ring` and `field`; Ann is the group `annihilation` of step 2). **Ann, Ring, Field** (polynomials and fractions over the atoms), computed in `Fraction Polynomial Fraction Integer` with a fresh symbol per atom. `ring` with `quotients` now requires `field` (decision 0009, amended). Tests: random terms built in parallel in `SymbolicTerm` and in `Polynomial Integer` or `Fraction Polynomial Integer` agree on equality, and equal variants of each ($`h+g-h`$, $`gk/k`$, …) have one normal form (200 trials each, mutation-checked); $`\sqrt2^{\,2} \ne 2`$ under Field but $`= 2`$ in `GeneralSymbolicExpression`; (N3) by `check` on 300 random terms; (Disp).
6. **Retire the 2017 machinery:** `Symbolic(R, A)`, the axiom categories and domains, `join`, `SINFunctions`, and the interim `Inverse` home of the negation and reciprocal rewrites (decision 0007). Port `sexpr2.input` to `SymbolicTerm` and its groups.
7. **Done with steps 3–5.** **Shared with design (I):** let `GeneralSymbolicExpression(R, A)` accept sound rungs as presentation axioms (for example C for sorted display), keeping (Disp) and (Val). The normalisers live in `gsexpr.spad`, so `GeneralSymbolicExpression` accepts every group, and (Disp) and (Val) are tested for each rung.

## 4. Open questions, for when the work reaches them

- Categories: which FriCAS categories each admissible $`A`$ may claim (spec §3.2): for example `AbelianMonoid` at P3 with Id, `CommutativeRing` at Ring.
- Floats as numerals: `Float` has no exact arithmetic, so is Num sound for them? Probably restrict Num to exact numerals.
- Display of P4/M4 forms: settled in step 4 (spec §3.4, "Trees of P4, M4 and M5"): the constant last in a sum, the numeral first in a product. Review with examples.
- Whether the user-rule AC matcher (note §2.3, item 5) is wanted at all for design (II).
