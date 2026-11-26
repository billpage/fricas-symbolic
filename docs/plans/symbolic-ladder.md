# Plan: rebuilding `Symbolic(R, A)` on the ladder of normalisers

*2026-11-26. Planning document; implements decision [0008](../decisions/0008-ladder-of-normalisers.md) and spec §3.4–3.5. Status: not started.*

## 1. Goal

Replace the rewriting core of `Symbolic(R, A)` in `src/algebra/sexpr.spad` with normalisers that build the canonical forms of spec §3.4, one rung at a time. At every step `make check` passes, and each landed rung has tests of (N1) and (N2).

## 2. Read first

Spec §2–3 (especially §3.4, §3.5), §4.2; decisions 0001, 0007, 0008; the note [2026-11-26-commutativity-and-hidden-rewrites](../notes/2026-11-26-commutativity-and-hidden-rewrites.md); `src/algebra/sexpr.spad` (`Symbolic`, `SINFunctions`, the axiom categories); `src/input/sexpr2.input`.

## 3. Steps

Each step is one pull request: code, tests named by spec label, and the status updated in `docs/INDEX.md`.

1. **The term order (Ord).** A package with `smaller?` implementing §3.5 on `InputForm` normal forms. Tests: irreflexive, antisymmetric, transitive and total on all pairs and triples drawn from a list of about 30 varied terms, compared exhaustively. It is not yet wired in.
2. **Representation and the rung switch.** `Symbolic(R, A)` computes from $`A`$ which rungs apply, and rejects inadmissible combinations at instantiation. `None` remains P0/M0. The 2017 axiom domains map onto rungs: `CommutativePlus` is P1, `AssociativePlus` with it is P3, and so on.
3. **P1–P3 and M1–M3** (C, A, AC): sorted binary nodes, flat words, flat sorted lists. Tests: for every small term, all permutations and regroupings allowed by the rung give one normal form (N2), with the bracketing test of `gsexpr.input` as the model; and terms that are different under the rung keep different forms.
4. **P4 and M4–M5** (linear combinations; power products) with `FreeModule`, signed sums and quotients as powers. Tests as in step 3, plus (N3) against `Expression` on random terms.
5. **Ann, Ring, Field** (polynomials and fractions over the atoms) with `SparseMultivariatePolynomial` and `Fraction`. Tests as above, plus examples where Ring/Field equality is strictly weaker than `Expression`'s ($`\sqrt2^{\,2}`$ against $`2`$).
6. **Retire the 2017 machinery:** the axiom categories' rewrite procedures, `SINFunctions` `smaller?`, and the interim `Inverse` home of the negation and reciprocal rewrites (decision 0007). Port `sexpr2.input` to the rungs.
7. **Shared with design (I):** let `GeneralSymbolicExpression(R, A)` accept sound rungs as presentation axioms (for example C for sorted display), keeping (Disp) and (Val).

## 4. Open questions, for when the work reaches them

- Categories: which FriCAS categories each admissible $`A`$ may claim (spec §3.2): for example `AbelianMonoid` at P3 with Id, `CommutativeRing` at Ring.
- Floats as numerals: `Float` has no exact arithmetic, so is Num sound for them? Probably restrict Num to exact numerals.
- Display of P4/M4 forms: the constant last and the numeral first are proposed (§3.5); confirm with examples.
- Whether the user-rule AC matcher (note §2.3, item 5) is wanted at all for design (II).
