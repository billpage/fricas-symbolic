# 0008. One library of normalisers, the ladder of axiom sets, and the term order $`\prec`$

- Status: Accepted
- Date: 2026-11-26
- Decided by: Bill Page
- Spec: §3.2, §3.4, §3.5, §5

## Context

`Symbolic(R, A)` implements its axioms as rewrite procedures on binary trees, ordered by a `smaller?` whose totality was never shown. Commutativity cannot be a rewrite rule, and general rewriting modulo AC (matching, extended rules, AC-compatible orders, AC critical pairs) is a large project. The note of 2026-11-26 (§2.2) observed that the useful axiom sets are the axioms of known free algebras, whose canonical forms can be built directly.

## Options

1. Keep rewriting, and build a general AC rewriting engine with a completion check.
2. Build canonical forms of free algebras: one normaliser per admissible axiom set, arranged as a ladder (lattice) of rungs from the term algebra up to polynomials and rational functions in uninterpreted atoms, with a structural total order to sort atoms.

## Decision

Option 2, as specified in §3.4–3.5:

- A normaliser $`N_A`$ is correct (N1) and canonical (N2); with a sound $`A`$ it preserves values (N3).
- **Both constructors share the normalisers.** `Symbolic(R, A)` has the normal forms as carrier and their identity as equality. `GeneralSymbolicExpression(R, A)` uses them as presentation axioms with semantic equality, so any sound admissible $`A`$ can serve there.
- **Rungs:** P0–P4 for $`+`$ (up to linear combinations with numeral coefficients); M0–M5 for $`\cdot`$ (up to power products with integer exponents); linking axioms Ann, Ring (distributivity, giving polynomials) and Field (distributivity with M5, giving reduced fractions).
- **Admissible sets** are the combinations whose requirements are met. Others are rejected when the domain is instantiated.
- **$`\prec`$:** numerals before symbols before compounds; numerals by value, which requires $`R`$ to be `Comparable`; symbols by `Symbol`'s order; compounds lexicographically by (name, arity, arguments). It is a strict total order (Proposition 4), and its choice affects only the display.

## Consequences

- No AC matching or completion is needed for the built-in axioms. The proof obligation per rung is (N1) and (N2), shown by the free-algebra normal form, and testable exhaustively on small terms.
- The 2017 axiom categories and `SINFunctions` `smaller?` are replaced rung by rung; `sexpr2.input` keeps testing the 2017 behaviour until each rung lands.
- The Ring and Field rungs give polynomial and rational-function identity with uninterpreted functions, strictly weaker than `Expression`'s equality.
- User rewrite rules over `Symbolic` still need an AC matcher (note §2.3, item 5); out of scope here.
- Work plan: [`docs/plans/symbolic-ladder.md`](../plans/symbolic-ladder.md).
