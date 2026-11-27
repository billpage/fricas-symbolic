# Index of labels

Every labelled goal, condition, axiom group and result in the [specification](spec/sexpr-spec.md), with its section, its standing and the tests that check it. A row identifies a label; it does not carry its hypotheses, so read the section before relying on it.

Tests are named by file and `testcase`: `gsexpr` is `src/input/gsexpr.input`, `symterm` is `src/input/symterm.input`. The 2017 `sexpr2.input` was retired with `Symbolic(R, A)` ([note](notes/2026-11-26-retiring-symbolic.md)). "—" means not yet tested.

## Goals

| Label | Section | Says | Standing | Tests |
|---|---|---|---|---|
| G1 | §1 | Display as entered; what you see is what you get | Goal; made precise as (Disp) | gsexpr: "written form is kept"; "presentation axioms A_P" (near misses); "Disp: …" |
| G2 | §1 | Same meaning as `Expression` | Goal | gsexpr: "equality and zero test agree" |
| G3 | §1 | Purely syntactic work, $`1+2 \ne 3`$ | Goal | gsexpr: "identities only: numbers are not folded (G3)"; symterm: "ported from sexpr2 ex1"; "ported from sexpr2: G3, no groups keep the written form" |
| G4 | §1 | Rewrite rules act on the written structure | Goal | gsexpr: "rewrite rules act on the expression as written"; for `SymbolicTerm`, open (plan §4) |
| G5 | §1 | Axioms selectable per domain | Goal | gsexpr: the two A_P test cases (two parameter values) |
| G6 | §1 | Library algorithms correct | Goal | gsexpr: "integration is correct"; "summation and limits are correct" |
| G7 | §1 | Rewriting terminates and is deterministic | Goal | — (V4) |
| G8 | §1 | Formatting through `coerce: % -> OutputForm` | Goal | — (display is checked by eye; see spec §8) |

## Conditions and results

| Label | Section | Says | Standing | Tests |
|---|---|---|---|---|
| (S) | §2.3 | Soundness of an axiom set for `Expression` | Definition | — |
| Lemma 1 | §2.3 | (S) implies $`=_A \subseteq \equiv`$ | Proved | — |
| (T), (CR) | §2.4 | Termination; confluence | Definitions | — |
| (Disp) | §5 | The one-line display reads back as the stored form | Required (Bill, 2026-11-26); holds for the 28 shapes and 12 mixed integer cases tested, for negative numerals since decision 0010, and for float numerals by construction | gsexpr: "Disp: the displayed text reads back as the stored form", "negative numerals read back", "floats as numerals in GeneralSymbolicExpression(Float, A_P)"; symterm: "floats as numerals in SymbolicTerm(Float, A)" |
| (Val) | §3.3 | Invariant: value = evaluation of form | Required of design (I) | gsexpr: `check` in "integration is correct", "summation and limits are correct", "rewrite rules …", "presentation axioms A_P" |
| (N1), (N2), (N3) | §3.4 | A normaliser is correct and canonical, and preserves values when $`A`$ is sound | Required of every rung (decision 0008) | (N1), (N2): the rung tests below; (N3): gsexpr "linear, powers, quotients: (N3) on random terms" |
| Rungs P0–P4, M0–M5, Ann, Ring, Field | §3.4 | The ladder of admissible axiom sets and their normal forms | All rungs in both constructors (P4: `linear`; M4: `powers`; M5: `quotients`; Ring: `ring`; Field: `field`) | symterm: "no groups: P0/M0"; "A_P groups"; "A_P with associativity"; "commutativity alone"; "commutativity with associativity" and "A_P with commutativity and associativity" (exhaustive: 4,200 and 8,400 terms); symterm: "linear: P4", "powers and quotients: M4, M5" (random property tests, 150 trials each), "powers without quotients", "linear with powers and quotients", "ring: polynomials over the atoms", "field: reduced fractions over the atoms" (property tests against `Polynomial Integer` and `Fraction Polynomial Integer`), "display reads back … under linear, powers, quotients"; gsexpr: "commutativity as a presentation group" (exhaustive, with (Val)), "linear, powers, quotients in GeneralSymbolicExpression" |
| Admissibility | §3.4 | Unknown groups, unimplemented groups, missing requirements, and `ring` with `quotients` but without `field`, are rejected at instantiation | Implemented (`SymbolicAxiomGroups`) in both constructors | symterm: "admissibility" |
| `eval` (bridge) | §3.2 | $`T/{=_A}`$ is free in the variety of $`A`$: `eval` extends any map of the symbols into a ring $`D`$ satisfying $`A`$; read-back from forms | Implemented (decision 0011): `SymbolicTermFunctions2`, `InputFormEvaluation` | symterm: "bridge: eval is the homomorphism extending phi" (random terms against a model), "adding and dropping axioms by read-back", "without commutativity, into matrices", "refused targets" (must fail), "float numerals" |
| Prop. 4, (Ord) | §3.5 | $`\prec`$ is a strict total order | Proved; implemented as `SymbolicTermOrder` (in `gsexpr.spad`) | gsexpr: "Ord: the term order is a strict total order" (37 terms, all pairs and triples); symterm: "term order on numerals: exact, then float, by value" |
| Prop. 2 | §3.3 | Sound + terminating $`A`$ ⇒ (Val) preserved, pair domain ≅ its image in `Expression` | Proved; in Lean for $`A \subseteq A_P \cup \mathrm{Assoc}`$: `nf_refines` (L2), plan §3.5 | via (Val) |
| Theorem 3 | §4.1, §4.1.1 | $`A_P`$ sound, terminating, confluent; extended to $`A_P \cup \mathrm{Assoc}`$ in §4.1.1 | Proved (sketch: critical pairs listed); the pair $`0-0`$ without Num was missing (Lean L10) and is joined by $`-0\to 0`$ since decision 0012. Proved in Lean for every union of the groups: `eqA_iff_nf_eq`, `L9_terminating` (plan §3.5) | gsexpr: "Id: -0 -> 0 joins 0-0 without Num"; Lean part 1: L1–L9, with L7 and L10 as regressions for the rule sets without (AN) and without $`-0\to 0`$ |

## Axiom groups

| Label | Section | Rules | Standing | Tests |
|---|---|---|---|---|
| Id | §4.1 | $`0+x,\ x+0,\ x-0,\ 0-x,\ -0,\ 1\cdot x,\ x\cdot 1,\ x/1,\ x^1,\ x^0`$ | Implemented in both constructors (`identities`); $`-0\to 0`$ added by decision 0012 | gsexpr: "presentation axioms A_P"; "identities only …"; "Id: -0 -> 0 joins 0-0 without Num"; symterm: "Id: -0 -> 0 in SymbolicTerm" |
| Ann | §4.1 | $`0\cdot x,\ x\cdot 0`$ | Implemented (`annihilation`) | gsexpr: "presentation axioms A_P" |
| Inv | §4.1 | $`-(-x),\ 1/(1/x)`$ | Implemented (`involutions`) | gsexpr: "presentation axioms A_P"; "identities only …" (must not fire) |
| Assoc (optional) | §4.1.1 | $`x \circ (y \circ z) \to (x \circ y) \circ z`$, $`\circ \in \{+, \cdot\}`$ | Implemented (`associativity`), with the completion rule (AN); sound, terminating and confluent with $`A_P`$ | gsexpr: "Assoc: rules (A) and (AN)"; "Assoc: not in A_P"; "Assoc: all bracketings agree" (6250 expressions) |
| Num | §4.1 | Fold operations on numerals | Implemented (`numerals`); with float numerals exact, then rounded, sound up to rounding (decision 0010) | gsexpr: "presentation axioms A_P"; "identities only …" (must not fire); "floats as numerals …", "DoubleFloat numerals"; symterm: "floats as numerals in SymbolicTerm(Float, A)" (property test with decimals) |
| C (`commutativity`) | §3.4 | Sorted operands of $`+`$ and $`\cdot`$ | Implemented (rungs P1/M1, with `associativity` P3/M3) | symterm: "commutativity alone", "commutativity with associativity"; gsexpr: "commutativity as a presentation group" |
| `linear` | §3.4 | Doubles, Cancels, signed sums, numeral times sum (rung P4) | Implemented (2026-11-26) | symterm: "linear: P4", "linear with powers and quotients"; gsexpr: "linear, powers, quotients …" |
| `powers`, `quotients` | §3.4 | Squares; Divides with $`x/y \approx x \cdot y^{-1}`$ (rungs M4, M5) | Implemented (2026-11-26) | symterm: "powers and quotients: M4, M5", "powers without quotients"; gsexpr: "linear, powers, quotients …" |
| `ring`, `field` | §3.4 | Distributivity: polynomials, and reduced fractions, over the atoms (rungs Ring, Field) | Implemented (2026-11-26); `ring` with `quotients` requires `field` | symterm: "ring: polynomials over the atoms", "field: reduced fractions over the atoms"; gsexpr: "ring and field in GeneralSymbolicExpression", "ring and field: (N3) on random terms" |
| Doubles (2017) | §4.2 | Collect like terms | Superseded by `linear`; 2017 domain retired 2026-11-26 | symterm: "ported from sexpr2: Doubles, coefficient on either side" |
| Commutative, Associative, Distributive, Cancels, Divides, Inverse, AntiCommutative (2017) | §4.2 | See the table in §4.2 | Retired 2026-11-26; mapped to groups in the [note](notes/2026-11-26-retiring-symbolic.md) | symterm: "ported from sexpr2 ex2, ex3" |
