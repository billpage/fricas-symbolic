# Index of labels

Every labelled goal, condition, axiom group and result in the [specification](spec/sexpr-spec.md), with its section, its standing and the tests that check it. A row identifies a label; it does not carry its hypotheses, so read the section before relying on it.

Tests are named by file and `testcase`: `gsexpr` is `src/input/gsexpr.input`, `sexpr2` is `src/input/sexpr2.input`. "—" means not yet tested.

## Goals

| Label | Section | Says | Standing | Tests |
|---|---|---|---|---|
| G1 | §1 | Display as entered; what you see is what you get | Goal; made precise as (Disp) | gsexpr: "written form is kept"; "presentation axioms A_P" (near misses); "Disp: …" |
| G2 | §1 | Same meaning as `Expression` | Goal | gsexpr: "equality and zero test agree" |
| G3 | §1 | Purely syntactic work, $`1+2 \ne 3`$ | Goal | gsexpr: "identities only: numbers are not folded (G3)"; sexpr2: "ex1"; "G3: Symbolic(Integer, None) keeps the written form" |
| G4 | §1 | Rewrite rules act on the written structure | Goal | gsexpr: "rewrite rules act on the expression as written"; sexpr2: "ex4" |
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
| (Disp) | §5 | The one-line display reads back as the stored form | Required (Bill, 2026-11-26); holds for the 28 shapes and 12 mixed integer cases tested | gsexpr: "Disp: the displayed text reads back as the stored form" |
| (Val) | §3.3 | Invariant: value = evaluation of form | Required of design (I) | gsexpr: `check` in "integration is correct", "summation and limits are correct", "rewrite rules …", "presentation axioms A_P" |
| (N1), (N2), (N3) | §3.4 | A normaliser is correct and canonical, and preserves values when $`A`$ is sound | Required of every rung (decision 0008) | — (plan step 3 onwards) |
| Rungs P0–P4, M0–M5, Ann, Ring, Field | §3.4 | The ladder of admissible axiom sets and their normal forms | P0/M0, P1/M1, P2/M2, P3/M3 with the $`A_P`$ groups, in both constructors; P4, M4–M5, Ring, Field not yet built | symterm: "no groups: P0/M0"; "A_P groups"; "A_P with associativity"; "commutativity alone"; "commutativity with associativity" and "A_P with commutativity and associativity" (exhaustive: 4,200 and 8,400 terms); gsexpr: "commutativity as a presentation group" (exhaustive, with (Val)); sexpr2: "G3: …" (2017 `Symbolic`, P0/M0) |
| Admissibility | §3.4 | Unknown groups, unimplemented groups and missing requirements are rejected at instantiation | Implemented (`SymbolicAxiomGroups`) in both constructors | symterm: "admissibility" |
| Prop. 4, (Ord) | §3.5 | $`\prec`$ is a strict total order | Proved; implemented as `SymbolicTermOrder` (in `gsexpr.spad`) | gsexpr: "Ord: the term order is a strict total order" (37 terms, all pairs and triples) |
| Prop. 2 | §3.3 | Sound + terminating $`A`$ ⇒ (Val) preserved, pair domain ≅ its image in `Expression` | Proved | via (Val) |
| Theorem 3 | §4.1, §4.1.1 | $`A_P`$ sound, terminating, confluent; extended to $`A_P \cup \mathrm{Assoc}`$ in §4.1.1 | Proved (sketch: critical pairs listed) | — (V4: confluence by construction order; V5: Lean) |

## Axiom groups

| Label | Section | Rules | Standing | Tests |
|---|---|---|---|---|
| Id | §4.1 | $`0+x,\ x+0,\ x-0,\ 0-x,\ 1\cdot x,\ x\cdot 1,\ x/1,\ x^1,\ x^0`$ | Implemented in `GeneralSymbolicExpression` (`identities`) | gsexpr: "presentation axioms A_P"; "identities only …" |
| Ann | §4.1 | $`0\cdot x,\ x\cdot 0`$ | Implemented (`annihilation`) | gsexpr: "presentation axioms A_P" |
| Inv | §4.1 | $`-(-x),\ 1/(1/x)`$ | Implemented (`involutions`) | gsexpr: "presentation axioms A_P"; "identities only …" (must not fire) |
| Assoc (optional) | §4.1.1 | $`x \circ (y \circ z) \to (x \circ y) \circ z`$, $`\circ \in \{+, \cdot\}`$ | Implemented (`associativity`), with the completion rule (AN); sound, terminating and confluent with $`A_P`$ | gsexpr: "Assoc: rules (A) and (AN)"; "Assoc: not in A_P"; "Assoc: all bracketings agree" (6250 expressions) |
| Num | §4.1 | Fold operations on numerals | Implemented (`numerals`) | gsexpr: "presentation axioms A_P"; "identities only …" (must not fire) |
| Doubles (2017) | §4.2 | Collect like terms | Coefficient-side bug fixed (2026-11-25); still needs AC matching | sexpr2: "Doubles: coefficient on either side" |
| Commutative, Associative, Distributive, Cancels, Divides, Inverse, AntiCommutative (2017) | §4.2 | See the table in §4.2 | Under review for design (II) | sexpr2: "ex2" |
