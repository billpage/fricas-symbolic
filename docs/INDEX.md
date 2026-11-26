# Index of labels

Every labelled goal, condition, axiom group and result in the [specification](spec/sexpr-spec.md), with its section, its standing and the tests that check it. A row identifies a label; it does not carry its hypotheses, so read the section before relying on it.

Tests are named by file and `testcase`: `sympair` is `src/input/sympair.input`, `sexpr2` is `src/input/sexpr2.input`. "—" means not yet tested.

## Goals

| Label | Section | Says | Standing | Tests |
|---|---|---|---|---|
| G1 | §1 | Display as entered; what you see is what you get | Goal; made precise as (Disp) | sympair: "written form is kept"; "presentation axioms A_P" (near misses); "Disp: …" |
| G2 | §1 | Same meaning as `Expression` | Goal | sympair: "equality and zero test agree" |
| G3 | §1 | Purely syntactic work, $`1+2 \ne 3`$ | Goal | sympair: "identities only: numbers are not folded (G3)"; sexpr2: "ex1" |
| G4 | §1 | Rewrite rules act on the written structure | Goal | sympair: "rewrite rules act on the expression as written"; sexpr2: "ex4" |
| G5 | §1 | Axioms selectable per domain | Goal | sympair: the two A_P test cases (two parameter values) |
| G6 | §1 | Library algorithms correct | Goal | sympair: "integration is correct"; "summation and limits are correct" |
| G7 | §1 | Rewriting terminates and is deterministic | Goal | — (V4) |
| G8 | §1 | Formatting through `coerce: % -> OutputForm` | Goal | — (display is checked by eye; see spec §8) |

## Conditions and results

| Label | Section | Says | Standing | Tests |
|---|---|---|---|---|
| (S) | §2.3 | Soundness of an axiom set for `Expression` | Definition | — |
| Lemma 1 | §2.3 | (S) implies $`=_A \subseteq \equiv`$ | Proved | — |
| (T), (CR) | §2.4 | Termination; confluence | Definitions | — |
| (Disp) | §5 | The one-line display reads back as the stored form | Required (Bill, 2026-11-26); holds for the 28 shapes tested | sympair: "Disp: the displayed text reads back as the stored form" |
| (Val) | §3.3 | Invariant: value = evaluation of form | Required of design (I) | sympair: `check` in "integration is correct", "summation and limits are correct", "rewrite rules …", "presentation axioms A_P" |
| Prop. 2 | §3.3 | Sound + terminating $`A`$ ⇒ (Val) preserved, pair domain ≅ its image in `Expression` | Proved | via (Val) |
| Theorem 3 | §4.1, §4.1.1 | $`A_P`$ sound, terminating, confluent; extended to $`A_P \cup \mathrm{Assoc}`$ in §4.1.1 | Proved (sketch: critical pairs listed) | — (V4: confluence by construction order; V5: Lean) |

## Axiom groups

| Label | Section | Rules | Standing | Tests |
|---|---|---|---|---|
| Id | §4.1 | $`0+x,\ x+0,\ x-0,\ 0-x,\ 1\cdot x,\ x\cdot 1,\ x/1,\ x^1,\ x^0`$ | Implemented in `SymbolicPair` (`identities`) | sympair: "presentation axioms A_P"; "identities only …" |
| Ann | §4.1 | $`0\cdot x,\ x\cdot 0`$ | Implemented (`annihilation`) | sympair: "presentation axioms A_P" |
| Inv | §4.1 | $`-(-x),\ 1/(1/x)`$ | Implemented (`involutions`) | sympair: "presentation axioms A_P"; "identities only …" (must not fire) |
| Assoc (optional) | §4.1.1 | $`x \circ (y \circ z) \to (x \circ y) \circ z`$, $`\circ \in \{+, \cdot\}`$ | Specified (decision 0005); sound, terminating and confluent with $`A_P`$; not yet implemented | — |
| Num | §4.1 | Fold operations on numerals | Implemented (`numerals`) | sympair: "presentation axioms A_P"; "identities only …" (must not fire) |
| Doubles (2017) | §4.2 | Collect like terms | Coefficient-side bug fixed (2026-11-25); still needs AC matching | sexpr2: "Doubles: coefficient on either side" |
| Commutative, Associative, Distributive, Cancels, Divides, Inverse, AntiCommutative (2017) | §4.2 | See the table in §4.2 | Under review for design (II) | sexpr2: "ex2" |
