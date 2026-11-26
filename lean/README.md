# Lean proofs for fricas-symbolic

Lean 4.36.0 with Mathlib v4.36.0, pinned in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json` (never run `lake update`). The plan, the decisions and the
recorded results are in [`../docs/plans/lean-presentation-axioms.md`](../docs/plans/lean-presentation-axioms.md).

| Module | Contents |
|---|---|
| `FricasSymbolic/Term.lean` | terms, size, μ |
| `FricasSymbolic/Eval.lean` | partial evaluation in a field of characteristic 0 |
| `FricasSymbolic/Normalize.lean` | `Ax`, the smart constructors mirrored from `src/algebra/gsexpr.spad`, `nf` |
| `FricasSymbolic/Form.lean` | terms printed as FriCAS prints their `InputForm` |
| `FricasSymbolic/CrossCheck.lean`, `crosscheck/crosscheck.spad` | the differential test against `GeneralSymbolicExpression` |
| `FricasSymbolic/Soundness.lean` | L1, L2 |
| `FricasSymbolic/Rewriting.lean` | the rules of the spec as `Root`, `Step`, `IsNF`, `EqA` |
| `FricasSymbolic/Regressions.lean` | L7, L10 |
| `Axioms.lean` | `#print axioms` of the cited theorems (not part of the library) |

**Build.** On STRIX: `lean_build("fricas-symbolic", ref)` on a pushed branch (skill
`lean`). Elsewhere: `lake exe cache get && lake build` in this folder. No CI job builds Lean.

**Differential test.** In Lean, `run A s0 n d` from `FricasSymbolic.CrossCheck`; in FriCAS, compile
`crosscheck/crosscheck.spad` after `gsexpr.spad` and call `run(s0, n, d)$LeanCrossCheck(A)`.
Equal results mean equal forms for all `n` terms.
