# Plan: a Lean proof for the presentation axioms

*2026-11-26. Planning document and hand-off for a separate conversation. Status: started; `lean/` project built (§5), theorems not yet begun.*

## 1. Goal

Prove in Lean 4, with Mathlib, that the normaliser of `GeneralSymbolicExpression(R, A)` does what the specification claims, for every combination of the axiom groups Id, Ann, Inv, Num (spec §4.1) and Assoc with its completion rule (AN) (spec §4.1.1):

1. it preserves values: invariant (Val), via Proposition 2;
2. it terminates;
3. its results are normal forms;
4. it gives equal terms equal results: if $`s =_A t`$ then $`\mathrm{nf}(s) = \mathrm{nf}(t)`$. This is the content of "terminating and confluent" in Theorem 3.

Item 4 is the one that matters most. On 2026-11-26 a hand proof of confluence for Assoc missed the critical pair $`x + (1+2)`$: Num inside gives $`x+3`$, while Assoc at the root gives the normal form $`(x+1)+2`$. The completion rule (AN) was added only after Bill asked about it. A machine-checked proof would have caught that.

## 2. Read first

- `AGENTS.md`, `CONTRIBUTING.md`: delivery on `claude/<topic>` branches, specification first.
- Spec §2 (framework), §3.3 (design (I), invariant (Val)), §4.1 (Theorem 3), §4.1.1 (Assoc, (AN), the measure $`\mu`$, critical pairs).
- Decisions 0002, 0005.
- `src/algebra/gsexpr.spad`: the smart constructors `+`, `-` (unary and binary), `*`, `/`, `^` after the comment "Presentation axioms". The Lean definitions should mirror them clause by clause, so that the theorems are about the code and not about an idealisation of it.

## 3. What to formalise

### 3.1 Syntax

```lean
inductive Term where
  | num : ℚ → Term          -- numerals: constants of Frac(R), here R = ℤ
  | var : String → Term
  | add : Term → Term → Term
  | sub : Term → Term → Term
  | neg : Term → Term
  | mul : Term → Term → Term
  | div : Term → Term → Term
  | pow : Term → ℤ → Term   -- integer exponents only, as the rules use
```

Named functions ($`\sin`$, …) and rational exponents are left out of version 1. No rule of $`A_P`$ or Assoc looks inside them, so a later version can add them as uninterpreted applications.

### 3.2 Semantics: partial, as in the spec

Mathlib's division is total ($`x/0 = 0`$), but `Expression` raises an error on division by zero, and condition (S) is stated for partial evaluation. So evaluation should return `Option`:

```lean
variable {K : Type} [Field K] [CharZero K]
def eval (ρ : String → K) : Term → Option K
-- div: none if the denominator evaluates to 0
-- pow with a negative exponent: none if the base is 0; 0 ^ 0 = 1 (as in FriCAS)
```

Soundness is then *refinement*: if the left side is defined, the right side is defined with the same value. The right side may be defined where the left side is not; for example, Ann turns $`0 \cdot (1/0)`$ into $`0`$.

### 3.3 The normaliser

A structure of flags `Ax := {id ann inv num assoc : Bool}` stands for the parameter $`A`$. L7 needs a normaliser without (AN), which the package does not offer: give the Lean `Ax` an extra flag `an` (default `true`, used only by L7) rather than a second copy of `sAdd` and `sMul`. Smart constructors `sAdd A a b`, `sSub`, `sNeg`, `sMul`, `sDiv`, `sPow` follow the Spad clauses in the same order, and

```lean
def nf (A : Ax) : Term → Term
  | .add a b => sAdd A (nf A a) (nf A b)
  | …                                   -- bottom-up, as the domain builds terms
```

`sAdd` and `sMul` recurse under Assoc: `sAdd x (add y₁ y₂) = sAdd (sAdd x y₁) y₂`. The outer call's second argument is the result of no recursive call, so `termination_by (y.size, x.size)` (lexicographic) covers (A) even though the first argument is. Write the (AN) clause as `sAdd x₁ (.num (n + m))`, which is what the Spad clause `first kids x + (second kids x + y)` computes (Num fires first on two numerals); written as a nested `sAdd`, its second argument would be a recursive result whose size Lean cannot see.

Three points where the Lean functions cannot copy the Spad code literally:

- Each Spad constructor first computes `value x ∘ value y` in `Expression R`, which raises an error when a denominator is the zero expression; the Lean constructors are total and skip this. The Lean theorems therefore cover more terms than the domain can build (for example $`0\cdot(1/0)`$), which is harmless for soundness and makes L5 stronger.
- Num must not fold $`n/0`$ or $`0^{e}`$ with $`e<0`$: Mathlib's `ℚ` gives `1/0 = 0` and `0 ^ (-1 : ℤ) = 0`, where FriCAS raises an error. Leave those nodes unfolded.
- `lit?(x, n)` in the Spad code tests the form of a leaf and `numeral?` tests that a leaf's value is in $`\mathrm{Frac}(R)`$; in version 1 both are `.num q` (with `q = n`), since there are no other leaves with constant values.

### 3.4 Theorems

| No. | Statement | Spec |
|---|---|---|
| L1 | Each smart constructor refines evaluation: `eval ρ (.add a b) = some v → eval ρ (sAdd A a b) = some v`, and likewise for the others | (S), Lemma 1 |
| L2 | `eval ρ t = some v → eval ρ (nf A t) = some v` | (Val), Prop. 2 |
| L3 | `nf` is total: it terminates, by structural recursion plus the measure for Assoc | (T) |
| L4 | Define `Step A` as the root rules closed under contexts, and `IsNF A t` as "no `Step` from `t`". Then `IsNF A (nf A t)` | |
| L5 | `Step A s t → nf A s = nf A t`, hence by induction `EqvGen (Step A) s t → nf A s = nf A t` | (CR), Theorem 3 |
| L6 | `IsNF A t → nf A t = t`, hence `nf A (nf A t) = nf A t` | idempotence |
| L7 | Regression: with (AN) removed, L5 fails; the witness is the step `x + (1+2)` → `(x+1)+2` (by (A)), whose two sides get `x+3` and `(x+1)+2` | §4.1.1 |
| L8 | `Relation.ReflTransGen (Step A) t (nf A t)`: the normaliser only takes steps of the axioms | |
| L9 | `Step A` is well founded (its converse is `WellFounded`), by the measure $`(\lvert t\rvert, \mu(t))`$ | (T), §4.1.1 |

L4, L5 and L8 together give the Church–Rosser property: if $`s =_A t`$ then $`s \to^* \mathrm{nf}(s) = \mathrm{nf}(t) \;{}^*\!\!\leftarrow t`$, with $`\mathrm{nf}(s)`$ a normal form. That is confluence, and $`\mathrm{nf}`$ chooses exactly one normal form per $`=_A`$ class. Without L8 the list does not tie $`\mathrm{nf}(t)`$ to $`t`$ at all: L2 relates their values, not their classes. Termination of the rewriting relation (every rewrite sequence ends) is L9; L3 only says that one strategy, bottom-up, ends. This route avoids formalising Newman's lemma and critical pairs in general.

**`Step` must come from the spec, not from the code.** Define the root rules from the axiom lists of spec §4.1 and §4.1.1, each with its side conditions, and not by unfolding the smart constructors; otherwise L5 is true by construction and proves nothing about the code. In particular (AN) is $`(x\circ n)\circ m \to x \circ k`$ with $`k`$ the folded numeral, and Num on $`n/m`$ and on $`n^{e}`$ with $`e<0`$ has the side condition that the numeral denominator or base is not $`0`$. Mathlib's `Relation` library has the closure operators (`Relation.ReflTransGen`, `EqvGen`) if they are wanted.

Every theorem should be stated for all `A : Ax`, or at least for the combinations the package offers: subsets of {Id, Ann, Inv, Num}, with and without Assoc.

## 4. Repository layout

The layout follows the shared Lean setup on STRIX (skill `lean`): one project per repository, in `lean/`, pinned to Lean v4.36.0 and Mathlib v4.36.0.

```
lean/
├── README.md               what is proved, how to build
├── lean-toolchain          leanprover/lean4:v4.36.0
├── lakefile.toml           Mathlib rev v4.36.0; library FricasSymbolic
├── lake-manifest.json      exact commits (Mathlib fc4f59e5); never `lake update`
├── FricasSymbolic.lean     imports the modules below
└── FricasSymbolic/
    ├── Term.lean           syntax, size, μ          (done)
    ├── Eval.lean           partial evaluation
    ├── Normalize.lean      Ax, smart constructors, nf
    ├── Theorems.lean       L1–L9
    └── Axioms.lean         #print axioms of the cited theorems
```

Builds run with `lean_build("fricas-symbolic", ref)` on a pushed branch. Options for CI: a separate workflow `lean.yml` running `lake exe cache get && lake build`, triggered only by changes under `lean/`. To be decided; see §6.

## 5. Environment

Lean 4.36.0 and Mathlib v4.36.0 run in the `lean` container on STRIX (skill `lean`, setup in `billpage/lean-docker`), and the repository is registered there. Checked on 2026-11-26:

- `run_lean` in the scratch project: status `ok`, `Lean.versionString = "4.36.0"`; the definitions of `Term.lean` with an `#eval` of the (A) step $`x+(y+z) \to (x+y)+z`$ gave sizes 5 and 5 and $`\mu`$ 4 and 2, a fall of $`\lvert z\rvert + 1`$ as in spec §4.1.1 (run `20261126-153033-term-scaffold`);
- `lean_build` of `claude/lean-ap` at `1c5a348`: status `ok`; `lake exe cache get` unpacked the Mathlib cache and nothing of Mathlib was compiled; the only warnings are Mathlib's harmless "consider adding `module`" (log `20261126-153104-build-fricas-symbolic`).

The workspace installation (elan and the Mathlib cache in the chat container) and its fallbacks are no longer needed.

## 6. Decisions for Bill (at the start of that conversation)

1. CI: a Lean job on changes under `lean/`, or recorded `lean_build` runs on STRIX only?
2. Scope of version 1: $`A_P`$ only, or $`A_P`$ with Assoc and (AN)? Including Assoc is recommended, since that is where the 2026-11-26 error was.
3. The field: any `[Field K] [CharZero K]`, or `ℚ`? Generality costs little with Mathlib.

## 7. Done when

- `lean_build` returns status `ok` (no errors, no `sorry`), and `#print axioms` of each theorem lists at most `propext`, `Classical.choice`, `Quot.sound` (skill `lean`, "Recorded results");
- spec §6 (V5) and `docs/INDEX.md` show Theorem 3 and its §4.1.1 extension as "proved in Lean", with the theorem names;
- the work arrives in a pull request from `claude/lean-ap`.

## References

- F. Baader, T. Nipkow, *Term Rewriting and All That*, Cambridge University Press (1998): normal forms and confluence (ch. 2), critical pairs (ch. 6).
- The Mathlib Community, "The Lean mathematical library", *CPP 2020*, 367–381.
