# Plan: a Lean proof for the presentation axioms

*2026-11-26. Planning document and hand-off for a separate conversation. Status: not started.*

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

A structure of flags `Ax := {id ann inv num assoc : Bool}` stands for the parameter $`A`$. Smart constructors `sAdd A a b`, `sSub`, `sNeg`, `sMul`, `sDiv`, `sPow` follow the Spad clauses in the same order, and

```lean
def nf (A : Ax) : Term → Term
  | .add a b => sAdd A (nf A a) (nf A b)
  | …                                   -- bottom-up, as the domain builds terms
```

`sAdd` and `sMul` recurse under Assoc: `sAdd x (add y₁ y₂) = sAdd (sAdd x y₁) y₂`. Their termination needs the measure $`(\lvert t\rvert, \mu(t))`$ of spec §4.1.1 (`termination_by`).

### 3.4 Theorems

| No. | Statement | Spec |
|---|---|---|
| L1 | Each smart constructor refines evaluation: `eval ρ (.add a b) = some v → eval ρ (sAdd A a b) = some v`, and likewise for the others | (S), Lemma 1 |
| L2 | `eval ρ t = some v → eval ρ (nf A t) = some v` | (Val), Prop. 2 |
| L3 | `nf` is total: it terminates, by structural recursion plus the measure for Assoc | (T) |
| L4 | Define `Step A` as the root rules closed under contexts, and `IsNF A t` as "no `Step` from `t`". Then `IsNF A (nf A t)` | |
| L5 | `Step A s t → nf A s = nf A t`, hence by induction `EqvGen (Step A) s t → nf A s = nf A t` | (CR), Theorem 3 |
| L6 | `IsNF A t → nf A t = t`, hence `nf A (nf A t) = nf A t` | idempotence |
| L7 | Regression: with (AN) removed, L5 fails; the witness is `x + (1+2)` | §4.1.1 |

L4–L6 together show that $`\mathrm{nf}`$ chooses exactly one normal form per $`=_A`$ class, which is termination plus confluence. This route avoids formalising Newman's lemma and critical pairs in general. Mathlib's `Relation` library has the closure operators (`Relation.ReflTransGen`, `EqvGen`) if they are wanted.

Every theorem should be stated for all `A : Ax`, or at least for the combinations the package offers: subsets of {Id, Ann, Inv, Num}, with and without Assoc.

## 4. Repository layout

```
formal/
├── README.md            what is proved, how to build
├── lean-toolchain       pinned Lean version
├── lakefile.toml        Mathlib pinned to a release tag
└── Formal/
    ├── Term.lean        syntax, size, μ
    ├── Eval.lean        partial evaluation
    ├── Normalize.lean   Ax, smart constructors, nf
    └── Theorems.lean    L1–L7
```

Options for CI: a separate workflow `lean.yml` running `lake exe cache get && lake build`, triggered only by changes under `formal/` because of the Mathlib download. To be decided in the conversation; see §6.

## 5. Environment: check first

Checked from the chat workspace on 2026-11-26:
- `release.lean-lang.org` and `reservoir.lean-lang.org` answer;
- GitHub release downloads work (the FriCAS binary is fetched that way);
- the Mathlib cache host was **not** confirmed.

The first task of the conversation is to install `elan` and run `lake exe cache get` in a scratch project. Building Mathlib from source instead would take hours. Fallbacks, in order:

1. Run the proofs only in GitHub Actions, where the cache is known to work.
2. A smaller proof without Mathlib, using a concrete field such as `ℚ` with core lemmas. Weaker: it doesn't cover every field `K`.

## 6. Decisions for Bill (at the start of that conversation)

1. CI: a Lean job on changes under `formal/`, or local builds only?
2. Scope of version 1: $`A_P`$ only, or $`A_P`$ with Assoc and (AN)? Including Assoc is recommended, since that is where the 2026-11-26 error was.
3. The field: any `[Field K] [CharZero K]`, or `ℚ`? Generality costs little with Mathlib.

## 7. Done when

- `lake build` succeeds with no `sorry`, in CI or as a recorded run;
- spec §6 (V5) and `docs/INDEX.md` show Theorem 3 and its §4.1.1 extension as "proved in Lean", with the theorem names;
- the work arrives in a pull request from `claude/lean-ap`.

## References

- F. Baader, T. Nipkow, *Term Rewriting and All That*, Cambridge University Press (1998): normal forms and confluence (ch. 2), critical pairs (ch. 6).
- The Mathlib Community, "The Lean mathematical library", *CPP 2020*, 367–381.
