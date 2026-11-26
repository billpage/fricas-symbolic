# Plan: Lean proofs for fricas-symbolic

*2026-11-26. Planning document and hand-off for a separate conversation. Status: `lean/` project built (§6); part 1 started (`Term`, `size`, `μ`); no theorems yet. Revised the same day for the design as it now stands: the ladder of normalisers (decisions 0008, 0009), float numerals (0010) and the bridge (0011). The file name is kept for the links to it.*

## 1. What Lean can do here

The package rests on four kinds of claim. Each kind gets its own Lean route:

| Claim | Where | Lean route | Part |
|---|---|---|---|
| The presentation axioms $`A_P`$, with Assoc and (AN), are sound, terminating and confluent | Theorem 3, §4.1.1 | a rewriting system: `Step` from the spec, `nf` mirroring the Spad code; L1–L9 | 1 |
| The term order $`\prec`$ is a strict total order | Prop. 4, §3.5 | structural induction on trees | 2 |
| Each rung's normaliser is correct and canonical, (N1) and (N2) | §3.4, decision 0008 | $`T/{=_A}`$ is isomorphic to a free algebra that Mathlib has: `Multiset`, `Finsupp`, `MvPolynomial`, `FractionRing` | 3 |
| Every group is sound for `Expression`, and `eval` is well defined for any $`D`$ satisfying $`A`$ | (S), Lemma 1; decision 0011 | each axiom holds in $`D`$; the universal property (`MvPolynomial.aeval`) | 4 |

What Lean cannot settle, and stays with the FriCAS tests: (Disp), which depends on FriCAS's formatter and parser; and float numerals, which are sound only up to rounding (decision 0010). Lean works with exact numerals in $`\mathbb{Q}`$.

The reason for parts 1 and 3 is the same: on 2026-11-26 a hand proof of confluence for Assoc missed the critical pair $`x + (1+2)`$. Num inside gives $`x+3`$, while Assoc at the root gives the normal form $`(x+1)+2`$. The completion rule (AN) was added only after Bill asked about it. Machine checking catches that kind of omission.

## 2. Read first

- `AGENTS.md`, `CONTRIBUTING.md`: delivery on `claude/<topic>` branches, specification first.
- Spec §2 (framework: terms, evaluation, soundness), §3.2–3.5 (the two designs, the ladder, the term order), §4.1 and §4.1.1 (Theorem 3, Assoc, (AN), the measure $`\mu`$).
- Decisions 0002, 0005 (part 1); 0008, 0009 (part 3); 0010 (why floats are out of scope); 0011 (part 4).
- Skill `lean` (the STRIX container, `run_lean`, `lean_build`, the pins, "Recorded results").
- Code, in `src/algebra/gsexpr.spad`:
  - the smart constructors `+`, `-` (unary and binary), `*`, `/`, `^` of `GeneralSymbolicExpression`, after the comment "Presentation axioms". For $`A \subseteq A_P \cup \{\text{associativity}\}`$ only their Id, Ann, Inv, Num and Assoc clauses fire;
  - `SymbolicTermOrder` (the term order);
  - "Linear combinations and power products" (P4, M4, M5) and "Polynomials and reduced fractions" (Ring, Field);
  - `InputFormEvaluation`, and `SymbolicTermFunctions2` in `symterm.spad` (the bridge).

## 3. Part 1: the presentation axioms as a rewriting system

This is the plan of the first version, unchanged in substance. It applies to `GeneralSymbolicExpression(R, A)` with $`A \subseteq \{\text{identities}, \text{annihilation}, \text{involutions}, \text{numerals}\}`$, with or without `associativity`.

### 3.1 Syntax

Done in `lean/FricasSymbolic/Term.lean`:

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

`size` and `mu` ($`\lvert t\rvert`$ and $`\mu(t)`$ of §4.1.1) are defined there. Named functions and rational exponents are left out: no rule of $`A_P`$ or Assoc looks inside them.

A Lean `num q` with `q < 0` stands for the FriCAS form `(- n)` of a negative numeral (decision 0010). The theorems are about terms, not about their `InputForm` encoding.

### 3.2 Semantics: partial, as in the spec

Mathlib's division is total ($`x/0 = 0`$), but `Expression` raises an error, and condition (S) is stated for partial evaluation. So:

```lean
variable {K : Type} [Field K] [CharZero K]
def eval (ρ : String → K) : Term → Option K
-- div: none if the denominator evaluates to 0
-- pow with a negative exponent: none if the base is 0; 0 ^ 0 = 1 (as in FriCAS)
```

Soundness is *refinement*: if the left side is defined, the right side is defined with the same value. The right side may be defined where the left side is not; for example, Ann turns $`0 \cdot (1/0)`$ into $`0`$.

### 3.3 The normaliser

A structure of flags `Ax := {id ann inv num assoc an : Bool}` stands for $`A`$. The flag `an` (default `true`) exists only for L7, which needs a normaliser without (AN). Smart constructors `sAdd A a b`, `sSub`, `sNeg`, `sMul`, `sDiv`, `sPow` follow the Spad clauses in the same order, and `nf` builds bottom-up, as the domain does:

```lean
def nf (A : Ax) : Term → Term
  | .add a b => sAdd A (nf A a) (nf A b)
  | …
```

`sAdd` and `sMul` recurse under Assoc: `sAdd x (add y₁ y₂) = sAdd (sAdd x y₁) y₂`. The outer call's second argument is the result of no recursive call, so `termination_by (y.size, x.size)` (lexicographic) covers (A). Write the (AN) clause as `sAdd x₁ (.num (n + m))`. That is what the Spad clause `first kids x + (second kids x + y)` computes, because Num fires first on two numerals.

Points where the Lean functions cannot copy the Spad code literally:

- **Error checks.** Each Spad constructor first computes `value x ∘ value y` in `Expression R`, which raises an error on a zero denominator. The Lean constructors are total and skip this check. The theorems therefore cover more terms than the domain can build (for example $`0 \cdot (1/0)`$), which makes L5 stronger.
- **Undefined folds.** Num must not fold $`n/0`$ or $`0^{e}`$ with $`e<0`$. Mathlib's `ℚ` gives `1/0 = 0`, but FriCAS raises an error; leave those nodes unfolded.
- **Numeral tests.** Since decision 0010, `numeral?` recognises a leaf by the form of a numeral, and `lit?(x, n)` compares its value with $`n`$. In Lean both are `.num q`.

### 3.4 Theorems

| No. | Statement | Spec |
|---|---|---|
| L1 | Each smart constructor refines evaluation: `eval ρ (.add a b) = some v → eval ρ (sAdd A a b) = some v`, and likewise | (S), Lemma 1 |
| L2 | `eval ρ t = some v → eval ρ (nf A t) = some v` | (Val), Prop. 2 |
| L3 | `nf` is total: it terminates, by structural recursion plus the measure for Assoc | (T) |
| L4 | With `Step A` the root rules closed under contexts and `IsNF A t` meaning "no `Step` from `t`": `IsNF A (nf A t)` | |
| L5 | `Step A s t → nf A s = nf A t`, hence `EqvGen (Step A) s t → nf A s = nf A t` | (CR), Theorem 3 |
| L6 | `IsNF A t → nf A t = t`, hence `nf A (nf A t) = nf A t` | idempotence |
| L7 | Regression: without (AN), L5 fails; the witness is the step `x + (1+2) → (x+1)+2` (by (A)), whose two sides get `x+3` and `(x+1)+2` | §4.1.1 |
| L8 | `Relation.ReflTransGen (Step A) t (nf A t)`: the normaliser only takes steps of the axioms | |
| L9 | `Step A` is well founded (its converse is `WellFounded`), by the measure $`(\lvert t\rvert, \mu(t))`$ | (T), §4.1.1 |

L4, L5 and L8 together give the Church–Rosser property: if $`s =_A t`$ then $`s \to^* \mathrm{nf}(s) = \mathrm{nf}(t) \;{}^*\!\!\leftarrow t`$, with $`\mathrm{nf}(s)`$ a normal form. So $`\mathrm{nf}`$ chooses exactly one normal form per $`=_A`$ class. Without L8, nothing ties $`\mathrm{nf}(t)`$ to $`t`$: L2 relates their values, not their classes. Termination of the rewriting relation is L9; L3 only says that one strategy, bottom-up, ends. This route avoids formalising Newman's lemma and critical pairs in general.

**`Step` must come from the spec, not from the code.** Define the root rules from the axiom lists of spec §4.1 and §4.1.1, each with its side conditions, and not by unfolding the smart constructors. Otherwise L5 is true by construction and proves nothing about the code. In particular, (AN) is $`(x\circ n)\circ m \to x \circ k`$ with $`k`$ the folded numeral. Num on $`n/m`$ and on $`n^{e}`$ with $`e<0`$ has the side condition that the numeral denominator or base is not $`0`$.

State every theorem for all `A : Ax`, or at least for the combinations the package offers: subsets of {Id, Ann, Inv, Num}, with and without Assoc.

## 4. Part 2: the term order

`SymbolicTermOrder` compares `InputForm` trees (spec §3.5): numerals by kind (exact, then float) and value, with ties by shape; symbols, strings and other atoms by their own orders; compound terms by head, arity and arguments, recursively. Model the trees as

```lean
inductive Tree where
  | int : ℤ → Tree
  | sym : String → Tree
  | str : String → Tree
  | node : Tree → List Tree → Tree     -- head and arguments
```

with numeral recognition `numeral? : Tree → Option (Bool × ℚ)` as in `numeralForm` (integers, `(/ m n)`, float literals `(float m e b)`, and their negations `(- n)`). Prove:

| No. | Statement | Spec |
|---|---|---|
| O1 | `lt` is irreflexive and transitive | Prop. 4 |
| O2 | `lt` is total on distinct trees: `s ≠ t → lt s t ∨ lt t s` | Prop. 4 |

`Tree` is a nested inductive type (a `List Tree` inside), so the recursion goes through a mutual or `List`-aware definition. Mathlib's `List.Lex` gives the argument comparison. The proof in the spec is by induction on $`\max(\lvert s\rvert, \lvert t\rvert)`$.

## 5. Part 3: the rungs are free algebras

The ladder's normalisers are not rewriting systems (decision 0008). They compute the canonical element of a free algebra directly. So the statement to prove is an isomorphism, not confluence: $`T/{=_A} \cong F_A`$ for a known free algebra $`F_A`$. (N1) and (N2) then follow.

### 5.1 Set-up

Work over an abstract type of atoms `σ` with `[DecidableEq σ] [LinearOrder σ]`. The atoms are the normal forms whose head is not an arithmetic operator (spec §3.4, "Atoms"). Terms over `σ`:

```lean
inductive ATerm (σ : Type) where
  | num : ℚ → ATerm σ
  | atom : σ → ATerm σ
  | add | sub | mul | div : ATerm σ → ATerm σ → ATerm σ
  | neg : ATerm σ → ATerm σ
  | pow : ATerm σ → ℤ → ATerm σ
```

For a rung $`A`$, define `Step A` from the axioms of spec §3.4 (as in part 1: from the spec, with side conditions), `Equiv A := EqvGen (Step A)`, an interpretation `φ_A : ATerm σ → F_A` (partial where division by zero arises), and a read-back `rb_A : F_A → ATerm σ`.

The flat version, with atoms opaque, is exact for the Ring and Field rungs. There every non-arithmetic subterm is an atom, and the atoms are compared by identity of their (already normal) forms. The rungs without distributivity, P1–P4 and M1–M5, have products of sums as atoms of $`+`$ and sums as atoms of $`\cdot`$. For them the flat version proves one operator at a time, and the nested version (§5.4) is later work.

### 5.2 Theorems

| No. | Rung | $`F_A`$ in Mathlib | Statement |
|---|---|---|---|
| R1 | P3 (AC for $`+`$) | `Multiset σ` (with `Multiset.sort` for the read-back) | `Equiv A s t ↔ φ s = φ t` for sums of atoms |
| R2 | P4 (`linear`) | `σ →₀ ℚ`, plus a constant | the same, for linear combinations; numeral coefficients fold |
| R3 | M4, M5 (`powers`, `quotients`) | `σ →₀ ℕ`, `σ →₀ ℤ` (`Multiplicative`), with a coefficient in `ℚ` | the same, for power products |
| R4 | Ring (`ring`) | `MvPolynomial σ ℚ` | `Equiv Ring s t ↔ φ s = φ t`: the free commutative $`\mathbb{Q}`$-algebra on σ |
| R5 | Field (`field`) | `FractionRing (MvPolynomial σ ℚ)` | the same where `φ` is defined (no division by the zero polynomial) |
| R6 | each | | `Equiv A t (rb (φ t))`; with R1–R5 this gives (N1) and (N2) for `N := rb ∘ φ` |

Each "↔" has an easy and a hard half:
- **"→"** says that every axiom holds in $`F_A`$; it is a short induction on `EqvGen`.
- **"←"** says that the axioms reach every equation of $`F_A`$. It follows from R6: $`s =_A \mathrm{rb}(\varphi s) = \mathrm{rb}(\varphi t) =_A t`$.

R6 is the work: it shows by induction on the term that the axioms bring every term to the read-back of its value.

R4 is the flagship and the right place to start part 3. Mathlib does most of it (`MvPolynomial.aeval`, `MvPolynomial.induction_on`), and it is the classical theorem that the free commutative $`\mathbb{Q}`$-algebra is the polynomial ring. R1–R3 are warm-ups on one operator. R5 needs care with partiality: $`x/x = 1`$ holds where $`x \ne 0`$, and $`1/(x-x)`$ is undefined.

### 5.3 Tying the theorems to the code

R1–R6 prove that the *mathematical* normaliser $`\mathrm{rb} \circ \varphi`$ is correct and canonical. The Spad normalisers compute it incrementally, node by node, and build trees in particular shapes: the constant last, the first negative term as a unary minus, numerator over denominator, integer-scaled fractions. Two ways to tie them together, to be chosen (§8):

1. **Differential testing.** Write `rb` to produce exactly the Spad trees: terms in $`\prec`$ order, with the conventions of spec §3.4, "Trees of P4, M4 and M5". Then `#eval` it on random terms and compare with `run_fricas` on the same terms (skill `lean`, "Verification across systems"). Cheap to run; needs $`\prec`$ in Lean (part 2) and care with the conventions.
2. **Mirror the code.** Define the incremental smart constructors as in part 1, and prove that they agree with $`\mathrm{rb} \circ \varphi`$. Stronger, and much more work for P4–Field.

Option 1 is recommended.

### 5.4 Later

- **Nested atoms**, for P1–P4 and M1–M5: atoms of one operator that contain the other, e.g. $`x \cdot (y+1)`$ as an atom of $`+`$ under `linear` without `ring`. The canonical forms are then nested multisets and finite supports, which Mathlib does not have as one type.
- **Operator applications** as atoms whose arguments are normal forms, e.g. $`\sin(x + x) = \sin(2x)`$ under `linear`.
- **The admissibility amendment** of decision 0009: with `ring` and `quotients` but without `field`, the incremental normaliser gives $`(y+1)^{-1}(y+1)`$ and $`1`$ for equal terms. Stating this needs the mirrored normaliser of §5.3, option 2.

## 6. Part 4: soundness and the bridge

These theorems are short once the definitions of parts 1 and 3 exist, and they carry the most weight for users.

| No. | Statement | Spec |
|---|---|---|
| E1 | For every group of decision 0009, each axiom instance refines partial evaluation in any field $`K`$ of characteristic 0 | (S), Lemma 1: every group is sound for `Expression` |
| E2 | For `D` with `[CommRing D] [Algebra ℚ D]` and `φ : σ → D`, evaluation of terms in `D` respects `Equiv Ring`, and equals `MvPolynomial.aeval φ ∘ φ_Ring` | decision 0011: `eval` is well defined, and is the unique homomorphism |
| E3 | The same for every admissible $`A`$, given what `SymbolicTermFunctions2` checks: a commutative ring for `commutativity`, `linear`, `powers` and `ring`; a field for `quotients` and `field` (with partial evaluation); `Algebra ℚ D` for `numerals` | decision 0011: the category checks are sufficient. Weaker structures would do for some groups, e.g. a $`\mathbb{Q}`$-module for `linear` alone; the checks could then be relaxed |
| E4 | Without commutativity, evaluation into any ring (with `Algebra ℚ D` if numerals occur) respects the theory of `[associativity, identities]`; matrices are an instance | the matrix example of the tests |

E1 is part 1's L1 extended to the ladder's groups. E2 is the universal property of `MvPolynomial`. It is the precise form of decision 0011's statement that `SymbolicTerm(R, A)` is free in the variety of $`A`$.

## 7. Repository layout and environment

One Lean project per repository, in `lean/`, pinned to Lean v4.36.0 and Mathlib v4.36.0 (skill `lean`, "Pins"):

```
lean/
├── README.md               what is proved, how to build
├── lean-toolchain          leanprover/lean4:v4.36.0
├── lakefile.toml           Mathlib rev v4.36.0; library FricasSymbolic
├── lake-manifest.json      exact commits (Mathlib fc4f59e5); never `lake update`
├── FricasSymbolic.lean     imports the modules below
└── FricasSymbolic/
    ├── Term.lean           part 1: syntax, size, μ          (done)
    ├── Eval.lean           part 1: partial evaluation
    ├── Normalize.lean      part 1: Ax, smart constructors, nf
    ├── Theorems.lean       part 1: L1–L9
    ├── Order.lean          part 2: Tree, numeral?, lt; O1–O2
    ├── ATerm.lean          part 3: terms over atoms, Step and Equiv per rung
    ├── Rungs.lean          part 3: R1–R6
    ├── Bridge.lean         part 4: E1–E4
    └── Axioms.lean         #print axioms of the cited theorems
```

The Lean container runs on STRIX, and the repository is registered there. Checked on 2026-11-26:

- `run_lean` in the scratch project: status `ok`, `Lean.versionString = "4.36.0"`. The definitions of `Term.lean` with an `#eval` of the (A) step $`x+(y+z) \to (x+y)+z`$ gave sizes 5 and 5 and $`\mu`$ 4 and 2: a fall of $`\lvert z\rvert + 1`$, as spec §4.1.1 says (run `20261126-153033-term-scaffold`).
- `lean_build` of `claude/lean-ap` at `1c5a348`: status `ok`. `lake exe cache get` unpacked the Mathlib cache, and nothing of Mathlib was compiled. The only warnings are Mathlib's harmless "consider adding `module`" (log `20261126-153104-build-fricas-symbolic`).

Work cycle: edit, commit, push a `claude/<topic>` branch, `lean_build("fricas-symbolic", ref)`, read the messages; `run_lean(project="fricas-symbolic")` to probe goals between builds. A Claude Code session in the cloud cannot reach STRIX; it can install Lean in the workspace instead (skill `lean`).

## 8. Decisions for Bill (at the start of that conversation)

1. **Order of the parts.** Recommended: part 1 (already started; it is where the 2026-11-26 error was), then part 2 (small), then R4 and E2 (the core of the ladder and of the bridge), then the rest.
2. **Tying part 3 to the code** (§5.3): differential testing (recommended) or mirroring the Spad normalisers.
3. **CI:** a Lean job on changes under `lean/`, or recorded `lean_build` runs on STRIX only?
4. **Generality:** any `[Field K] [CharZero K]` in E1, and any commutative $`\mathbb{Q}`$-algebra in E2 (recommended; it costs little with Mathlib), or `ℚ` only.

## 9. Done when

For each part, separately:

- `lean_build` returns status `ok` (no errors, no `sorry`), and `#print axioms` of each cited theorem lists at most `propext`, `Classical.choice` and `Quot.sound` (skill `lean`, "Recorded results");
- spec §6 (V5) and `docs/INDEX.md` show the claims as "proved in Lean", with the theorem names, the commit and the build log: Theorem 3 and its §4.1.1 extension (part 1), Prop. 4 (part 2), (N1) and (N2) per rung (part 3), (S) per group and the bridge (part 4);
- each part arrives in its own pull request from a `claude/lean-<part>` branch.

## References

- G. Birkhoff, "On the structure of abstract algebras", *Proc. Cambridge Phil. Soc.* 31 (1935) 433–454: free algebras of a variety.
- F. Baader, T. Nipkow, *Term Rewriting and All That*, Cambridge University Press (1998): normal forms and confluence (ch. 2), critical pairs (ch. 6).
- The Mathlib Community, "The Lean mathematical library", *CPP 2020*, 367–381.
