# Plan: Lean proofs for fricas-symbolic

*2026-11-26. Planning document and hand-off for a separate conversation. Status (evening): Bill's decisions recorded (§8). Part 1 is done (§3.5): L1–L10 are proved, and the mirrored normaliser agrees with FriCAS on 9,800 random terms. Theorem 3 holds for every axiom set the package offers, now that decision 0012 adds $`-0\to 0`$ to Id; L10 is the regression for the rule set before it. Part 2 is done (§4.1): Prop. 4, the term order is a strict total order, float numerals included. R4 and E2 are proved (§5.5): Ring terms are equal under the axioms exactly when they are the same polynomial, and `eval` is the universal map. The mirror of the Spad Ring normaliser agrees with FriCAS on 2,700 random terms, and its two theorems are proved (§5.5): its read-back is correct and canonical, so with R4 the mirror decides the theory `Ring`. E1 is proved (§6.1): every axiom group of decision 0009 is sound for partial evaluation. Revised the same day for the design as it now stands: the ladder of normalisers (decisions 0008, 0009), float numerals (0010) and the bridge (0011). The file name is kept for the links to it.*

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

Mathlib's division is total ($`x/0 = 0`$), but `Expression` raises an error, and condition (S) is stated for partial evaluation. So (done in `Eval.lean`):

```lean
variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
def eval (ρ : String → K) : Term → Option K
-- div: none if the denominator evaluates to 0
-- pow with a negative exponent: none if the base is 0; 0 ^ 0 = 1 (as in FriCAS)
```

The hypotheses are what FriCAS provides for `Expression R` (§8, decision 4). `Expression R` is itself such a `K`, with each variable sent to itself, so the theorems for all such `K` and $`\rho`$ include the statement about `Expression R`.

Soundness is *refinement*: if the left side is defined, the right side is defined with the same value. The right side may be defined where the left side is not; for example, Ann turns $`0 \cdot (1/0)`$ into $`0`$.

### 3.3 The normaliser

Done in `Normalize.lean`. A structure of flags `Ax := {id ann inv num assoc an : Bool}` stands for $`A`$. The flag `an` (default `true`) exists only for L7, which needs a normaliser without (AN). Smart constructors `sAdd A a b`, `sSub`, `sNeg`, `sMul`, `sDiv`, `sPow` follow the Spad clauses in the same order, and `nf` builds bottom-up, as the domain does:

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

**Differential test** (`CrossCheck.lean`, `lean/crosscheck/crosscheck.spad`). Lean and a Spad package generate the same pseudo-random terms from the same linear congruential generator, normalise them, and return a checksum of the printed forms. Denominators and bases of negative powers are drawn from terms with nonzero values, so FriCAS raises no division error. On 2026-11-26 the checksums agreed for 13 axiom sets × 400 terms of depth 4 (seed 20261126) and 6 sets × 300 terms of depth 6 (seed 7): the sets with Num at commit `2e4c87d` (run `20261126-184801-crosscheck-fricas`), the others and the depth-6 runs at `1e4744b`, after the fix to the Spad helper described below (the Lean code is the same at both commits). The sets were every single group, $`\emptyset`$ (which shows that the two generators agree), and the combinations Id+Num, Id+Ann+Inv, $`A_P`$, $`A_P`$+Assoc, Num+Assoc, Id+Assoc and Ann+Num+Assoc. Further runs: `20261126-184901-crosscheck-fricas-2`, `…-184750-crosscheck-lean` and `…-184902-crosscheck-lean-2`. (An earlier mismatch came from Lisp's pretty-printer, which breaks long forms across lines; the Spad side now joins them.)

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
| L10 | With Id as before decision 0012 (without $`-0\to 0`$) and without Num, `0 - 0` steps to the distinct normal forms `0` (by $`x-0\to x`$) and `-0` (by $`0-x\to -x`$), so $`=_A`$ does not determine `nf` | Theorem 3, decision 0012 |

**L10 is a counterexample to spec Theorem 3** as stated ("$`A_P`$ and every union of its groups is … confluent"). The proof joins the overlap $`0-0`$ through Num ($`-0 \to 0`$), which a union without Num does not have. FriCAS agrees: in `GeneralSymbolicExpression(Integer, [identities])`, `0 - 0` has form `0` and `-0` has form `(- 0)`, with or without Ann and Inv (run `20261126-184235-id-zero-minus-zero`). The other root overlaps of $`A_P`$ do not need Num. **Resolved by decision 0012 (Bill, 2026-11-26, option (a)):** Id contains $`-0\to 0`$. In Lean, `Root` gains `id_neg_zero` and `sNeg` the matching clause. A flag `Ax.negzero` (always `true` in the package, like `an`) lets L10 state the old rule set, so L10 is now a regression test like L7. L5 is proved under the hypotheses `A.id → A.num ∨ A.negzero` and `A.an`. Both hold for every `A` the package offers (`eqA_iff_nf_eq'`), and L10 and L7 show that neither can be dropped.

L4, L5 and L8 together give the Church–Rosser property: if $`s =_A t`$ then $`s \to^* \mathrm{nf}(s) = \mathrm{nf}(t) \;{}^*\!\!\leftarrow t`$, with $`\mathrm{nf}(s)`$ a normal form. So $`\mathrm{nf}`$ chooses exactly one normal form per $`=_A`$ class. Without L8, nothing ties $`\mathrm{nf}(t)`$ to $`t`$: L2 relates their values, not their classes. Termination of the rewriting relation is L9; L3 only says that one strategy, bottom-up, ends. This route avoids formalising Newman's lemma and critical pairs in general.

**`Step` must come from the spec, not from the code.** Define the root rules from the axiom lists of spec §4.1 and §4.1.1, each with its side conditions, and not by unfolding the smart constructors. Otherwise L5 is true by construction and proves nothing about the code. In particular, (AN) is $`(x\circ n)\circ m \to x \circ k`$ with $`k`$ the folded numeral. Num on $`n/m`$ and on $`n^{e}`$ with $`e<0`$ has the side condition that the numeral denominator or base is not $`0`$.

State every theorem for all `A : Ax`, or at least for the combinations the package offers: subsets of {Id, Ann, Inv, Num}, with and without Assoc.

### 3.5 Recorded results

Commit `3f47236` on `claude/lean-part1`, Lean 4.36.0 and Mathlib v4.36.0, 2026-11-26. `lean_build` status `ok` (log `20261126-185346-build-fricas-symbolic`). `#print axioms` of every theorem below lists only `propext`, `Classical.choice` and `Quot.sound` (run `20261126-185354-axioms-part1`, file `lean/Axioms.lean`). No CI builds Lean (§8).

| No. | Lean | What it says |
|---|---|---|
| L1 | `sAdd_refines`, `sSub_refines`, `sNeg_refines`, `sMul_refines`, `sDiv_refines`, `sPow_refines` | for every `A`, every field `K` of characteristic 0 and every assignment ρ: if the node as written has value $`v`$, the node the constructor builds has value $`v`$ |
| L2 | `nf_refines` | the same for `nf`, by induction on the term: (Val) |
| L3 | the definitions of `sAdd`, `sMul` and `nf` | Lean accepts them only with a termination proof: `termination_by (y.size, x.size)` for `sAdd` and `sMul`, structural recursion for `nf` |
| L7 | `L7_without_AN`, `L7_with_AN` | with (AN) switched off, the (A) step `x+(1+2) → (x+1)+2` joins terms whose normal forms are `x+3` and `(x+1)+2`; with (AN) both are `x+3` |
| L10 | `L10_id_without_num`, `L10_not_confluent`, `L10_with_negzero` | for `A = {Id}` without $`-0\to 0`$: `0-0` steps to `0` and to `-0`, both normal forms, so some $`s =_A t`$ have $`\mathrm{nf}(s) \ne \mathrm{nf}(t)`$; with the rule (decision 0012), both normalise to `0` |

**Termination, normal forms and confluence** (`Confluence.lean`). Commit `ffee161` on `claude/lean-confluence` (after merging decision 0012), `lean_build` status `ok` (log `20261126-223605-build-fricas-symbolic`); `#print axioms` of every theorem below and above lists only `propext`, `Classical.choice` and `Quot.sound` (runs `20261126-204522-axioms-part1-confluence` and `20261126-223634-part1-0012-axioms-crosscheck`).

**Differential test after decision 0012.** At `ffee161`, with `gsexpr.spad` containing the new clause, the checksums agree for 14 axiom sets (the 13 above and Id+Inv), each at depth 4 (400 terms, seed 20261126) and depth 6 (300 terms, seed 7): 9,800 terms (runs `20261126-223637-crosscheck-fricas-0012` and `20261126-223634-part1-0012-axioms-crosscheck`). The sets with Id and without Num changed checksum from the earlier runs on both sides, as the new rule predicts.

| No. | Lean | What it says |
|---|---|---|
| L9 | `L9_terminating` | for every `A`, `Step A` is well founded: every step lowers $`(\lvert t\rvert, \mu(t))`$ lexicographically (`step_decreases`) |
| L4 | `L4_nf_isNF` | for every `A`, `nf A t` is a normal form; each smart constructor maps normal forms to normal forms |
| L6 | `L6_nf_of_isNF`, `nf_nf` | for every `A`, `nf` fixes normal forms, hence is idempotent |
| L8 | `L8_steps_to_nf` | for every `A`, $`t \to^* \mathrm{nf}(t)`$: each clause of each smart constructor is a sequence of rule applications |
| — | `sAdd_assoc`, `sMul_assoc`, `sAdd_an`, `sMul_an` | with associativity and (AN), the smart constructors for $`+`$ and $`\cdot`$ are associative on normal forms, and satisfy (AN) on them |
| L5 | `L5_step`, `L5_eqA`, `eqA_iff_nf_eq`, `eqA_iff_nf_eq'` | if Id comes with Num or with $`-0\to 0`$, and (AN) is on: $`s =_A t \iff \mathrm{nf}(s) = \mathrm{nf}(t)`$. `eqA_iff_nf_eq'` states it for every `A` the package offers, with no hypothesis |
| — | `church_rosser`, `unique_nf` | under the same hypotheses: $`s =_A t`$ implies a common reduct, and two normal forms equal under $`A`$ are the same term |

**In words.** `EqA A` is the equivalence relation generated by the rules of spec §4.1 and §4.1.1 applied anywhere in a term: the equational theory $`=_A`$ of §2.3, with Num's side conditions. `nf A` is the function that `GeneralSymbolicExpression(R, A)` computes when it builds a term bottom-up (§3.3, with the differential test). So `eqA_iff_nf_eq'` says that for every union of the groups Id, Ann, Inv, Num and Assoc, the domain's normal form decides $`=_A`$. With L9 (termination) and L1 (soundness) this is Theorem 3 as amended by decision 0012. Without the amendment, L10 shows the theorem is false for Id without Num.

**How the proof goes.** L5's root cases reduce to identities between smart constructors on normal forms (`L5_root`). All are local except associativity. `sAdd_assoc` follows the clauses of `sAdd A Y Z`, by well-founded recursion on $`(\lvert Z\rvert, \lvert Y\rvert)`$. Its two key lemmas are `sAdd_an`, which is (AN) on normal forms by induction on the left operand, and `sAdd_add_right`, which says $`W + (Z_1+Z_2) = (W+Z_1)+Z_2`$ for a normal form $`Z_1+Z_2`$. The (AN) case of the recursion is exactly the critical pair $`x+(1+2)`$ of 2026-11-26: it needs `sAdd_an`, which needs (AN). `sMul_assoc` is the same, with three more cases for annihilation and the identity.

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

### 4.1 Recorded results (2026-11-26)

Branch `claude/lean-order`, commit `d31fe49`, Lean 4.36.0 and Mathlib v4.36.0. `lean_build` status `ok` (log `20261126-233138-build-fricas-symbolic`). `#print axioms` of every theorem below lists only `propext`, `Classical.choice` and `Quot.sound` (run `20261126-233148-axioms-part2`).

**The mirror** (`Order.lean`). `Tree` models `InputForm` trees: integer atoms, float atoms, symbols, strings, other atoms, and compound forms `(head arg₁ … argₙ)`. `numeralForm`, `kind`, `lt` (`smaller?`), `structural` (`structural?`) and `ltList` (its argument loop) follow the Spad code clause by clause. Float numerals are included (Bill, 2026-11-26): a float atom by its exact value, a float literal `(float m e b)` or `(($elt DoubleFloat float) m e b)` by its tree. Checked against FriCAS, or stated as assumptions:

- `Symbol`'s `smaller?` and `String`'s `<` are the order of Lean's `String` (by character code): checked on symbols `X, a, ab, b, float, sin, x, x1, y` and strings `"", "B", "a", "ab", "b"` (runs `20261126-232443-order-probe`, `…-232458-order-probe-2`).
- Two distinct float atoms have distinct values: integral doubles convert to integer atoms, and `0.0` and `-0.0` both to the integer `0` (checked), so the gap a signed zero could open does not arise.
- Other atoms compare by `unparse`, so they are modelled by that string. This assumes `unparse` is injective on them (assumption; no such atoms occur in the package's forms).

**Differential test** (`Order.lean`, `Check`; `lean/crosscheck/ordercheck.spad`). Both sides generate the same pseudo-random trees: numerals of every form, quotients with zero denominators, float literals with bases 0–3, compound trees with numeral and compound heads. Each side compares all ordered pairs. For seeds 20261126, 7 and 42, 60 trees at depths 3 and 4, the count of `true` results and the checksum agree: 21,600 comparisons (runs `20261126-232647-ordercheck-fricas`, `…-232630-ordercheck-lean`, and `…-233122-part2-axioms-crosscheck` after the last change to `lt`).

| No. | Lean (`OrderProofs.lean`) | What it says |
|---|---|---|
| O1 | `O1_irrefl`, `O1_trans` | `lt t t = false`; `lt a b` and `lt b c` give `lt a c`, for all trees |
| O2 | `O2_total` | `a ≠ b` gives `lt a b` or `lt b a` |
| — | `isStrictTotalOrder` | Mathlib's `IsStrictTotalOrder Tree (lt · · = true)` |

**In words.** Prop. 4 holds for `SymbolicTermOrder` as written, on every tree of the model, float numerals included: the order is a strict total order. The proof (`good_depth`) is by strong induction on depth. If `lt` is a strict total order on the trees of depth $`< d`$, then the argument loop is a strict order on lists of them, total on distinct lists of the same length. `structural` is then a strict order, total unless both trees are atoms. And `lt` is a strict total order on the trees of depth $`< d+1`$, being lexicographic in kind, then value, string or nothing, then `structural`. The one place `structural` cannot separate two trees, two distinct atoms, never arises: two numeral atoms of the same kind and value are the same atom.

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

**Decided (Bill, 2026-11-26): mirror the code (option 2).** The differential test of part 1 (§3.3) stays as a cheap check that the mirror is faithful, and extends to the rungs.

### 5.4 Later

- **Nested atoms**, for P1–P4 and M1–M5: atoms of one operator that contain the other, e.g. $`x \cdot (y+1)`$ as an atom of $`+`$ under `linear` without `ring`. The canonical forms are then nested multisets and finite supports, which Mathlib does not have as one type.
- **Operator applications** as atoms whose arguments are normal forms, e.g. $`\sin(x + x) = \sin(2x)`$ under `linear`.
- **The admissibility amendment** of decision 0009: with `ring` and `quotients` but without `field`, the incremental normaliser gives $`(y+1)^{-1}(y+1)`$ and $`1`$ for equal terms. Stating this needs the mirrored normaliser of §5.3, option 2.

### 5.5 R4 and E2: recorded results (2026-11-27)

Branch `claude/lean-ring` (on top of `claude/lean-order`), `Ring.lean`. `lean_build` status `ok` at `b9a5203` (log `20261127-140417-build-fricas-symbolic`); `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` (run `20261127-140440-axioms-r4-e2`).

**Terms and axioms.** `RTerm σ` has numerals, atoms, $`+`$, $`-`$ (binary and unary), $`\cdot`$, powers with exponent in $`\mathbb{N}`$, and division by a numeral (`divn`). These are exactly the operations the Spad Ring rung reads as polynomial operations (`toF`; anything else is an atom). `Step` is the standard presentation of commutative $`\mathbb{Q}`$-algebras: associativity, commutativity and identities of $`+`$ and $`\cdot`$; $`-x + x \to 0`$; $`x - y \to x + (-y)`$; $`0\cdot x \to 0`$; distributivity; numeral folding of $`+`$ and $`\cdot`$; $`x^0 \to 1`$, $`x^{n+1} \to x^n\cdot x`$; $`x/q \to x\cdot q^{-1}`$ for a numeral $`q \ne 0`$. Each rule is a law of the groups that `ring` requires (§3.4 of the spec names them only by group, so this list is the Lean reading of "the axioms of the rung `ring`").

| No. | Lean | What it says |
|---|---|---|
| R4 | `R4_equiv_iff` | for terms without division by the numeral $`0`$ (`Defined`): $`s =_{\mathrm{Ring}} t \iff \varphi(s) = \varphi(t)`$ in `MvPolynomial σ ℚ` |
| — | `phi_equiv` | "→" alone, for all terms: every axiom holds in the polynomial ring |
| — | `psi_phi` | $`\psi(\varphi(t)) = [t]`$, where $`\psi = `$ `aeval (atom ·)` maps into the terms modulo the axioms |
| E2 | `E2_eval_eq_aeval` | for every `[CommRing D] [Algebra ℚ D]` and `f : σ → D`: evaluating a term in `D` equals `aeval f (φ t)` |
| E2 | `E2_eval_respects` | evaluation respects $`=_{\mathrm{Ring}}`$, so `eval` is well defined on the quotient |
| E2 | `E2_unique` | `aeval f` is the only $`\mathbb{Q}`$-algebra map from `MvPolynomial σ ℚ` to `D` extending `f` |

**How the proof goes.** The terms modulo the axioms form a commutative ring `Q σ`: each ring law is one axiom, or two composed. With numerals, `Q σ` is a $`\mathbb{Q}`$-algebra, since `num_add` and `num_mul` make $`q \mapsto [q]`$ a ring map. The universal property of `MvPolynomial` gives $`\psi`$, and $`\psi(\varphi(t)) = [t]`$ by induction on $`t`$. So $`\varphi(s) = \varphi(t)`$ gives $`[s] = [t]`$. No read-back is needed for R4 itself. The restriction to `Defined` terms is necessary: $`x/0`$ and $`0`$ have the same image under Mathlib's total division, but no axiom relates them.

**In words.** Two Ring terms are equal under the Ring axioms exactly when they are the same polynomial over $`\mathbb{Q}`$ in their atoms: $`\mathbb{Q}[\sigma]`$ is the free commutative $`\mathbb{Q}`$-algebra. And for any commutative ring `D` containing $`\mathbb{Q}`$, evaluation of terms is well defined modulo the axioms and is the unique algebra map extending the values of the atoms. That is decision 0011's `eval` for the rung `ring`, with exactly the categories `SymbolicTermFunctions2` checks.

**The mirror** (§5.3, option 2; `RingMirror.lean`, 2026-11-27). The Spad constructors of the rung `ring` are `fromF ∘ op ∘ toF`, and `RingMirror.lean` follows that code on the trees of part 2 (`Order.Tree`, the `InputForm` of a node). The pieces mirrored are:
- `ratoms`, `toF` (with `intExp` and `rpow`), and `fromF` for the constant denominators of this rung, which is `linOf`: `toLin`, `linBuild`, `mergeT`, and monomials from `prodBuild`, `mergeF`, `facNode` and `mulChain`;
- the clauses of `+`, `-`, `*`, `/` and `^` in front of the Ring clause: numeral folding, the identities, annihilation and involutions;
- the leaves `numNode` and `intNode`.

The polynomial arithmetic is naive (lists of terms), because `linBuild` merges equal monomials and drops zero coefficients, as in the Spad code.

**Differential test** (`RingMirror.Check`; `lean/crosscheck/ringcheck.spad`). The same pseudo-random terms are built on both sides: symbols, numerals, $`+`$, $`-`$, $`\cdot`$, division by a numeral, division by a nonzero term (an atom of the rung), and powers with exponents $`-1`$ to $`3`$ (negative exponents are atoms). For $`A_1`$ = `[commutativity, associativity, identities, numerals, linear, powers, ring]` and $`A_2 = A_1`$ + `[annihilation, involutions]`, seeds 20261126, 7 and 42, 300 terms of depth 3 and 150 of depth 4, the checksums of the printed forms agree: 2,700 terms (runs `20261127-141927-ringcheck-fricas`, `…-141928-ringmirror-crosscheck`). The spec's examples agree too: $`x(x+1)`$ gives `x+x^2`, $`(x+1)(x-1)`$ gives `x^2-1`, $`y-2x+1`$ gives `(-(2*x))+y+1` (run `…-141846-ringcheck-probe`). An earlier mismatch came from Lisp's printer, which labels a subtree that occurs twice (`#1=(/ y z)` … `#1#`); the Spad helper now prints forms itself.

**Read-back: recorded results** (`RingReadback.lean`, 2026-11-27). Merged to `main` as `6c6d70b` (PR #25, from commit `49d2efa` on `claude/lean-ring-readback`), Lean 4.36.0 and Mathlib v4.36.0. `lean_build` status `ok` at `6c6d70b` (log `20261127-151546-build-fricas-symbolic`; at `49d2efa`, log `20261127-150004-build-fricas-symbolic`); `#print axioms` of each theorem below lists only `propext`, `Classical.choice` and `Quot.sound` (run `20261127-150021-ringreadback-axioms`).

A tree is read as a polynomial by `rd : Tree → MvPolynomial Tree ℚ`, clause by clause as `toF`, with the variable $`X_t`$ at an atom $`t`$. An *atom of the rung* (`IsAtom`) is a tree that reads back as its own variable. A polynomial `p` over the atom list `al` is *well formed* (`WF`) when the trees of `al` are atoms of the rung, its indices are in range and its exponents are positive, as `toF` produces them. A *normal form* (`NF`) is `fromP al p` for a well-formed `p`.

| Lean | What it says |
|---|---|
| `rd_fromP` | **read-back is correct**: `rd (fromP al p)` is the polynomial of `p`, the index $`i`$ read as `al[i]`; no hypotheses |
| `rd_rAdd`, `rd_rSub`, `rd_rNeg`, `rd_rMul`, `rd_rDiv`, `rd_rPow` | each constructor is the polynomial operation: `rd (rAdd x y) = rd x + rd y`, and so on (`rDiv` by a numeral, `rPow` with exponent in $`\mathbb{N}`$); no hypotheses |
| `fromP_canonical` | **read-back is canonical**: for well-formed `p` over `al` and `p'` over `al'`, the same polynomial gives the same tree |
| `NF_canonical` | two normal forms with the same `rd` are the same tree |
| `rd_nfR`, `NF_nfR` | the normaliser `nfR : RTerm String → Tree`, built from the constructors with symbols as atoms, gives a normal form whose `rd` is `rename sym (φ t)` |
| `nfR_eq_iff` | **(N1) and (N2) for the mirror**: for defined terms, `nfR A s = nfR A t` $`\iff`$ $`s =_{\mathrm{Ring}} t`$, for every choice of the optional groups `annihilation`, `involutions` |

**How the proofs go.** Correctness is bookkeeping: the merge functions keep the sum over equal keys, the sorts are permutations, and the shapes `linBuild` prints ($`-t`$, $`a + t`$, $`a - t`$, the constant last) read back to the signed sum. Canonicity has two levels. A monomial's factor list depends only on its exponent vector: `mergeF` leaves one entry per base, holding the sum of its exponents, so two monomials with the same vector give permutations of the same list, and sorting by part 2's order turns those into the same list. Over atoms of the rung, the key `mulChain 1` of a factor list reads back as the monomial $`X^n`$, so equal keys mean equal monomials. Then the entries that survive `mergeT` are exactly the pairs (factor list of $`n`$, coefficient of $`X^n`$) with nonzero coefficient, and a list sorted strictly by key is determined by its entries. The constant is the coefficient of $`X^0`$. Finally, normal forms are closed under the constructors: the atoms `ratoms` collects from a normal form are atoms of the rung, and `toF` of an operand is well formed. So `nfR` gives normal forms, and with R4 and the injectivity of `rename sym`, equal trees correspond exactly to equal polynomials and to $`=_{\mathrm{Ring}}`$.

**What it covers.** The theorems are about the Lean mirror; the mirror agrees with the Spad code on the differential test above (2,700 terms). `nfR` is the bottom-up use of the constructors on terms of the Ring fragment (symbols, numerals, $`+`$, $`-`$, $`\cdot`$, powers with exponent in $`\mathbb{N}`$, division by a numeral). Atoms other than symbols, such as $`x/y`$ or $`x^{-1}`$, enter the canonicity theorem only through `IsAtom`. Sanity check: `nfR` of $`(x+1)(x-1)`$ and of $`x^2-1`$ both print `(- (^ x 2) 1)` (run `20261127-150029-nfR-sanity`).

## 6. Part 4: soundness and the bridge

These theorems are short once the definitions of parts 1 and 3 exist, and they carry the most weight for users.

| No. | Statement | Spec |
|---|---|---|
| E1 | For every group of decision 0009, each axiom instance refines partial evaluation in any field $`K`$ of characteristic 0 | (S), Lemma 1: every group is sound for `Expression` |
| E2 | For `D` with `[CommRing D] [Algebra ℚ D]` and `φ : σ → D`, evaluation of terms in `D` respects `Equiv Ring`, and equals `MvPolynomial.aeval φ ∘ φ_Ring` | decision 0011: `eval` is well defined, and is the unique homomorphism |
| E3 | The same for every admissible $`A`$, given what `SymbolicTermFunctions2` checks: a commutative ring for `commutativity`, `linear`, `powers` and `ring`; a field for `quotients` and `field` (with partial evaluation); `Algebra ℚ D` for `numerals` | decision 0011: the category checks are sufficient. Weaker structures would do for some groups, e.g. a $`\mathbb{Q}`$-module for `linear` alone; the checks could then be relaxed |
| E4 | Without commutativity, evaluation into any ring (with `Algebra ℚ D` if numerals occur) respects the theory of `[associativity, identities]`; matrices are an instance | the matrix example of the tests |

E1 is part 1's L1 extended to the ladder's groups. E2 is the universal property of `MvPolynomial`. It is the precise form of decision 0011's statement that `SymbolicTerm(R, A)` is free in the variety of $`A`$.

### 6.1 E1: recorded results (2026-11-27)

Branch `claude/lean-e1`, `Groups.lean`, commit `32e28aa`, Lean 4.36.0 and Mathlib v4.36.0. `lean_build` status `ok` (log `20261127-152212-build-fricas-symbolic`); `#print axioms` of each theorem below lists only `propext`, `Classical.choice` and `Quot.sound` (run `20261127-152218-axioms-e1`).

**The axioms of the groups.** Part 1's `Root` lists the rules of `identities`, `annihilation`, `involutions`, `numerals` and `associativity` (with (AN)). Spec §3.4 names the axioms of the other groups without listing them, so `Ladder` gives the Lean reading, from the spec's tables and checked against the clauses of `gsexpr.spad` that each group enables ($`n, m`$ numerals):

| Group | Rules (oriented as the normaliser applies them) |
|---|---|
| `commutativity` | $`x+y \to y+x`$, $`x\cdot y \to y\cdot x`$ |
| `linear` | $`x-y \to x+(-1)\cdot y`$, $`-x \to (-1)\cdot x`$, $`n\cdot x+m\cdot x \to (n+m)\cdot x`$, $`n\cdot(m\cdot x) \to (nm)\cdot x`$, $`n\cdot(x+y) \to n\cdot x+n\cdot y`$, $`0\cdot x \to 0`$. Division is not linear: $`x/2`$ is an atom |
| `powers` | $`x^m x^n \to x^{m+n}`$, $`(x^m)^n \to x^{mn}`$, $`(xy)^n \to x^n y^n`$, for $`m, n \ge 0`$ |
| `quotients` | $`x/y \to x\cdot y^{-1}`$, and the three power rules for all $`m, n \in \mathbb{Z}`$; Divides follows: $`x\cdot x^{-1} = x^1 x^{-1} \to x^0 \to 1`$ |
| `ring` | $`x\cdot(y+z) \to x\cdot y+x\cdot z`$; $`x/q \to q^{-1}\cdot x`$ for a numeral $`q \ne 0`$ |
| `field` | no rule of its own: with `ring` and `quotients` it is the theory of reduced fractions, and it lets those two groups be used together (decision 0009, amended) |

| Lean | What it says |
|---|---|
| `E1_root` | every instance of every rule of part 1's groups refines evaluation: where the left side has a value in a field of characteristic 0, the right side has the same value |
| `E1_ladder` | the same for every rule of `Ladder` |
| `E1_step`, `E1_steps` | the same for one step, and for any number of steps, of any union of the groups, at any position (`GStep`): Lemma 1 in its oriented form, and (N3) for any normaliser whose result is reached by such steps |
| `quo_add_reversed_unsound` | must fail: read right to left, `quo_add` turns the defined $`0^0`$ into the undefined $`0^1\cdot 0^{-1}`$, so the orientation matters |
| `anticommutative_unsound` | must fail: the 2017 AntiCommutative axiom $`x\cdot y \to -(y\cdot x)`$ is unsound, which is why it has no group |

**Side conditions.** Only rules that divide or take a negative power need care, and there "the left side is defined" is exactly the condition needed. For example, $`x^m x^n \to x^{m+n}`$ with $`x = 0`$ is defined only for $`m, n \ge 0`$, where $`0^{m+n} = 0^m 0^n`$ ($`0^0 = 1`$, as in FriCAS). $`(x^m)^n \to x^{mn}`$ with $`x = 0`$ and $`m > 0`$ needs $`n \ge 0`$ on the left, since $`0^m = 0`$. No rule needs $`x \ne 0`$ as an extra hypothesis.

**For the spec.** The table above could replace the group names in spec §3.4 ("Axiom groups and admissible sets"), so that the spec, the Spad code and Lean list the same rules. That is a change to what the constructors promise, so it is for Bill to decide (AGENTS.md).

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
    ├── Term.lean           part 1: syntax, size, μ                     (done)
    ├── Eval.lean           part 1: partial evaluation                  (done)
    ├── Normalize.lean      part 1: Ax, smart constructors, nf          (done)
    ├── Form.lean           part 1: forms as FriCAS prints them         (done)
    ├── CrossCheck.lean     part 1: differential test with crosscheck/  (done)
    ├── Soundness.lean      part 1: L1, L2                              (done)
    ├── Rewriting.lean      part 1: Root, Step, IsNF, EqA from the spec (done)
    ├── Regressions.lean    part 1: L7, L10                             (done)
    ├── Confluence.lean     part 1: L4–L6, L8, L9; Theorem 3          (done)
    ├── Order.lean          part 2: Tree, numeralForm, lt; differential test  (done)
    ├── OrderProofs.lean    part 2: O1, O2                              (done)
    ├── ATerm.lean          part 3: terms over atoms, Step and Equiv per rung
    ├── Rungs.lean          part 3: R1–R6
    └── Bridge.lean         part 4: E1–E4
lean/Axioms.lean            #print axioms of the cited theorems (outside the library)
lean/crosscheck/            the Spad side of the differential test
```

The Lean container runs on STRIX, and the repository is registered there. Checked on 2026-11-26:

- `run_lean` in the scratch project: status `ok`, `Lean.versionString = "4.36.0"`. The definitions of `Term.lean` with an `#eval` of the (A) step $`x+(y+z) \to (x+y)+z`$ gave sizes 5 and 5 and $`\mu`$ 4 and 2: a fall of $`\lvert z\rvert + 1`$, as spec §4.1.1 says (run `20261126-153033-term-scaffold`).
- `lean_build` of `claude/lean-ap` at `1c5a348`: status `ok`. `lake exe cache get` unpacked the Mathlib cache, and nothing of Mathlib was compiled. The only warnings are Mathlib's harmless "consider adding `module`" (log `20261126-153104-build-fricas-symbolic`).

Work cycle: edit, commit, push a `claude/<topic>` branch, `lean_build("fricas-symbolic", ref)`, read the messages; `run_lean(project="fricas-symbolic")` to probe goals between builds. A Claude Code session in the cloud cannot reach STRIX; it can install Lean in the workspace instead (skill `lean`).

## 8. Decisions (Bill, 2026-11-26)

1. **Order of the parts:** part 1, then part 2, then R4 and E2 (Ring and the bridge), then the rest.
2. **Tying part 3 to the code:** mirror the Spad normalisers in Lean (§5.3, option 2), keeping the differential test as a check.
3. **CI:** none for Lean. Results are recorded `lean_build` runs on STRIX (skill `lean`, "Recorded results").
4. **Generality:** the hypotheses of the soundness theorems are limited to what FriCAS provides, explicitly (the categories the code checks) or implicitly (the categories of the domains it uses). Each FriCAS category is matched by the Mathlib class with the same meaning, with nothing weaker (no semirings or modules where FriCAS asks for a ring) and nothing stronger (no orderings, no `ℚ` only):

   | FriCAS | Mathlib | Used in |
   |---|---|---|
   | `Expression R` with `R : GcdDomain` and `CharacteristicZero` (so a `Field` with `CharacteristicZero`), and `=` from `SetCategory` | `[Field K] [CharZero K] [DecidableEq K]` | part 1 (L1, L2); E1 |
   | `D : Ring` (`SymbolicTermFunctions2`, `InputFormEvaluation`) | `[Ring D]` | E4 |
   | `D has CommutativeRing` (for `commutativity`, `linear`, `powers`, `ring`) | `[CommRing D]` | E2, E3 |
   | `D has Field` (for `quotients`, `field`); partial evaluation needs `=` | `[Field D] [DecidableEq D]` | E3 |
   | `D has Algebra(Fraction Integer)` (for `numerals`) | `[Algebra ℚ D]` | E2–E4 |

   E3's remark that weaker structures would do for some groups stays a remark: the theorems use the categories FriCAS checks.

**Decided after the first round:**

5. **Theorem 3 and Id without Num** (L10). **Decided (Bill, 2026-11-26): option (a), decision [0012](../decisions/0012-minus-zero.md).** The three ways to repair the spec were:
   - (a) add $`-0 \to 0`$ to Id. It is sound, shrinks the term, and is what Knuth–Bendix completion adds; the Spad change is one clause in unary `-`;
   - (b) make Id require Num (`SymbolicAxiomGroups.requires`). This removes `[identities]` alone, which the tests use for G1 and G3;
   - (c) weaken Theorem 3 to unions in which Id comes with Num, and document the two normal forms of `0 - 0` otherwise.

   (a) keeps every combination the package offers, and it is the smallest change to the presentation.

## 9. Done when

For each part, separately:

- `lean_build` returns status `ok` (no errors, no `sorry`), and `#print axioms` of each cited theorem lists at most `propext`, `Classical.choice` and `Quot.sound` (skill `lean`, "Recorded results");
- spec §6 (V5) and `docs/INDEX.md` show the claims as "proved in Lean", with the theorem names, the commit and the build log: Theorem 3 and its §4.1.1 extension (part 1), Prop. 4 (part 2), (N1) and (N2) per rung (part 3), (S) per group and the bridge (part 4);
- each part arrives in its own pull request from a `claude/lean-<part>` branch.

## References

- G. Birkhoff, "On the structure of abstract algebras", *Proc. Cambridge Phil. Soc.* 31 (1935) 433–454: free algebras of a variety.
- F. Baader, T. Nipkow, *Term Rewriting and All That*, Cambridge University Press (1998): normal forms and confluence (ch. 2), critical pairs (ch. 6).
- The Mathlib Community, "The Lean mathematical library", *CPP 2020*, 367–381.
