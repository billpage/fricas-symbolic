import FricasSymbolic.Rewriting
import FricasSymbolic.Soundness
import Mathlib.Tactic.Ring

/-!
# E1: every axiom group of decision 0009 is sound for partial evaluation

Plan §6, E1; spec §2.3, condition (S) and Lemma 1.

The groups `identities`, `annihilation`, `involutions`, `numerals` and `associativity`
(with (AN)) are part 1's `Root` rules. `Ladder` lists the rules of the other groups as spec §3.4
("Axiom groups and admissible sets") states them since decision 0013, checked against
the clauses of `src/algebra/gsexpr.spad` that each group enables. Each rule is oriented as the normaliser applies it; `n`, `m`
are numerals (`.num`):

* `commutativity`: $x+y → y+x$, $x·y → y·x$.
* `linear` (P4: Doubles, Cancels, signed sums, scalar multiplication):
  $x-y → x+(-1)·y$, $-x → (-1)·x$, $n·x+m·x → (n+m)·x$, $n·(m·x) → (nm)·x$,
  $n·(x+y) → n·x+n·y$, $0·x → 0$. Division is not linear: $x/2$ is an atom.
* `powers` (M4: Squares, power products with exponents in ℕ):
  $x^m·x^n → x^{m+n}$, $(x^m)^n → x^{mn}$, $(x·y)^n → x^n·y^n$ for $m, n ≥ 0$.
* `quotients` (M5: Divides, exponents in ℤ): $x/y → x·y^{-1}$, and the three power
  rules for all $m, n ∈ ℤ$. Divides, $x/x → 1$, follows: $x·x^{-1} = x^1·x^{-1} → x^0 → 1$.
* `ring` (distributivity): $x·(y+z) → x·y+x·z$, and $x/q → q^{-1}·x$ for a numeral
  $q ≠ 0$ (the Spad Ring clause reads a division by a numeral as scaling).
* `field`: no rule of its own. With `ring` and `quotients` it is the theory of
  reduced fractions; it exists so that `ring` and `quotients` may be used together
  (decision 0009, amended), and the normaliser then works with arbitrary
  denominators.

E1 (`E1_root`, `E1_ladder`): every instance $l → r$ of every rule refines evaluation:
wherever $l$ has a value in a field of characteristic 0, $r$ has the same value. The
side conditions where a rule divides or takes a negative power are exactly "the left
side is defined". `E1_steps`: the same for any number of steps of any union of the
groups, at any position.
-/

namespace FricasSymbolic

open Term

/-- The groups of decision 0009 beyond part 1's. -/
inductive Group where
  | commutativity | linear | powers | quotients | ring | field
  deriving DecidableEq

/-- The axioms of the ladder's groups, oriented as the normalisers apply them. -/
inductive Ladder : Group → Term → Term → Prop
  -- commutativity
  | comm_add (x y : Term) : Ladder .commutativity (.add x y) (.add y x)
  | comm_mul (x y : Term) : Ladder .commutativity (.mul x y) (.mul y x)
  -- linear
  | lin_sub (x y : Term) : Ladder .linear (.sub x y) (.add x (.mul (.num (-1)) y))
  | lin_neg (x : Term) : Ladder .linear (.neg x) (.mul (.num (-1)) x)
  | lin_collect (x : Term) (n m : ℚ) :
      Ladder .linear (.add (.mul (.num n) x) (.mul (.num m) x)) (.mul (.num (n + m)) x)
  | lin_scale (x : Term) (n m : ℚ) :
      Ladder .linear (.mul (.num n) (.mul (.num m) x)) (.mul (.num (n * m)) x)
  | lin_distrib (x y : Term) (n : ℚ) :
      Ladder .linear (.mul (.num n) (.add x y)) (.add (.mul (.num n) x) (.mul (.num n) y))
  | lin_zero (x : Term) : Ladder .linear (.mul (.num 0) x) (.num 0)
  -- powers: exponents in ℕ
  | pow_add (x : Term) (m n : ℤ) : 0 ≤ m → 0 ≤ n →
      Ladder .powers (.mul (.pow x m) (.pow x n)) (.pow x (m + n))
  | pow_pow (x : Term) (m n : ℤ) : 0 ≤ m → 0 ≤ n →
      Ladder .powers (.pow (.pow x m) n) (.pow x (m * n))
  | pow_mul (x y : Term) (n : ℤ) : 0 ≤ n →
      Ladder .powers (.pow (.mul x y) n) (.mul (.pow x n) (.pow y n))
  -- quotients: exponents in ℤ
  | quo_div (x y : Term) : Ladder .quotients (.div x y) (.mul x (.pow y (-1)))
  | quo_add (x : Term) (m n : ℤ) :
      Ladder .quotients (.mul (.pow x m) (.pow x n)) (.pow x (m + n))
  | quo_pow (x : Term) (m n : ℤ) : Ladder .quotients (.pow (.pow x m) n) (.pow x (m * n))
  | quo_mul (x y : Term) (n : ℤ) :
      Ladder .quotients (.pow (.mul x y) n) (.mul (.pow x n) (.pow y n))
  -- ring
  | ring_distrib (x y z : Term) :
      Ladder .ring (.mul x (.add y z)) (.add (.mul x y) (.mul x z))
  | ring_divn (x : Term) (q : ℚ) : q ≠ 0 → Ladder .ring (.div x (.num q)) (.mul (.num q⁻¹) x)

section Rules

variable {K : Type*} [Field K] [DecidableEq K] (ρ : String → K)

/-- The three power rules, for all exponents in ℤ, where the left side is defined. -/
theorem zpow_add_rule {x : Term} {m n : ℤ} {v : K}
    (h : (Term.mul (.pow x m) (.pow x n)).eval ρ = some v) : (Term.pow x (m + n)).eval ρ = some v := by
  obtain ⟨a, b, ha, hb, rfl⟩ := (eval_mul ρ).1 h
  obtain ⟨u, hu, hu0, rfl⟩ := (eval_pow ρ).1 ha
  obtain ⟨u', hu', hu0', rfl⟩ := (eval_pow ρ).1 hb
  rw [hu] at hu'
  cases hu'
  refine (eval_pow ρ).2 ⟨u, hu, ?_, ?_⟩
  · rintro ⟨rfl, hmn⟩
    have hm : 0 ≤ m := by by_contra h'; exact hu0 ⟨rfl, by omega⟩
    have hn : 0 ≤ n := by by_contra h'; exact hu0' ⟨rfl, by omega⟩
    omega
  · by_cases hz : u = 0
    · subst hz
      have hm : 0 ≤ m := by by_contra h'; exact hu0 ⟨rfl, by omega⟩
      have hn : 0 ≤ n := by by_contra h'; exact hu0' ⟨rfl, by omega⟩
      by_cases h0 : m + n = 0
      · have : m = 0 ∧ n = 0 := by omega
        rw [this.1, this.2]; simp
      · exact zpow_add' (Or.inr (Or.inl h0))
    · exact zpow_add₀ hz m n

theorem zpow_pow_rule {x : Term} {m n : ℤ} {v : K}
    (h : (Term.pow (.pow x m) n).eval ρ = some v) : (Term.pow x (m * n)).eval ρ = some v := by
  obtain ⟨a, ha, ha0, rfl⟩ := (eval_pow ρ).1 h
  obtain ⟨u, hu, hu0, rfl⟩ := (eval_pow ρ).1 ha
  refine (eval_pow ρ).2 ⟨u, hu, ?_, zpow_mul u m n⟩
  rintro ⟨rfl, hmn⟩
  have hm : 0 ≤ m := by by_contra h'; exact hu0 ⟨rfl, by omega⟩
  rcases hm.eq_or_lt with hm0 | hm0
  · subst hm0; simp at hmn
  · have hn : n < 0 := by
      by_contra h'
      have : 0 ≤ m * n := Int.mul_nonneg hm (by omega)
      omega
    exact ha0 ⟨by rw [zero_zpow m hm0.ne'], hn⟩

theorem zpow_mul_rule {x y : Term} {n : ℤ} {v : K}
    (h : (Term.pow (.mul x y) n).eval ρ = some v) :
    (Term.mul (.pow x n) (.pow y n)).eval ρ = some v := by
  obtain ⟨a, ha, ha0, rfl⟩ := (eval_pow ρ).1 h
  obtain ⟨u, w, hu, hw, rfl⟩ := (eval_mul ρ).1 ha
  refine (eval_mul ρ).2 ⟨u ^ n, w ^ n, (eval_pow ρ).2 ⟨u, hu, ?_, rfl⟩,
    (eval_pow ρ).2 ⟨w, hw, ?_, rfl⟩, (mul_zpow u w n).symm⟩
  · rintro ⟨rfl, hn⟩; exact ha0 ⟨by simp, hn⟩
  · rintro ⟨rfl, hn⟩; exact ha0 ⟨by simp, hn⟩

end Rules

/-- **E1 for the groups of part 1** (`identities`, `annihilation`, `involutions`,
`numerals`, `associativity` with (AN)): every rule instance refines evaluation. -/
theorem E1_root {A : Ax} {l r : Term} (h : Root A l r) : Refines r l := by
  intro K _ _ _ ρ v hl
  cases h with
  | id_add_l x =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_add ρ).1 hl; simp at ha; subst ha; simpa using hb
  | id_add_r x =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_add ρ).1 hl; simp at hb; subst hb; simpa using ha
  | id_sub_r x =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_sub ρ).1 hl; simp at hb; subst hb; simpa using ha
  | id_sub_l x =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_sub ρ).1 hl; simp at ha; subst ha
    exact (eval_neg ρ).2 ⟨b, hb, by ring⟩
  | id_neg_zero =>
    obtain ⟨a, ha, rfl⟩ := (eval_neg ρ).1 hl; simp at ha; subst ha; simp
  | id_mul_l x =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_mul ρ).1 hl; simp at ha; subst ha; simpa using hb
  | id_mul_r x =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_mul ρ).1 hl; simp at hb; subst hb; simpa using ha
  | id_div x =>
    obtain ⟨a, b, ha, hb, -, rfl⟩ := (eval_div ρ).1 hl; simp at hb; subst hb; simpa using ha
  | id_pow1 x =>
    obtain ⟨a, ha, -, rfl⟩ := (eval_pow ρ).1 hl; simpa using ha
  | id_pow0 x =>
    obtain ⟨a, ha, -, rfl⟩ := (eval_pow ρ).1 hl; simp
  | ann_l x =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_mul ρ).1 hl; simp at ha; subst ha; simp
  | ann_r x =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_mul ρ).1 hl; simp at hb; subst hb; simp
  | inv_neg x =>
    obtain ⟨a, ha, rfl⟩ := (eval_neg ρ).1 hl
    obtain ⟨b, hb, rfl⟩ := (eval_neg ρ).1 ha
    simpa using hb
  | inv_div x =>
    obtain ⟨a, b, ha, hb, hb0, rfl⟩ := (eval_div ρ).1 hl
    obtain ⟨c, d, hc, hd, hd0, rfl⟩ := (eval_div ρ).1 hb
    simp at ha hc; subst ha hc
    simpa using hd
  | num_add p q =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_add ρ).1 hl; simp at ha hb; subst ha hb; simp
  | num_sub p q =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_sub ρ).1 hl; simp at ha hb; subst ha hb; simp
  | num_mul p q =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_mul ρ).1 hl; simp at ha hb; subst ha hb; simp
  | num_neg p =>
    obtain ⟨a, ha, rfl⟩ := (eval_neg ρ).1 hl; simp at ha; subst ha; simp
  | num_div p q _ hq =>
    obtain ⟨a, b, ha, hb, -, rfl⟩ := (eval_div ρ).1 hl; simp at ha hb; subst ha hb; simp
  | num_pow p n _ _ =>
    obtain ⟨a, ha, -, rfl⟩ := (eval_pow ρ).1 hl; simp at ha; subst ha; simp
  | assoc_add x y z =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_add ρ).1 hl
    obtain ⟨c, d, hc, hd, rfl⟩ := (eval_add ρ).1 hb
    exact (eval_add ρ).2 ⟨a + c, d, (eval_add ρ).2 ⟨a, c, ha, hc, rfl⟩, hd, by ring⟩
  | assoc_mul x y z =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_mul ρ).1 hl
    obtain ⟨c, d, hc, hd, rfl⟩ := (eval_mul ρ).1 hb
    exact (eval_mul ρ).2 ⟨a * c, d, (eval_mul ρ).2 ⟨a, c, ha, hc, rfl⟩, hd, by ring⟩
  | an_add x n m =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_add ρ).1 hl
    obtain ⟨c, d, hc, hd, rfl⟩ := (eval_add ρ).1 ha
    simp at hb hd; subst hb hd
    exact (eval_add ρ).2 ⟨c, _, hc, eval_num ρ _, by push_cast; ring⟩
  | an_mul x n m =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_mul ρ).1 hl
    obtain ⟨c, d, hc, hd, rfl⟩ := (eval_mul ρ).1 ha
    simp at hb hd; subst hb hd
    exact (eval_mul ρ).2 ⟨c, _, hc, eval_num ρ _, by push_cast; ring⟩

/-- **E1 for the ladder's groups** (`commutativity`, `linear`, `powers`, `quotients`,
`ring`; `field` has no rule of its own): every rule instance refines evaluation. -/
theorem E1_ladder {g : Group} {l r : Term} (h : Ladder g l r) : Refines r l := by
  intro K _ _ _ ρ v hl
  cases h with
  | comm_add x y =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_add ρ).1 hl
    exact (eval_add ρ).2 ⟨b, a, hb, ha, add_comm b a⟩
  | comm_mul x y =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_mul ρ).1 hl
    exact (eval_mul ρ).2 ⟨b, a, hb, ha, mul_comm b a⟩
  | lin_sub x y =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_sub ρ).1 hl
    exact (eval_add ρ).2 ⟨a, _, ha, (eval_mul ρ).2 ⟨_, b, eval_num ρ _, hb, rfl⟩,
      by push_cast; ring⟩
  | lin_neg x =>
    obtain ⟨a, ha, rfl⟩ := (eval_neg ρ).1 hl
    exact (eval_mul ρ).2 ⟨_, a, eval_num ρ _, ha, by push_cast; ring⟩
  | lin_collect x n m =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_add ρ).1 hl
    obtain ⟨c, d, hc, hd, rfl⟩ := (eval_mul ρ).1 ha
    obtain ⟨c', d', hc', hd', rfl⟩ := (eval_mul ρ).1 hb
    simp at hc hc'; subst hc hc'
    rw [hd] at hd'; cases hd'
    exact (eval_mul ρ).2 ⟨_, d, eval_num ρ _, hd, by push_cast; ring⟩
  | lin_scale x n m =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_mul ρ).1 hl
    obtain ⟨c, d, hc, hd, rfl⟩ := (eval_mul ρ).1 hb
    simp at ha hc; subst ha hc
    exact (eval_mul ρ).2 ⟨_, d, eval_num ρ _, hd, by push_cast; ring⟩
  | lin_distrib x y n =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_mul ρ).1 hl
    obtain ⟨c, d, hc, hd, rfl⟩ := (eval_add ρ).1 hb
    simp at ha; subst ha
    exact (eval_add ρ).2 ⟨_, _, (eval_mul ρ).2 ⟨_, c, eval_num ρ _, hc, rfl⟩,
      (eval_mul ρ).2 ⟨_, d, eval_num ρ _, hd, rfl⟩, by ring⟩
  | lin_zero x =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_mul ρ).1 hl; simp at ha; subst ha; simp
  | pow_add x m n _ _ => exact zpow_add_rule ρ hl
  | pow_pow x m n _ _ => exact zpow_pow_rule ρ hl
  | pow_mul x y n _ => exact zpow_mul_rule ρ hl
  | quo_div x y =>
    obtain ⟨a, b, ha, hb, hb0, rfl⟩ := (eval_div ρ).1 hl
    exact (eval_mul ρ).2 ⟨a, _, ha, (eval_pow ρ).2 ⟨b, hb, fun h => hb0 h.1, rfl⟩,
      by rw [zpow_neg_one, div_eq_mul_inv]⟩
  | quo_add x m n => exact zpow_add_rule ρ hl
  | quo_pow x m n => exact zpow_pow_rule ρ hl
  | quo_mul x y n => exact zpow_mul_rule ρ hl
  | ring_distrib x y z =>
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_mul ρ).1 hl
    obtain ⟨c, d, hc, hd, rfl⟩ := (eval_add ρ).1 hb
    exact (eval_add ρ).2 ⟨_, _, (eval_mul ρ).2 ⟨a, c, ha, hc, rfl⟩,
      (eval_mul ρ).2 ⟨a, d, ha, hd, rfl⟩, by ring⟩
  | ring_divn x q _ =>
    obtain ⟨a, b, ha, hb, hb0, rfl⟩ := (eval_div ρ).1 hl
    simp at hb; subst hb
    exact (eval_mul ρ).2 ⟨_, a, eval_num ρ _, ha, by push_cast; rw [div_eq_inv_mul]⟩

/-! ## Any number of steps, at any position -/

/-- One step with the rules of part 1's groups in `A` and of the ladder's groups `G`. -/
inductive GStep (A : Ax) (G : Group → Prop) : Term → Term → Prop
  | root {l r : Term} : Root A l r → GStep A G l r
  | ladder {g : Group} {l r : Term} : G g → Ladder g l r → GStep A G l r
  | add_l {a a' : Term} (b : Term) : GStep A G a a' → GStep A G (.add a b) (.add a' b)
  | add_r (a : Term) {b b' : Term} : GStep A G b b' → GStep A G (.add a b) (.add a b')
  | sub_l {a a' : Term} (b : Term) : GStep A G a a' → GStep A G (.sub a b) (.sub a' b)
  | sub_r (a : Term) {b b' : Term} : GStep A G b b' → GStep A G (.sub a b) (.sub a b')
  | neg {a a' : Term} : GStep A G a a' → GStep A G (.neg a) (.neg a')
  | mul_l {a a' : Term} (b : Term) : GStep A G a a' → GStep A G (.mul a b) (.mul a' b)
  | mul_r (a : Term) {b b' : Term} : GStep A G b b' → GStep A G (.mul a b) (.mul a b')
  | div_l {a a' : Term} (b : Term) : GStep A G a a' → GStep A G (.div a b) (.div a' b)
  | div_r (a : Term) {b b' : Term} : GStep A G b b' → GStep A G (.div a b) (.div a b')
  | pow {a a' : Term} (n : ℤ) : GStep A G a a' → GStep A G (.pow a n) (.pow a' n)

theorem E1_step {A : Ax} {G : Group → Prop} {s t : Term} (h : GStep A G s t) : Refines t s := by
  induction h with
  | root h => exact E1_root h
  | ladder _ h => exact E1_ladder h
  | add_l b _ ih =>
    intro K _ _ _ ρ v hs
    obtain ⟨x, y, hx, hy, rfl⟩ := (eval_add ρ).1 hs
    exact (eval_add ρ).2 ⟨x, y, ih K ρ x hx, hy, rfl⟩
  | add_r a _ ih =>
    intro K _ _ _ ρ v hs
    obtain ⟨x, y, hx, hy, rfl⟩ := (eval_add ρ).1 hs
    exact (eval_add ρ).2 ⟨x, y, hx, ih K ρ y hy, rfl⟩
  | sub_l b _ ih =>
    intro K _ _ _ ρ v hs
    obtain ⟨x, y, hx, hy, rfl⟩ := (eval_sub ρ).1 hs
    exact (eval_sub ρ).2 ⟨x, y, ih K ρ x hx, hy, rfl⟩
  | sub_r a _ ih =>
    intro K _ _ _ ρ v hs
    obtain ⟨x, y, hx, hy, rfl⟩ := (eval_sub ρ).1 hs
    exact (eval_sub ρ).2 ⟨x, y, hx, ih K ρ y hy, rfl⟩
  | neg _ ih =>
    intro K _ _ _ ρ v hs
    obtain ⟨x, hx, rfl⟩ := (eval_neg ρ).1 hs
    exact (eval_neg ρ).2 ⟨x, ih K ρ x hx, rfl⟩
  | mul_l b _ ih =>
    intro K _ _ _ ρ v hs
    obtain ⟨x, y, hx, hy, rfl⟩ := (eval_mul ρ).1 hs
    exact (eval_mul ρ).2 ⟨x, y, ih K ρ x hx, hy, rfl⟩
  | mul_r a _ ih =>
    intro K _ _ _ ρ v hs
    obtain ⟨x, y, hx, hy, rfl⟩ := (eval_mul ρ).1 hs
    exact (eval_mul ρ).2 ⟨x, y, hx, ih K ρ y hy, rfl⟩
  | div_l b _ ih =>
    intro K _ _ _ ρ v hs
    obtain ⟨x, y, hx, hy, hy0, rfl⟩ := (eval_div ρ).1 hs
    exact (eval_div ρ).2 ⟨x, y, ih K ρ x hx, hy, hy0, rfl⟩
  | div_r a _ ih =>
    intro K _ _ _ ρ v hs
    obtain ⟨x, y, hx, hy, hy0, rfl⟩ := (eval_div ρ).1 hs
    exact (eval_div ρ).2 ⟨x, y, hx, ih K ρ y hy, hy0, rfl⟩
  | pow n _ ih =>
    intro K _ _ _ ρ v hs
    obtain ⟨x, hx, hx0, rfl⟩ := (eval_pow ρ).1 hs
    exact (eval_pow ρ).2 ⟨x, ih K ρ x hx, hx0, rfl⟩

/-- **E1, many steps** (Lemma 1 in its oriented form): rewriting with the rules of any
groups, any number of times at any positions, keeps the value wherever the term has one. -/
theorem E1_steps {A : Ax} {G : Group → Prop} {s t : Term}
    (h : Relation.ReflTransGen (GStep A G) s t) : Refines t s := by
  induction h with
  | refl => intro K _ _ _ ρ v hs; exact hs
  | tail _ hst ih => exact fun K _ _ _ ρ v hs => E1_step hst K ρ v (ih K ρ v hs)

/-! ## Regressions: what E1 does not allow -/

/-- The rules are sound only in their direction: read right to left, `quo_add` with
`x = 0`, `m = 1`, `n = -1` turns the defined `0^0 = 1` into the undefined `0^1·0^(-1)`. -/
theorem quo_add_reversed_unsound :
    ¬ Refines (.mul (.pow (.num 0) 1) (.pow (.num 0) (-1))) (.pow (.num 0) (1 + -1)) := by
  intro h
  have := h ℚ (fun _ => 0) 1 (by simp [eval])
  simp [eval] at this

/-- The 2017 AntiCommutative axiom $x·y → -(y·x)$ is not sound (spec §4.2), which is why
decision 0009 gives it no group. -/
theorem anticommutative_unsound :
    ¬ Refines (.neg (.mul (.var "x") (.var "x"))) (.mul (.var "x") (.var "x")) := by
  intro h
  have := h ℚ (fun _ => 1) 1 (by simp [eval])
  simp [eval] at this
  exact absurd this (by decide)

end FricasSymbolic
