import FricasSymbolic.Eval
import FricasSymbolic.Normalize
import Mathlib.Tactic.Ring

/-!
# Part 1: soundness of the normaliser (L1, L2)

L1: each smart constructor refines evaluation. If the node as written has a
value, the node as the constructor builds it has the same value (spec §2.3,
condition (S); Lemma 1).

L2: `nf` refines evaluation, which is the invariant (Val) of spec §3.3 and
Proposition 2.

`K` is any field of characteristic zero with decidable equality: what FriCAS
provides for `Expression R` (see `Eval.lean`).
-/

namespace FricasSymbolic

namespace Term

section evalLemmas

variable {K : Type*} [Field K] [DecidableEq K] (ρ : String → K)

@[simp] theorem eval_num (q : ℚ) : eval ρ (num q) = some (q : K) := rfl

@[simp] theorem eval_var (s : String) : eval ρ (var s) = some (ρ s) := rfl

theorem eval_add {a b : Term} {v : K} :
    eval ρ (add a b) = some v ↔ ∃ x y, eval ρ a = some x ∧ eval ρ b = some y ∧ x + y = v := by
  simp [eval, Option.bind_eq_some_iff]

theorem eval_sub {a b : Term} {v : K} :
    eval ρ (sub a b) = some v ↔ ∃ x y, eval ρ a = some x ∧ eval ρ b = some y ∧ x - y = v := by
  simp [eval, Option.bind_eq_some_iff]

theorem eval_mul {a b : Term} {v : K} :
    eval ρ (mul a b) = some v ↔ ∃ x y, eval ρ a = some x ∧ eval ρ b = some y ∧ x * y = v := by
  simp [eval, Option.bind_eq_some_iff]

theorem eval_neg {a : Term} {v : K} :
    eval ρ (neg a) = some v ↔ ∃ x, eval ρ a = some x ∧ -x = v := by
  simp [eval, Option.bind_eq_some_iff]

theorem eval_div {a b : Term} {v : K} :
    eval ρ (div a b) = some v ↔
      ∃ x y, eval ρ a = some x ∧ eval ρ b = some y ∧ y ≠ 0 ∧ x / y = v := by
  simp [eval, Option.bind_eq_some_iff]

theorem eval_pow {a : Term} {n : ℤ} {v : K} :
    eval ρ (pow a n) = some v ↔ ∃ x, eval ρ a = some x ∧ ¬ (x = 0 ∧ n < 0) ∧ x ^ n = v := by
  simp [eval, Option.bind_eq_some_iff]

end evalLemmas

theorem isAdd_eq {t : Term} (h : t.isAdd = true) : t = add t.fst t.snd := by
  cases t <;> simp_all [isAdd, fst, snd]

theorem isMul_eq {t : Term} (h : t.isMul = true) : t = mul t.fst t.snd := by
  cases t <;> simp_all [isMul, fst, snd]

theorem isDiv_eq {t : Term} (h : t.isDiv = true) : t = div t.fst t.snd := by
  cases t <;> simp_all [isDiv, fst, snd]

theorem isNeg_eq {t : Term} (h : t.isNeg = true) : t = neg t.fst := by
  cases t <;> simp_all [isNeg, fst]

theorem isNum_eq {t : Term} (h : t.isNum = true) : t = num t.nv := by
  cases t <;> simp_all [isNum, nv]

theorem isLit_eq {t : Term} {q : ℚ} (h : t.isLit q = true) : t = num q := by
  cases t <;> simp_all [isLit, isNum, nv]

end Term

open Term

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K] (ρ : String → K) (A : Ax)

/-- L1 for `+`. -/
theorem sAdd_refines (x y : Term) :
    ∀ v : K, (add x y).eval ρ = some v → (sAdd A x y).eval ρ = some v := by
  induction x, y using sAdd.induct A with
  | case1 x y h =>
    intro v hv
    rw [sAdd]; simp only [h, ↓reduceIte]
    simp only [Bool.and_eq_true] at h
    rw [isNum_eq h.1.2, isNum_eq h.2] at hv
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_add ρ).1 hv
    simp at ha hb; subst ha hb; simp [Rat.cast_add]
  | case2 x y h1 h =>
    intro v hv
    rw [sAdd]; simp only [h1, h, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.and_eq_true] at h
    rw [isLit_eq h.2] at hv
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_add ρ).1 hv
    simp at ha; subst ha; simpa using hb
  | case3 x y h1 h2 h =>
    intro v hv
    rw [sAdd]; simp only [h1, h2, h, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.and_eq_true] at h
    rw [isLit_eq h.2] at hv
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_add ρ).1 hv
    simp at hb; subst hb; simpa using ha
  | case4 x y h1 h2 h3 h _ _ ih1 ih2 =>
    intro v hv
    rw [sAdd]; simp only [h1, h2, h3, h, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    simp only [Bool.and_eq_true] at h
    rw [isAdd_eq h.2] at hv
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_add ρ).1 hv
    obtain ⟨b1, b2, hb1, hb2, rfl⟩ := (eval_add ρ).1 hb
    apply ih2
    rw [eval_add]
    exact ⟨a + b1, b2, ih1 _ ((eval_add ρ).2 ⟨a, b1, ha, hb1, rfl⟩), hb2, by ring⟩
  | case5 x y h1 h2 h3 h4 h _ _ ih =>
    intro v hv
    rw [sAdd]; simp only [h1, h2, h3, h4, h, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, hy⟩, hx⟩, hxs⟩ := h
    rw [isAdd_eq hx, isNum_eq hy, isNum_eq hxs] at hv
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_add ρ).1 hv
    obtain ⟨a1, a2, ha1, ha2, rfl⟩ := (eval_add ρ).1 ha
    simp at hb ha2; subst hb ha2
    apply ih
    rw [eval_add]
    exact ⟨a1, _, ha1, rfl, by simp [Rat.cast_add]; ring⟩
  | case6 x y h1 h2 h3 h4 h5 =>
    intro v hv
    rw [sAdd]; simp only [h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    exact hv

/-- L1 for `*`. -/
theorem sMul_refines (x y : Term) :
    ∀ v : K, (mul x y).eval ρ = some v → (sMul A x y).eval ρ = some v := by
  induction x, y using sMul.induct A with
  | case1 x y h =>
    intro v hv
    rw [sMul]; simp only [h, ↓reduceIte]
    simp only [Bool.and_eq_true] at h
    rw [isNum_eq h.1.2, isNum_eq h.2] at hv
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_mul ρ).1 hv
    simp at ha hb; subst ha hb; simp [Rat.cast_mul]
  | case2 x y h1 h =>
    intro v hv
    rw [sMul]; simp only [h1, h, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_mul ρ).1 hv
    rcases h.2 with h0 | h0
    · rw [isLit_eq h0] at ha; simp at ha; subst ha; simp
    · rw [isLit_eq h0] at hb; simp at hb; subst hb; simp
  | case3 x y h1 h2 h =>
    intro v hv
    rw [sMul]; simp only [h1, h2, h, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.and_eq_true] at h
    rw [isLit_eq h.2] at hv
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_mul ρ).1 hv
    simp at ha; subst ha; simpa using hb
  | case4 x y h1 h2 h3 h =>
    intro v hv
    rw [sMul]; simp only [h1, h2, h3, h, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.and_eq_true] at h
    rw [isLit_eq h.2] at hv
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_mul ρ).1 hv
    simp at hb; subst hb; simpa using ha
  | case5 x y h1 h2 h3 h4 h _ _ ih1 ih2 =>
    intro v hv
    rw [sMul]; simp only [h1, h2, h3, h4, h, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    simp only [Bool.and_eq_true] at h
    rw [isMul_eq h.2] at hv
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_mul ρ).1 hv
    obtain ⟨b1, b2, hb1, hb2, rfl⟩ := (eval_mul ρ).1 hb
    apply ih2
    rw [eval_mul]
    exact ⟨a * b1, b2, ih1 _ ((eval_mul ρ).2 ⟨a, b1, ha, hb1, rfl⟩), hb2, by ring⟩
  | case6 x y h1 h2 h3 h4 h5 h _ _ ih =>
    intro v hv
    rw [sMul]; simp only [h1, h2, h3, h4, h5, h, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, hy⟩, hx⟩, hxs⟩ := h
    rw [isMul_eq hx, isNum_eq hy, isNum_eq hxs] at hv
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_mul ρ).1 hv
    obtain ⟨a1, a2, ha1, ha2, rfl⟩ := (eval_mul ρ).1 ha
    simp at hb ha2; subst hb ha2
    apply ih
    rw [eval_mul]
    exact ⟨a1, _, ha1, rfl, by simp [Rat.cast_mul]; ring⟩
  | case7 x y h1 h2 h3 h4 h5 h6 =>
    intro v hv
    rw [sMul]; simp only [h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    exact hv

/-- L1 for unary `-`. -/
theorem sNeg_refines (x : Term) :
    ∀ v : K, (neg x).eval ρ = some v → (sNeg A x).eval ρ = some v := by
  intro v hv
  unfold sNeg
  split_ifs with h1 h2
  · simp only [Bool.and_eq_true] at h1
    rw [isNum_eq h1.2] at hv
    obtain ⟨a, ha, rfl⟩ := (eval_neg ρ).1 hv
    simp at ha; subst ha; simp
  · simp only [Bool.and_eq_true] at h2
    rw [isNeg_eq h2.2] at hv
    obtain ⟨a, ha, rfl⟩ := (eval_neg ρ).1 hv
    obtain ⟨b, hb, rfl⟩ := (eval_neg ρ).1 ha
    simpa using hb
  · exact hv

/-- L1 for binary `-`. -/
theorem sSub_refines (x y : Term) :
    ∀ v : K, (sub x y).eval ρ = some v → (sSub A x y).eval ρ = some v := by
  intro v hv
  unfold sSub
  split_ifs with h1 h2 h3
  · simp only [Bool.and_eq_true] at h1
    rw [isNum_eq h1.1.2, isNum_eq h1.2] at hv
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_sub ρ).1 hv
    simp at ha hb; subst ha hb; simp [Rat.cast_sub]
  · simp only [Bool.and_eq_true] at h2
    rw [isLit_eq h2.2] at hv
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_sub ρ).1 hv
    simp at hb; subst hb; simpa using ha
  · simp only [Bool.and_eq_true] at h3
    rw [isLit_eq h3.2] at hv
    obtain ⟨a, b, ha, hb, rfl⟩ := (eval_sub ρ).1 hv
    simp at ha; subst ha
    exact sNeg_refines ρ A y _ ((eval_neg ρ).2 ⟨b, hb, by simp⟩)
  · exact hv

/-- L1 for `/`. -/
theorem sDiv_refines (x y : Term) :
    ∀ v : K, (div x y).eval ρ = some v → (sDiv A x y).eval ρ = some v := by
  intro v hv
  unfold sDiv
  split_ifs with h1 h2 h3
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h1
    rw [isNum_eq h1.1.1.2, isNum_eq h1.1.2] at hv
    obtain ⟨a, b, ha, hb, _, rfl⟩ := (eval_div ρ).1 hv
    simp at ha hb; subst ha hb; simp [Rat.cast_div]
  · simp only [Bool.and_eq_true] at h2
    rw [isLit_eq h2.2] at hv
    obtain ⟨a, b, ha, hb, _, rfl⟩ := (eval_div ρ).1 hv
    simp at hb; subst hb; simpa using ha
  · simp only [Bool.and_eq_true] at h3
    obtain ⟨⟨⟨_, hx⟩, hy⟩, hyf⟩ := h3
    rw [isLit_eq hx, isDiv_eq hy, isLit_eq hyf] at hv
    obtain ⟨a, b, ha, hb, hb0, rfl⟩ := (eval_div ρ).1 hv
    obtain ⟨c, d, hc, hd, hd0, rfl⟩ := (eval_div ρ).1 hb
    simp at ha hc; subst ha hc
    simpa using hd
  · exact hv

/-- L1 for `^` with an integer exponent. -/
theorem sPow_refines (x : Term) (n : ℤ) :
    ∀ v : K, (pow x n).eval ρ = some v → (sPow A x n).eval ρ = some v := by
  intro v hv
  unfold sPow
  split_ifs with h1 h2 h3
  · simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      ne_eq, decide_eq_false_iff_not, not_lt] at h1
    rw [isNum_eq h1.1.2] at hv
    obtain ⟨a, ha, _, rfl⟩ := (eval_pow ρ).1 hv
    simp at ha; subst ha; simp [Rat.cast_zpow]
  · simp only [Bool.and_eq_true, beq_iff_eq] at h2
    obtain ⟨a, ha, _, rfl⟩ := (eval_pow ρ).1 hv
    rw [h2.2] at *; simpa using ha
  · simp only [Bool.and_eq_true, beq_iff_eq] at h3
    obtain ⟨a, ha, _, rfl⟩ := (eval_pow ρ).1 hv
    rw [h3.2]; simp
  · exact hv

/-- L2: the normal form refines evaluation, (Val) and Proposition 2. -/
theorem nf_refines (t : Term) : ∀ v : K, t.eval ρ = some v → (nf A t).eval ρ = some v := by
  induction t with
  | num q => intro v hv; exact hv
  | var s => intro v hv; exact hv
  | add a b iha ihb =>
    intro v hv
    obtain ⟨x, y, hx, hy, rfl⟩ := (eval_add ρ).1 hv
    exact sAdd_refines ρ A _ _ _ ((eval_add ρ).2 ⟨x, y, iha x hx, ihb y hy, rfl⟩)
  | sub a b iha ihb =>
    intro v hv
    obtain ⟨x, y, hx, hy, rfl⟩ := (eval_sub ρ).1 hv
    exact sSub_refines ρ A _ _ _ ((eval_sub ρ).2 ⟨x, y, iha x hx, ihb y hy, rfl⟩)
  | neg a iha =>
    intro v hv
    obtain ⟨x, hx, rfl⟩ := (eval_neg ρ).1 hv
    exact sNeg_refines ρ A _ _ ((eval_neg ρ).2 ⟨x, iha x hx, rfl⟩)
  | mul a b iha ihb =>
    intro v hv
    obtain ⟨x, y, hx, hy, rfl⟩ := (eval_mul ρ).1 hv
    exact sMul_refines ρ A _ _ _ ((eval_mul ρ).2 ⟨x, y, iha x hx, ihb y hy, rfl⟩)
  | div a b iha ihb =>
    intro v hv
    obtain ⟨x, y, hx, hy, hy0, rfl⟩ := (eval_div ρ).1 hv
    exact sDiv_refines ρ A _ _ _ ((eval_div ρ).2 ⟨x, y, iha x hx, ihb y hy, hy0, rfl⟩)
  | pow a n iha =>
    intro v hv
    obtain ⟨x, hx, hx0, rfl⟩ := (eval_pow ρ).1 hv
    exact sPow_refines ρ A _ _ _ ((eval_pow ρ).2 ⟨x, iha x hx, hx0, rfl⟩)

end FricasSymbolic
