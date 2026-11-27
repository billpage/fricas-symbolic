import FricasSymbolic.Rewriting
import FricasSymbolic.Soundness

/-!
# Part 1: termination, normal forms and confluence (L4, L5, L6, L8, L9)

* **L9** `L9_terminating`: every step lowers `(|t|, μ(t))` lexicographically
  (spec §4.1.1), so `Step A` is well founded.
* **L4** `L4_nf_isNF`: `nf A t` is a normal form.
* **L8** `L8_steps_to_nf`: `t →* nf A t`; the normaliser takes only steps of the axioms.
* **L6** `L6_nf_of_isNF`: `nf` fixes normal forms; hence it is idempotent.
* **L5** `L5_step`, `L5_eqA`: one step does not change the normal form, hence terms equal
  under the axioms have the same normal form. Hypotheses: Id comes with Num (L10 shows
  why), and (AN) is on (L7 shows why).

With L4 and L8, L5 gives the Church–Rosser property: `s =_A t` implies
`s →* nf s = nf t ←* t`.
-/

namespace FricasSymbolic

open Term Relation

/-! ## L9: termination -/

/-- The order of spec §4.1.1: `(|t|, μ(t))`, lexicographically. -/
def SizeMuLt (t s : Term) : Prop :=
  t.size < s.size ∨ (t.size = s.size ∧ t.mu < s.mu)

theorem root_decreases {A : Ax} {s t : Term} (h : Root A s t) : SizeMuLt t s := by
  cases h with
  | id_pow0 x _ => have := size_pos x; simp [SizeMuLt, size]; omega
  | _ => simp only [SizeMuLt, size, mu]; omega

theorem step_decreases {A : Ax} {s t : Term} (h : Step A s t) : SizeMuLt t s := by
  induction h with
  | root r => exact root_decreases r
  | add_l b _ ih | sub_l b _ ih | mul_l b _ ih | div_l b _ ih =>
    simp only [SizeMuLt, size, mu] at ih ⊢; omega
  | add_r a _ ih | sub_r a _ ih | mul_r a _ ih | div_r a _ ih =>
    simp only [SizeMuLt, size, mu] at ih ⊢; omega
  | neg _ ih | pow n _ ih =>
    simp only [SizeMuLt, size, mu] at ih ⊢; omega

/-- L9: `Step A` terminates: its converse is well founded. -/
theorem L9_terminating (A : Ax) : WellFounded (fun t s => Step A s t) := by
  have wf : WellFounded
      (fun t s : Term => Prod.Lex (· < ·) (· < ·) (t.size, t.mu) (s.size, s.mu)) :=
    InvImage.wf (fun t : Term => (t.size, t.mu))
      (WellFounded.prod_lex wellFounded_lt wellFounded_lt)
  refine Subrelation.wf (fun {t s} h => ?_) wf
  rcases step_decreases h with h1 | ⟨h1, h2⟩
  · exact Prod.Lex.left _ _ h1
  · simp only [h1]; exact Prod.Lex.right _ h2

/-! ## Normal forms: decomposition -/

variable {A : Ax}

namespace IsNF

theorem not_root {s : Term} (h : IsNF A s) {t : Term} : ¬ Root A s t :=
  fun r => h _ (Step.root r)

theorem add_l {a b : Term} (h : IsNF A (.add a b)) : IsNF A a := fun _ s => h _ (Step.add_l b s)
theorem add_r {a b : Term} (h : IsNF A (.add a b)) : IsNF A b := fun _ s => h _ (Step.add_r a s)
theorem sub_l {a b : Term} (h : IsNF A (.sub a b)) : IsNF A a := fun _ s => h _ (Step.sub_l b s)
theorem sub_r {a b : Term} (h : IsNF A (.sub a b)) : IsNF A b := fun _ s => h _ (Step.sub_r a s)
theorem mul_l {a b : Term} (h : IsNF A (.mul a b)) : IsNF A a := fun _ s => h _ (Step.mul_l b s)
theorem mul_r {a b : Term} (h : IsNF A (.mul a b)) : IsNF A b := fun _ s => h _ (Step.mul_r a s)
theorem div_l {a b : Term} (h : IsNF A (.div a b)) : IsNF A a := fun _ s => h _ (Step.div_l b s)
theorem div_r {a b : Term} (h : IsNF A (.div a b)) : IsNF A b := fun _ s => h _ (Step.div_r a s)
theorem neg' {a : Term} (h : IsNF A (.neg a)) : IsNF A a := fun _ s => h _ (Step.neg s)
theorem pow' {a : Term} {n : ℤ} (h : IsNF A (.pow a n)) : IsNF A a := fun _ s => h _ (Step.pow n s)

theorem num (q : ℚ) : IsNF A (.num q) := by
  intro t h; cases h with | root r => cases r

theorem var (s : String) : IsNF A (.var s) := by
  intro t h; cases h with | root r => cases r

theorem add {a b : Term} (ha : IsNF A a) (hb : IsNF A b) (hr : ∀ t, ¬ Root A (.add a b) t) :
    IsNF A (.add a b) := by
  intro t h
  cases h with
  | root r => exact hr _ r
  | add_l _ s => exact ha _ s
  | add_r _ s => exact hb _ s

theorem sub {a b : Term} (ha : IsNF A a) (hb : IsNF A b) (hr : ∀ t, ¬ Root A (.sub a b) t) :
    IsNF A (.sub a b) := by
  intro t h
  cases h with
  | root r => exact hr _ r
  | sub_l _ s => exact ha _ s
  | sub_r _ s => exact hb _ s

theorem mul {a b : Term} (ha : IsNF A a) (hb : IsNF A b) (hr : ∀ t, ¬ Root A (.mul a b) t) :
    IsNF A (.mul a b) := by
  intro t h
  cases h with
  | root r => exact hr _ r
  | mul_l _ s => exact ha _ s
  | mul_r _ s => exact hb _ s

theorem div {a b : Term} (ha : IsNF A a) (hb : IsNF A b) (hr : ∀ t, ¬ Root A (.div a b) t) :
    IsNF A (.div a b) := by
  intro t h
  cases h with
  | root r => exact hr _ r
  | div_l _ s => exact ha _ s
  | div_r _ s => exact hb _ s

theorem neg {a : Term} (ha : IsNF A a) (hr : ∀ t, ¬ Root A (.neg a) t) : IsNF A (.neg a) := by
  intro t h
  cases h with
  | root r => exact hr _ r
  | neg s => exact ha _ s

theorem pow {a : Term} {n : ℤ} (ha : IsNF A a) (hr : ∀ t, ¬ Root A (.pow a n) t) :
    IsNF A (.pow a n) := by
  intro t h
  cases h with
  | root r => exact hr _ r
  | pow _ s => exact ha _ s

end IsNF

/-! ## L6: the smart constructors fix normal forms -/

theorem sAdd_eq_of_isNF {x y : Term} (h : IsNF A (.add x y)) : sAdd A x y = .add x y := by
  rw [sAdd]
  have g1 : ¬ (A.num && x.isNum && y.isNum) = true := by
    intro g; simp only [Bool.and_eq_true] at g
    rw [isNum_eq g.1.2, isNum_eq g.2] at h; exact h.not_root (Root.num_add _ _ g.1.1)
  have g2 : ¬ (A.id && x.isLit 0) = true := by
    intro g; simp only [Bool.and_eq_true] at g
    rw [isLit_eq g.2] at h; exact h.not_root (Root.id_add_l _ g.1)
  have g3 : ¬ (A.id && y.isLit 0) = true := by
    intro g; simp only [Bool.and_eq_true] at g
    rw [isLit_eq g.2] at h; exact h.not_root (Root.id_add_r _ g.1)
  have g4 : ¬ (A.assoc && y.isAdd) = true := by
    intro g; simp only [Bool.and_eq_true] at g
    rw [isAdd_eq g.2] at h; exact h.not_root (Root.assoc_add _ _ _ g.1)
  have g5 : ¬ (A.assoc && A.num && A.an && y.isNum && x.isAdd && x.snd.isNum) = true := by
    intro g; simp only [Bool.and_eq_true] at g
    obtain ⟨⟨⟨⟨⟨ha, hn⟩, han⟩, hy⟩, hx⟩, hxs⟩ := g
    rw [isAdd_eq hx, isNum_eq hy, isNum_eq hxs] at h
    exact h.not_root (Root.an_add _ _ _ ha hn han)
  simp only [g1, g2, g3, g4, g5, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]

theorem sMul_eq_of_isNF {x y : Term} (h : IsNF A (.mul x y)) : sMul A x y = .mul x y := by
  rw [sMul]
  have g1 : ¬ (A.num && x.isNum && y.isNum) = true := by
    intro g; simp only [Bool.and_eq_true] at g
    rw [isNum_eq g.1.2, isNum_eq g.2] at h; exact h.not_root (Root.num_mul _ _ g.1.1)
  have g2 : ¬ (A.ann && (x.isLit 0 || y.isLit 0)) = true := by
    intro g; simp only [Bool.and_eq_true, Bool.or_eq_true] at g
    rcases g.2 with g' | g'
    · rw [isLit_eq g'] at h; exact h.not_root (Root.ann_l _ g.1)
    · rw [isLit_eq g'] at h; exact h.not_root (Root.ann_r _ g.1)
  have g3 : ¬ (A.id && x.isLit 1) = true := by
    intro g; simp only [Bool.and_eq_true] at g
    rw [isLit_eq g.2] at h; exact h.not_root (Root.id_mul_l _ g.1)
  have g4 : ¬ (A.id && y.isLit 1) = true := by
    intro g; simp only [Bool.and_eq_true] at g
    rw [isLit_eq g.2] at h; exact h.not_root (Root.id_mul_r _ g.1)
  have g5 : ¬ (A.assoc && y.isMul) = true := by
    intro g; simp only [Bool.and_eq_true] at g
    rw [isMul_eq g.2] at h; exact h.not_root (Root.assoc_mul _ _ _ g.1)
  have g6 : ¬ (A.assoc && A.num && A.an && y.isNum && x.isMul && x.snd.isNum) = true := by
    intro g; simp only [Bool.and_eq_true] at g
    obtain ⟨⟨⟨⟨⟨ha, hn⟩, han⟩, hy⟩, hx⟩, hxs⟩ := g
    rw [isMul_eq hx, isNum_eq hy, isNum_eq hxs] at h
    exact h.not_root (Root.an_mul _ _ _ ha hn han)
  simp only [g1, g2, g3, g4, g5, g6, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]

theorem sNeg_eq_of_isNF {x : Term} (h : IsNF A (.neg x)) : sNeg A x = .neg x := by
  unfold sNeg
  have g1 : ¬ (A.num && x.isNum) = true := by
    intro g; simp only [Bool.and_eq_true] at g
    rw [isNum_eq g.2] at h; exact h.not_root (Root.num_neg _ g.1)
  have g2 : ¬ (A.inv && x.isNeg) = true := by
    intro g; simp only [Bool.and_eq_true] at g
    rw [isNeg_eq g.2] at h; exact h.not_root (Root.inv_neg _ g.1)
  simp only [g1, g2, Bool.false_eq_true, ↓reduceIte]

theorem sSub_eq_of_isNF {x y : Term} (h : IsNF A (.sub x y)) : sSub A x y = .sub x y := by
  unfold sSub
  have g1 : ¬ (A.num && x.isNum && y.isNum) = true := by
    intro g; simp only [Bool.and_eq_true] at g
    rw [isNum_eq g.1.2, isNum_eq g.2] at h; exact h.not_root (Root.num_sub _ _ g.1.1)
  have g2 : ¬ (A.id && y.isLit 0) = true := by
    intro g; simp only [Bool.and_eq_true] at g
    rw [isLit_eq g.2] at h; exact h.not_root (Root.id_sub_r _ g.1)
  have g3 : ¬ (A.id && x.isLit 0) = true := by
    intro g; simp only [Bool.and_eq_true] at g
    rw [isLit_eq g.2] at h; exact h.not_root (Root.id_sub_l _ g.1)
  simp only [g1, g2, g3, Bool.false_eq_true, ↓reduceIte]

theorem sDiv_eq_of_isNF {x y : Term} (h : IsNF A (.div x y)) : sDiv A x y = .div x y := by
  unfold sDiv
  have g1 : ¬ (A.num && x.isNum && y.isNum && y.nv != 0) = true := by
    intro g; simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at g
    rw [isNum_eq g.1.1.2, isNum_eq g.1.2] at h
    exact h.not_root (Root.num_div _ _ g.1.1.1 g.2)
  have g2 : ¬ (A.id && y.isLit 1) = true := by
    intro g; simp only [Bool.and_eq_true] at g
    rw [isLit_eq g.2] at h; exact h.not_root (Root.id_div _ g.1)
  have g3 : ¬ (A.inv && x.isLit 1 && y.isDiv && y.fst.isLit 1) = true := by
    intro g; simp only [Bool.and_eq_true] at g
    obtain ⟨⟨⟨hi, hx⟩, hy⟩, hyf⟩ := g
    rw [isLit_eq hx, isDiv_eq hy, isLit_eq hyf] at h
    exact h.not_root (Root.inv_div _ hi)
  simp only [g1, g2, g3, Bool.false_eq_true, ↓reduceIte]

theorem sPow_eq_of_isNF {x : Term} {n : ℤ} (h : IsNF A (.pow x n)) : sPow A x n = .pow x n := by
  unfold sPow
  have g1 : ¬ (A.num && x.isNum && !(x.nv == 0 && decide (n < 0))) = true := by
    intro g
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      ne_eq, decide_eq_false_iff_not] at g
    rw [isNum_eq g.1.2] at h
    exact h.not_root (Root.num_pow _ _ g.1.1 (by rcases g.2 with g' | g' <;> simp_all))
  have g2 : ¬ (A.id && n == 1) = true := by
    intro g; simp only [Bool.and_eq_true, beq_iff_eq] at g
    rw [g.2] at h; exact h.not_root (Root.id_pow1 _ g.1)
  have g3 : ¬ (A.id && n == 0) = true := by
    intro g; simp only [Bool.and_eq_true, beq_iff_eq] at g
    rw [g.2] at h; exact h.not_root (Root.id_pow0 _ g.1)
  simp only [g1, g2, g3, Bool.false_eq_true, ↓reduceIte]

/-- L6: `nf` fixes normal forms. -/
theorem L6_nf_of_isNF {t : Term} (h : IsNF A t) : nf A t = t := by
  induction t with
  | num q => rfl
  | var s => rfl
  | add a b iha ihb => simp only [nf, iha h.add_l, ihb h.add_r]; exact sAdd_eq_of_isNF h
  | sub a b iha ihb => simp only [nf, iha h.sub_l, ihb h.sub_r]; exact sSub_eq_of_isNF h
  | neg a iha => simp only [nf, iha h.neg']; exact sNeg_eq_of_isNF h
  | mul a b iha ihb => simp only [nf, iha h.mul_l, ihb h.mul_r]; exact sMul_eq_of_isNF h
  | div a b iha ihb => simp only [nf, iha h.div_l, ihb h.div_r]; exact sDiv_eq_of_isNF h
  | pow a n iha => simp only [nf, iha h.pow']; exact sPow_eq_of_isNF h

/-! ## L4: the smart constructors build normal forms -/

theorem isNum_iff {t : Term} : t.isNum = true ↔ ∃ q, t = .num q := by
  cases t <;> simp [isNum]

theorem isLit_iff {t : Term} {q : ℚ} : t.isLit q = true ↔ t = .num q := by
  cases t <;> simp [isLit, isNum, nv]

theorem isAdd_iff {t : Term} : t.isAdd = true ↔ ∃ a b, t = .add a b := by
  cases t <;> simp [isAdd]

theorem isMul_iff {t : Term} : t.isMul = true ↔ ∃ a b, t = .mul a b := by
  cases t <;> simp [isMul]

theorem isDiv_iff {t : Term} : t.isDiv = true ↔ ∃ a b, t = .div a b := by
  cases t <;> simp [isDiv]

theorem isNeg_iff {t : Term} : t.isNeg = true ↔ ∃ a, t = .neg a := by
  cases t <;> simp [isNeg]

theorem sAdd_isNF (x y : Term) : IsNF A x → IsNF A y → IsNF A (sAdd A x y) := by
  induction x, y using sAdd.induct A with
  | case1 x y h =>
    intro _ _; rw [sAdd]; simp only [h, ↓reduceIte]; exact IsNF.num _
  | case2 x y h1 h =>
    intro _ hy; rw [sAdd]; simp only [h1, h, Bool.false_eq_true, ↓reduceIte]; exact hy
  | case3 x y h1 h2 h =>
    intro hx _; rw [sAdd]; simp only [h1, h2, h, Bool.false_eq_true, ↓reduceIte]; exact hx
  | case4 x y h1 h2 h3 h _ _ ih1 ih2 =>
    intro hx hy
    rw [sAdd]; simp only [h1, h2, h3, h, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    simp only [Bool.and_eq_true] at h
    have hy' : IsNF A (.add y.fst y.snd) := isAdd_eq h.2 ▸ hy
    exact ih2 (ih1 hx hy'.add_l) hy'.add_r
  | case5 x y h1 h2 h3 h4 h _ _ ih =>
    intro hx _
    rw [sAdd]; simp only [h1, h2, h3, h4, h, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    simp only [Bool.and_eq_true] at h
    have hx' : IsNF A (.add x.fst x.snd) := isAdd_eq h.1.2 ▸ hx
    exact ih hx'.add_l (IsNF.num _)
  | case6 x y h1 h2 h3 h4 h5 =>
    intro hx hy
    rw [sAdd]; simp only [h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    refine IsNF.add hx hy fun t r => ?_
    cases r <;> simp_all [isNum, isLit, nv, isAdd, snd]

theorem sMul_isNF (x y : Term) : IsNF A x → IsNF A y → IsNF A (sMul A x y) := by
  induction x, y using sMul.induct A with
  | case1 x y h =>
    intro _ _; rw [sMul]; simp only [h, ↓reduceIte]; exact IsNF.num _
  | case2 x y h1 h =>
    intro _ _; rw [sMul]; simp only [h1, h, Bool.false_eq_true, ↓reduceIte]; exact IsNF.num _
  | case3 x y h1 h2 h =>
    intro _ hy; rw [sMul]; simp only [h1, h2, h, Bool.false_eq_true, ↓reduceIte]; exact hy
  | case4 x y h1 h2 h3 h =>
    intro hx _; rw [sMul]; simp only [h1, h2, h3, h, Bool.false_eq_true, ↓reduceIte]; exact hx
  | case5 x y h1 h2 h3 h4 h _ _ ih1 ih2 =>
    intro hx hy
    rw [sMul]; simp only [h1, h2, h3, h4, h, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    simp only [Bool.and_eq_true] at h
    have hy' : IsNF A (.mul y.fst y.snd) := isMul_eq h.2 ▸ hy
    exact ih2 (ih1 hx hy'.mul_l) hy'.mul_r
  | case6 x y h1 h2 h3 h4 h5 h _ _ ih =>
    intro hx _
    rw [sMul]; simp only [h1, h2, h3, h4, h5, h, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    simp only [Bool.and_eq_true] at h
    have hx' : IsNF A (.mul x.fst x.snd) := isMul_eq h.1.2 ▸ hx
    exact ih hx'.mul_l (IsNF.num _)
  | case7 x y h1 h2 h3 h4 h5 h6 =>
    intro hx hy
    rw [sMul]; simp only [h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    refine IsNF.mul hx hy fun t r => ?_
    cases r <;> simp_all [isNum, isLit, nv, isMul, snd]

theorem sNeg_isNF {x : Term} (hx : IsNF A x) : IsNF A (sNeg A x) := by
  unfold sNeg
  split_ifs with h1 h2
  · exact IsNF.num _
  · simp only [Bool.and_eq_true] at h2
    have hx' : IsNF A (.neg x.fst) := isNeg_eq h2.2 ▸ hx
    exact hx'.neg'
  · refine IsNF.neg hx fun t r => ?_
    cases r <;> simp_all [isNum, isNeg]

theorem sSub_isNF {x y : Term} (hx : IsNF A x) (hy : IsNF A y) : IsNF A (sSub A x y) := by
  unfold sSub
  split_ifs with h1 h2 h3
  · exact IsNF.num _
  · exact hx
  · exact sNeg_isNF hy
  · refine IsNF.sub hx hy fun t r => ?_
    cases r <;> simp_all [isNum, isLit, nv]

theorem sDiv_isNF {x y : Term} (hx : IsNF A x) (hy : IsNF A y) : IsNF A (sDiv A x y) := by
  unfold sDiv
  split_ifs with h1 h2 h3
  · exact IsNF.num _
  · exact hx
  · simp only [Bool.and_eq_true] at h3
    have hy' : IsNF A (.div y.fst y.snd) := isDiv_eq h3.1.2 ▸ hy
    exact hy'.div_r
  · refine IsNF.div hx hy fun t r => ?_
    cases r <;> simp_all [isNum, isLit, nv, isDiv, fst]

theorem sPow_isNF {x : Term} {n : ℤ} (hx : IsNF A x) : IsNF A (sPow A x n) := by
  unfold sPow
  split_ifs with h1 h2 h3
  · exact IsNF.num _
  · exact hx
  · exact IsNF.num _
  · refine IsNF.pow hx fun t r => ?_
    cases r <;> simp_all [isNum, nv]

/-- L4: `nf A t` is a normal form. -/
theorem L4_nf_isNF (t : Term) : IsNF A (nf A t) := by
  induction t with
  | num q => exact IsNF.num q
  | var s => exact IsNF.var s
  | add a b iha ihb => exact sAdd_isNF _ _ iha ihb
  | sub a b iha ihb => exact sSub_isNF iha ihb
  | neg a iha => exact sNeg_isNF iha
  | mul a b iha ihb => exact sMul_isNF _ _ iha ihb
  | div a b iha ihb => exact sDiv_isNF iha ihb
  | pow a n iha => exact sPow_isNF iha

/-- Idempotence (with L6). -/
theorem nf_nf (t : Term) : nf A (nf A t) = nf A t := L6_nf_of_isNF (L4_nf_isNF t)

/-! ## L8: the smart constructors take only steps of the axioms -/

/-- `→*`, the reflexive-transitive closure of `Step A`. -/
abbrev Steps (A : Ax) := ReflTransGen (Step A)

namespace Steps

theorem add_l {a a' : Term} (b : Term) (h : Steps A a a') : Steps A (.add a b) (.add a' b) :=
  h.lift (fun a => Term.add a b) fun _ _ s => Step.add_l b s
theorem add_r (a : Term) {b b' : Term} (h : Steps A b b') : Steps A (.add a b) (.add a b') :=
  h.lift (fun b => Term.add a b) fun _ _ s => Step.add_r a s
theorem sub_l {a a' : Term} (b : Term) (h : Steps A a a') : Steps A (.sub a b) (.sub a' b) :=
  h.lift (fun a => Term.sub a b) fun _ _ s => Step.sub_l b s
theorem sub_r (a : Term) {b b' : Term} (h : Steps A b b') : Steps A (.sub a b) (.sub a b') :=
  h.lift (fun b => Term.sub a b) fun _ _ s => Step.sub_r a s
theorem mul_l {a a' : Term} (b : Term) (h : Steps A a a') : Steps A (.mul a b) (.mul a' b) :=
  h.lift (fun a => Term.mul a b) fun _ _ s => Step.mul_l b s
theorem mul_r (a : Term) {b b' : Term} (h : Steps A b b') : Steps A (.mul a b) (.mul a b') :=
  h.lift (fun b => Term.mul a b) fun _ _ s => Step.mul_r a s
theorem div_l {a a' : Term} (b : Term) (h : Steps A a a') : Steps A (.div a b) (.div a' b) :=
  h.lift (fun a => Term.div a b) fun _ _ s => Step.div_l b s
theorem div_r (a : Term) {b b' : Term} (h : Steps A b b') : Steps A (.div a b) (.div a b') :=
  h.lift (fun b => Term.div a b) fun _ _ s => Step.div_r a s
theorem neg {a a' : Term} (h : Steps A a a') : Steps A (.neg a) (.neg a') :=
  h.lift Term.neg fun _ _ s => Step.neg s
theorem pow {a a' : Term} (n : ℤ) (h : Steps A a a') : Steps A (.pow a n) (.pow a' n) :=
  h.lift (fun a => Term.pow a n) fun _ _ s => Step.pow n s

theorem root {s t : Term} (r : Root A s t) : Steps A s t := ReflTransGen.single (Step.root r)

end Steps

theorem sAdd_steps (x y : Term) : Steps A (.add x y) (sAdd A x y) := by
  induction x, y using sAdd.induct A with
  | case1 x y h =>
    rw [sAdd]; simp only [h, ↓reduceIte]
    simp only [Bool.and_eq_true, isNum_iff] at h
    obtain ⟨⟨hn, p, rfl⟩, q, rfl⟩ := h
    exact Steps.root (Root.num_add p q hn)
  | case2 x y h1 h =>
    rw [sAdd]; simp only [h1, h, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.and_eq_true, isLit_iff] at h
    obtain ⟨hi, rfl⟩ := h
    exact Steps.root (Root.id_add_l y hi)
  | case3 x y h1 h2 h =>
    rw [sAdd]; simp only [h1, h2, h, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.and_eq_true, isLit_iff] at h
    obtain ⟨hi, rfl⟩ := h
    exact Steps.root (Root.id_add_r x hi)
  | case4 x y h1 h2 h3 h _ _ ih1 ih2 =>
    rw [sAdd]; simp only [h1, h2, h3, h, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    simp only [Bool.and_eq_true, isAdd_iff] at h
    obtain ⟨ha, y1, y2, rfl⟩ := h
    simp only [fst, snd] at ih1 ih2 ⊢
    exact (Steps.root (Root.assoc_add x y1 y2 ha)).trans ((Steps.add_l y2 ih1).trans ih2)
  | case5 x y h1 h2 h3 h4 h _ _ ih =>
    rw [sAdd]; simp only [h1, h2, h3, h4, h, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    simp only [Bool.and_eq_true, isNum_iff, isAdd_iff] at h
    obtain ⟨⟨⟨⟨⟨ha, hn⟩, han⟩, m, rfl⟩, x1, x2, rfl⟩, hx2⟩ := h
    simp only [snd] at hx2
    obtain ⟨p, rfl⟩ := hx2
    simp only [fst, snd, nv] at ih ⊢
    exact (Steps.root (Root.an_add x1 p m ha hn han)).trans ih
  | case6 x y h1 h2 h3 h4 h5 =>
    rw [sAdd]; simp only [h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    exact ReflTransGen.refl

theorem sMul_steps (x y : Term) : Steps A (.mul x y) (sMul A x y) := by
  induction x, y using sMul.induct A with
  | case1 x y h =>
    rw [sMul]; simp only [h, ↓reduceIte]
    simp only [Bool.and_eq_true, isNum_iff] at h
    obtain ⟨⟨hn, p, rfl⟩, q, rfl⟩ := h
    exact Steps.root (Root.num_mul p q hn)
  | case2 x y h1 h =>
    rw [sMul]; simp only [h1, h, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.and_eq_true, Bool.or_eq_true, isLit_iff] at h
    obtain ⟨ha, rfl | rfl⟩ := h
    · exact Steps.root (Root.ann_l y ha)
    · exact Steps.root (Root.ann_r x ha)
  | case3 x y h1 h2 h =>
    rw [sMul]; simp only [h1, h2, h, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.and_eq_true, isLit_iff] at h
    obtain ⟨hi, rfl⟩ := h
    exact Steps.root (Root.id_mul_l y hi)
  | case4 x y h1 h2 h3 h =>
    rw [sMul]; simp only [h1, h2, h3, h, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.and_eq_true, isLit_iff] at h
    obtain ⟨hi, rfl⟩ := h
    exact Steps.root (Root.id_mul_r x hi)
  | case5 x y h1 h2 h3 h4 h _ _ ih1 ih2 =>
    rw [sMul]; simp only [h1, h2, h3, h4, h, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    simp only [Bool.and_eq_true, isMul_iff] at h
    obtain ⟨ha, y1, y2, rfl⟩ := h
    simp only [fst, snd] at ih1 ih2 ⊢
    exact (Steps.root (Root.assoc_mul x y1 y2 ha)).trans ((Steps.mul_l y2 ih1).trans ih2)
  | case6 x y h1 h2 h3 h4 h5 h _ _ ih =>
    rw [sMul]; simp only [h1, h2, h3, h4, h5, h, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    simp only [Bool.and_eq_true, isNum_iff, isMul_iff] at h
    obtain ⟨⟨⟨⟨⟨ha, hn⟩, han⟩, m, rfl⟩, x1, x2, rfl⟩, hx2⟩ := h
    simp only [snd] at hx2
    obtain ⟨p, rfl⟩ := hx2
    simp only [fst, snd, nv] at ih ⊢
    exact (Steps.root (Root.an_mul x1 p m ha hn han)).trans ih
  | case7 x y h1 h2 h3 h4 h5 h6 =>
    rw [sMul]; simp only [h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    exact ReflTransGen.refl

theorem sNeg_steps (x : Term) : Steps A (.neg x) (sNeg A x) := by
  unfold sNeg
  split_ifs with h1 h2
  · simp only [Bool.and_eq_true, isNum_iff] at h1
    obtain ⟨hn, p, rfl⟩ := h1
    exact Steps.root (Root.num_neg p hn)
  · simp only [Bool.and_eq_true, isNeg_iff] at h2
    obtain ⟨hi, a, rfl⟩ := h2
    exact Steps.root (Root.inv_neg a hi)
  · exact ReflTransGen.refl

theorem sSub_steps (x y : Term) : Steps A (.sub x y) (sSub A x y) := by
  unfold sSub
  split_ifs with h1 h2 h3
  · simp only [Bool.and_eq_true, isNum_iff] at h1
    obtain ⟨⟨hn, p, rfl⟩, q, rfl⟩ := h1
    exact Steps.root (Root.num_sub p q hn)
  · simp only [Bool.and_eq_true, isLit_iff] at h2
    obtain ⟨hi, rfl⟩ := h2
    exact Steps.root (Root.id_sub_r x hi)
  · simp only [Bool.and_eq_true, isLit_iff] at h3
    obtain ⟨hi, rfl⟩ := h3
    exact (Steps.root (Root.id_sub_l y hi)).trans (sNeg_steps y)
  · exact ReflTransGen.refl

theorem sDiv_steps (x y : Term) : Steps A (.div x y) (sDiv A x y) := by
  unfold sDiv
  split_ifs with h1 h2 h3
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, isNum_iff] at h1
    obtain ⟨⟨⟨hn, p, rfl⟩, q, rfl⟩, hq⟩ := h1
    exact Steps.root (Root.num_div p q hn hq)
  · simp only [Bool.and_eq_true, isLit_iff] at h2
    obtain ⟨hi, rfl⟩ := h2
    exact Steps.root (Root.id_div x hi)
  · simp only [Bool.and_eq_true, isLit_iff, isDiv_iff] at h3
    obtain ⟨⟨⟨hi, rfl⟩, a, b, rfl⟩, hf⟩ := h3
    simp only [fst] at hf
    subst hf
    exact Steps.root (Root.inv_div b hi)
  · exact ReflTransGen.refl

theorem sPow_steps (x : Term) (n : ℤ) : Steps A (.pow x n) (sPow A x n) := by
  unfold sPow
  split_ifs with h1 h2 h3
  · simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      ne_eq, decide_eq_false_iff_not, isNum_iff] at h1
    obtain ⟨⟨hn, p, rfl⟩, h⟩ := h1
    exact Steps.root (Root.num_pow p n hn (by rcases h with h | h <;> simp_all [nv]))
  · simp only [Bool.and_eq_true, beq_iff_eq] at h2
    obtain ⟨hi, rfl⟩ := h2
    exact Steps.root (Root.id_pow1 x hi)
  · simp only [Bool.and_eq_true, beq_iff_eq] at h3
    obtain ⟨hi, rfl⟩ := h3
    exact Steps.root (Root.id_pow0 x hi)
  · exact ReflTransGen.refl

/-- L8: `t →* nf A t`: the normaliser only takes steps of the axioms. -/
theorem L8_steps_to_nf (t : Term) : Steps A t (nf A t) := by
  induction t with
  | num q => exact ReflTransGen.refl
  | var s => exact ReflTransGen.refl
  | add a b iha ihb =>
    exact (Steps.add_l b iha).trans ((Steps.add_r _ ihb).trans (sAdd_steps _ _))
  | sub a b iha ihb =>
    exact (Steps.sub_l b iha).trans ((Steps.sub_r _ ihb).trans (sSub_steps _ _))
  | neg a iha => exact (Steps.neg iha).trans (sNeg_steps _)
  | mul a b iha ihb =>
    exact (Steps.mul_l b iha).trans ((Steps.mul_r _ ihb).trans (sMul_steps _ _))
  | div a b iha ihb =>
    exact (Steps.div_l b iha).trans ((Steps.div_r _ ihb).trans (sDiv_steps _ _))
  | pow a n iha => exact (Steps.pow n iha).trans (sPow_steps _ _)

/-! ## L5, local identities: the root rules that need no associativity -/

section local_identities

variable (A)

theorem sAdd_num_num (hn : A.num = true) (p q : ℚ) : sAdd A (.num p) (.num q) = .num (p + q) := by
  rw [sAdd]; simp [hn, isNum, nv]

theorem sMul_num_num (hn : A.num = true) (p q : ℚ) : sMul A (.num p) (.num q) = .num (p * q) := by
  rw [sMul]; simp [hn, isNum, nv]

theorem sAdd_zero_l (hi : A.id = true) (X : Term) : sAdd A (.num 0) X = X := by
  rw [sAdd]; cases X <;> simp [hi, isNum, isLit, nv]

theorem sAdd_zero_r (hi : A.id = true) (X : Term) : sAdd A X (.num 0) = X := by
  rw [sAdd]; cases X <;> simp [hi, isNum, isLit, nv]
  intro _ h; exact h.symm

theorem sSub_zero_r (hi : A.id = true) (X : Term) : sSub A X (.num 0) = X := by
  unfold sSub; cases X <;> simp [hi, isNum, isLit, nv]

theorem sSub_zero_l (hi : A.id = true) (hn : A.num = true) (X : Term) :
    sSub A (.num 0) X = sNeg A X := by
  unfold sSub sNeg; cases X <;> simp [hi, hn, isNum, isLit, nv]

theorem sMul_one_l (hi : A.id = true) (X : Term) : sMul A (.num 1) X = X := by
  rw [sMul]; cases X <;> simp [hi, isNum, isLit, nv]
  intro _ _ h; exact h.symm

theorem sMul_one_r (hi : A.id = true) (X : Term) : sMul A X (.num 1) = X := by
  rw [sMul]; cases X <;> simp [hi, isNum, isLit, nv]
  intro _; split_ifs <;> simp_all

theorem sMul_zero_l (ha : A.ann = true) (X : Term) : sMul A (.num 0) X = .num 0 := by
  rw [sMul]; cases X <;> simp [ha, isNum, isLit, nv]

theorem sMul_zero_r (ha : A.ann = true) (X : Term) : sMul A X (.num 0) = .num 0 := by
  rw [sMul]; cases X <;> simp [ha, isNum, isLit, nv]

theorem sDiv_one_r (hi : A.id = true) (X : Term) : sDiv A X (.num 1) = X := by
  unfold sDiv; cases X <;> simp [hi, isNum, isLit, nv]

theorem sPow_one (hi : A.id = true) (X : Term) : sPow A X 1 = X := by
  unfold sPow; cases X <;> simp [hi, isNum, nv]

theorem sPow_zero (hi : A.id = true) (X : Term) : sPow A X 0 = .num 1 := by
  unfold sPow; cases X <;> simp [hi, isNum, nv]

theorem sNeg_sNeg (hi : A.inv = true) {X : Term} (hX : IsNF A X) : sNeg A (sNeg A X) = X := by
  cases X with
  | num q => by_cases hn : A.num = true <;> simp [sNeg, hi, hn, isNum, isNeg, nv, fst]
  | neg a =>
    rw [show sNeg A (.neg a) = a by simp [sNeg, hi, isNum, isNeg, fst]]
    exact sNeg_eq_of_isNF hX
  | _ => simp [sNeg, hi, isNum, isNeg, fst]

theorem sDiv_one_div (hi : A.inv = true) (X : Term) :
    sDiv A (.num 1) (.div (.num 1) X) = X := by
  unfold sDiv; simp [hi, isNum, isLit, isDiv, nv, fst, snd]

theorem sDiv_one_plain {X : Term} (h1 : X.isNum = false) (h2 : X.isDiv = false) :
    sDiv A (.num 1) X = .div (.num 1) X := by
  unfold sDiv; simp [h1, h2, isLit]

theorem sDiv_inv (hi : A.inv = true) {X : Term} (hX : IsNF A X) :
    sDiv A (.num 1) (sDiv A (.num 1) X) = X := by
  by_cases h1 : X.isNum = true
  · obtain ⟨q, rfl⟩ := isNum_iff.1 h1
    by_cases hn : A.num = true
    · by_cases hq : q = 0
      · subst hq
        have e : sDiv A (.num 1) (.num 0) = .div (.num 1) (.num 0) := by
          unfold sDiv; simp [isNum, isLit, isDiv, nv]
        rw [e, sDiv_one_div A hi]
      · have e : sDiv A (.num 1) (.num q) = .num q⁻¹ := by
          unfold sDiv; simp [hn, hq, isNum, nv]
        rw [e]; unfold sDiv; simp [hn, hq, isNum, nv]
    · by_cases hid : A.id = true ∧ q = 1
      · obtain ⟨hid, rfl⟩ := hid
        have e : sDiv A (.num 1) (.num 1) = .num 1 := by
          unfold sDiv; simp [hn, hid, isNum, isLit, nv]
        rw [e, e]
      · have e : sDiv A (.num 1) (.num q) = .div (.num 1) (.num q) := by
          unfold sDiv
          have : ¬ (A.id && (Term.num q).isLit 1) = true := by
            simpa [isLit, isNum, nv] using hid
          simp only [this, Bool.false_eq_true, ↓reduceIte]
          simp [hn, isDiv]
        rw [e, sDiv_one_div A hi]
  by_cases h2 : X.isDiv = true
  · obtain ⟨a, b, rfl⟩ := isDiv_iff.1 h2
    by_cases ha : a = .num 1
    · subst ha
      rw [show sDiv A (.num 1) (.div (.num 1) b) = b from sDiv_one_div A hi b]
      exact sDiv_eq_of_isNF hX
    · have h3 : a.isLit 1 = false := Bool.eq_false_iff.2 fun h => ha (isLit_iff.1 h)
      have e : sDiv A (.num 1) (.div a b) = .div (.num 1) (.div a b) := by
        unfold sDiv
        have g2 : (Term.div a b).isLit 1 = false := rfl
        simp only [fst, h3, g2, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        simp [isNum]
      rw [e, sDiv_one_div A hi]
  · rw [sDiv_one_plain A (X := X) (by simpa using h1) (by simpa using h2), sDiv_one_div A hi]

end local_identities

/-! ## L5, associativity: `sAdd` and `sMul` are associative on normal forms

This is where the hand proof of 2026-11-26 went wrong: without (AN) the
statement is false (L7). The proof follows the clauses of `sAdd Y Z`, by
well-founded recursion on `(|Z|, |Y|)`. -/

section assoc_add

variable (A)

theorem sAdd_an_path (ha : A.assoc = true) (hn : A.num = true) (han : A.an = true) {m : ℚ}
    (hz : ¬ (A.id = true ∧ m = 0)) (X : Term) (n : ℚ) :
    sAdd A (.add X (.num n)) (.num m) = sAdd A X (.num (n + m)) := by
  have g3 : ¬ (A.id && (Term.num m).isLit 0) = true := by simpa [isLit, isNum, nv] using hz
  conv_lhs => rw [sAdd]
  simp only [g3, Bool.false_eq_true, ↓reduceIte]
  simp [ha, hn, han, isNum, isLit, isAdd, fst, snd, nv]

theorem sAdd_plain {X : Term} {n : ℚ} (h1 : X.isNum = false)
    (h2 : ¬ (X.isAdd = true ∧ X.snd.isNum = true)) (hz : ¬ (A.id = true ∧ n = 0)) :
    sAdd A X (.num n) = .add X (.num n) := by
  have g1 : ¬ (A.num && X.isNum && (Term.num n).isNum) = true := by simp [h1]
  have g2 : ¬ (A.id && X.isLit 0) = true := by simp [isLit, h1]
  have g3 : ¬ (A.id && (Term.num n).isLit 0) = true := by simpa [isLit, isNum, nv] using hz
  have g4 : ¬ (A.assoc && (Term.num n).isAdd) = true := by simp [isAdd]
  have g5 : ¬ (A.assoc && A.num && A.an && (Term.num n).isNum && X.isAdd && X.snd.isNum) = true := by
    intro h; simp only [Bool.and_eq_true] at h; exact h2 ⟨h.1.2, h.2⟩
  rw [sAdd]; simp only [g1, g2, g3, g4, g5, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]

theorem sAdd_an_plain (ha : A.assoc = true) (hn : A.num = true) (han : A.an = true) {X : Term}
    (h1 : X.isNum = false) (h2 : ¬ (X.isAdd = true ∧ X.snd.isNum = true)) (n m : ℚ) :
    sAdd A (sAdd A X (.num n)) (.num m) = sAdd A X (.num (n + m)) := by
  by_cases hz : A.id = true ∧ n = 0
  · obtain ⟨hi, rfl⟩ := hz; rw [sAdd_zero_r A hi, zero_add]
  rw [sAdd_plain A h1 h2 hz]
  by_cases hm : A.id = true ∧ m = 0
  · obtain ⟨hi, rfl⟩ := hm; rw [sAdd_zero_r A hi, add_zero, sAdd_plain A h1 h2 hz]
  · rw [sAdd_an_path A ha hn han hm]

/-- (AN) holds for `sAdd` on normal forms: `(X + n) + m = X + (n + m)`. -/
theorem sAdd_an (ha : A.assoc = true) (hn : A.num = true) (han : A.an = true) (X : Term)
    (hX : IsNF A X) (n m : ℚ) :
    sAdd A (sAdd A X (.num n)) (.num m) = sAdd A X (.num (n + m)) := by
  induction X generalizing n m with
  | num p => rw [sAdd_num_num A hn, sAdd_num_num A hn, sAdd_num_num A hn, add_assoc]
  | add X1 X2 ih1 _ =>
    by_cases hp : X2.isNum = true
    · obtain ⟨p, rfl⟩ := isNum_iff.1 hp
      by_cases hz : A.id = true ∧ n = 0
      · obtain ⟨hi, rfl⟩ := hz; rw [sAdd_zero_r A hi, zero_add]
      rw [sAdd_an_path A ha hn han hz X1 p, ih1 hX.add_l]
      by_cases hz' : A.id = true ∧ n + m = 0
      · rw [add_assoc, hz'.2, add_zero, sAdd_zero_r A hz'.1]
        exact sAdd_eq_of_isNF hX
      · rw [sAdd_an_path A ha hn han hz' X1 p, add_assoc]
    · exact sAdd_an_plain A ha hn han rfl (by simp [isAdd, snd, hp]) n m
  | _ => exact sAdd_an_plain A ha hn han rfl (by simp [isAdd]) n m

theorem sAdd_add_right (ha : A.assoc = true) (Z1 Z2 : Term) (hZ : IsNF A (.add Z1 Z2))
    (W : Term) : sAdd A W (.add Z1 Z2) = sAdd A (sAdd A W Z1) Z2 := by
  by_cases g2 : A.id = true ∧ W = .num 0
  · obtain ⟨hi, rfl⟩ := g2
    rw [sAdd_zero_l A hi, sAdd_zero_l A hi]; exact (sAdd_eq_of_isNF hZ).symm
  · have g2' : ¬ (A.id && W.isLit 0) = true := by simpa [isLit_iff] using g2
    conv_lhs => rw [sAdd]
    simp only [g2', Bool.false_eq_true, ↓reduceIte]
    simp [ha, isNum, isLit, isAdd, fst, snd]

/-- `sAdd` is associative on normal forms (needs (AN) when Num is present). -/
theorem sAdd_assoc (ha : A.assoc = true) (han : A.an = true) (X Y Z : Term)
    (hX : IsNF A X) (hY : IsNF A Y) (hZ : IsNF A Z) :
    sAdd A X (sAdd A Y Z) = sAdd A (sAdd A X Y) Z := by
  by_cases c1 : A.num = true ∧ Y.isNum = true ∧ Z.isNum = true
  · obtain ⟨hn, hy, hz⟩ := c1
    obtain ⟨p, rfl⟩ := isNum_iff.1 hy
    obtain ⟨q, rfl⟩ := isNum_iff.1 hz
    rw [sAdd_num_num A hn, sAdd_an A ha hn han X hX p q]
  by_cases c2 : A.id = true ∧ Y = .num 0
  · obtain ⟨hi, rfl⟩ := c2; rw [sAdd_zero_l A hi, sAdd_zero_r A hi]
  by_cases c3 : A.id = true ∧ Z = .num 0
  · obtain ⟨hi, rfl⟩ := c3; rw [sAdd_zero_r A hi, sAdd_zero_r A hi]
  by_cases c4 : Z.isAdd = true
  · obtain ⟨Z1, Z2, rfl⟩ := isAdd_iff.1 c4
    rw [sAdd_add_right A ha Z1 Z2 hZ Y, sAdd_add_right A ha Z1 Z2 hZ (sAdd A X Y),
      sAdd_assoc ha han X (sAdd A Y Z1) Z2 hX (sAdd_isNF _ _ hY hZ.add_l) hZ.add_r,
      sAdd_assoc ha han X Y Z1 hX hY hZ.add_l]
  by_cases c5 : A.num = true ∧ Z.isNum = true ∧ Y.isAdd = true ∧ Y.snd.isNum = true
  · obtain ⟨hn, hz, hy, hys⟩ := c5
    obtain ⟨m, rfl⟩ := isNum_iff.1 hz
    obtain ⟨Y1, Y2, rfl⟩ := isAdd_iff.1 hy
    simp only [snd] at hys
    obtain ⟨n, rfl⟩ := isNum_iff.1 hys
    have hz3 : ¬ (A.id = true ∧ m = 0) := fun h => c3 ⟨h.1, by rw [h.2]⟩
    rw [sAdd_an_path A ha hn han hz3 Y1 n, sAdd_add_right A ha Y1 (.num n) hY X,
      sAdd_an A ha hn han _ (sAdd_isNF _ _ hX hY.add_l) n m,
      sAdd_assoc ha han X Y1 (.num (n + m)) hX hY.add_l (IsNF.num _)]
  · have g1 : ¬ (A.num && Y.isNum && Z.isNum) = true := by
      intro h; simp only [Bool.and_eq_true] at h; exact c1 ⟨h.1.1, h.1.2, h.2⟩
    have g2 : ¬ (A.id && Y.isLit 0) = true := by simpa [isLit_iff] using c2
    have g3 : ¬ (A.id && Z.isLit 0) = true := by simpa [isLit_iff] using c3
    have g4 : ¬ (A.assoc && Z.isAdd) = true := by
      intro h; simp only [Bool.and_eq_true] at h; exact c4 h.2
    have g5 : ¬ (A.assoc && A.num && A.an && Z.isNum && Y.isAdd && Y.snd.isNum) = true := by
      intro h; simp only [Bool.and_eq_true] at h
      exact c5 ⟨h.1.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
    have e : sAdd A Y Z = .add Y Z := by
      rw [sAdd]; simp only [g1, g2, g3, g4, g5, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    have hYZ : IsNF A (.add Y Z) := e ▸ sAdd_isNF _ _ hY hZ
    rw [e, sAdd_add_right A ha Y Z hYZ X]
termination_by (Z.size, Y.size)
decreasing_by
  all_goals
    subst_vars
    first
      | exact Prod.Lex.left _ _ (by simp only [size]; omega)
      | exact Prod.Lex.right' _ (by simp [size]) (by simp only [size]; omega)

end assoc_add

section assoc_mul

variable (A)

theorem sMul_an_path (ha : A.assoc = true) (hn : A.num = true) (han : A.an = true) {m : ℚ}
    (hz : ¬ (A.ann = true ∧ m = 0)) (ho : ¬ (A.id = true ∧ m = 1)) (X : Term) (n : ℚ) :
    sMul A (.mul X (.num n)) (.num m) = sMul A X (.num (n * m)) := by
  have g2 : ¬ (A.ann && ((Term.mul X (.num n)).isLit 0 || (Term.num m).isLit 0)) = true := by
    simpa [isLit, isNum, nv] using hz
  have g4 : ¬ (A.id && (Term.num m).isLit 1) = true := by simpa [isLit, isNum, nv] using ho
  conv_lhs => rw [sMul]
  simp only [g2, g4, Bool.false_eq_true, ↓reduceIte]
  simp [ha, hn, han, isNum, isLit, isMul, fst, snd, nv]

theorem sMul_plain {X : Term} {n : ℚ} (h1 : X.isNum = false)
    (h2 : ¬ (X.isMul = true ∧ X.snd.isNum = true)) (hz : ¬ (A.ann = true ∧ n = 0))
    (ho : ¬ (A.id = true ∧ n = 1)) : sMul A X (.num n) = .mul X (.num n) := by
  have hl0 : X.isLit 0 = false := by simp [isLit, h1]
  have hl1 : X.isLit 1 = false := by simp [isLit, h1]
  have g1 : ¬ (A.num && X.isNum && (Term.num n).isNum) = true := by simp [h1]
  have g2 : ¬ (A.ann && (X.isLit 0 || (Term.num n).isLit 0)) = true := by
    simp only [hl0, Bool.false_or]; simpa [isLit, isNum, nv] using hz
  have g3 : ¬ (A.id && X.isLit 1) = true := by simp [hl1]
  have g4 : ¬ (A.id && (Term.num n).isLit 1) = true := by simpa [isLit, isNum, nv] using ho
  have g5 : ¬ (A.assoc && (Term.num n).isMul) = true := by simp [isMul]
  have g6 : ¬ (A.assoc && A.num && A.an && (Term.num n).isNum && X.isMul && X.snd.isNum) = true := by
    intro h; simp only [Bool.and_eq_true] at h; exact h2 ⟨h.1.2, h.2⟩
  rw [sMul]; simp only [g1, g2, g3, g4, g5, g6, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]

/-- The cases of (AN) for `*` that annihilation or the identity settle, for any `X`. -/
theorem sMul_an_easy {X : Term} {n m : ℚ}
    (h : (A.ann = true ∧ n = 0) ∨ (A.ann = true ∧ m = 0) ∨ (A.id = true ∧ n = 1)) :
    sMul A (sMul A X (.num n)) (.num m) = sMul A X (.num (n * m)) := by
  rcases h with ⟨hA, rfl⟩ | ⟨hA, rfl⟩ | ⟨hi, rfl⟩
  · simp only [zero_mul, sMul_zero_r A hA, sMul_zero_l A hA]
  · simp only [mul_zero, sMul_zero_r A hA]
  · simp only [one_mul, sMul_one_r A hi]

theorem sMul_an_plain (ha : A.assoc = true) (hn : A.num = true) (han : A.an = true) {X : Term}
    (h1 : X.isNum = false) (h2 : ¬ (X.isMul = true ∧ X.snd.isNum = true)) (n m : ℚ) :
    sMul A (sMul A X (.num n)) (.num m) = sMul A X (.num (n * m)) := by
  by_cases he : (A.ann = true ∧ n = 0) ∨ (A.ann = true ∧ m = 0) ∨ (A.id = true ∧ n = 1)
  · exact sMul_an_easy A he
  simp only [not_or] at he
  obtain ⟨hz, hm, ho⟩ := he
  rw [sMul_plain A h1 h2 hz ho]
  by_cases hm1 : A.id = true ∧ m = 1
  · obtain ⟨hi, rfl⟩ := hm1; rw [sMul_one_r A hi, mul_one, sMul_plain A h1 h2 hz ho]
  · rw [sMul_an_path A ha hn han hm hm1]

/-- (AN) holds for `sMul` on normal forms: `(X · n) · m = X · (n m)`. -/
theorem sMul_an (ha : A.assoc = true) (hn : A.num = true) (han : A.an = true) (X : Term)
    (hX : IsNF A X) (n m : ℚ) :
    sMul A (sMul A X (.num n)) (.num m) = sMul A X (.num (n * m)) := by
  induction X generalizing n m with
  | num p => rw [sMul_num_num A hn, sMul_num_num A hn, sMul_num_num A hn, mul_assoc]
  | mul X1 X2 ih1 _ =>
    by_cases hp : X2.isNum = true
    · obtain ⟨p, rfl⟩ := isNum_iff.1 hp
      by_cases he : (A.ann = true ∧ n = 0) ∨ (A.ann = true ∧ m = 0) ∨ (A.id = true ∧ n = 1)
      · exact sMul_an_easy A he
      simp only [not_or] at he
      obtain ⟨hz, hm, ho⟩ := he
      rw [sMul_an_path A ha hn han hz ho X1 p, ih1 hX.mul_l]
      have hnm : ¬ (A.ann = true ∧ n * m = 0) := by
        rintro ⟨hA, h⟩
        rcases mul_eq_zero.1 h with h | h
        · exact hz ⟨hA, h⟩
        · exact hm ⟨hA, h⟩
      by_cases ho' : A.id = true ∧ n * m = 1
      · rw [mul_assoc, ho'.2, mul_one, sMul_one_r A ho'.1]
        exact sMul_eq_of_isNF hX
      · rw [sMul_an_path A ha hn han hnm ho' X1 p, mul_assoc]
    · exact sMul_an_plain A ha hn han rfl (by simp [isMul, snd, hp]) n m
  | _ => exact sMul_an_plain A ha hn han rfl (by simp [isMul]) n m

theorem sMul_mul_right (ha : A.assoc = true) (Z1 Z2 : Term) (hZ : IsNF A (.mul Z1 Z2))
    (W : Term) : sMul A W (.mul Z1 Z2) = sMul A (sMul A W Z1) Z2 := by
  by_cases g2 : A.ann = true ∧ W = .num 0
  · obtain ⟨hA, rfl⟩ := g2; simp only [sMul_zero_l A hA]
  by_cases g3 : A.id = true ∧ W = .num 1
  · obtain ⟨hi, rfl⟩ := g3
    rw [sMul_one_l A hi, sMul_one_l A hi]; exact (sMul_eq_of_isNF hZ).symm
  have g2' : ¬ (A.ann && (W.isLit 0 || (Term.mul Z1 Z2).isLit 0)) = true := by
    simpa [isLit_iff] using g2
  have g3' : ¬ (A.id && W.isLit 1) = true := by simpa [isLit_iff] using g3
  conv_lhs => rw [sMul]
  simp only [g2', g3', Bool.false_eq_true, ↓reduceIte]
  simp [ha, isNum, isLit, isMul, fst, snd]

/-- `sMul` is associative on normal forms (needs (AN) when Num is present). -/
theorem sMul_assoc (ha : A.assoc = true) (han : A.an = true) (X Y Z : Term)
    (hX : IsNF A X) (hY : IsNF A Y) (hZ : IsNF A Z) :
    sMul A X (sMul A Y Z) = sMul A (sMul A X Y) Z := by
  by_cases c1 : A.num = true ∧ Y.isNum = true ∧ Z.isNum = true
  · obtain ⟨hn, hy, hz⟩ := c1
    obtain ⟨p, rfl⟩ := isNum_iff.1 hy
    obtain ⟨q, rfl⟩ := isNum_iff.1 hz
    rw [sMul_num_num A hn, sMul_an A ha hn han X hX p q]
  by_cases c2 : A.ann = true ∧ (Y = .num 0 ∨ Z = .num 0)
  · obtain ⟨hA, rfl | rfl⟩ := c2 <;> simp only [sMul_zero_l A hA, sMul_zero_r A hA]
  by_cases c3 : A.id = true ∧ Y = .num 1
  · obtain ⟨hi, rfl⟩ := c3; rw [sMul_one_l A hi, sMul_one_r A hi]
  by_cases c4 : A.id = true ∧ Z = .num 1
  · obtain ⟨hi, rfl⟩ := c4; rw [sMul_one_r A hi, sMul_one_r A hi]
  by_cases c5 : Z.isMul = true
  · obtain ⟨Z1, Z2, rfl⟩ := isMul_iff.1 c5
    rw [sMul_mul_right A ha Z1 Z2 hZ Y, sMul_mul_right A ha Z1 Z2 hZ (sMul A X Y),
      sMul_assoc ha han X (sMul A Y Z1) Z2 hX (sMul_isNF _ _ hY hZ.mul_l) hZ.mul_r,
      sMul_assoc ha han X Y Z1 hX hY hZ.mul_l]
  by_cases c6 : A.num = true ∧ Z.isNum = true ∧ Y.isMul = true ∧ Y.snd.isNum = true
  · obtain ⟨hn, hz, hy, hys⟩ := c6
    obtain ⟨m, rfl⟩ := isNum_iff.1 hz
    obtain ⟨Y1, Y2, rfl⟩ := isMul_iff.1 hy
    simp only [snd] at hys
    obtain ⟨n, rfl⟩ := isNum_iff.1 hys
    have hz3 : ¬ (A.ann = true ∧ m = 0) := fun h => c2 ⟨h.1, Or.inr (by rw [h.2])⟩
    have ho3 : ¬ (A.id = true ∧ m = 1) := fun h => c4 ⟨h.1, by rw [h.2]⟩
    rw [sMul_an_path A ha hn han hz3 ho3 Y1 n, sMul_mul_right A ha Y1 (.num n) hY X,
      sMul_an A ha hn han _ (sMul_isNF _ _ hX hY.mul_l) n m,
      sMul_assoc ha han X Y1 (.num (n * m)) hX hY.mul_l (IsNF.num _)]
  · have g1 : ¬ (A.num && Y.isNum && Z.isNum) = true := by
      intro h; simp only [Bool.and_eq_true] at h; exact c1 ⟨h.1.1, h.1.2, h.2⟩
    have g2 : ¬ (A.ann && (Y.isLit 0 || Z.isLit 0)) = true := by
      intro h; simp only [Bool.and_eq_true, Bool.or_eq_true, isLit_iff] at h; exact c2 h
    have g3 : ¬ (A.id && Y.isLit 1) = true := by simpa [isLit_iff] using c3
    have g4 : ¬ (A.id && Z.isLit 1) = true := by simpa [isLit_iff] using c4
    have g5 : ¬ (A.assoc && Z.isMul) = true := by
      intro h; simp only [Bool.and_eq_true] at h; exact c5 h.2
    have g6 : ¬ (A.assoc && A.num && A.an && Z.isNum && Y.isMul && Y.snd.isNum) = true := by
      intro h; simp only [Bool.and_eq_true] at h
      exact c6 ⟨h.1.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
    have e : sMul A Y Z = .mul Y Z := by
      rw [sMul]; simp only [g1, g2, g3, g4, g5, g6, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    have hYZ : IsNF A (.mul Y Z) := e ▸ sMul_isNF _ _ hY hZ
    rw [e, sMul_mul_right A ha Y Z hYZ X]
termination_by (Z.size, Y.size)
decreasing_by
  all_goals
    subst_vars
    first
      | exact Prod.Lex.left _ _ (by simp only [size]; omega)
      | exact Prod.Lex.right' _ (by simp [size]) (by simp only [size]; omega)

end assoc_mul

/-! ## L5: a step does not change the normal form -/

/-- Each root rule of the spec preserves `nf`. Hypotheses: Id comes with Num (L10), and (AN)
is on (L7). -/
theorem L5_root (hid : A.id = true → A.num = true) (han : A.an = true) {s t : Term}
    (r : Root A s t) : nf A s = nf A t := by
  cases r with
  | id_add_l x hi => simp only [nf]; exact sAdd_zero_l A hi _
  | id_add_r x hi => simp only [nf]; exact sAdd_zero_r A hi _
  | id_sub_r x hi => simp only [nf]; exact sSub_zero_r A hi _
  | id_sub_l x hi => simp only [nf]; exact sSub_zero_l A hi (hid hi) _
  | id_mul_l x hi => simp only [nf]; exact sMul_one_l A hi _
  | id_mul_r x hi => simp only [nf]; exact sMul_one_r A hi _
  | id_div x hi => simp only [nf]; exact sDiv_one_r A hi _
  | id_pow1 x hi => simp only [nf]; exact sPow_one A hi _
  | id_pow0 x hi => simp only [nf]; exact sPow_zero A hi _
  | ann_l x h => simp only [nf]; exact sMul_zero_l A h _
  | ann_r x h => simp only [nf]; exact sMul_zero_r A h _
  | inv_neg x h => simp only [nf]; exact sNeg_sNeg A h (L4_nf_isNF _)
  | inv_div x h => simp only [nf]; exact sDiv_inv A h (L4_nf_isNF _)
  | num_add p q h => simp only [nf]; exact sAdd_num_num A h p q
  | num_sub p q h => simp only [nf]; unfold sSub; simp [h, isNum, nv]
  | num_mul p q h => simp only [nf]; exact sMul_num_num A h p q
  | num_neg p h => simp only [nf]; unfold sNeg; simp [h, isNum, nv]
  | num_div p q h hq => simp only [nf]; unfold sDiv; simp [h, hq, isNum, nv]
  | num_pow p n h hp =>
    simp only [nf]; unfold sPow
    by_cases hp0 : p = 0
    · have hn : ¬ n < 0 := fun hn => hp ⟨hp0, hn⟩
      simp [h, isNum, nv, hp0, hn]
    · simp [h, isNum, nv, hp0]
  | assoc_add x y z ha =>
    simp only [nf]
    exact sAdd_assoc A ha han _ _ _ (L4_nf_isNF x) (L4_nf_isNF y) (L4_nf_isNF z)
  | assoc_mul x y z ha =>
    simp only [nf]
    exact sMul_assoc A ha han _ _ _ (L4_nf_isNF x) (L4_nf_isNF y) (L4_nf_isNF z)
  | an_add x n m ha hn han' =>
    simp only [nf]; exact sAdd_an A ha hn han' _ (L4_nf_isNF x) n m
  | an_mul x n m ha hn han' =>
    simp only [nf]; exact sMul_an A ha hn han' _ (L4_nf_isNF x) n m

/-- L5: one step does not change the normal form. -/
theorem L5_step (hid : A.id = true → A.num = true) (han : A.an = true) {s t : Term}
    (h : Step A s t) : nf A s = nf A t := by
  induction h with
  | root r => exact L5_root hid han r
  | add_l b _ ih | sub_l b _ ih | mul_l b _ ih | div_l b _ ih => simp only [nf, ih]
  | add_r a _ ih | sub_r a _ ih | mul_r a _ ih | div_r a _ ih => simp only [nf, ih]
  | neg _ ih | pow n _ ih => simp only [nf, ih]

/-- L5: terms equal under the axioms have the same normal form (Theorem 3). -/
theorem L5_eqA (hid : A.id = true → A.num = true) (han : A.an = true) {s t : Term}
    (h : EqA A s t) : nf A s = nf A t := by
  induction h with
  | rel _ _ h => exact L5_step hid han h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem Steps.to_eqA {s t : Term} (h : Steps A s t) : EqA A s t := by
  induction h with
  | refl => exact EqvGen.refl _
  | tail _ h ih => exact EqvGen.trans _ _ _ ih (EqvGen.rel _ _ h)

/-- Theorem 3 as a decision procedure: `s =_A t` exactly when `nf A s = nf A t`. -/
theorem eqA_iff_nf_eq (hid : A.id = true → A.num = true) (han : A.an = true) {s t : Term} :
    EqA A s t ↔ nf A s = nf A t := by
  refine ⟨L5_eqA hid han, fun h => ?_⟩
  have hs := Steps.to_eqA (L8_steps_to_nf (A := A) s)
  have ht := Steps.to_eqA (L8_steps_to_nf (A := A) t)
  rw [h] at hs
  exact EqvGen.trans _ _ _ hs (EqvGen.symm _ _ ht)

/-- Church–Rosser: terms equal under the axioms rewrite to a common term. -/
theorem church_rosser (hid : A.id = true → A.num = true) (han : A.an = true) {s t : Term}
    (h : EqA A s t) : ∃ u, Steps A s u ∧ Steps A t u :=
  ⟨nf A s, L8_steps_to_nf s, L5_eqA hid han h ▸ L8_steps_to_nf t⟩

/-- Unique normal forms: two normal forms equal under the axioms are the same term. -/
theorem unique_nf (hid : A.id = true → A.num = true) (han : A.an = true) {s t : Term}
    (hs : IsNF A s) (ht : IsNF A t) (h : EqA A s t) : s = t := by
  rw [← L6_nf_of_isNF hs, ← L6_nf_of_isNF ht]; exact L5_eqA hid han h

end FricasSymbolic
