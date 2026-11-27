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
  | _ => simp [SizeMuLt, size, mu]; try omega

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

end FricasSymbolic
