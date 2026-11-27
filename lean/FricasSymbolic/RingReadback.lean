import FricasSymbolic.RingMirror
import Mathlib.Algebra.MvPolynomial.Basic

namespace FricasSymbolic.RingMirror
open FricasSymbolic.Order Tree MvPolynomial

mutual
theorem teq_eq : ∀ (a b : Tree), teq a b = true → a = b
  | int n, b => by cases b <;> simp [teq]
  | flt n, b => by cases b <;> simp [teq]
  | sym n, b => by cases b <;> simp [teq]
  | Tree.str n, b => by cases b <;> simp [teq]
  | atom n, b => by cases b <;> simp [teq]
  | node h as, b => by
    cases b <;> simp only [teq, Bool.and_eq_true, reduceCtorEq, false_implies, node.injEq]
    exact fun ⟨h1, h2⟩ => ⟨teq_eq h _ h1, teqL_eq as _ h2⟩
theorem teqL_eq : ∀ (as bs : List Tree), teqL as bs = true → as = bs
  | [], bs => by cases bs <;> simp [teqL]
  | a :: as, bs => by
    cases bs <;> simp only [teqL, Bool.and_eq_true, reduceCtorEq, false_implies, List.cons.injEq]
    exact fun ⟨h1, h2⟩ => ⟨teq_eq a _ h1, teqL_eq as _ h2⟩
end

mutual
theorem teq_refl : ∀ a : Tree, teq a a = true
  | int n => by simp [teq]
  | flt n => by simp [teq]
  | sym n => by simp [teq]
  | Tree.str n => by simp [teq]
  | atom n => by simp [teq]
  | node h as => by simp only [teq, teq_refl h, teqL_refl as, Bool.and_self]
theorem teqL_refl : ∀ as : List Tree, teqL as as = true
  | [] => by simp [teqL]
  | a :: as => by simp only [teqL, teq_refl a, teqL_refl as, Bool.and_self]
end

theorem teq_iff {a b : Tree} : teq a b = true ↔ a = b :=
  ⟨teq_eq a b, fun h => h ▸ teq_refl a⟩

instance : DecidableEq Tree := fun a b =>
  if h : teq a b then isTrue (teq_iff.1 h) else isFalse (fun e => h (teq_iff.2 e))

theorem teq_eq_decide (a b : Tree) : teq a b = decide (a = b) := by
  by_cases h : a = b
  · simp [h, teq_refl]
  · simpa [h] using fun e => h (teq_iff.1 e)

theorem numeralForm_numNode (q : ℚ) : numeralForm (numNode q) = some (false, q) := by
  have pos : ∀ r : ℚ, numeralForm (if r.den = 1 then int r.num else
      node (sym "/") [int r.num, int r.den]) = some (false, r) := by
    intro r
    split_ifs with h
    · simp [numeralForm, Rat.intCast_num_of_den_eq_one h]
    · simp [numeralForm, Rat.num_div_den]
  unfold numNode
  split_ifs with h
  · simp only [numeralForm, beq_self_eq_true, ↓reduceIte, pos, Option.map_some, neg_neg]
  · exact pos q

theorem isNum_numNode (q : ℚ) : isNum (numNode q) = true := by
  simp [isNum, numeralForm_numNode]

theorem val_numNode (q : ℚ) : val (numNode q) = q := by
  simp [val, numeralForm_numNode]

theorem numeralForm_node2 {h : String} (hh : h ≠ "/") (a b : Tree) :
    numeralForm (node (sym h) [a, b]) = none := by
  cases a <;> cases b <;> simp [numeralForm, hh]

theorem isNum_node2 {h : String} (hh : h ≠ "/") (a b : Tree) :
    isNum (node (sym h) [a, b]) = false := by
  simp [isNum, numeralForm_node2 hh]

/-! ## Reading a tree as a polynomial over its atoms -/

/-- `rd`: a tree read as a polynomial, clause by clause as `toF`, with `X t` at an atom. -/
noncomputable def rd (t : Tree) : MvPolynomial Tree ℚ :=
  if isNum t then C (val t) else
  match t with
  | node (sym "+") [a, b] => rd a + rd b
  | node (sym "-") [a] => - rd a
  | node (sym "-") [a, b] => rd a - rd b
  | node (sym "*") [a, b] => rd a * rd b
  | node (sym "/") [a, b] => if isNum b then C (val b)⁻¹ * rd a else X t
  | node (sym "^") [b, e] =>
    match rpow (node (sym "^") [b, e]) with
    | some n => rd b ^ n
    | none => X t
  | _ => X t

theorem ite_false_cond {α : Type*} {c : Bool} (h : c = false) (a b : α) :
    (if c = true then a else b) = b := by simp [h]

theorem rd_num {t : Tree} (h : isNum t = true) : rd t = C (val t) := by
  unfold rd; simp [h]

theorem rd_numNode (q : ℚ) : rd (numNode q) = C q := by
  rw [rd_num (isNum_numNode q), val_numNode]

theorem rd_add (a b : Tree) : rd (node (sym "+") [a, b]) = rd a + rd b := by
  rw [rd, ite_false_cond (isNum_node2 (h := "+") (by decide) a b)]

theorem rd_sub (a b : Tree) : rd (node (sym "-") [a, b]) = rd a - rd b := by
  rw [rd, ite_false_cond (isNum_node2 (h := "-") (by decide) a b)]

theorem rd_mul (a b : Tree) : rd (node (sym "*") [a, b]) = rd a * rd b := by
  rw [rd, ite_false_cond (isNum_node2 (h := "*") (by decide) a b)]

theorem rd_neg (a : Tree) : rd (node (sym "-") [a]) = - rd a := by
  by_cases h : isNum a = true
  · have h1 : numeralForm (node (sym "-") [a]) = (numeralForm a).map fun p => (p.1, -p.2) := by
      simp [numeralForm]
    have h2 : isNum (node (sym "-") [a]) = true := by
      simp only [isNum, h1, Option.isSome_map]; exact h
    rw [rd_num h2, rd_num h]
    simp only [val, h1]
    cases hn : numeralForm a <;> simp
  · have h2 : isNum (node (sym "-") [a]) = false := by
      simp only [isNum, numeralForm, beq_self_eq_true, ↓reduceIte, Option.isSome_map]
      simpa [isNum] using h
    rw [rd, ite_false_cond h2]

theorem rd_pow (b : Tree) (e : ℕ) : rd (node (sym "^") [b, int e]) = rd b ^ e := by
  rw [rd, ite_false_cond (isNum_node2 (h := "^") (by decide) b (int e))]
  simp [rpow, intExp, numeralForm]

theorem rd_foldl_mul (rs : List Tree) (r : Tree) :
    rd (rs.foldl (fun acc t => arith "*" [acc, t]) r) = rd r * (rs.map rd).prod := by
  induction rs generalizing r with
  | nil => simp
  | cons t rs ih =>
    rw [List.foldl_cons, ih]
    simp only [arith, rd_mul, List.map_cons, List.prod_cons, mul_assoc]

theorem rd_mulChain (c : ℚ) (fs : List Tree) : rd (mulChain c fs) = C c * (fs.map rd).prod := by
  unfold mulChain
  by_cases h : c ≠ 1 ∨ fs = []
  · simp only [h, ↓reduceIte, rd_foldl_mul, rd_numNode]
  · simp only [h, ↓reduceIte]
    simp only [ne_eq, not_or, not_not] at h
    obtain ⟨rfl, hfs⟩ := h
    obtain ⟨r, rs, rfl⟩ := List.exists_cons_of_ne_nil hfs
    simp [rd_foldl_mul]

end FricasSymbolic.RingMirror
