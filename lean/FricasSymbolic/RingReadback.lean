import FricasSymbolic.RingMirror
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

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

/-! ## Merging and sorting, generically -/

section Generic
variable {α β γ : Type*}

/-- One step of `mergeF` and `mergeT`: `x` added to the entry with the same key, or
appended. -/
def mins [Add β] (k : α → Tree) (x : α × β) : List (α × β) → List (α × β)
  | [] => [x]
  | y :: r => if k y.1 = k x.1 then (y.1, y.2 + x.2) :: r else y :: mins k x r

theorem step_eq [Add β] (k : α → Tree) (x : α × β) (acc : List (α × β)) :
    (match acc.findIdx? (fun g => teq (k g.1) (k x.1)) with
      | some i => acc.modify i (fun g => (g.1, g.2 + x.2))
      | none => acc ++ [x]) = mins k x acc := by
  induction acc with
  | nil => simp [mins]
  | cons y r ih =>
    rw [List.findIdx?_cons]
    by_cases h : k y.1 = k x.1
    · simp [h, teq_refl, mins]
    · have h' : teq (k y.1) (k x.1) = false := by simpa [teq_eq_decide] using h
      simp only [h', mins, h, Bool.false_eq_true, ↓reduceIte]
      cases hr : r.findIdx? (fun g => teq (k g.1) (k x.1)) with
      | none => simp only [hr] at ih; simp [← ih]
      | some i => simp only [hr] at ih; simp [← ih]

theorem sum_mins [Add β] [AddCommMonoid γ] (k : α → Tree) (v : Tree → β → γ)
    (hv : ∀ t a b, v t (a + b) = v t a + v t b) (x : α × β) (acc : List (α × β)) :
    ((mins k x acc).map fun y => v (k y.1) y.2).sum
      = (acc.map fun y => v (k y.1) y.2).sum + v (k x.1) x.2 := by
  induction acc with
  | nil => simp [mins]
  | cons y r ih =>
    by_cases h : k y.1 = k x.1
    · simp only [mins, h, ↓reduceIte, List.map_cons, List.sum_cons, hv]
      abel
    · simp only [mins, h, ↓reduceIte, List.map_cons, List.sum_cons, ih]
      abel

theorem sum_foldl_mins [Add β] [AddCommMonoid γ] (k : α → Tree) (v : Tree → β → γ)
    (hv : ∀ t a b, v t (a + b) = v t a + v t b) (l acc : List (α × β)) :
    ((l.foldl (fun acc x => mins k x acc) acc).map fun y => v (k y.1) y.2).sum
      = (acc.map fun y => v (k y.1) y.2).sum + (l.map fun y => v (k y.1) y.2).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, ih, sum_mins k v hv, List.map_cons, List.sum_cons]
    abel

theorem prod_mins [Add β] [CommMonoid γ] (k : α → Tree) (v : Tree → β → γ)
    (hv : ∀ t a b, v t (a + b) = v t a * v t b) (x : α × β) (acc : List (α × β)) :
    ((mins k x acc).map fun y => v (k y.1) y.2).prod
      = (acc.map fun y => v (k y.1) y.2).prod * v (k x.1) x.2 := by
  induction acc with
  | nil => simp [mins]
  | cons y r ih =>
    by_cases h : k y.1 = k x.1
    · simp only [mins, h, ↓reduceIte, List.map_cons, List.prod_cons, hv]
      rw [← h]; ac_rfl
    · simp only [mins, h, ↓reduceIte, List.map_cons, List.prod_cons, ih]
      ac_rfl

theorem prod_foldl_mins [Add β] [CommMonoid γ] (k : α → Tree) (v : Tree → β → γ)
    (hv : ∀ t a b, v t (a + b) = v t a * v t b) (l acc : List (α × β)) :
    ((l.foldl (fun acc x => mins k x acc) acc).map fun y => v (k y.1) y.2).prod
      = (acc.map fun y => v (k y.1) y.2).prod * (l.map fun y => v (k y.1) y.2).prod := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, ih, prod_mins k v hv, List.map_cons, List.prod_cons]
    ac_rfl

theorem mins_map {β' : Type*} [Add β] [Add β'] (k : α → Tree) (f : β → β')
    (hf : ∀ a b, f (a + b) = f a + f b) (x : α × β) (acc : List (α × β)) :
    mins k (x.1, f x.2) (acc.map fun y => (y.1, f y.2))
      = (mins k x acc).map fun y => (y.1, f y.2) := by
  induction acc with
  | nil => simp [mins]
  | cons y r ih => by_cases h : k y.1 = k x.1 <;> simp [mins, h, ih, hf]

theorem foldl_mins_map {β' : Type*} [Add β] [Add β'] (k : α → Tree) (f : β → β')
    (hf : ∀ a b, f (a + b) = f a + f b) (l acc : List (α × β)) :
    (l.map fun y => (y.1, f y.2)).foldl (fun acc x => mins k x acc)
        (acc.map fun y => (y.1, f y.2))
      = (l.foldl (fun acc x => mins k x acc) acc).map fun y => (y.1, f y.2) := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.foldl_cons, mins_map k f hf, ih]

/-- Insertion by key, the shape of `insertLt` and `insertTerm`. -/
def insBy (k : α → Tree) (a : α) : List α → List α
  | [] => [a]
  | b :: bs => if lt (k a) (k b) then a :: b :: bs else b :: insBy k a bs

theorem insBy_perm (k : α → Tree) (a : α) (l : List α) : (insBy k a l).Perm (a :: l) := by
  induction l with
  | nil => simp [insBy]
  | cons b bs ih =>
    unfold insBy
    split_ifs
    · exact List.Perm.refl _
    · exact ((ih.cons b).trans (List.Perm.swap a b bs))

theorem foldr_insBy_perm (k : α → Tree) (l : List α) : (l.foldr (insBy k) []).Perm l := by
  induction l with
  | nil => simp
  | cons a l ih => exact (insBy_perm k a _).trans (ih.cons a)

end Generic

theorem insertLt_eq (a : Tree) (l : List Tree) : insertLt a l = insBy id a l := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp [insertLt, insBy, ih]

theorem insertTerm_eq (a : List Tree × ℚ) (l : List (List Tree × ℚ)) :
    insertTerm a l = insBy (fun x => mulChain 1 x.1) a l := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp [insertTerm, insBy, ih]

theorem sortLt_eq (l : List Tree) : sortLt l = l.foldr (insBy id) [] := by
  unfold sortLt
  congr 1
  funext a l
  exact insertLt_eq a l

theorem mergeF_eq (fs : List (Tree × ℤ)) :
    mergeF fs = (fs.foldl (fun acc x => mins id x acc) []).filter (·.2 ≠ 0) := by
  unfold mergeF
  dsimp only
  congr 2
  funext acc x
  rcases x with ⟨b, e⟩
  exact step_eq id (b, e) acc

theorem mergeT_eq (ts : List (List Tree × ℚ)) :
    mergeT ts = (ts.foldl (fun acc x => mins (fun fs => mulChain 1 fs) x acc) []).filter
      (·.2 ≠ 0) := by
  unfold mergeT
  dsimp only
  congr 2
  funext acc x
  rcases x with ⟨fs, c⟩
  exact step_eq (fun fs => mulChain 1 fs) (fs, c) acc

/-- `mergeF` on natural exponents. -/
def mergeN (L : List (Tree × ℕ)) : List (Tree × ℕ) :=
  (L.foldl (fun acc x => mins id x acc) []).filter (·.2 ≠ 0)

theorem mergeF_cast (L : List (Tree × ℕ)) :
    mergeF (L.map fun x => (x.1, (x.2 : ℤ))) = (mergeN L).map fun x => (x.1, (x.2 : ℤ)) := by
  rw [mergeF_eq, mergeN]
  have h := foldl_mins_map id (fun n : ℕ => (n : ℤ)) (fun a b => by push_cast; rfl) L []
  simp only [List.map_nil] at h
  rw [h, List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  simp

theorem prod_mergeN {γ : Type*} [CommMonoid γ] (v : Tree → γ) (L : List (Tree × ℕ)) :
    ((mergeN L).map fun x => v x.1 ^ x.2).prod = (L.map fun x => v x.1 ^ x.2).prod := by
  unfold mergeN
  have hf : ∀ l : List (Tree × ℕ), ((l.filter (·.2 ≠ 0)).map fun x => v x.1 ^ x.2).prod
      = (l.map fun x => v x.1 ^ x.2).prod := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.filter_cons]
      split_ifs with h <;> simp_all
  rw [hf]
  have := prod_foldl_mins id (fun t (n : ℕ) => v t ^ n) (fun t a b => pow_add _ _ _) L []
  simpa using this

/-! ## Read-back is correct -/

theorem rd_facNode (b : Tree) (e : ℕ) (he : e ≠ 0) : rd (facNode b e) = rd b ^ e := by
  unfold facNode
  by_cases h1 : e = 1
  · subst h1; simp
  · have h1' : ¬ ((e : ℤ) = 1) := by exact_mod_cast h1
    simp only [h1', ↓reduceIte]
    have : intNode (e : ℤ) = int (e : ℤ) := by simp [intNode]
    rw [arith, this, rd_pow]

/-- The polynomial of `p` with each index `i` read as the tree `al[i]`. -/
noncomputable def ev (al : List Tree) (p : Poly) : MvPolynomial Tree ℚ :=
  (p.map fun x => C x.2 * (x.1.map fun y => rd (al.getD y.1 (int 0)) ^ y.2).prod).sum

theorem rd_mono (al : List Tree) (m : List (ℕ × ℕ)) :
    rd (mulChain 1 (facTrees al m)) = (m.map fun y => rd (al.getD y.1 (int 0)) ^ y.2).prod := by
  rw [rd_mulChain, map_one, one_mul, facTrees, sortLt_eq,
    ((foldr_insBy_perm id _).map rd).prod_eq]
  have hL : (m.map fun (y : ℕ × ℕ) => (al.getD y.1 (int 0), (y.2 : ℤ)))
      = (m.map fun y => (al.getD y.1 (int 0), y.2)).map fun x => (x.1, (x.2 : ℤ)) := by
    simp
  rw [hL, mergeF_cast, List.map_map, List.map_map]
  have hm : ∀ x ∈ mergeN (m.map fun y => (al.getD y.1 (int 0), y.2)), x.2 ≠ 0 := by
    intro x hx
    simpa [mergeN] using (List.mem_filter.1 hx).2
  rw [List.map_congr_left (g := fun x : Tree × ℕ => rd x.1 ^ x.2) ?_]
  · rw [prod_mergeN rd]
    simp [List.map_map, Function.comp_def]
  · intro x hx
    simpa using rd_facNode x.1 x.2 (hm x hx)

end FricasSymbolic.RingMirror
