import FricasSymbolic.RingMirror
import FricasSymbolic.OrderProofs
import FricasSymbolic.Ring
import Mathlib.Algebra.MvPolynomial.Rename
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

theorem rd_foldl_step (g : Tree → List Tree × ℚ → Tree)
    (hg : ∀ acc x, rd (g acc x) = rd acc + C x.2 * rd (mulChain 1 x.1))
    (l : List (List Tree × ℚ)) (a : Tree) :
    rd (l.foldl g a) = rd a + (l.map fun x => C x.2 * rd (mulChain 1 x.1)).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, hg]; simp [add_assoc]

theorem rd_trm (fs : List Tree) (c : ℚ) :
    rd (if |c| = 1 then mulChain 1 fs else mulChain |c| fs) = C |c| * rd (mulChain 1 fs) := by
  split_ifs with h
  · rw [h, map_one, one_mul]
  · rw [rd_mulChain, rd_mulChain, map_one, one_mul]

theorem rd_sgn (c : ℚ) (T : Tree) (P : MvPolynomial Tree ℚ) (hT : rd T = C |c| * P) :
    rd (if 0 < c then T else arith "-" [T]) = C c * P := by
  by_cases h0 : 0 < c
  · simp only [h0, ↓reduceIte, hT, abs_of_pos h0]
  · simp only [h0, ↓reduceIte, arith, rd_neg, hT, abs_of_nonpos (le_of_not_gt h0), map_neg]
    ring

theorem rd_sgn2 (c : ℚ) (acc T : Tree) (P : MvPolynomial Tree ℚ) (hT : rd T = C |c| * P) :
    rd (if 0 < c then arith "+" [acc, T] else arith "-" [acc, T]) = rd acc + C c * P := by
  by_cases h0 : 0 < c
  · simp only [h0, ↓reduceIte, arith, rd_add, hT, abs_of_pos h0]
  · simp only [h0, ↓reduceIte, arith, rd_sub, hT, abs_of_nonpos (le_of_not_gt h0), map_neg]
    ring

theorem rd_const (c0 : ℚ) (acc : Tree) :
    rd (if c0 = 0 then acc else if 0 < c0 then arith "+" [acc, numNode |c0|]
      else arith "-" [acc, numNode |c0|]) = rd acc + C c0 := by
  by_cases hz : c0 = 0
  · simp [hz]
  · by_cases h0 : 0 < c0
    · simp only [hz, h0, ↓reduceIte, arith, rd_add, rd_numNode, abs_of_pos h0]
    · simp only [hz, h0, ↓reduceIte, arith, rd_sub, rd_numNode,
        abs_of_nonpos (le_of_not_gt h0), map_neg]
      ring

theorem sum_mergeT (ts : List (List Tree × ℚ)) :
    ((mergeT ts).map fun x => C x.2 * rd (mulChain 1 x.1)).sum
      = (ts.map fun x => C x.2 * rd (mulChain 1 x.1)).sum := by
  rw [mergeT_eq]
  have hf : ∀ l : List (List Tree × ℚ), ((l.filter (·.2 ≠ 0)).map
      fun x => C x.2 * rd (mulChain 1 x.1)).sum = (l.map fun x => C x.2 * rd (mulChain 1 x.1)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.filter_cons]
      split_ifs with h <;> simp_all
  rw [hf]
  have := sum_foldl_mins (fun fs => mulChain 1 fs) (fun t (c : ℚ) => C c * rd t)
    (fun t a b => by rw [map_add, add_mul]) ts []
  simpa using this

theorem rd_linBuild (c0 : ℚ) (ts : List (List Tree × ℚ)) :
    rd (linBuild c0 ts) = C c0 + (ts.map fun x => C x.2 * rd (mulChain 1 x.1)).sum := by
  have hs : (((mergeT ts).foldr insertTerm []).map fun x => C x.2 * rd (mulChain 1 x.1)).sum
      = (ts.map fun x => C x.2 * rd (mulChain 1 x.1)).sum := by
    have e : (mergeT ts).foldr insertTerm []
        = (mergeT ts).foldr (insBy (fun x => mulChain 1 x.1)) [] := by
      congr 1; funext a l; exact insertTerm_eq a l
    rw [e, ((foldr_insBy_perm _ _).map _).sum_eq, sum_mergeT]
  unfold linBuild
  dsimp only
  rw [← hs]
  generalize (mergeT ts).foldr insertTerm [] = ms
  cases ms with
  | nil => simp [rd_numNode]
  | cons e rest =>
    obtain ⟨fs, c⟩ := e
    dsimp only
    rw [rd_const, rd_foldl_step _ ?_, rd_sgn c _ _ (rd_trm fs c)]
    · simp only [List.map_cons, List.sum_cons]
      abel
    · intro acc x
      obtain ⟨fs', c'⟩ := x
      exact rd_sgn2 c' acc _ _ (rd_trm fs' c')

theorem foldl_add_snd (l : Poly) (a : ℚ) :
    l.foldl (fun s t => s + t.2) a = a + (l.map (·.2)).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih, add_assoc]

theorem sum_split {γ : Type*} [AddCommMonoid γ] (l : Poly) (f : List (ℕ × ℕ) × ℚ → γ) :
    (l.map f).sum = ((l.filter (·.1 = [])).map f).sum + ((l.filter (·.1 ≠ [])).map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    by_cases h : x.1 = [] <;> simp [List.filter_cons, h, ih] <;> abel

/-- **Read-back is correct.** The tree `fromP al p` reads back as the polynomial of `p`,
with each index `i` read as the tree `al[i]`. -/
theorem rd_fromP (al : List Tree) (p : Poly) : rd (fromP al p) = ev al p := by
  unfold fromP ev
  dsimp only
  rw [rd_linBuild, foldl_add_snd, zero_add, map_list_sum, List.map_map, List.map_map]
  conv_rhs => rw [sum_split p]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro x hx
    have : x.1 = [] := by simpa using (List.mem_filter.1 hx).2
    simp [this]
  · congr 1
    apply List.map_congr_left
    intro x _
    simp [rd_mono]

/-! ## Reading the operands: `toF` agrees with `rd` -/

theorem mem_addAtom {l : List Tree} {t x : Tree} : x ∈ addAtom l t ↔ x ∈ l ∨ x = t := by
  unfold addAtom
  split_ifs with h
  · obtain ⟨y, hy, e⟩ := List.any_eq_true.1 h
    rw [teq_iff] at e
    subst e
    constructor
    · exact Or.inl
    · rintro (h | rfl) <;> assumption
  · simp

theorem sub_ratoms (l : List Tree) (t : Tree) (x : Tree) (h : x ∈ l) : x ∈ ratoms l t := by
  fun_induction ratoms l t <;> simp_all [mem_addAtom]

theorem atomIdx_spec {al : List Tree} {t : Tree} (h : t ∈ al) :
    al.getD (atomIdx al t) (int 0) = t := by
  unfold atomIdx
  induction al with
  | nil => simp at h
  | cons y r ih =>
    rw [List.findIdx?_cons]
    by_cases hy : y = t
    · subst hy; simp [teq_refl]
    · have hy' : teq y t = false := by simpa [teq_eq_decide] using hy
      have hr : t ∈ r := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hy
        · exact h
      have := ih hr
      simp only [hy', Bool.false_eq_true, ↓reduceIte]
      cases hf : r.findIdx? (fun x => teq x t) with
      | none =>
        rw [hf] at this
        simp at this
        rw [List.findIdx?_eq_none_iff] at hf
        simpa [teq_refl] using hf t hr
      | some i => rw [hf] at this; simpa using this

theorem ev_pconst (al : List Tree) (q : ℚ) : ev al (pconst q) = C q := by simp [ev, pconst]

theorem ev_pvar (al : List Tree) (i : ℕ) : ev al (pvar i) = rd (al.getD i (int 0)) := by
  simp [ev, pvar]

theorem ev_append (al : List Tree) (p q : Poly) : ev al (p ++ q) = ev al p + ev al q := by
  simp [ev]

theorem ev_cons (al : List Tree) (x : List (ℕ × ℕ) × ℚ) (p : Poly) :
    ev al (x :: p) = C x.2 * (x.1.map fun y => rd (al.getD y.1 (int 0)) ^ y.2).prod
      + ev al p := by
  simp [ev]

theorem ev_pneg (al : List Tree) (p : Poly) : ev al (pneg p) = - ev al p := by
  induction p with
  | nil => simp [pneg, ev]
  | cons x p ih =>
    have : pneg (x :: p) = (x.1, -x.2) :: pneg p := rfl
    rw [this, ev_cons, ev_cons, ih, map_neg]; ring

theorem ev_pscale (al : List Tree) (k : ℚ) (p : Poly) : ev al (pscale k p) = C k * ev al p := by
  induction p with
  | nil => simp [pscale, ev]
  | cons x p ih =>
    have : pscale k (x :: p) = (x.1, k * x.2) :: pscale k p := rfl
    rw [this, ev_cons, ev_cons, ih, map_mul]; ring

theorem ev_pmul (al : List Tree) (p q : Poly) : ev al (pmul p q) = ev al p * ev al q := by
  induction p with
  | nil => simp [pmul, ev]
  | cons x p ih =>
    have : pmul (x :: p) q = (q.map fun y => (x.1 ++ y.1, x.2 * y.2)) ++ pmul p q := by
      simp [pmul]
    rw [this, ev_append, ih, ev_cons, add_mul]
    congr 1
    clear ih this
    induction q with
    | nil => simp [ev]
    | cons y q ihq =>
      rw [List.map_cons, ev_cons, ev_cons, ihq]
      simp only [List.map_append, List.prod_append, map_mul]
      ring

theorem ev_ppow (al : List Tree) (p : Poly) (n : ℕ) : ev al (ppow p n) = ev al p ^ n := by
  induction n with
  | zero => simp [ppow, ev_pconst]
  | succ n ih => rw [ppow, ev_pmul, ih, pow_succ]

/-- The operands read as polynomials over the atom list are their read-backs, when the
atom list holds their atoms. -/
theorem ev_toF (al l : List Tree) (t : Tree) (h : ∀ a ∈ ratoms l t, a ∈ al) :
    ev al (toF al t) = rd t := by
  have atom : ∀ t, t ∈ al → (toF al t = pvar (atomIdx al t)) → ev al (toF al t) = rd t := by
    intro t ht e
    rw [e, ev_pvar, atomIdx_spec ht]
  fun_induction ratoms l t
  case case1 t l hn =>
    have : toF al t = pconst (val t) := by unfold toF; simp [hn]
    rw [this, ev_pconst, rd_num hn]
  case case2 l a b hn iha ihb =>
    rw [toF, ite_false_cond (isNum_node2 (h := "+") (by decide) a b), rd_add, ev_append,
      iha (fun x hx => h x (sub_ratoms _ b x hx)), ihb h]
  case case3 l a hn iha =>
    rw [toF, ite_false_cond (by simpa using hn), rd_neg, ev_pneg, iha h]
  case case4 l a b hn iha ihb =>
    rw [toF, ite_false_cond (isNum_node2 (h := "-") (by decide) a b), rd_sub, ev_append,
      ev_pneg, iha (fun x hx => h x (sub_ratoms _ b x hx)), ihb h, sub_eq_add_neg]
  case case5 l a b hn iha ihb =>
    rw [toF, ite_false_cond (isNum_node2 (h := "*") (by decide) a b), rd_mul, ev_pmul,
      iha (fun x hx => h x (sub_ratoms _ b x hx)), ihb h]
  case case6 l a b hb hn iha ihb =>
    have e1 : toF al (node (sym "/") [a, b]) = pscale (val b)⁻¹ (toF al a) := by
      rw [toF, ite_false_cond (by simpa using hn)]; simp [hb]
    have e2 : rd (node (sym "/") [a, b]) = C (val b)⁻¹ * rd a := by
      rw [rd, ite_false_cond (by simpa using hn)]; simp [hb]
    rw [e1, e2, ev_pscale, iha (fun x hx => h x (sub_ratoms _ b x hx))]
  case case7 l a b hb hn =>
    apply atom _ (h _ (by simp [mem_addAtom]))
    rw [toF, ite_false_cond (by simpa using hn)]; simp [hb]
  case case8 l b e n hr hn ihb =>
    have e1 : toF al (node (sym "^") [b, e]) = ppow (toF al b) n := by
      rw [toF, ite_false_cond (by simpa using hn)]; simp [hr]
    have e2 : rd (node (sym "^") [b, e]) = rd b ^ n := by
      rw [rd, ite_false_cond (by simpa using hn)]; simp [hr]
    rw [e1, e2, ev_ppow, ihb h]
  case case9 l b e hr hn =>
    apply atom _ (h _ (by simp [mem_addAtom]))
    rw [toF, ite_false_cond (by simpa using hn)]; simp [hr]
  case case10 t l hn h1 h2 h3 h4 h5 h6 =>
    apply atom _ (h _ (by simp [mem_addAtom]))
    rw [toF]
    all_goals first | assumption | simp [hn]

/-! ## The constructors compute in the polynomial ring over the atoms -/

theorem rd_ring1 (x : Tree) (f : Poly → Poly) (F : MvPolynomial Tree ℚ → MvPolynomial Tree ℚ)
    (hf : ∀ al p, ev al (f p) = F (ev al p)) : rd (ring1 x f) = F (rd x) := by
  unfold ring1
  rw [rd_fromP, hf, ev_toF _ [] x (fun a ha => ha)]

theorem rd_ring2 (x y : Tree) (f : Poly → Poly → Poly)
    (F : MvPolynomial Tree ℚ → MvPolynomial Tree ℚ → MvPolynomial Tree ℚ)
    (hf : ∀ al p q, ev al (f p q) = F (ev al p) (ev al q)) :
    rd (ring2 x y f) = F (rd x) (rd y) := by
  unfold ring2
  rw [rd_fromP, hf, ev_toF _ [] x (fun a ha => sub_ratoms _ y a ha),
    ev_toF _ (ratoms [] x) y (fun a ha => ha)]

theorem rd_lit {t : Tree} {q : ℚ} (h : lit t q = true) : rd t = C q := by
  simp only [lit, Bool.and_eq_true, beq_iff_eq] at h
  rw [rd_num h.1, h.2]

theorem rd_rAdd (x y : Tree) : rd (rAdd x y) = rd x + rd y := by
  unfold rAdd
  split_ifs with h
  · simp only [Bool.and_eq_true] at h
    rw [rd_numNode, rd_num h.1, rd_num h.2, map_add]
  · exact rd_ring2 x y _ (· + ·) (fun al p q => ev_append al p q)

theorem rd_rSub (x y : Tree) : rd (rSub x y) = rd x - rd y := by
  unfold rSub
  split_ifs with h
  · simp only [Bool.and_eq_true] at h
    rw [rd_numNode, rd_num h.1, rd_num h.2, map_sub]
  · exact rd_ring2 x y _ (· - ·) (fun al p q => by rw [ev_append, ev_pneg, sub_eq_add_neg])

theorem rd_rNeg (x : Tree) : rd (rNeg x) = - rd x := by
  unfold rNeg
  split_ifs with h
  · rw [rd_numNode, rd_num h, map_neg]
  · exact rd_ring1 x _ (- ·) (fun al p => ev_pneg al p)

theorem rd_rMul (A : RAx) (x y : Tree) : rd (rMul A x y) = rd x * rd y := by
  unfold rMul
  split_ifs with h1 h2 h3 h4
  · simp only [Bool.and_eq_true] at h1
    rw [rd_numNode, rd_num h1.1, rd_num h1.2, map_mul]
  · simp only [Bool.and_eq_true, Bool.or_eq_true] at h2
    rcases h2.2 with h | h <;> simp [rd_numNode, rd_lit h]
  · rw [rd_lit h3, map_one, one_mul]
  · rw [rd_lit h4, map_one, mul_one]
  · exact rd_ring2 x y _ (· * ·) (fun al p q => ev_pmul al p q)

theorem rd_rDiv (A : RAx) (x y : Tree) (hy : isNum y = true) :
    rd (rDiv A x y) = C (val y)⁻¹ * rd x := by
  unfold rDiv
  split_ifs with h1
  · simp only [Bool.and_eq_true] at h1
    rw [rd_numNode, rd_num h1.1, div_eq_inv_mul, map_mul]
  · exact rd_ring2 x y _ (fun p _ => C (val y)⁻¹ * p) (fun al p q => ev_pscale al _ p)

theorem rd_rPow (x : Tree) (n : ℕ) : rd (rPow x n) = rd x ^ n := by
  unfold rPow
  split_ifs with h1 h2 h3 h4
  · rw [rd_numNode, rd_num h1, zpow_natCast, map_pow]
  · have : n = 1 := by exact_mod_cast h2
    rw [this, pow_one]
  · have : n = 0 := by exact_mod_cast h3
    rw [this, rd_numNode, pow_zero, map_one]
  · exact rd_ring1 x _ (· ^ n) (fun al p => by simpa using ev_ppow al p n)
  · exact absurd (Int.natCast_nonneg n) h4

/-! ## Read-back is canonical -/

/-! ### Merging: keys, origins and sums -/

section MergeFacts
variable {α β : Type*}

/-- The sum of the values with key `t`. -/
def S [AddCommMonoid β] (k : α → Tree) (l : List (α × β)) (t : Tree) : β :=
  ((l.filter fun y => k y.1 = t).map (·.2)).sum

theorem S_nil [AddCommMonoid β] (k : α → Tree) (t : Tree) : S k ([] : List (α × β)) t = 0 := by
  simp [S]

theorem S_cons [AddCommMonoid β] (k : α → Tree) (y : α × β) (l : List (α × β)) (t : Tree) :
    S k (y :: l) t = (if k y.1 = t then y.2 else 0) + S k l t := by
  unfold S
  by_cases h : k y.1 = t <;> simp [List.filter_cons, h]

theorem S_append [AddCommMonoid β] (k : α → Tree) (l l' : List (α × β)) (t : Tree) :
    S k (l ++ l') t = S k l t + S k l' t := by
  simp [S, List.filter_append]

theorem S_mins [AddCommMonoid β] (k : α → Tree) (x : α × β) (acc : List (α × β)) (t : Tree) :
    S k (mins k x acc) t = S k acc t + if k x.1 = t then x.2 else 0 := by
  induction acc with
  | nil => simp [mins, S_cons, S_nil]
  | cons y r ih =>
    by_cases h : k y.1 = k x.1
    · simp only [mins, h, ↓reduceIte, S_cons]
      split_ifs <;> simp_all [add_assoc, add_comm]
    · simp only [mins, h, ↓reduceIte, S_cons, ih, add_assoc]

theorem S_foldl [AddCommMonoid β] (k : α → Tree) (l acc : List (α × β)) (t : Tree) :
    S k (l.foldl (fun acc x => mins k x acc) acc) t = S k acc t + S k l t := by
  induction l generalizing acc with
  | nil => simp [S_nil]
  | cons x l ih => rw [List.foldl_cons, ih, S_mins, S_cons]; abel

theorem mem_mins [Add β] (k : α → Tree) (x : α × β) (acc : List (α × β)) (y : α × β)
    (hy : y ∈ mins k x acc) : y.1 = x.1 ∨ ∃ z ∈ acc, z.1 = y.1 := by
  induction acc with
  | nil => simp [mins] at hy; simp [hy]
  | cons w r ih =>
    unfold mins at hy
    split_ifs at hy with h
    · rcases List.mem_cons.1 hy with e | e
      · exact Or.inr ⟨w, by simp, by simp [e]⟩
      · exact Or.inr ⟨y, by simp [e], rfl⟩
    · rcases List.mem_cons.1 hy with e | e
      · exact Or.inr ⟨w, by simp, by simp [e]⟩
      · rcases ih e with h1 | ⟨z, hz, h2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨z, by simp [hz], h2⟩

theorem cover_mins [Add β] (k : α → Tree) (x : α × β) (acc : List (α × β)) (z : α × β)
    (hz : z ∈ x :: acc) : ∃ y ∈ mins k x acc, k y.1 = k z.1 := by
  induction acc with
  | nil => simp at hz; subst hz; exact ⟨z, by simp [mins], rfl⟩
  | cons w r ih =>
    unfold mins
    split_ifs with h
    · rcases List.mem_cons.1 hz with e | e
      · subst e; exact ⟨(w.1, w.2 + z.2), by simp, h⟩
      · rcases List.mem_cons.1 e with e | e
        · subst e; exact ⟨(z.1, z.2 + x.2), by simp, rfl⟩
        · exact ⟨z, by simp [e], rfl⟩
    · rcases List.mem_cons.1 hz with e | e
      · obtain ⟨y, hy, h'⟩ := ih (by simp [e])
        exact ⟨y, by simp [hy], h'⟩
      · rcases List.mem_cons.1 e with e | e
        · subst e; exact ⟨z, by simp, rfl⟩
        · obtain ⟨y, hy, h'⟩ := ih (by simp [e])
          exact ⟨y, by simp [hy], h'⟩

theorem nodup_mins [Add β] (k : α → Tree) (x : α × β) (acc : List (α × β))
    (hn : (acc.map fun y => k y.1).Nodup) : ((mins k x acc).map fun y => k y.1).Nodup := by
  induction acc with
  | nil => simp [mins]
  | cons w r ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn
    unfold mins
    split_ifs with h
    · simpa using hn
    · simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
      refine ⟨fun y hy e => ?_, ih hn.2⟩
      rcases mem_mins k x r y hy with h1 | ⟨z, hz, h2⟩
      · exact h (by rw [← e, h1])
      · exact hn.1 z hz (by rw [h2, e])

theorem nodup_foldl [Add β] (k : α → Tree) (l acc : List (α × β))
    (hn : (acc.map fun y => k y.1).Nodup) :
    ((l.foldl (fun acc x => mins k x acc) acc).map fun y => k y.1).Nodup := by
  induction l generalizing acc with
  | nil => simpa using hn
  | cons x l ih => exact ih _ (nodup_mins k x acc hn)

theorem origin_foldl [Add β] (k : α → Tree) (l acc : List (α × β)) (y : α × β)
    (hy : y ∈ l.foldl (fun acc x => mins k x acc) acc) :
    ∃ z ∈ acc ++ l, z.1 = y.1 := by
  induction l generalizing acc with
  | nil => exact ⟨y, by simpa using hy, rfl⟩
  | cons x l ih =>
    obtain ⟨z, hz, e⟩ := ih _ hy
    rcases List.mem_append.1 hz with hz | hz
    · rcases mem_mins k x acc z hz with h1 | ⟨w, hw, h2⟩
      · exact ⟨x, by simp, h1 ▸ e⟩
      · exact ⟨w, by simp [hw], h2.trans e⟩
    · exact ⟨z, by simp [hz], e⟩

theorem cover_foldl [Add β] (k : α → Tree) (l acc : List (α × β)) (z : α × β)
    (hz : z ∈ acc ++ l) : ∃ y ∈ l.foldl (fun acc x => mins k x acc) acc, k y.1 = k z.1 := by
  induction l generalizing acc z with
  | nil => exact ⟨z, by simpa using hz, rfl⟩
  | cons x l ih =>
    rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨w, hw, e⟩ := cover_mins k x acc z (by simp [hz])
      obtain ⟨y, hy, e'⟩ := ih (mins k x acc) w (by simp [hw])
      exact ⟨y, hy, e'.trans e⟩
    · rcases List.mem_cons.1 hz with e | e
      · subst e
        obtain ⟨w, hw, e⟩ := cover_mins k z acc z (by simp)
        obtain ⟨y, hy, e'⟩ := ih (mins k z acc) w (by simp [hw])
        exact ⟨y, hy, e'.trans e⟩
      · exact ih (mins k x acc) z (by simp [e])

theorem S_of_mem [AddCommMonoid β] (k : α → Tree) (r : List (α × β))
    (hn : (r.map fun y => k y.1).Nodup) (y : α × β) (hy : y ∈ r) : S k r (k y.1) = y.2 := by
  induction r with
  | nil => simp at hy
  | cons w r ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn
    rw [S_cons]
    rcases List.mem_cons.1 hy with e | e
    · subst e
      have : S k r (k y.1) = 0 := by
        unfold S
        rw [List.filter_eq_nil_iff.2 (fun z hz => by simpa using hn.1 z hz)]
        simp
      simp [this]
    · have h : k w.1 ≠ k y.1 := fun h => hn.1 y e h.symm
      simp [h, ih hn.2 e]

/-- The merge of `l`: one entry per key, holding the sum of the values with that key. -/
def R [Add β] (k : α → Tree) (l : List (α × β)) : List (α × β) :=
  l.foldl (fun acc x => mins k x acc) []

theorem R_val [AddCommMonoid β] (k : α → Tree) (l : List (α × β)) (y : α × β)
    (hy : y ∈ R k l) : y.2 = S k l (k y.1) := by
  have h1 := S_of_mem k (R k l) (nodup_foldl k l [] (by simp)) y hy
  rw [R, S_foldl, S_nil, zero_add] at h1
  exact h1.symm

end MergeFacts

/-! ### Sorting: the sorted list is determined -/

theorem lt_asymm {a b : Tree} (h : lt a b = true) : lt b a = false := by
  by_contra h'
  have := O1_trans h (Bool.not_eq_false _ ▸ h')
  simp [O1_irrefl] at this

section SortFacts
variable {α : Type*}

theorem insBy_sorted (k : α → Tree) (a : α) (l : List α)
    (hl : l.Pairwise fun x y => lt (k y) (k x) = false) :
    (insBy k a l).Pairwise fun x y => lt (k y) (k x) = false := by
  induction l with
  | nil => simp [insBy]
  | cons b bs ih =>
    rw [List.pairwise_cons] at hl
    unfold insBy
    split_ifs with h
    · refine List.Pairwise.cons ?_ (List.Pairwise.cons hl.1 hl.2)
      intro c hc
      rcases List.mem_cons.1 hc with e | e
      · subst e; exact lt_asymm h
      · by_contra h'
        have := O1_trans (Bool.not_eq_false _ ▸ h') h
        rw [hl.1 c e] at this; contradiction
    · refine List.Pairwise.cons ?_ (ih hl.2)
      intro c hc
      rcases List.mem_cons.1 ((insBy_perm k a bs).subset hc) with e | e
      · subst e; simpa using h
      · exact hl.1 c e

theorem foldr_insBy_sorted (k : α → Tree) (l : List α) :
    (l.foldr (insBy k) []).Pairwise fun x y => lt (k y) (k x) = false := by
  induction l with
  | nil => simp
  | cons a l ih => exact insBy_sorted k a _ ih

/-- Two lists sorted strictly by key with the same elements are equal. -/
theorem eq_of_strict (k : α → Tree) : ∀ {l l' : List α},
    l.Pairwise (fun a b => lt (k a) (k b) = true) →
    l'.Pairwise (fun a b => lt (k a) (k b) = true) → (∀ x, x ∈ l ↔ x ∈ l') → l = l'
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => by simpa using (h b).2 (by simp)
  | a :: _, [], _, _, h => by simpa using (h a).1 (by simp)
  | a :: as, b :: bs, hl, hl', h => by
    rw [List.pairwise_cons] at hl hl'
    have hab : a = b := by
      by_contra hne
      have ha : a ∈ bs := by
        rcases List.mem_cons.1 ((h a).1 (by simp)) with e | e
        · exact absurd e hne
        · exact e
      have hb : b ∈ as := by
        rcases List.mem_cons.1 ((h b).2 (by simp)) with e | e
        · exact absurd e.symm hne
        · exact e
      have := O1_trans (hl.1 b hb) (hl'.1 a ha)
      simp [O1_irrefl] at this
    subst hab
    rw [eq_of_strict k hl.2 hl'.2 (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)]
    · rcases List.mem_cons.1 ((h x).1 (by simp [hx])) with e | e
      · subst e; have := hl.1 _ hx; simp [O1_irrefl] at this
      · exact e
    · rcases List.mem_cons.1 ((h x).2 (by simp [hx])) with e | e
      · subst e; have := hl'.1 _ hx; simp [O1_irrefl] at this
      · exact e

/-- Two sorted permutations of each other are equal (keys the trees themselves). -/
theorem eq_of_perm_sorted : ∀ {l l' : List Tree}, l.Perm l' →
    l.Pairwise (fun x y => lt y x = false) → l'.Pairwise (fun x y => lt y x = false) → l = l'
  | [], [], _, _, _ => rfl
  | [], b :: _, h, _, _ => by simpa using h.length_eq
  | a :: _, [], h, _, _ => by simpa using h.length_eq
  | a :: as, b :: bs, h, hl, hl' => by
    rw [List.pairwise_cons] at hl hl'
    have hab : a = b := by
      by_contra hne
      have ha : a ∈ bs := by
        rcases List.mem_cons.1 (h.subset (by simp : a ∈ a :: as)) with e | e
        · exact absurd e hne
        · exact e
      have hb : b ∈ as := by
        rcases List.mem_cons.1 (h.symm.subset (by simp : b ∈ b :: bs)) with e | e
        · exact absurd e.symm hne
        · exact e
      rcases O2_total hne with h1 | h1
      · rw [hl'.1 a ha] at h1; contradiction
      · rw [hl.1 b hb] at h1; contradiction
    subst hab
    rw [eq_of_perm_sorted (h.cons_inv) hl.2 hl'.2]

end SortFacts

/-! ### Monomials: the factor list depends only on the exponent vector -/

/-- The sorted factor trees of a list of (base, exponent), as `facTrees` builds them. -/
def facs (L : List (Tree × ℕ)) : List Tree :=
  sortLt ((mergeN L).map fun x => facNode x.1 x.2)

/-- The (base, exponent) pairs of a monomial over `al`. -/
def Lof (al : List Tree) (m : List (ℕ × ℕ)) : List (Tree × ℕ) :=
  m.map fun y => (al.getD y.1 (int 0), y.2)

theorem facTrees_eq (al : List Tree) (m : List (ℕ × ℕ)) : facTrees al m = facs (Lof al m) := by
  unfold facTrees facs Lof
  have hL : (m.map fun (y : ℕ × ℕ) => (al.getD y.1 (int 0), (y.2 : ℤ)))
      = (m.map fun y => (al.getD y.1 (int 0), y.2)).map fun x => (x.1, (x.2 : ℤ)) := by
    simp
  rw [hL, mergeF_cast, List.map_map]
  rfl

/-- The exponent vector of a list of (base, exponent). -/
noncomputable def N (L : List (Tree × ℕ)) : Tree →₀ ℕ :=
  (L.map fun x => Finsupp.single x.1 x.2).sum

theorem N_apply (L : List (Tree × ℕ)) (b : Tree) : N L b = S id L b := by
  induction L with
  | nil => simp [N, S_nil]
  | cons x L ih =>
    rw [S_cons]
    simp only [N, List.map_cons, List.sum_cons, Finsupp.add_apply] at ih ⊢
    rw [ih, Finsupp.single_apply]
    rfl

theorem prod_X (L : List (Tree × ℕ)) :
    (L.map fun x => (X x.1 : MvPolynomial Tree ℚ) ^ x.2).prod = monomial (N L) 1 := by
  induction L with
  | nil => simp [N]
  | cons x L ih =>
    rw [List.map_cons, List.prod_cons, ih, X_pow_eq_monomial, monomial_mul_monomial, one_mul]
    simp [N]

theorem mem_mergeN (L : List (Tree × ℕ)) (x : Tree × ℕ) :
    x ∈ mergeN L ↔ x.2 = N L x.1 ∧ x.2 ≠ 0 := by
  rw [N_apply]
  unfold mergeN
  rw [List.mem_filter]
  constructor
  · rintro ⟨hx, h0⟩
    exact ⟨R_val id L x hx, by simpa using h0⟩
  · rintro ⟨hv, h0⟩
    have : ∃ z ∈ L, z.1 = x.1 := by
      by_contra hne
      simp only [not_exists, not_and] at hne
      apply h0
      rw [hv]
      unfold S
      rw [List.filter_eq_nil_iff.2 (fun z hz => by simpa using hne z hz)]
      simp
    obtain ⟨z, hz, e⟩ := this
    obtain ⟨y, hy, e'⟩ := cover_foldl id L [] z (by simpa using hz)
    have hy2 := R_val id L y hy
    have e1 : y.1 = x.1 := by simpa [e] using e'
    have : y = x := Prod.ext e1 (by rw [hy2, hv]; simp [e1])
    subst this
    exact ⟨hy, by simpa using h0⟩

theorem nodup_mergeN (L : List (Tree × ℕ)) : (mergeN L).Nodup := by
  have h := nodup_foldl id L [] (by simp)
  apply List.Nodup.of_map Prod.fst
  exact h.sublist (List.Sublist.map _ List.filter_sublist)

theorem facs_congr {L L' : List (Tree × ℕ)} (h : N L = N L') : facs L = facs L' := by
  have hp : (mergeN L).Perm (mergeN L') :=
    (List.perm_ext_iff_of_nodup (nodup_mergeN L) (nodup_mergeN L')).2
      (fun x => by rw [mem_mergeN, mem_mergeN, h])
  unfold facs
  rw [sortLt_eq, sortLt_eq]
  apply eq_of_perm_sorted
  · exact (foldr_insBy_perm id _).trans ((hp.map _).trans (foldr_insBy_perm id _).symm)
  · exact foldr_insBy_sorted id _
  · exact foldr_insBy_sorted id _

theorem rd_facs (L : List (Tree × ℕ)) :
    rd (mulChain 1 (facs L)) = (L.map fun x => rd x.1 ^ x.2).prod := by
  rw [rd_mulChain, map_one, one_mul, facs, sortLt_eq,
    ((foldr_insBy_perm id _).map rd).prod_eq, List.map_map]
  rw [List.map_congr_left (g := fun x : Tree × ℕ => rd x.1 ^ x.2) ?_]
  · exact prod_mergeN rd L
  · intro x hx
    simpa using rd_facNode x.1 x.2 ((mem_mergeN L x).1 hx).2

/-- An atom of the rung: it reads back as itself, and `ratoms` collects it as itself. -/
def IsAtom (t : Tree) : Prop := rd t = X t ∧ ∀ l, ratoms l t = addAtom l t

theorem rd_facs_atoms {L : List (Tree × ℕ)} (hL : ∀ x ∈ L, IsAtom x.1) :
    rd (mulChain 1 (facs L)) = monomial (N L) 1 := by
  rw [rd_facs, ← prod_X]
  congr 1
  apply List.map_congr_left
  intro x hx
  rw [(hL x hx).1]

/-- Over atoms of the rung, the key of a monomial (`mulChain 1` of its factors) determines its
exponent vector. -/
theorem N_of_key {L L' : List (Tree × ℕ)} (hL : ∀ x ∈ L, IsAtom x.1)
    (hL' : ∀ x ∈ L', IsAtom x.1) (h : mulChain 1 (facs L) = mulChain 1 (facs L')) :
    N L = N L' := by
  have := congrArg rd h
  rw [rd_facs_atoms hL, rd_facs_atoms hL'] at this
  exact monomial_left_injective one_ne_zero this

/-! ### Polynomials: the tree depends only on the polynomial -/

/-- `p` is well formed over `al`: the trees of `al` are atoms of the rung, the indices of `p`
are in range, and its exponents are positive (as `toF` produces them). -/
def WF (al : List Tree) (p : Poly) : Prop :=
  (∀ a ∈ al, IsAtom a) ∧ ∀ x ∈ p, ∀ y ∈ x.1, y.1 < al.length ∧ y.2 ≠ 0

theorem atoms_Lof {al : List Tree} {p : Poly} (hw : WF al p) {x : List (ℕ × ℕ) × ℚ}
    (hx : x ∈ p) : ∀ z ∈ Lof al x.1, IsAtom z.1 := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
  have hi := (hw.2 x hx y hy).1
  apply hw.1
  rw [← List.getElem_eq_getD (int 0)]
  exact List.getElem_mem hi

theorem N_Lof_ne_zero {al : List Tree} {p : Poly} (hw : WF al p) {x : List (ℕ × ℕ) × ℚ}
    (hx : x ∈ p) (hne : x.1 ≠ []) : N (Lof al x.1) ≠ 0 := by
  obtain ⟨y, m, hm⟩ := List.exists_cons_of_ne_nil hne
  have he := (hw.2 x hx y (by simp [hm])).2
  intro h0
  have := congrArg (· (al.getD y.1 (int 0))) h0
  simp only [N_apply, Lof, hm, List.map_cons, S_cons, id, ↓reduceIte, Finsupp.coe_zero,
    Pi.zero_apply] at this
  omega

theorem coeff_sum_monomial (q : Poly) (f : List (ℕ × ℕ) × ℚ → (Tree →₀ ℕ)) (n : Tree →₀ ℕ) :
    ((q.map fun x => monomial (f x) x.2).sum).coeff n
      = ((q.filter fun x => f x = n).map (·.2)).sum := by
  induction q with
  | nil => simp
  | cons x q ih =>
    rw [List.map_cons, List.sum_cons]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply]
    rw [ih, coeff_monomial]
    by_cases h : f x = n <;> simp [h]

theorem ev_eq {al : List Tree} {p : Poly} (hw : WF al p) :
    ev al p = (p.map fun x => monomial (N (Lof al x.1)) x.2).sum := by
  unfold ev
  congr 1
  apply List.map_congr_left
  intro x hx
  have : (x.1.map fun y => rd (al.getD y.1 (int 0)) ^ y.2)
      = (Lof al x.1).map fun z => (X z.1 : MvPolynomial Tree ℚ) ^ z.2 := by
    unfold Lof
    rw [List.map_map]
    apply List.map_congr_left
    intro y hy
    have h1 : rd (al.getD y.1 (int 0)) = X (al.getD y.1 (int 0)) :=
      ((atoms_Lof hw hx) (al.getD y.1 (int 0), y.2) (List.mem_map.2 ⟨y, hy, rfl⟩)).1
    rw [h1]
    rfl
  rw [this, prod_X, C_mul_monomial, mul_one]

theorem coeff_ev {al : List Tree} {p : Poly} (hw : WF al p) (n : Tree →₀ ℕ) :
    (ev al p).coeff n = ((p.filter fun x => N (Lof al x.1) = n).map (·.2)).sum := by
  rw [ev_eq hw, coeff_sum_monomial]

/-- The non-constant terms of `p`, with their factor trees, as `fromP` lists them. -/
def tsOf (al : List Tree) (p : Poly) : List (List Tree × ℚ) :=
  (p.filter (·.1 ≠ [])).map fun x => (facTrees al x.1, x.2)

theorem S_tsOf {al : List Tree} {p : Poly} (hw : WF al p) {L : List (Tree × ℕ)}
    (hL : ∀ z ∈ L, IsAtom z.1) (hN : N L ≠ 0) :
    S (fun fs => mulChain 1 fs) (tsOf al p) (mulChain 1 (facs L)) = (ev al p).coeff (N L) := by
  rw [coeff_ev hw]
  unfold S tsOf
  rw [List.filter_map, List.map_map, List.filter_filter,
    List.filter_congr (q := fun x => decide (N (Lof al x.1) = N L)) ?_]
  · rfl
  intro x hx
  rw [Bool.eq_iff_iff]
  simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq, ne_eq]
  rw [facTrees_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact N_of_key (atoms_Lof hw hx) hL h1
  · intro h
    refine ⟨by rw [facs_congr h], fun h0 => hN ?_⟩
    rw [← h, h0]
    simp [Lof, N]

/-- The sorted, merged terms of `p`, as `linBuild` computes them. -/
def msOf (al : List Tree) (p : Poly) : List (List Tree × ℚ) :=
  (mergeT (tsOf al p)).foldr insertTerm []

theorem msOf_perm (al : List Tree) (p : Poly) : (msOf al p).Perm (mergeT (tsOf al p)) := by
  have e : (mergeT (tsOf al p)).foldr insertTerm []
      = (mergeT (tsOf al p)).foldr (insBy (fun x => mulChain 1 x.1)) [] := by
    congr 1; funext a l; exact insertTerm_eq a l
  unfold msOf
  rw [e]
  exact foldr_insBy_perm _ _

theorem mergeT_R (ts : List (List Tree × ℚ)) :
    mergeT ts = (R (fun fs => mulChain 1 fs) ts).filter (·.2 ≠ 0) := mergeT_eq ts

theorem mem_msOf {al : List Tree} {p : Poly} (hw : WF al p) (fs : List Tree) (c : ℚ) :
    (fs, c) ∈ msOf al p ↔ c ≠ 0 ∧ ∃ L : List (Tree × ℕ), (∀ z ∈ L, IsAtom z.1) ∧ N L ≠ 0 ∧
      fs = facs L ∧ c = (ev al p).coeff (N L) := by
  rw [(msOf_perm al p).mem_iff, mergeT_R, List.mem_filter]
  simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  have from_ts : ∀ z ∈ tsOf al p, ∃ x ∈ p, x.1 ≠ [] ∧ z = (facs (Lof al x.1), x.2) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    rw [List.mem_filter] at hx
    exact ⟨x, hx.1, by simpa using hx.2, by rw [facTrees_eq]⟩
  constructor
  · rintro ⟨hm, hc⟩
    obtain ⟨z, hz, e⟩ := origin_foldl _ _ [] _ hm
    obtain ⟨x, hx, hne, rfl⟩ := from_ts z (by simpa using hz)
    simp only at e
    refine ⟨hc, Lof al x.1, atoms_Lof hw hx, N_Lof_ne_zero hw hx hne, e.symm, ?_⟩
    have hv := R_val _ _ _ hm
    simp only at hv
    rw [hv, ← e, S_tsOf hw (atoms_Lof hw hx) (N_Lof_ne_zero hw hx hne)]
  · rintro ⟨hc, L, hL, hN, rfl, hcv⟩
    have hf : (p.filter fun x => N (Lof al x.1) = N L) ≠ [] := by
      intro h0
      rw [coeff_ev hw, h0] at hcv
      simp at hcv
      exact hc hcv
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hf
    rw [List.mem_filter, decide_eq_true_eq] at hx
    have hne : x.1 ≠ [] := fun h0 => hN (by rw [← hx.2, h0]; simp [Lof, N])
    have hz : (facs (Lof al x.1), x.2) ∈ tsOf al p := by
      unfold tsOf
      exact List.mem_map.2 ⟨x, List.mem_filter.2 ⟨hx.1, by simpa using hne⟩,
        by rw [facTrees_eq]⟩
    obtain ⟨y, hy, ek⟩ := cover_foldl (fun fs => mulChain 1 fs) _ [] _ (by simpa using hz)
    obtain ⟨w, hw', ew⟩ := origin_foldl _ _ [] _ hy
    obtain ⟨x', hx', hne', rfl⟩ := from_ts w (by simpa using hw')
    simp only at ew ek
    rw [← ew] at ek
    have hN' : N (Lof al x'.1) = N L :=
      (N_of_key (atoms_Lof hw hx') (atoms_Lof hw hx.1) ek).trans hx.2
    have hy1 : y.1 = facs L := by rw [← ew, facs_congr hN']
    have hy2 : y.2 = c := by
      rw [R_val _ _ _ hy, hy1, hcv]
      exact S_tsOf hw hL hN
    have : y = (facs L, c) := Prod.ext hy1 hy2
    subst this
    exact ⟨hy, hc⟩

theorem msOf_sorted (al : List Tree) (p : Poly) :
    (msOf al p).Pairwise fun a b => lt (mulChain 1 a.1) (mulChain 1 b.1) = true := by
  have h1 : (msOf al p).Pairwise fun a b => lt (mulChain 1 b.1) (mulChain 1 a.1) = false := by
    have e : msOf al p = (mergeT (tsOf al p)).foldr (insBy (fun x => mulChain 1 x.1)) [] := by
      unfold msOf; congr 1; funext a l; exact insertTerm_eq a l
    rw [e]
    exact foldr_insBy_sorted _ _
  have h2 : ((msOf al p).map fun a => mulChain 1 a.1).Nodup := by
    apply ((msOf_perm al p).map _).nodup_iff.2
    rw [mergeT_R]
    exact (nodup_foldl (fun fs => mulChain 1 fs) _ [] (by simp)).sublist
      (List.Sublist.map _ List.filter_sublist)
  rw [List.Nodup, List.pairwise_map] at h2
  refine (h1.and h2).imp fun {a b} ⟨hab, hne⟩ => ?_
  rcases O2_total hne with h | h
  · exact h
  · rw [hab] at h; contradiction

theorem c0_eq {al : List Tree} {p : Poly} (hw : WF al p) :
    (p.filter (·.1 = [])).foldl (fun s t => s + t.2) 0 = (ev al p).coeff 0 := by
  rw [foldl_add_snd, zero_add, coeff_ev hw]
  suffices hf : p.filter (·.1 = []) = p.filter fun x => N (Lof al x.1) = 0 by rw [hf]
  apply List.filter_congr
  intro x hx
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · intro h; simp [h, Lof, N]
  · intro h; by_contra hne; exact N_Lof_ne_zero hw hx hne h

/-- **Read-back is canonical.** Over atoms of the rung, the tree `fromP al p` depends only on
the polynomial `p` denotes. -/
theorem fromP_canonical {al al' : List Tree} {p p' : Poly} (hw : WF al p) (hw' : WF al' p')
    (h : ev al p = ev al' p') : fromP al p = fromP al' p' := by
  have hms : msOf al p = msOf al' p' := by
    apply eq_of_strict (fun x => mulChain 1 x.1) (msOf_sorted al p) (msOf_sorted al' p')
    rintro ⟨fs, c⟩
    rw [mem_msOf hw, mem_msOf hw', h]
  unfold fromP linBuild
  dsimp only
  rw [c0_eq hw, c0_eq hw', h]
  unfold msOf tsOf at hms
  rw [hms]

/-! ## Normal forms of the mirror: closed under the constructors, decided by `rd` -/

/-- A normal form: a read-back over atoms of the rung of a well-formed polynomial. -/
def NF (t : Tree) : Prop := ∃ al p, WF al p ∧ t = fromP al p

/-- Two normal forms with the same polynomial are the same tree. -/
theorem NF_canonical {t t' : Tree} (ht : NF t) (ht' : NF t') (h : rd t = rd t') : t = t' := by
  obtain ⟨al, p, hw, rfl⟩ := ht
  obtain ⟨al', p', hw', rfl⟩ := ht'
  rw [rd_fromP, rd_fromP] at h
  exact fromP_canonical hw hw' h

theorem NF_numNode (q : ℚ) : NF (numNode q) :=
  ⟨[], [([], q)], ⟨by simp, by simp⟩, by simp [fromP, linBuild, mergeT]⟩

theorem NF_atom {b : Tree} (hb : IsAtom b) : NF b :=
  ⟨[b], [([(0, 1)], 1)], ⟨by simpa using hb, by simp⟩, by
    simp [fromP, linBuild, mergeT, facTrees, mergeF, mulChain, facNode, sortLt, insertLt,
      insertTerm]⟩

/-! ### The atoms of a normal form -/

/-- Every atom `ratoms` collects from `t` is an atom of the rung. -/
def AtomsOK (t : Tree) : Prop := ∀ l a, a ∈ ratoms l t → a ∈ l ∨ IsAtom a

theorem AtomsOK_num {t : Tree} (h : isNum t = true) : AtomsOK t := by
  intro l a ha
  left
  unfold ratoms at ha
  simpa [h] using ha

theorem AtomsOK_node2 {s : String} {a b : Tree}
    (ha : AtomsOK a) (hb : AtomsOK b)
    (hr : ∀ l, ratoms l (node (sym s) [a, b]) = ratoms (ratoms l a) b) :
    AtomsOK (node (sym s) [a, b]) := by
  intro l x hx
  rw [hr] at hx
  rcases hb _ x hx with h | h
  · exact ha l x h
  · exact Or.inr h

theorem AtomsOK_add {a b : Tree} (ha : AtomsOK a) (hb : AtomsOK b) :
    AtomsOK (node (sym "+") [a, b]) :=
  AtomsOK_node2 ha hb fun l => by
    rw [ratoms, ite_false_cond (isNum_node2 (h := "+") (by decide) a b)]

theorem AtomsOK_sub {a b : Tree} (ha : AtomsOK a) (hb : AtomsOK b) :
    AtomsOK (node (sym "-") [a, b]) :=
  AtomsOK_node2 ha hb fun l => by
    rw [ratoms, ite_false_cond (isNum_node2 (h := "-") (by decide) a b)]

theorem AtomsOK_mul {a b : Tree} (ha : AtomsOK a) (hb : AtomsOK b) :
    AtomsOK (node (sym "*") [a, b]) :=
  AtomsOK_node2 ha hb fun l => by
    rw [ratoms, ite_false_cond (isNum_node2 (h := "*") (by decide) a b)]

theorem AtomsOK_neg {a : Tree} (ha : AtomsOK a) : AtomsOK (node (sym "-") [a]) := by
  by_cases h : isNum (node (sym "-") [a]) = true
  · exact AtomsOK_num h
  · intro l x hx
    rw [ratoms, ite_false_cond (by simpa using h)] at hx
    exact ha l x hx

theorem AtomsOK_atom {b : Tree} (hb : IsAtom b) : AtomsOK b := by
  intro l x hx
  rw [hb.2, mem_addAtom] at hx
  rcases hx with h | rfl
  · exact Or.inl h
  · exact Or.inr hb

theorem AtomsOK_facNode {b : Tree} (hb : IsAtom b) (e : ℕ) : AtomsOK (facNode b e) := by
  unfold facNode
  split_ifs
  · exact AtomsOK_atom hb
  · intro l x hx
    have : intNode (e : ℤ) = int (e : ℤ) := by simp [intNode]
    rw [arith, this, ratoms, ite_false_cond (isNum_node2 (h := "^") (by decide) b _)] at hx
    simp only [rpow, intExp, numeralForm] at hx
    exact AtomsOK_atom hb l x hx

theorem foldl_induct {α : Type*} (P : Tree → Prop) (g : Tree → α → Tree) (l : List α)
    (a : Tree) (ha : P a) (hg : ∀ acc x, x ∈ l → P acc → P (g acc x)) : P (l.foldl g a) := by
  induction l generalizing a with
  | nil => exact ha
  | cons x l ih =>
    exact ih _ (hg a x (by simp) ha) (fun acc y hy h => hg acc y (by simp [hy]) h)

theorem AtomsOK_mulChain (c : ℚ) {fs : List Tree} (h : ∀ f ∈ fs, AtomsOK f) :
    AtomsOK (mulChain c fs) := by
  unfold mulChain
  have hn := AtomsOK_num (isNum_numNode c)
  dsimp only
  split
  · exact hn
  · rename_i r rs e
    have h' : ∀ f ∈ r :: rs, AtomsOK f := by
      intro f hf
      split_ifs at e with hc
      · rw [← e] at hf
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hn
        · exact h f hf
      · rw [← e] at hf; exact h f hf
    exact foldl_induct _ _ rs r (h' r (by simp))
      (fun acc t ht hacc => AtomsOK_mul hacc (h' t (by simp [ht])))

theorem AtomsOK_ite {c : Prop} [Decidable c] {a b : Tree} (ha : AtomsOK a) (hb : AtomsOK b) :
    AtomsOK (if c then a else b) := by
  split_ifs
  · exact ha
  · exact hb

theorem AtomsOK_trm (fs : List Tree) (c : ℚ) (h : ∀ f ∈ fs, AtomsOK f) :
    AtomsOK (if |c| = 1 then mulChain 1 fs else mulChain |c| fs) := by
  split_ifs
  · exact AtomsOK_mulChain 1 h
  · exact AtomsOK_mulChain _ h

theorem AtomsOK_linBuild (c0 : ℚ) (ts : List (List Tree × ℚ))
    (h : ∀ x ∈ ts, ∀ f ∈ x.1, AtomsOK f) : AtomsOK (linBuild c0 ts) := by
  have hms : ∀ y ∈ (mergeT ts).foldr insertTerm [], ∀ f ∈ y.1, AtomsOK f := by
    intro y hy
    have e : (mergeT ts).foldr insertTerm []
        = (mergeT ts).foldr (insBy (fun x => mulChain 1 x.1)) [] := by
      congr 1; funext a l; exact insertTerm_eq a l
    rw [e] at hy
    have hy' := (foldr_insBy_perm _ _).subset hy
    rw [mergeT_R, List.mem_filter] at hy'
    obtain ⟨z, hz, ez⟩ := origin_foldl _ _ [] _ hy'.1
    rw [← ez]
    exact h z (by simpa using hz)
  unfold linBuild
  dsimp only
  generalize (mergeT ts).foldr insertTerm [] = ms at hms
  cases ms with
  | nil => exact AtomsOK_num (isNum_numNode c0)
  | cons e rest =>
    obtain ⟨fs, c⟩ := e
    dsimp only
    have htrm : ∀ y ∈ (fs, c) :: rest,
        AtomsOK (if |y.2| = 1 then mulChain 1 y.1 else mulChain |y.2| y.1) :=
      fun y hy => AtomsOK_trm _ _ (hms y hy)
    have hn := AtomsOK_num (isNum_numNode |c0|)
    have hacc : ∀ g : Tree → List Tree × ℚ → Tree,
        (∀ acc x, x ∈ rest → AtomsOK acc → AtomsOK (g acc x)) →
        AtomsOK (rest.foldl g (if 0 < c then (if |c| = 1 then mulChain 1 fs else mulChain |c| fs)
          else arith "-" [if |c| = 1 then mulChain 1 fs else mulChain |c| fs])) := by
      intro g hg
      apply foldl_induct _ g rest _ _ hg
      exact AtomsOK_ite (htrm (fs, c) (by simp)) (AtomsOK_neg (htrm (fs, c) (by simp)))
    have hg : ∀ acc x, x ∈ rest → AtomsOK acc →
        AtomsOK (if 0 < x.2 then arith "+" [acc, if |x.2| = 1 then mulChain 1 x.1
          else mulChain |x.2| x.1] else arith "-" [acc, if |x.2| = 1 then mulChain 1 x.1
          else mulChain |x.2| x.1]) := fun acc x hx h =>
      AtomsOK_ite (AtomsOK_add h (htrm x (by simp [hx]))) (AtomsOK_sub h (htrm x (by simp [hx])))
    have := hacc _ hg
    exact AtomsOK_ite this (AtomsOK_ite (AtomsOK_add this hn) (AtomsOK_sub this hn))

theorem AtomsOK_fromP {al : List Tree} {p : Poly} (hw : WF al p) : AtomsOK (fromP al p) := by
  unfold fromP
  apply AtomsOK_linBuild
  intro x hx f hf
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  have hy' := List.mem_filter.1 hy
  simp only [facTrees_eq, facs, sortLt_eq] at hf
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ((foldr_insBy_perm id _).subset hf)
  have hz' := hz
  unfold mergeN at hz'
  obtain ⟨w, hw', ew⟩ := origin_foldl id _ [] _ (List.mem_filter.1 hz').1
  rw [← ew]
  exact AtomsOK_facNode (atoms_Lof hw hy'.1 w (by simpa using hw')) _

/-! ### Well-formed polynomials from `toF` -/

/-- The monomial part of `WF`. -/
def Wm (al : List Tree) (p : Poly) : Prop := ∀ x ∈ p, ∀ y ∈ x.1, y.1 < al.length ∧ y.2 ≠ 0

theorem Wm_append {al : List Tree} {p q : Poly} (hp : Wm al p) (hq : Wm al q) :
    Wm al (p ++ q) := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact hp x h
  · exact hq x h

theorem Wm_pneg {al : List Tree} {p : Poly} (hp : Wm al p) : Wm al (pneg p) := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
  exact hp z hz

theorem Wm_pscale {al : List Tree} {p : Poly} (k : ℚ) (hp : Wm al p) : Wm al (pscale k p) := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
  exact hp z hz

theorem Wm_pmul {al : List Tree} {p q : Poly} (hp : Wm al p) (hq : Wm al q) :
    Wm al (pmul p q) := by
  intro x hx
  simp only [pmul, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  intro y hy
  rcases List.mem_append.1 hy with h | h
  · exact hp a ha y h
  · exact hq b hb y h

theorem Wm_ppow {al : List Tree} {p : Poly} (hp : Wm al p) (n : ℕ) : Wm al (ppow p n) := by
  induction n with
  | zero => intro x hx; simp [ppow, pconst] at hx; simp [hx]
  | succ n ih => exact Wm_pmul ih hp

theorem atomIdx_lt {al : List Tree} {t : Tree} (h : t ∈ al) : atomIdx al t < al.length := by
  have : ∃ i, al.findIdx? (fun x => teq x t) = some i ∧ i < al.length := by
    induction al with
    | nil => simp at h
    | cons y r ih =>
      rw [List.findIdx?_cons]
      by_cases hy : y = t
      · subst hy; simp [teq_refl]
      · have hy' : teq y t = false := by simpa [teq_eq_decide] using hy
        have hr : t ∈ r := by
          rcases List.mem_cons.1 h with h | h
          · exact absurd h.symm hy
          · exact h
        obtain ⟨i, hi, hl⟩ := ih hr
        exact ⟨i + 1, by simp [hy', hi], by simp; omega⟩
  obtain ⟨i, hi, hl⟩ := this
  unfold atomIdx
  rw [hi]
  exact hl

theorem Wm_toF (al l : List Tree) (t : Tree) (h : ∀ a ∈ ratoms l t, a ∈ al) :
    Wm al (toF al t) := by
  have atom : ∀ t, t ∈ al → (toF al t = pvar (atomIdx al t)) → Wm al (toF al t) := by
    intro t ht e
    rw [e]
    intro x hx
    simp only [pvar, List.mem_singleton] at hx
    subst hx
    intro y hy
    simp only [List.mem_singleton] at hy
    subst hy
    exact ⟨atomIdx_lt ht, one_ne_zero⟩
  fun_induction ratoms l t
  case case1 t l hn =>
    have : toF al t = pconst (val t) := by unfold toF; simp [hn]
    rw [this]
    intro x hx
    simp [pconst] at hx
    simp [hx]
  case case2 l a b hn iha ihb =>
    rw [toF, ite_false_cond (isNum_node2 (h := "+") (by decide) a b)]
    exact Wm_append (iha (fun x hx => h x (sub_ratoms _ b x hx))) (ihb h)
  case case3 l a hn iha =>
    rw [toF, ite_false_cond (by simpa using hn)]
    exact Wm_pneg (iha h)
  case case4 l a b hn iha ihb =>
    rw [toF, ite_false_cond (isNum_node2 (h := "-") (by decide) a b)]
    exact Wm_append (iha (fun x hx => h x (sub_ratoms _ b x hx))) (Wm_pneg (ihb h))
  case case5 l a b hn iha ihb =>
    rw [toF, ite_false_cond (isNum_node2 (h := "*") (by decide) a b)]
    exact Wm_pmul (iha (fun x hx => h x (sub_ratoms _ b x hx))) (ihb h)
  case case6 l a b hb hn iha ihb =>
    have e1 : toF al (node (sym "/") [a, b]) = pscale (val b)⁻¹ (toF al a) := by
      rw [toF, ite_false_cond (by simpa using hn)]; simp [hb]
    rw [e1]
    exact Wm_pscale _ (iha (fun x hx => h x (sub_ratoms _ b x hx)))
  case case7 l a b hb hn =>
    apply atom _ (h _ (by simp [mem_addAtom]))
    rw [toF, ite_false_cond (by simpa using hn)]; simp [hb]
  case case8 l b e n hr hn ihb =>
    have e1 : toF al (node (sym "^") [b, e]) = ppow (toF al b) n := by
      rw [toF, ite_false_cond (by simpa using hn)]; simp [hr]
    rw [e1]
    exact Wm_ppow (ihb h) n
  case case9 l b e hr hn =>
    apply atom _ (h _ (by simp [mem_addAtom]))
    rw [toF, ite_false_cond (by simpa using hn)]; simp [hr]
  case case10 t l hn h1 h2 h3 h4 h5 h6 =>
    apply atom _ (h _ (by simp [mem_addAtom]))
    rw [toF]
    all_goals first | assumption | simp [hn]

/-! ### Closure under the constructors -/

theorem NF_ring2 {x y : Tree} (hx : NF x) (hy : NF y) (f : Poly → Poly → Poly)
    (hf : ∀ al p q, Wm al p → Wm al q → Wm al (f p q)) : NF (ring2 x y f) := by
  obtain ⟨alx, px, hwx, rfl⟩ := hx
  obtain ⟨aly, py, hwy, rfl⟩ := hy
  set X := fromP alx px
  set Y := fromP aly py
  refine ⟨ratoms (ratoms [] X) Y, _, ⟨fun a ha => ?_, hf _ _ _ ?_ ?_⟩, rfl⟩
  · rcases AtomsOK_fromP hwy _ a ha with h | h
    · rcases AtomsOK_fromP hwx _ a h with h | h
      · simp at h
      · exact h
    · exact h
  · exact Wm_toF _ [] X (fun a ha => sub_ratoms _ Y a ha)
  · exact Wm_toF _ (ratoms [] X) Y (fun a ha => ha)

theorem NF_ring1 {x : Tree} (hx : NF x) (f : Poly → Poly)
    (hf : ∀ al p, Wm al p → Wm al (f p)) : NF (ring1 x f) := by
  obtain ⟨alx, px, hwx, rfl⟩ := hx
  set X := fromP alx px
  refine ⟨ratoms [] X, _, ⟨fun a ha => ?_, hf _ _ ?_⟩, rfl⟩
  · rcases AtomsOK_fromP hwx _ a ha with h | h
    · simp at h
    · exact h
  · exact Wm_toF _ [] X (fun a ha => ha)

theorem NF_rAdd {x y : Tree} (hx : NF x) (hy : NF y) : NF (rAdd x y) := by
  unfold rAdd
  split_ifs
  · exact NF_numNode _
  · exact NF_ring2 hx hy _ fun _ _ _ hp hq => Wm_append hp hq

theorem NF_rSub {x y : Tree} (hx : NF x) (hy : NF y) : NF (rSub x y) := by
  unfold rSub
  split_ifs
  · exact NF_numNode _
  · exact NF_ring2 hx hy _ fun _ _ _ hp hq => Wm_append hp (Wm_pneg hq)

theorem NF_rNeg {x : Tree} (hx : NF x) : NF (rNeg x) := by
  unfold rNeg
  split_ifs
  · exact NF_numNode _
  · exact NF_ring1 hx _ fun _ _ hp => Wm_pneg hp

theorem NF_rMul (A : RAx) {x y : Tree} (hx : NF x) (hy : NF y) : NF (rMul A x y) := by
  unfold rMul
  split_ifs
  · exact NF_numNode _
  · exact NF_numNode _
  · exact hy
  · exact hx
  · exact NF_ring2 hx hy _ fun _ _ _ hp hq => Wm_pmul hp hq

theorem NF_rDiv (A : RAx) {x y : Tree} (hx : NF x) (hy : NF y) (hn : isNum y = true) :
    NF (rDiv A x y) := by
  unfold rDiv
  split_ifs
  · exact NF_numNode _
  · exact NF_ring2 hx hy _ fun _ _ _ hp _ => Wm_pscale _ hp

theorem NF_rPow {x : Tree} (hx : NF x) (n : ℕ) : NF (rPow x n) := by
  unfold rPow
  split_ifs with h1 h2 h3 h4
  · exact NF_numNode _
  · exact hx
  · exact NF_numNode _
  · exact NF_ring1 hx _ fun _ _ hp => Wm_ppow hp _
  · exact absurd (Int.natCast_nonneg n) h4

/-! ## The mirror decides the theory `Ring` (with R4) -/

open FricasSymbolic.Ring in
/-- The mirror as a normaliser of `RTerm String`: atoms are symbols, and each operation is
the corresponding constructor of the rung. -/
def nfR (A : RAx) : RTerm String → Tree
  | .num q => numNode q
  | .atom a => sym a
  | .add a b => rAdd (nfR A a) (nfR A b)
  | .sub a b => rSub (nfR A a) (nfR A b)
  | .neg a => rNeg (nfR A a)
  | .mul a b => rMul A (nfR A a) (nfR A b)
  | .pow a n => rPow (nfR A a) n
  | .divn a q => rDiv A (nfR A a) (numNode q)

theorem isAtom_sym (a : String) : IsAtom (sym a) := by
  have hn : isNum (sym a) = false := by simp [isNum, numeralForm]
  constructor
  · rw [rd]
    all_goals simp [hn]
  · intro l
    rw [ratoms]
    all_goals simp [hn]

open FricasSymbolic.Ring in
/-- (N1) for the mirror: the normal form reads back as the polynomial the term denotes. -/
theorem rd_nfR (A : RAx) (t : RTerm String) : rd (nfR A t) = rename sym (phi t) := by
  induction t with
  | num q => simp [nfR, phi, rd_numNode]
  | atom a => simp [nfR, phi, (isAtom_sym a).1]
  | add a b iha ihb => simp [nfR, phi, rd_rAdd, iha, ihb]
  | sub a b iha ihb => simp [nfR, phi, rd_rSub, iha, ihb]
  | neg a iha => simp [nfR, phi, rd_rNeg, iha]
  | mul a b iha ihb => simp [nfR, phi, rd_rMul, iha, ihb]
  | pow a n iha => simp [nfR, phi, rd_rPow, iha]
  | divn a q iha =>
    simp only [nfR, phi, rd_rDiv A _ _ (isNum_numNode q), val_numNode, iha, map_mul, rename_C]
    ring

open FricasSymbolic.Ring in
theorem NF_nfR (A : RAx) (t : RTerm String) : NF (nfR A t) := by
  induction t with
  | num q => exact NF_numNode q
  | atom a => exact NF_atom (isAtom_sym a)
  | add a b iha ihb => exact NF_rAdd iha ihb
  | sub a b iha ihb => exact NF_rSub iha ihb
  | neg a iha => exact NF_rNeg iha
  | mul a b iha ihb => exact NF_rMul A iha ihb
  | pow a n iha => exact NF_rPow iha n
  | divn a q iha => exact NF_rDiv A iha (NF_numNode q) (isNum_numNode q)

open FricasSymbolic.Ring in
/-- **(N1) and (N2) for the mirror.** Two defined terms have the same normal form exactly when
they are equal in the theory `Ring`. -/
theorem nfR_eq_iff (A : RAx) {s t : RTerm String} (hs : s.Defined) (ht : t.Defined) :
    nfR A s = nfR A t ↔ Equiv s t := by
  rw [R4_equiv_iff hs ht]
  constructor
  · intro h
    have := congrArg rd h
    rw [rd_nfR, rd_nfR] at this
    exact rename_injective sym (fun a b h => by cases h; rfl) this
  · intro h
    exact NF_canonical (NF_nfR A s) (NF_nfR A t) (by rw [rd_nfR, rd_nfR, h])

end FricasSymbolic.RingMirror
