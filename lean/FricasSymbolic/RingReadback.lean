import FricasSymbolic.RingMirror
import FricasSymbolic.OrderProofs
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
      split_ifs <;> simp_all [add_assoc, add_comm, add_left_comm]
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
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
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
  | [], b :: _, h, _, _ => absurd h.symm (List.Perm.nil_eq ▸ by simp)
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

end FricasSymbolic.RingMirror
