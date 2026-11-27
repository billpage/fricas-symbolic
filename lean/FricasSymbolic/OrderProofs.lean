import FricasSymbolic.Order

/-!
# Part 2: the term order is a strict total order (O1, O2; spec Prop. 4)

`lt` is irreflexive and transitive (O1) and total on distinct trees (O2), for every
`InputForm` tree of the model, float numerals included.

The proof is by strong induction on depth (`good_depth`): if `lt` is a strict total
order on the trees of depth `< d`, then
* `ltList`, the argument loop, is a strict order on lists of such trees, total on
  distinct lists of the same length;
* `structural` is a strict order on trees whose head and arguments have depth `< d`,
  total unless both trees are atoms;
* `lt` is a strict total order on the trees of depth `< d + 1`: it is lexicographic
  in kind, then value (numerals), string (symbols, strings, other atoms) or nothing
  (compounds), then `structural`. Two numeral atoms of the same kind and value are
  the same atom, so `structural` is never asked to separate two distinct atoms.
-/

namespace FricasSymbolic.Order.Tree

/-! ## Depth -/

mutual
def depth : Tree → ℕ
  | node h as => max (depth h) (depthList as) + 1
  | _ => 0
def depthList : List Tree → ℕ
  | [] => 0
  | a :: as => max (depth a) (depthList as)
end

theorem depth_le_depthList {a : Tree} {as : List Tree} (h : a ∈ as) :
    depth a ≤ depthList as := by
  induction as with
  | nil => cases h
  | cons b bs ih =>
    rw [depthList]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem depth_head {h : Tree} {as : List Tree} {d : ℕ} (hd : depth (node h as) < d + 1) :
    depth h < d := by
  rw [depth] at hd; omega

theorem depth_arg {h a : Tree} {as : List Tree} {d : ℕ} (ha : a ∈ as)
    (hd : depth (node h as) < d + 1) : depth a < d := by
  rw [depth] at hd; have := depth_le_depthList ha; omega

/-! ## Kinds and values -/

theorem kind_node (h : Tree) (as : List Tree) :
    kind (node h as) = 0 ∨ kind (node h as) = 1 ∨ kind (node h as) = 5 := by
  unfold kind
  rcases numeralForm (node h as) with _ | ⟨f, q⟩
  · simp
  · cases f <;> simp

theorem kind_eq_two {t : Tree} (h : kind t = 2) : ∃ a, t = sym a := by
  cases t with
  | sym a => exact ⟨a, rfl⟩
  | node h as => rcases kind_node h as with e | e | e <;> omega
  | _ => simp [kind, numeralForm] at h

theorem kind_eq_three {t : Tree} (h : kind t = 3) : ∃ a, t = str a := by
  cases t with
  | str a => exact ⟨a, rfl⟩
  | node h as => rcases kind_node h as with e | e | e <;> omega
  | _ => simp [kind, numeralForm] at h

theorem kind_eq_four {t : Tree} (h : kind t = 4) : ∃ a, t = atom a := by
  cases t with
  | atom a => exact ⟨a, rfl⟩
  | node h as => rcases kind_node h as with e | e | e <;> omega
  | _ => simp [kind, numeralForm] at h

theorem kind_eq_five {t : Tree} (h : kind t = 5) : ∃ g as, t = node g as := by
  cases t with
  | node g as => exact ⟨g, as, rfl⟩
  | _ => simp [kind, numeralForm] at h

theorem kind_le_five (t : Tree) : kind t ≤ 5 := by
  unfold kind
  rcases numeralForm t with _ | ⟨f, q⟩
  · cases t <;> simp
  · cases f <;> simp

/-- Is the tree an atom (not compound)? -/
def isAtom : Tree → Bool
  | node _ _ => false
  | _ => true

/-- Two numeral atoms of the same kind and value are the same atom. -/
theorem eq_of_numeral_atoms {s t : Tree} (hs : isAtom s = true) (ht : isAtom t = true)
    (hk : kind s = kind t) (hk1 : kind s ≤ 1) (hv : val s = val t) : s = t := by
  cases s <;> cases t <;> simp_all [isAtom, kind, numeralForm, val]

/-! ## Equations of `lt`, `structural`, `ltList` -/

theorem lt_def (s t : Tree) :
    lt s t = if kind s ≠ kind t then decide (kind s < kind t)
      else if kind s ≤ 1 then (if val s ≠ val t then decide (val s < val t) else structural s t)
      else match atomLt s t with
        | some r => r
        | none => structural s t := by
  rw [lt]

theorem structural_node (hs ht : Tree) (as bs : List Tree) :
    structural (node hs as) (node ht bs) =
      if lt hs ht then true else if lt ht hs then false
      else if as.length ≠ bs.length then decide (as.length < bs.length)
      else ltList as bs := by
  rw [structural]

theorem structural_atom_left {s t : Tree} (hs : isAtom s = true) :
    structural s t = !isAtom t := by
  cases s <;> cases t <;> simp_all [isAtom, structural]

theorem structural_node_atom {g t : Tree} {as : List Tree} (ht : isAtom t = true) :
    structural (node g as) t = false := by
  cases t <;> simp_all [isAtom, structural]

theorem ltList_cons (a b : Tree) (as bs : List Tree) :
    ltList (a :: as) (b :: bs) = if lt a b then true else if lt b a then false else ltList as bs := by
  rw [ltList]

@[simp] theorem ltList_nil_left (bs : List Tree) : ltList [] bs = false := by
  cases bs <;> rw [ltList]

@[simp] theorem ltList_nil_right (as : List Tree) : ltList as [] = false := by
  cases as <;> rw [ltList]

/-! ## Strict total orders on a set of trees -/

/-- `lt` is a strict total order on the trees satisfying `S`. -/
structure Good (S : Tree → Prop) : Prop where
  irrefl : ∀ a, S a → lt a a = false
  trans : ∀ a b c, S a → S b → S c → lt a b = true → lt b c = true → lt a c = true
  total : ∀ a b, S a → S b → a ≠ b → lt a b = true ∨ lt b a = true

namespace Good

variable {S : Tree → Prop} (G : Good S)
include G

theorem eq_of_not {a b : Tree} (ha : S a) (hb : S b) (h1 : lt a b = false)
    (h2 : lt b a = false) : a = b := by
  by_contra hne
  rcases G.total a b ha hb hne with h | h <;> simp_all

theorem asymm {a b : Tree} (ha : S a) (hb : S b) (h : lt a b = true) : lt b a = false := by
  by_contra h'
  have := G.trans a b a ha hb ha h (by simpa using h')
  rw [G.irrefl a ha] at this; exact absurd this (by simp)

/-! ### The argument loop -/

theorem ltList_irrefl (l : List Tree) (hl : ∀ x ∈ l, S x) : ltList l l = false := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [ltList_cons, G.irrefl a (hl a (by simp))]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ih fun x hx => hl x (by simp [hx])

theorem ltList_trans (l1 : List Tree) : ∀ l2 l3 : List Tree, (∀ x ∈ l1, S x) →
    (∀ x ∈ l2, S x) → (∀ x ∈ l3, S x) →
    ltList l1 l2 = true → ltList l2 l3 = true → ltList l1 l3 = true := by
  induction l1 with
  | nil => intro l2 l3 _ _ _ h; simp at h
  | cons a as ih =>
    intro l2 l3 h1 h2 h3 e12 e23
    cases l2 with
    | nil => simp at e12
    | cons b bs =>
      cases l3 with
      | nil => simp at e23
      | cons c cs =>
        have sa := h1 a (by simp); have sb := h2 b (by simp); have sc := h3 c (by simp)
        rw [ltList_cons] at e12 e23 ⊢
        by_cases hab : lt a b = true
        · by_cases hbc : lt b c = true
          · simp [G.trans a b c sa sb sc hab hbc]
          · by_cases hcb : lt c b = true
            · simp [hbc, hcb] at e23
            · have : b = c := G.eq_of_not sb sc (by simpa using hbc) (by simpa using hcb)
              subst this; simp [hab]
        · by_cases hba : lt b a = true
          · simp [hab, hba] at e12
          have hab' : a = b := G.eq_of_not sa sb (by simpa using hab) (by simpa using hba)
          subst hab'
          simp only [hab, Bool.false_eq_true, ↓reduceIte] at e12 ⊢
          by_cases hac : lt a c = true
          · simp [hac]
          · by_cases hca : lt c a = true
            · simp [hac, hca] at e23
            · have : a = c := G.eq_of_not sa sc (by simpa using hac) (by simpa using hca)
              subst this
              simp only [hac, Bool.false_eq_true, ↓reduceIte] at e23 ⊢
              exact ih bs cs (fun x hx => h1 x (by simp [hx])) (fun x hx => h2 x (by simp [hx]))
                (fun x hx => h3 x (by simp [hx])) e12 e23

theorem ltList_total (l1 : List Tree) : ∀ l2 : List Tree, (∀ x ∈ l1, S x) →
    (∀ x ∈ l2, S x) → l1.length = l2.length → l1 ≠ l2 →
    ltList l1 l2 = true ∨ ltList l2 l1 = true := by
  induction l1 with
  | nil => intro l2 _ _ hl hne; cases l2 <;> simp_all
  | cons a as ih =>
    intro l2 h1 h2 hl hne
    cases l2 with
    | nil => simp at hl
    | cons b bs =>
      have sa := h1 a (by simp); have sb := h2 b (by simp)
      rw [ltList_cons, ltList_cons]
      by_cases hab : lt a b = true
      · simp [hab]
      by_cases hba : lt b a = true
      · simp [hba]
      have e : a = b := G.eq_of_not sa sb (by simpa using hab) (by simpa using hba)
      subst e
      simp only [hab, Bool.false_eq_true, ↓reduceIte]
      exact ih bs (fun x hx => h1 x (by simp [hx])) (fun x hx => h2 x (by simp [hx]))
        (by simpa using hl) (by simpa using hne)

/-! ### `structural` -/

/-- The head and arguments of a compound tree satisfy `S` (vacuous for atoms). -/
def Kids (S : Tree → Prop) : Tree → Prop
  | node h as => S h ∧ ∀ x ∈ as, S x
  | _ => True

omit G in
theorem kids_node {S : Tree → Prop} {h : Tree} {as : List Tree} (k : Kids S (node h as)) :
    S h ∧ ∀ x ∈ as, S x := k

theorem structural_irrefl (t : Tree) (kt : Kids S t) : structural t t = false := by
  cases t with
  | node h as =>
    obtain ⟨sh, sas⟩ := kids_node kt
    rw [structural_node, G.irrefl h sh]
    simp [G.ltList_irrefl as sas]
  | _ => simp [structural]

theorem structural_trans (a b c : Tree) (ka : Kids S a) (kb : Kids S b) (kc : Kids S c)
    (h1 : structural a b = true) (h2 : structural b c = true) : structural a c = true := by
  cases a with
  | node ha as =>
    cases b with
    | node hb bs =>
      cases c with
      | node hc cs =>
        obtain ⟨sha, sas⟩ := kids_node ka; obtain ⟨shb, sbs⟩ := kids_node kb
        obtain ⟨shc, scs⟩ := kids_node kc
        rw [structural_node] at h1 h2 ⊢
        -- heads
        by_cases e1 : lt ha hb = true
        · by_cases e2 : lt hb hc = true
          · simp [G.trans ha hb hc sha shb shc e1 e2]
          · by_cases e2' : lt hc hb = true
            · simp [e2, e2'] at h2
            · have : hb = hc := G.eq_of_not shb shc (by simpa using e2) (by simpa using e2')
              subst this; simp [e1]
        · by_cases e1' : lt hb ha = true
          · simp [e1, e1'] at h1
          have : ha = hb := G.eq_of_not sha shb (by simpa using e1) (by simpa using e1')
          subst this
          simp only [e1, Bool.false_eq_true, ↓reduceIte] at h1
          by_cases e2 : lt ha hc = true
          · simp [e2]
          · by_cases e2' : lt hc ha = true
            · simp [e2, e2'] at h2
            have : ha = hc := G.eq_of_not sha shc (by simpa using e2) (by simpa using e2')
            subst this
            simp only [e2, Bool.false_eq_true, ↓reduceIte] at h2 ⊢
            -- lengths, then arguments
            by_cases l1 : as.length = bs.length
            · by_cases l2 : bs.length = cs.length
              · simp only [l1, l2, ne_eq, not_true_eq_false, ↓reduceIte] at h1 h2 ⊢
                exact G.ltList_trans as bs cs sas sbs scs h1 h2
              · simp only [l1, l2, ne_eq, not_false_eq_true, ↓reduceIte, not_true_eq_false,
                  decide_eq_true_eq] at h1 h2 ⊢
                simp [l2, h2]
            · simp only [l1, ne_eq, not_false_eq_true, ↓reduceIte, decide_eq_true_eq] at h1
              by_cases l2 : bs.length = cs.length
              · simp only [l2, ne_eq, not_true_eq_false, ↓reduceIte] at h2
                have : as.length ≠ cs.length := by omega
                simp [this]; omega
              · simp only [l2, ne_eq, not_false_eq_true, ↓reduceIte, decide_eq_true_eq] at h2
                have : as.length ≠ cs.length := by omega
                simp [this]; omega
      | _ => simp [structural] at h2
    | _ => simp [structural] at h1
  | _ =>
    rw [structural_atom_left (by simp [isAtom])] at h1 ⊢
    cases b with
    | node hb bs =>
      cases c with
      | node _ _ => simp [isAtom]
      | _ => simp [structural] at h2
    | _ => simp [isAtom] at h1

theorem structural_total (a b : Tree) (ka : Kids S a) (kb : Kids S b)
    (hat : ¬ (isAtom a = true ∧ isAtom b = true)) (hne : a ≠ b) :
    structural a b = true ∨ structural b a = true := by
  cases a with
  | node ha as =>
    cases b with
    | node hb bs =>
      obtain ⟨sha, sas⟩ := kids_node ka; obtain ⟨shb, sbs⟩ := kids_node kb
      rw [structural_node, structural_node]
      by_cases e1 : lt ha hb = true
      · simp [e1]
      by_cases e1' : lt hb ha = true
      · simp [e1']
      have : ha = hb := G.eq_of_not sha shb (by simpa using e1) (by simpa using e1')
      subst this
      simp only [e1, Bool.false_eq_true, ↓reduceIte]
      by_cases l : as.length = bs.length
      · simp only [l, ne_eq, not_true_eq_false, ↓reduceIte]
        exact G.ltList_total as bs sas sbs l (fun h => hne (by rw [h]))
      · have l' : bs.length ≠ as.length := fun h => l h.symm
        simp only [l, l', ne_eq, not_false_eq_true, ↓reduceIte, decide_eq_true_eq]
        omega
    | _ => right; rw [structural_atom_left (by simp [isAtom])]; simp [isAtom]
  | _ =>
    cases b with
    | node hb bs => left; rw [structural_atom_left (by simp [isAtom])]; simp [isAtom]
    | _ => simp [isAtom] at hat

end Good

end FricasSymbolic.Order.Tree
