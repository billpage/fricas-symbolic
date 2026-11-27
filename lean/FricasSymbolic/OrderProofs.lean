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

theorem kind_eq_two {t : Tree} (hk : kind t = 2) : ∃ a, t = sym a := by
  cases t with
  | sym a => exact ⟨a, rfl⟩
  | node g as => rcases kind_node g as with e | e | e <;> omega
  | _ => simp [kind, numeralForm] at hk

theorem kind_eq_three {t : Tree} (hk : kind t = 3) : ∃ a, t = str a := by
  cases t with
  | str a => exact ⟨a, rfl⟩
  | node g as => rcases kind_node g as with e | e | e <;> omega
  | _ => simp [kind, numeralForm] at hk

theorem kind_eq_four {t : Tree} (hk : kind t = 4) : ∃ a, t = atom a := by
  cases t with
  | atom a => exact ⟨a, rfl⟩
  | node g as => rcases kind_node g as with e | e | e <;> omega
  | _ => simp [kind, numeralForm] at hk

theorem kind_eq_five {t : Tree} (hk : kind t = 5) : ∃ g as, t = node g as := by
  cases t with
  | node g as => exact ⟨g, as, rfl⟩
  | _ => simp [kind, numeralForm] at hk

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
      else (atomLt s t).getD (structural s t) := by
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
  cases bs <;> rw [ltList] <;> simp

@[simp] theorem ltList_nil_right (as : List Tree) : ltList as [] = false := by
  cases as <;> rw [ltList] <;> simp

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
                simp [h2]
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

/-! ## The induction step -/

theorem lt_kind_ne {a b : Tree} (h : kind a ≠ kind b) : lt a b = decide (kind a < kind b) := by
  rw [lt_def]; simp [h]

theorem lt_num {a b : Tree} (h : kind a = kind b) (h1 : kind a ≤ 1) :
    lt a b = if val a ≠ val b then decide (val a < val b) else structural a b := by
  rw [lt_def]; simp only [h, ne_eq, not_true_eq_false, ↓reduceIte]; simp only [← h, h1, ↓reduceIte]

theorem lt_atomic {a b : Tree} (h : kind a = kind b) (h1 : ¬ kind a ≤ 1) :
    lt a b = (atomLt a b).getD (structural a b) := by
  rw [lt_def]; simp only [h, ne_eq, not_true_eq_false, ↓reduceIte]; simp only [← h, h1, ↓reduceIte]

theorem kind_le_of_lt {a b : Tree} (h : lt a b = true) : kind a ≤ kind b := by
  by_cases e : kind a = kind b
  · exact le_of_eq e
  · rw [lt_kind_ne e] at h; simp at h; omega

theorem kids_of {d : ℕ} {t : Tree} (ht : depth t < d + 1) :
    Good.Kids (fun t => depth t < d) t := by
  cases t with
  | node h as => exact ⟨depth_head ht, fun x hx => depth_arg hx ht⟩
  | _ => trivial

/-- In kinds 2–5, `lt` is the order of the strings (kinds 2–4) or `structural` (kind 5). -/
theorem lt_atomic_cases {a b : Tree} (h : kind a = kind b) (h1 : ¬ kind a ≤ 1) :
    (∃ x y, a = sym x ∧ b = sym y ∧ lt a b = decide (x < y)) ∨
    (∃ x y, a = str x ∧ b = str y ∧ lt a b = decide (x < y)) ∨
    (∃ x y, a = atom x ∧ b = atom y ∧ lt a b = decide (x < y)) ∨
    (kind a = 5 ∧ (∃ g as, a = node g as) ∧ (∃ g bs, b = node g bs) ∧ lt a b = structural a b) := by
  rw [lt_atomic h h1]
  have hk := kind_le_five a
  have : kind a = 2 ∨ kind a = 3 ∨ kind a = 4 ∨ kind a = 5 := by omega
  rcases this with e | e | e | e
  · obtain ⟨x, rfl⟩ := kind_eq_two e; obtain ⟨y, rfl⟩ := kind_eq_two (h ▸ e)
    exact Or.inl ⟨x, y, rfl, rfl, rfl⟩
  · obtain ⟨x, rfl⟩ := kind_eq_three e; obtain ⟨y, rfl⟩ := kind_eq_three (h ▸ e)
    exact Or.inr (Or.inl ⟨x, y, rfl, rfl, rfl⟩)
  · obtain ⟨x, rfl⟩ := kind_eq_four e; obtain ⟨y, rfl⟩ := kind_eq_four (h ▸ e)
    exact Or.inr (Or.inr (Or.inl ⟨x, y, rfl, rfl, rfl⟩))
  · obtain ⟨g, as, rfl⟩ := kind_eq_five e; obtain ⟨g', bs, rfl⟩ := kind_eq_five (h ▸ e)
    exact Or.inr (Or.inr (Or.inr ⟨e, ⟨g, as, rfl⟩, ⟨g', bs, rfl⟩, by simp [atomLt]⟩))

theorem good_step (d : ℕ) (G : Good (fun t => depth t < d)) :
    Good (fun t => depth t < d + 1) where
  irrefl a ha := by
    by_cases h1 : kind a ≤ 1
    · rw [lt_num rfl h1]; simp [G.structural_irrefl a (kids_of ha)]
    · rcases lt_atomic_cases (a := a) (b := a) rfl h1 with
        ⟨x, y, e1, e2, e⟩ | ⟨x, y, e1, e2, e⟩ | ⟨x, y, e1, e2, e⟩ | ⟨_, _, _, e⟩
      · rw [e]; rw [e1] at e2; cases e2; simp
      · rw [e]; rw [e1] at e2; cases e2; simp
      · rw [e]; rw [e1] at e2; cases e2; simp
      · rw [e]; exact G.structural_irrefl a (kids_of ha)
  trans a b c ha hb hc h1 h2 := by
    have k1 := kind_le_of_lt h1; have k2 := kind_le_of_lt h2
    by_cases kac : kind a = kind c
    · have kab : kind a = kind b := by omega
      have kbc : kind b = kind c := by omega
      by_cases n : kind a ≤ 1
      · rw [lt_num kab n] at h1; rw [lt_num kbc (kab ▸ n)] at h2; rw [lt_num kac n]
        by_cases vab : val a = val b
        · by_cases vbc : val b = val c
          · simp only [vab, vbc, ne_eq, not_true_eq_false, ↓reduceIte] at h1 h2 ⊢
            exact G.structural_trans a b c (kids_of ha) (kids_of hb) (kids_of hc) h1 h2
          · simp only [vab, vbc, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte,
              decide_eq_true_eq] at h1 h2 ⊢
            simp [vbc, h2]
        · simp only [vab, ne_eq, not_false_eq_true, ↓reduceIte, decide_eq_true_eq] at h1
          by_cases vbc : val b = val c
          · simp only [vbc, ne_eq, not_true_eq_false, ↓reduceIte] at h2
            rw [vbc] at h1 vab; simp [vab, h1]
          · simp only [vbc, ne_eq, not_false_eq_true, ↓reduceIte, decide_eq_true_eq] at h2
            have : val a < val c := lt_trans h1 h2
            simp [ne_of_lt this, this]
      · rcases lt_atomic_cases kab n with
          ⟨x, y, rfl, rfl, e1⟩ | ⟨x, y, rfl, rfl, e1⟩ | ⟨x, y, rfl, rfl, e1⟩ | ⟨k5, _, _, e1⟩
        · rcases lt_atomic_cases kbc (kab ▸ n) with ⟨y', z, ey, rfl, e2⟩ | ⟨_, _, ey, _⟩ |
            ⟨_, _, ey, _⟩ | ⟨_, _, ⟨_, _, ey⟩, _⟩ <;> cases ey
          rcases lt_atomic_cases kac n with ⟨_, _, ex, ez, e3⟩ | ⟨_, _, ex, _⟩ | ⟨_, _, ex, _⟩ |
            ⟨_, ⟨_, _, ex⟩, _⟩ <;> cases ex
          cases ez; rw [e1] at h1; rw [e2] at h2; rw [e3]; simp at h1 h2 ⊢; exact lt_trans h1 h2
        · rcases lt_atomic_cases kbc (kab ▸ n) with ⟨_, _, ey, _⟩ | ⟨y', z, ey, rfl, e2⟩ |
            ⟨_, _, ey, _⟩ | ⟨_, _, ⟨_, _, ey⟩, _⟩ <;> cases ey
          rcases lt_atomic_cases kac n with ⟨_, _, ex, _⟩ | ⟨_, _, ex, ez, e3⟩ | ⟨_, _, ex, _⟩ |
            ⟨_, ⟨_, _, ex⟩, _⟩ <;> cases ex
          cases ez; rw [e1] at h1; rw [e2] at h2; rw [e3]; simp at h1 h2 ⊢; exact lt_trans h1 h2
        · rcases lt_atomic_cases kbc (kab ▸ n) with ⟨_, _, ey, _⟩ | ⟨_, _, ey, _⟩ |
            ⟨y', z, ey, rfl, e2⟩ | ⟨_, _, ⟨_, _, ey⟩, _⟩ <;> cases ey
          rcases lt_atomic_cases kac n with ⟨_, _, ex, _⟩ | ⟨_, _, ex, _⟩ | ⟨_, _, ex, ez, e3⟩ |
            ⟨_, ⟨_, _, ex⟩, _⟩ <;> cases ex
          cases ez; rw [e1] at h1; rw [e2] at h2; rw [e3]; simp at h1 h2 ⊢; exact lt_trans h1 h2
        · have k5b : kind b = 5 := kab ▸ k5
          rcases lt_atomic_cases kbc (by omega) with ⟨_, _, ey, _⟩ | ⟨_, _, ey, _⟩ |
            ⟨_, _, ey, _⟩ | ⟨_, _, _, e2⟩
          · subst ey; simp [kind, numeralForm] at k5b
          · subst ey; simp [kind, numeralForm] at k5b
          · subst ey; simp [kind, numeralForm] at k5b
          rcases lt_atomic_cases kac n with ⟨_, _, ex, _⟩ | ⟨_, _, ex, _⟩ |
            ⟨_, _, ex, _⟩ | ⟨_, _, _, e3⟩
          · subst ex; simp [kind, numeralForm] at k5
          · subst ex; simp [kind, numeralForm] at k5
          · subst ex; simp [kind, numeralForm] at k5
          rw [e1] at h1; rw [e2] at h2; rw [e3]
          exact G.structural_trans a b c (kids_of ha) (kids_of hb) (kids_of hc) h1 h2
    · rw [lt_kind_ne kac]; simp
      rcases Nat.lt_or_ge (kind a) (kind b) with h | h
      · omega
      · have : kind a = kind b := le_antisymm k1 h
        omega
  total a b ha hb hne := by
    by_cases k : kind a = kind b
    · by_cases n : kind a ≤ 1
      · rw [lt_num k n, lt_num k.symm (k ▸ n)]
        by_cases v : val a = val b
        · simp only [v, ne_eq, not_true_eq_false, ↓reduceIte]
          apply G.structural_total a b (kids_of ha) (kids_of hb) _ hne
          rintro ⟨ia, ib⟩; exact hne (eq_of_numeral_atoms ia ib k n v)
        · have v' : val b ≠ val a := fun e => v e.symm
          simp only [v, v', ne_eq, not_false_eq_true, ↓reduceIte, decide_eq_true_eq]
          exact lt_or_gt_of_ne v
      · rcases lt_atomic_cases k n with
          ⟨x, y, rfl, rfl, e⟩ | ⟨x, y, rfl, rfl, e⟩ | ⟨x, y, rfl, rfl, e⟩ | ⟨k5, ⟨g, as, rfl⟩, ⟨g', bs, rfl⟩, e⟩
        · rw [e, lt_atomic k.symm (k ▸ n)]; simp [atomLt]
          exact lt_or_gt_of_ne (fun h => hne (by rw [h]))
        · rw [e, lt_atomic k.symm (k ▸ n)]; simp [atomLt]
          exact lt_or_gt_of_ne (fun h => hne (by rw [h]))
        · rw [e, lt_atomic k.symm (k ▸ n)]; simp [atomLt]
          exact lt_or_gt_of_ne (fun h => hne (by rw [h]))
        · rw [e, lt_atomic k.symm (k ▸ n)]; simp only [atomLt, Option.getD_none]
          exact G.structural_total _ _ (kids_of ha) (kids_of hb) (by simp [isAtom]) hne
    · rw [lt_kind_ne k, lt_kind_ne (fun e => k e.symm)]
      simp; omega

theorem good_depth (d : ℕ) : Good (fun t => depth t < d) := by
  induction d with
  | zero => exact ⟨fun _ h => absurd h (by omega), fun _ _ _ h => absurd h (by omega),
      fun _ _ h => absurd h (by omega)⟩
  | succ d ih => exact good_step d ih

/-! ## O1, O2: Prop. 4 -/

/-- O1: the term order is irreflexive. -/
theorem O1_irrefl (t : Tree) : lt t t = false :=
  (good_depth (depth t + 1)).irrefl t (by omega)

/-- O1: the term order is transitive. -/
theorem O1_trans {a b c : Tree} (h1 : lt a b = true) (h2 : lt b c = true) : lt a c = true :=
  (good_depth (depth a + depth b + depth c + 1)).trans a b c (by omega) (by omega) (by omega)
    h1 h2

/-- O2: the term order is total on distinct trees. -/
theorem O2_total {a b : Tree} (h : a ≠ b) : lt a b = true ∨ lt b a = true :=
  (good_depth (depth a + depth b + 1)).total a b (by omega) (by omega) h

/-- Prop. 4 in Mathlib's terms: `lt` is a strict total order on trees. -/
instance : IsStrictTotalOrder Tree (fun a b => lt a b = true) where
  irrefl a := by simp [O1_irrefl]
  trans _ _ _ := O1_trans
  trichotomous a b := by
    by_cases h : a = b
    · exact Or.inr (Or.inl h)
    · rcases O2_total h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')

end FricasSymbolic.Order.Tree
