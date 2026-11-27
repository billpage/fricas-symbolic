import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Part 3, R4, and part 4, E2: the Ring rung is the polynomial ring

Plan §5 (R4) and §6 (E2). Terms of the Ring rung over an abstract type of atoms `σ`
(spec §3.4, "Atoms": the normal forms whose head is none of `+, -, ·`, a division by a
numeral, or a power with exponent in `ℕ`). `Step` is the standard presentation of
commutative `ℚ`-algebras; each rule is a law of the groups `commutativity`,
`associativity`, `identities`, `numerals`, `linear`, `powers` and `ring` that the rung
`ring` requires (spec §3.4).

* **R4** `R4_equiv_iff`: for terms without division by the numeral `0`, `s =_Ring t`
  exactly when `φ s = φ t` in `MvPolynomial σ ℚ`. The proof makes the terms modulo
  the axioms a commutative `ℚ`-algebra `Q` and uses the universal property of
  `MvPolynomial`: `ψ := aeval (atom ·)` satisfies `ψ (φ t) = [t]` (`psi_phi`).
* **E2** `E2_eval_respects`, `E2_eval_eq_aeval`, `E2_unique`: for every commutative ring
  `D` with `Algebra ℚ D` (what `SymbolicTermFunctions2` checks for `ring`: `CommutativeRing`
  and `Algebra(Fraction Integer)`) and every `f : σ → D`, evaluation respects `=_Ring`,
  equals `aeval f ∘ φ`, and `aeval f` is the only `ℚ`-algebra map extending `f`.
-/

namespace FricasSymbolic.Ring

/-- Terms of the Ring rung over atoms `σ`. `divn a q` is `a / q` for a numeral `q`. -/
inductive RTerm (σ : Type*) where
  | num : ℚ → RTerm σ
  | atom : σ → RTerm σ
  | add : RTerm σ → RTerm σ → RTerm σ
  | sub : RTerm σ → RTerm σ → RTerm σ
  | neg : RTerm σ → RTerm σ
  | mul : RTerm σ → RTerm σ → RTerm σ
  | pow : RTerm σ → ℕ → RTerm σ
  | divn : RTerm σ → ℚ → RTerm σ

variable {σ : Type*}

namespace RTerm

/-- No division by the numeral `0` (where `E` is undefined). -/
def Defined : RTerm σ → Prop
  | num _ | atom _ => True
  | add a b | sub a b | mul a b => a.Defined ∧ b.Defined
  | neg a | pow a _ => a.Defined
  | divn a q => a.Defined ∧ q ≠ 0

end RTerm

open RTerm

/-- The axioms of the Ring rung at the root. -/
inductive Root : RTerm σ → RTerm σ → Prop
  | add_assoc (x y z : RTerm σ) : Root (.add (.add x y) z) (.add x (.add y z))
  | add_comm (x y : RTerm σ) : Root (.add x y) (.add y x)
  | add_zero (x : RTerm σ) : Root (.add x (.num 0)) x
  | neg_add (x : RTerm σ) : Root (.add (.neg x) x) (.num 0)
  | sub (x y : RTerm σ) : Root (.sub x y) (.add x (.neg y))
  | mul_assoc (x y z : RTerm σ) : Root (.mul (.mul x y) z) (.mul x (.mul y z))
  | mul_comm (x y : RTerm σ) : Root (.mul x y) (.mul y x)
  | mul_one (x : RTerm σ) : Root (.mul x (.num 1)) x
  | zero_mul (x : RTerm σ) : Root (.mul (.num 0) x) (.num 0)
  | distrib (x y z : RTerm σ) : Root (.mul x (.add y z)) (.add (.mul x y) (.mul x z))
  | num_add (p q : ℚ) : Root (.add (.num p) (.num q)) (.num (p + q))
  | num_mul (p q : ℚ) : Root (.mul (.num p) (.num q)) (.num (p * q))
  | pow_zero (x : RTerm σ) : Root (.pow x 0) (.num 1)
  | pow_succ (x : RTerm σ) (n : ℕ) : Root (.pow x (n + 1)) (.mul (.pow x n) x)
  | divn (x : RTerm σ) (q : ℚ) : q ≠ 0 → Root (.divn x q) (.mul x (.num q⁻¹))

/-- One step: a rule at any position. -/
inductive Step : RTerm σ → RTerm σ → Prop
  | root {s t : RTerm σ} : Root s t → Step s t
  | add_l {a a' : RTerm σ} (b : RTerm σ) : Step a a' → Step (.add a b) (.add a' b)
  | add_r (a : RTerm σ) {b b' : RTerm σ} : Step b b' → Step (.add a b) (.add a b')
  | sub_l {a a' : RTerm σ} (b : RTerm σ) : Step a a' → Step (.sub a b) (.sub a' b)
  | sub_r (a : RTerm σ) {b b' : RTerm σ} : Step b b' → Step (.sub a b) (.sub a b')
  | neg {a a' : RTerm σ} : Step a a' → Step (.neg a) (.neg a')
  | mul_l {a a' : RTerm σ} (b : RTerm σ) : Step a a' → Step (.mul a b) (.mul a' b)
  | mul_r (a : RTerm σ) {b b' : RTerm σ} : Step b b' → Step (.mul a b) (.mul a b')
  | pow {a a' : RTerm σ} (n : ℕ) : Step a a' → Step (.pow a n) (.pow a' n)
  | divn {a a' : RTerm σ} (q : ℚ) : Step a a' → Step (.divn a q) (.divn a' q)

/-- `=_Ring`. -/
def Equiv (s t : RTerm σ) : Prop := Relation.EqvGen Step s t

namespace Equiv

open Relation

theorem refl' (t : RTerm σ) : Equiv t t := EqvGen.refl t
theorem symm' {s t : RTerm σ} (h : Equiv s t) : Equiv t s := EqvGen.symm _ _ h
theorem trans' {s t u : RTerm σ} (h1 : Equiv s t) (h2 : Equiv t u) : Equiv s u :=
  EqvGen.trans _ _ _ h1 h2
theorem root {s t : RTerm σ} (r : Root s t) : Equiv s t := EqvGen.rel _ _ (Step.root r)

/-- Congruence: a context lifts `Equiv`. -/
theorem lift {f : RTerm σ → RTerm σ} (hf : ∀ a a', Step a a' → Step (f a) (f a'))
    {a a' : RTerm σ} (h : Equiv a a') : Equiv (f a) (f a') := by
  induction h with
  | rel _ _ h => exact EqvGen.rel _ _ (hf _ _ h)
  | refl => exact EqvGen.refl _
  | symm _ _ _ ih => exact EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact EqvGen.trans _ _ _ ih1 ih2

theorem add {a a' b b' : RTerm σ} (ha : Equiv a a') (hb : Equiv b b') :
    Equiv (.add a b) (.add a' b') :=
  trans' (lift (f := fun x => .add x b) (fun _ _ s => Step.add_l b s) ha)
    (lift (f := fun x => .add a' x) (fun _ _ s => Step.add_r a' s) hb)

theorem sub {a a' b b' : RTerm σ} (ha : Equiv a a') (hb : Equiv b b') :
    Equiv (.sub a b) (.sub a' b') :=
  trans' (lift (f := fun x => .sub x b) (fun _ _ s => Step.sub_l b s) ha)
    (lift (f := fun x => .sub a' x) (fun _ _ s => Step.sub_r a' s) hb)

theorem mul {a a' b b' : RTerm σ} (ha : Equiv a a') (hb : Equiv b b') :
    Equiv (.mul a b) (.mul a' b') :=
  trans' (lift (f := fun x => .mul x b) (fun _ _ s => Step.mul_l b s) ha)
    (lift (f := fun x => .mul a' x) (fun _ _ s => Step.mul_r a' s) hb)

theorem neg {a a' : RTerm σ} (ha : Equiv a a') : Equiv (.neg a) (.neg a') :=
  lift (f := RTerm.neg) (fun _ _ s => Step.neg s) ha

end Equiv

instance setoid (σ : Type*) : Setoid (RTerm σ) where
  r := Equiv
  iseqv := ⟨Equiv.refl', Equiv.symm', Equiv.trans'⟩

/-- The terms modulo the axioms. -/
def Q (σ : Type*) := Quotient (setoid σ)

namespace Q

def mk (t : RTerm σ) : Q σ := Quotient.mk (setoid σ) t

theorem sound {s t : RTerm σ} (h : Equiv s t) : mk s = mk t := Quotient.sound h

theorem ind {p : Q σ → Prop} (h : ∀ t, p (mk t)) (x : Q σ) : p x := Quotient.ind h x

instance : Zero (Q σ) := ⟨mk (.num 0)⟩
instance : One (Q σ) := ⟨mk (.num 1)⟩
instance : Add (Q σ) := ⟨Quotient.map₂ RTerm.add fun _ _ ha _ _ hb => Equiv.add ha hb⟩
instance : Mul (Q σ) := ⟨Quotient.map₂ RTerm.mul fun _ _ ha _ _ hb => Equiv.mul ha hb⟩
instance : Sub (Q σ) := ⟨Quotient.map₂ RTerm.sub fun _ _ ha _ _ hb => Equiv.sub ha hb⟩
instance : Neg (Q σ) := ⟨Quotient.map RTerm.neg fun _ _ ha => Equiv.neg ha⟩

@[simp] theorem mk_add (a b : RTerm σ) : mk a + mk b = mk (.add a b) := rfl
@[simp] theorem mk_mul (a b : RTerm σ) : mk a * mk b = mk (.mul a b) := rfl
@[simp] theorem mk_sub (a b : RTerm σ) : mk a - mk b = mk (.sub a b) := rfl
@[simp] theorem mk_neg (a : RTerm σ) : -mk a = mk (.neg a) := rfl
theorem zero_def : (0 : Q σ) = mk (.num 0) := rfl
theorem one_def : (1 : Q σ) = mk (.num 1) := rfl

theorem r {s t : RTerm σ} (h : Root s t) : mk s = mk t := sound (Equiv.root h)

instance : CommRing (Q σ) where
  add_assoc := by
    intro a b c; induction a using ind; induction b using ind; induction c using ind
    simp only [mk_add]; exact r (Root.add_assoc _ _ _)
  zero_add := by
    intro a; induction a using ind
    rw [zero_def, mk_add, r (Root.add_comm _ _)]; exact r (Root.add_zero _)
  add_zero := by intro a; induction a using ind; rw [zero_def, mk_add]; exact r (Root.add_zero _)
  add_comm := by
    intro a b; induction a using ind; induction b using ind
    simp only [mk_add]; exact r (Root.add_comm _ _)
  mul_assoc := by
    intro a b c; induction a using ind; induction b using ind; induction c using ind
    simp only [mk_mul]; exact r (Root.mul_assoc _ _ _)
  one_mul := by
    intro a; induction a using ind
    rw [one_def, mk_mul, r (Root.mul_comm _ _)]; exact r (Root.mul_one _)
  mul_one := by intro a; induction a using ind; rw [one_def, mk_mul]; exact r (Root.mul_one _)
  zero_mul := by intro a; induction a using ind; rw [zero_def, mk_mul]; exact r (Root.zero_mul _)
  mul_zero := by
    intro a; induction a using ind
    rw [zero_def, mk_mul, r (Root.mul_comm _ _)]; exact r (Root.zero_mul _)
  left_distrib := by
    intro a b c; induction a using ind; induction b using ind; induction c using ind
    simp only [mk_add, mk_mul]; exact r (Root.distrib _ _ _)
  right_distrib := by
    intro a b c
    refine ind (fun x => ?_) a; refine ind (fun y => ?_) b; refine ind (fun z => ?_) c
    simp only [mk_add, mk_mul]
    exact sound (Equiv.trans' (Equiv.root (Root.mul_comm _ _))
      (Equiv.trans' (Equiv.root (Root.distrib _ _ _))
        (Equiv.add (Equiv.root (Root.mul_comm _ _)) (Equiv.root (Root.mul_comm _ _)))))
  mul_comm := by
    intro a b; induction a using ind; induction b using ind
    simp only [mk_mul]; exact r (Root.mul_comm _ _)
  neg_add_cancel := by
    intro a; induction a using ind; rw [mk_neg, mk_add, zero_def]; exact r (Root.neg_add _)
  sub_eq_add_neg := by
    intro a b; induction a using ind; induction b using ind
    rw [mk_sub, mk_neg, mk_add]; exact r (Root.sub _ _)
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Numerals: `q ↦ [q]` is a ring map `ℚ →+* Q σ`. -/
def numHom : ℚ →+* Q σ where
  toFun q := mk (.num q)
  map_one' := rfl
  map_mul' p q := (r (Root.num_mul p q)).symm
  map_zero' := rfl
  map_add' p q := (r (Root.num_add p q)).symm

instance : Algebra ℚ (Q σ) := RingHom.toAlgebra numHom

@[simp] theorem algebraMap_eq (q : ℚ) : algebraMap ℚ (Q σ) q = mk (.num q) := rfl

theorem mk_pow (a : RTerm σ) (n : ℕ) : mk a ^ n = mk (.pow a n) := by
  induction n with
  | zero => rw [pow_zero, one_def]; exact (r (Root.pow_zero a)).symm
  | succ n ih => rw [pow_succ, ih, mk_mul]; exact (r (Root.pow_succ a n)).symm

end Q

/-! ## The interpretation in `MvPolynomial σ ℚ` and its soundness -/

open MvPolynomial

/-- `φ_Ring`: the polynomial a term denotes (`divn a 0` gives `0`, as in Mathlib). -/
noncomputable def phi : RTerm σ → MvPolynomial σ ℚ
  | .num q => C q
  | .atom a => X a
  | .add a b => phi a + phi b
  | .sub a b => phi a - phi b
  | .neg a => - phi a
  | .mul a b => phi a * phi b
  | .pow a n => phi a ^ n
  | .divn a q => phi a * C q⁻¹

theorem phi_root {s t : RTerm σ} (h : Root s t) : phi s = phi t := by
  cases h <;> simp [phi, map_add, map_mul, pow_succ] <;> ring_nf

/-- Soundness ("→" of R4): every axiom holds in `MvPolynomial σ ℚ`. -/
theorem phi_step {s t : RTerm σ} (h : Step s t) : phi s = phi t := by
  induction h with
  | root r => exact phi_root r
  | _ => simp_all [phi]

theorem phi_equiv {s t : RTerm σ} (h : Equiv s t) : phi s = phi t := by
  induction h with
  | rel _ _ h => exact phi_step h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## The universal property: `ψ ∘ φ = [·]` -/

/-- `ψ`: the `ℚ`-algebra map `MvPolynomial σ ℚ → Q σ` sending `X a` to `[a]`. -/
noncomputable def psi : MvPolynomial σ ℚ →ₐ[ℚ] Q σ := aeval fun a => Q.mk (.atom a)

theorem psi_phi (t : RTerm σ) (ht : t.Defined) : psi (phi t) = Q.mk t := by
  induction t with
  | num q => simp [psi, phi]
  | atom a => simp [psi, phi, aeval_X]
  | add a b iha ihb => simp only [phi, map_add, iha ht.1, ihb ht.2, Q.mk_add]
  | sub a b iha ihb => simp only [phi, map_sub, iha ht.1, ihb ht.2, Q.mk_sub]
  | neg a iha => simp only [phi, map_neg, iha ht, Q.mk_neg]
  | mul a b iha ihb => simp only [phi, map_mul, iha ht.1, ihb ht.2, Q.mk_mul]
  | pow a n iha => simp only [phi, map_pow, iha ht, Q.mk_pow]
  | divn a q iha =>
    have hc : psi (C q⁻¹ : MvPolynomial σ ℚ) = Q.mk (.num q⁻¹) := by simp [psi]
    simp only [phi, map_mul, iha ht.1, hc, Q.mk_mul]
    exact (Q.r (Root.divn a q ht.2)).symm

/-- **R4**: for terms without division by the numeral `0`, `s =_Ring t` exactly when they
denote the same polynomial over `ℚ` in the atoms. -/
theorem R4_equiv_iff {s t : RTerm σ} (hs : s.Defined) (ht : t.Defined) :
    Equiv s t ↔ phi s = phi t := by
  refine ⟨phi_equiv, fun h => ?_⟩
  have : Q.mk s = Q.mk t := by rw [← psi_phi s hs, ← psi_phi t ht, h]
  exact Quotient.exact this

/-! ## E2: evaluation into a commutative `ℚ`-algebra is the universal map -/

section E2

variable {D : Type*} [CommRing D] [Algebra ℚ D] (f : σ → D)

/-- Evaluation of a term in `D` with the atoms sent by `f` (`eval` of decision 0011). -/
def evalD : RTerm σ → D
  | .num q => algebraMap ℚ D q
  | .atom a => f a
  | .add a b => evalD a + evalD b
  | .sub a b => evalD a - evalD b
  | .neg a => - evalD a
  | .mul a b => evalD a * evalD b
  | .pow a n => evalD a ^ n
  | .divn a q => evalD a * algebraMap ℚ D q⁻¹

/-- E2: evaluation is `aeval f ∘ φ`, i.e. it factors through the polynomial ring. -/
theorem E2_eval_eq_aeval (t : RTerm σ) : evalD f t = aeval f (phi t) := by
  induction t with
  | num q => simp [evalD, phi]
  | atom a => simp [evalD, phi, aeval_X]
  | add a b iha ihb => simp [evalD, phi, iha, ihb]
  | sub a b iha ihb => simp [evalD, phi, iha, ihb]
  | neg a iha => simp [evalD, phi, iha]
  | mul a b iha ihb => simp [evalD, phi, iha, ihb]
  | pow a n iha => simp [evalD, phi, iha]
  | divn a q iha => simp [evalD, phi, iha]

/-- E2: evaluation respects `=_Ring`: `eval` is well defined on `SymbolicTerm(R, A)`. -/
theorem E2_eval_respects {s t : RTerm σ} (h : Equiv s t) : evalD f s = evalD f t := by
  rw [E2_eval_eq_aeval, E2_eval_eq_aeval, phi_equiv h]

/-- E2: `aeval f` is the only `ℚ`-algebra map `MvPolynomial σ ℚ → D` extending `f`;
so `eval` is the unique homomorphism of decision 0011. -/
theorem E2_unique (g : MvPolynomial σ ℚ →ₐ[ℚ] D) (hg : ∀ a, g (X a) = f a) : g = aeval f :=
  algHom_ext fun a => by rw [hg, aeval_X]

end E2

end FricasSymbolic.Ring
