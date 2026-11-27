import FricasSymbolic.Term

/-!
# The normaliser of `GeneralSymbolicExpression(R, A)`, mirrored from the Spad code

Plan §3.3. `Ax` stands for the parameter `A`, restricted to the presentation
groups (spec §4.1) and associativity (spec §4.1.1). The smart constructors
follow the clauses of `+`, `-`, `*`, `/` and `^` in `src/algebra/gsexpr.spad`
(after the comment "Presentation axioms") in the same order, keeping only the
clauses that can fire for such an `A`. `nf` builds a term bottom-up, as the
domain does.

Where the Lean functions differ from the Spad code (plan §3.3):

* Each Spad constructor first computes `value x ∘ value y` in `Expression R`,
  which raises an error on a zero denominator. The Lean constructors are
  total and skip that check.
* Num does not fold `n / 0` or `0 ^ e` with `e < 0` (FriCAS raises an error,
  Mathlib's `ℚ` would give `0`); those clauses fall through.
* The (AN) clause `first kids x + (second kids x + y)` is written with the
  numeral already folded: under (AN) both are numerals, so Num fires first.
* The flags `an` and `negzero` (default `true`) do not exist in the package; they
  switch (AN) and Id's `-0 → 0` (decision 0012) off for the regression theorems L7
  and L10.
-/

namespace FricasSymbolic

/-- The axiom groups of `A` (spec §4.1, §4.1.1). -/
structure Ax where
  id : Bool := false
  ann : Bool := false
  inv : Bool := false
  num : Bool := false
  assoc : Bool := false
  /-- (AN) as part of `associativity` with `numerals`; only L7 sets it to `false`. -/
  an : Bool := true
  /-- `-0 → 0` as part of `identities` (decision 0012); only L10 sets it to `false`. -/
  negzero : Bool := true
  deriving DecidableEq, Repr

namespace Term

/-- Is the term a numeral (`numeral?` in the Spad code)? -/
def isNum : Term → Bool
  | num _ => true
  | _ => false

/-- The value of a numeral (`numVal`); `0` for other terms, where it is never used. -/
def nv : Term → ℚ
  | num q => q
  | _ => 0

/-- `lit?(t, n)`: a numeral of value `n`. -/
def isLit (t : Term) (n : ℚ) : Bool := t.isNum && t.nv == n

def isAdd : Term → Bool
  | add _ _ => true
  | _ => false

def isMul : Term → Bool
  | mul _ _ => true
  | _ => false

def isNeg : Term → Bool
  | neg _ => true
  | _ => false

def isDiv : Term → Bool
  | div _ _ => true
  | _ => false

/-- First operand of a node (`first kids`). -/
def fst : Term → Term
  | add a _ | sub a _ | mul a _ | div a _ => a
  | neg a | pow a _ => a
  | t => t

/-- Second operand of a binary node (`second kids`). -/
def snd : Term → Term
  | add _ b | sub _ b | mul _ b | div _ b => b
  | t => t

theorem size_fst_lt_of_isAdd {t : Term} (h : t.isAdd = true) : t.fst.size < t.size := by
  cases t <;> simp_all [isAdd, fst, size]; omega

theorem size_snd_lt_of_isAdd {t : Term} (h : t.isAdd = true) : t.snd.size < t.size := by
  cases t <;> simp_all [isAdd, snd, size]; omega

theorem size_fst_lt_of_isMul {t : Term} (h : t.isMul = true) : t.fst.size < t.size := by
  cases t <;> simp_all [isMul, fst, size]; omega

theorem size_snd_lt_of_isMul {t : Term} (h : t.isMul = true) : t.snd.size < t.size := by
  cases t <;> simp_all [isMul, snd, size]; omega

theorem size_of_isNum {t : Term} (h : t.isNum = true) : t.size = 1 := by
  cases t <;> simp_all [isNum, size]

end Term

open Term

variable (A : Ax)

/-- `x + y` (gsexpr.spad). -/
def sAdd (x y : Term) : Term :=
  if A.num && x.isNum && y.isNum then .num (x.nv + y.nv)
  else if A.id && x.isLit 0 then y
  else if A.id && y.isLit 0 then x
  else if h : A.assoc && y.isAdd then
    -- (A): x+(y1+y2) -> (x+y1)+y2
    have : y.fst.size < y.size := size_fst_lt_of_isAdd (by simp_all)
    have : y.snd.size < y.size := size_snd_lt_of_isAdd (by simp_all)
    sAdd (sAdd x y.fst) y.snd
  else if h : A.assoc && A.num && A.an && y.isNum && x.isAdd && x.snd.isNum then
    -- (AN): (x1+n)+m -> x1+k, k = n+m
    have : x.fst.size < x.size := size_fst_lt_of_isAdd (by simp_all)
    have : (Term.num (x.snd.nv + y.nv)).size = y.size := by
      rw [size_of_isNum (t := y) (by simp_all)]; rfl
    sAdd x.fst (.num (x.snd.nv + y.nv))
  else .add x y
termination_by (y.size, x.size)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ ‹_›
    | exact Prod.Lex.right' _ (le_of_eq ‹_›) ‹_›

/-- `- x` (gsexpr.spad). -/
def sNeg (x : Term) : Term :=
  if A.num && x.isNum then .num (- x.nv)
  else if A.id && A.negzero && x.isLit 0 then .num 0
  else if A.inv && x.isNeg then x.fst
  else .neg x

/-- `x - y` (gsexpr.spad). -/
def sSub (x y : Term) : Term :=
  if A.num && x.isNum && y.isNum then .num (x.nv - y.nv)
  else if A.id && y.isLit 0 then x
  else if A.id && x.isLit 0 then sNeg A y
  else .sub x y

/-- `x * y` (gsexpr.spad). -/
def sMul (x y : Term) : Term :=
  if A.num && x.isNum && y.isNum then .num (x.nv * y.nv)
  else if A.ann && (x.isLit 0 || y.isLit 0) then .num 0
  else if A.id && x.isLit 1 then y
  else if A.id && y.isLit 1 then x
  else if h : A.assoc && y.isMul then
    have : y.fst.size < y.size := size_fst_lt_of_isMul (by simp_all)
    have : y.snd.size < y.size := size_snd_lt_of_isMul (by simp_all)
    sMul (sMul x y.fst) y.snd
  else if h : A.assoc && A.num && A.an && y.isNum && x.isMul && x.snd.isNum then
    have : x.fst.size < x.size := size_fst_lt_of_isMul (by simp_all)
    have : (Term.num (x.snd.nv * y.nv)).size = y.size := by
      rw [size_of_isNum (t := y) (by simp_all)]; rfl
    sMul x.fst (.num (x.snd.nv * y.nv))
  else .mul x y
termination_by (y.size, x.size)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ ‹_›
    | exact Prod.Lex.right' _ (le_of_eq ‹_›) ‹_›

/-- `x / y` (gsexpr.spad). Num does not fold a zero denominator. -/
def sDiv (x y : Term) : Term :=
  if A.num && x.isNum && y.isNum && y.nv != 0 then .num (x.nv / y.nv)
  else if A.id && y.isLit 1 then x
  else if A.inv && x.isLit 1 && y.isDiv && y.fst.isLit 1 then y.snd
  else .div x y

/-- `x ^ n` for an integer `n` (gsexpr.spad). Num does not fold `0 ^ n` with `n < 0`. -/
def sPow (x : Term) (n : ℤ) : Term :=
  if A.num && x.isNum && !(x.nv == 0 && decide (n < 0)) then .num (x.nv ^ n)
  else if A.id && n == 1 then x
  else if A.id && n == 0 then .num 1
  else .pow x n

/-- The normal form: the term as the domain builds it, bottom-up. -/
def nf : Term → Term
  | .num q => .num q
  | .var s => .var s
  | .add a b => sAdd A (nf a) (nf b)
  | .sub a b => sSub A (nf a) (nf b)
  | .neg a => sNeg A (nf a)
  | .mul a b => sMul A (nf a) (nf b)
  | .div a b => sDiv A (nf a) (nf b)
  | .pow a n => sPow A (nf a) n

end FricasSymbolic
