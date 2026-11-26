import Mathlib.Algebra.Field.Rat

/-!
# Terms of `GeneralSymbolicExpression(ℤ, A)`, version 1

Plan `docs/plans/lean-presentation-axioms.md` §3.1. Numerals are constants of
`Frac ℤ = ℚ`; exponents are integers. Named functions and rational exponents
are left out of version 1.
-/

namespace FricasSymbolic

/-- Terms of `GeneralSymbolicExpression(ℤ, A)`, version 1. -/
inductive Term where
  | num : ℚ → Term
  | var : String → Term
  | add : Term → Term → Term
  | sub : Term → Term → Term
  | neg : Term → Term
  | mul : Term → Term → Term
  | div : Term → Term → Term
  | pow : Term → ℤ → Term
  deriving DecidableEq, Repr

namespace Term

/-- Number of nodes, `|t|` in spec §4.1.1. -/
def size : Term → ℕ
  | num _ | var _ => 1
  | add a b | sub a b | mul a b | div a b => a.size + b.size + 1
  | neg a | pow a _ => a.size + 1

/-- `μ(t)`, spec §4.1.1: the sum of `|r(u)|` over the `+` and `·` nodes `u` of `t`,
where `r(u)` is the right operand. -/
def mu : Term → ℕ
  | num _ | var _ => 0
  | add a b | mul a b => a.mu + b.mu + b.size
  | sub a b | div a b => a.mu + b.mu
  | neg a | pow a _ => a.mu

theorem size_pos (t : Term) : 0 < t.size := by
  cases t <;> simp [size]

end Term
end FricasSymbolic
