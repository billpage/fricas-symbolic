import FricasSymbolic.Term
import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.Algebra.Field.Rat

/-!
# Partial evaluation (spec §2.2)

`eval ρ t` is the value of `t` in a field `K` of characteristic zero, with the
variables given by `ρ`, or `none` where `t` divides by zero.

The hypotheses on `K` are those FriCAS provides for the value domain
`Expression R` of `GeneralSymbolicExpression(R, A)`: `R` is a `GcdDomain` with
`CharacteristicZero`, so `Expression R` is a `Field` with `CharacteristicZero`,
and `=` is decidable (`SetCategory`). In Mathlib these are `Field K`,
`CharZero K` and `DecidableEq K`. `Expression R` is itself such a `K`, with `ρ`
sending each variable to itself, so a theorem for every such `K` and `ρ`
includes the statement about `Expression R`.

As in `Expression`, `x / 0` and `0 ^ n` with `n < 0` are undefined, and
`0 ^ 0 = 1`.
-/

namespace FricasSymbolic

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

namespace Term

/-- Partial evaluation, spec §2.2. -/
def eval (ρ : String → K) : Term → Option K
  | num q => some (q : K)
  | var s => some (ρ s)
  | add a b => do let x ← eval ρ a; let y ← eval ρ b; pure (x + y)
  | sub a b => do let x ← eval ρ a; let y ← eval ρ b; pure (x - y)
  | neg a => do let x ← eval ρ a; pure (-x)
  | mul a b => do let x ← eval ρ a; let y ← eval ρ b; pure (x * y)
  | div a b => do
      let x ← eval ρ a; let y ← eval ρ b
      if y = 0 then none else pure (x / y)
  | pow a n => do
      let x ← eval ρ a
      if x = 0 ∧ n < 0 then none else pure (x ^ n)

/-- `s` refines `t`: wherever `t` is defined, `s` is defined with the same value
(spec §2.3, condition (S), for partial evaluation). -/
def Refines (s t : Term) : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] [DecidableEq K] (ρ : String → K) (v : K),
    t.eval ρ = some v → s.eval ρ = some v

end Term
end FricasSymbolic
