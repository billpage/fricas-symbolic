import FricasSymbolic.Term

/-!
# Printing terms as FriCAS prints their `InputForm`

Used to compare `nf` with `GeneralSymbolicExpression` on the same inputs (skill
`lean`, "Verification across systems"). A negative numeral prints as `(- n)` and
a fraction as `(/ p q)`, as decision 0010 writes numerals.
-/

namespace FricasSymbolic.Term

/-- A numeral as FriCAS prints its form. -/
def numForm (q : ℚ) : String :=
  let pos (r : ℚ) : String :=
    if r.den = 1 then toString r.num else s!"(/ {r.num} {r.den})"
  if q < 0 then s!"(- {pos (-q)})" else pos q

/-- The form of a term, as FriCAS prints an `InputForm`. -/
def toForm : Term → String
  | num q => numForm q
  | var s => s
  | add a b => s!"(+ {a.toForm} {b.toForm})"
  | sub a b => s!"(- {a.toForm} {b.toForm})"
  | neg a => s!"(- {a.toForm})"
  | mul a b => s!"(* {a.toForm} {b.toForm})"
  | div a b => s!"(/ {a.toForm} {b.toForm})"
  | pow a n => s!"(^ {a.toForm} {numForm n})"

end FricasSymbolic.Term
