import FricasSymbolic.Normalize
import FricasSymbolic.Form

/-!
# Differential testing of `nf` against `GeneralSymbolicExpression`

The same pseudo-random terms are generated here and by the Spad package
`LeanCrossCheck` (`lean/crosscheck/crosscheck.spad`), from the same linear
congruential generator. Each side normalises them, prints their forms and
returns the count and a checksum of the printed forms. With `A = ∅` nothing is
normalised, so equal checksums there show that the two generators agree.

Denominators and bases of negative powers are drawn from the "safe" terms
(variables, nonzero numerals, and products, quotients, negations and powers of
safe terms), whose values are nonzero, so FriCAS never raises a division error.
-/

namespace FricasSymbolic.CrossCheck

open Term

abbrev GenM := StateM ℕ

def nxt : GenM ℕ := modifyGet fun s =>
  let s' := (s * 1103515245 + 12345) % 2147483648
  (s', s')

def pick (n : ℕ) : GenM ℕ := do return (← nxt) / 65536 % n

def leaf (safe : Bool) : GenM Term := do
  let j ← pick 7
  return match j with
    | 0 => if safe then .num 3 else .num 0
    | 1 => .num 1
    | 2 => .num 2
    | 3 => .num (-1)
    | 4 => .var "x"
    | 5 => .var "y"
    | _ => .num (1 / 2)

def gen : ℕ → Bool → GenM Term
  | 0, safe => leaf safe
  | d + 1, true => do
      let k ← pick 5
      match k with
      | 0 => leaf true
      | 1 => do let a ← gen d true; let b ← gen d true; return .mul a b
      | 2 => do let a ← gen d true; let b ← gen d true; return .div a b
      | 3 => do let a ← gen d true; return .neg a
      | _ => do
          let e : ℤ := ((← pick 5 : ℕ) : ℤ) - 2
          let a ← gen d true
          return .pow a e
  | d + 1, false => do
      let k ← pick 8
      match k with
      | 1 => do let a ← gen d false; let b ← gen d false; return .add a b
      | 2 => do let a ← gen d false; let b ← gen d false; return .sub a b
      | 3 => do let a ← gen d false; return .neg a
      | 4 => do let a ← gen d false; let b ← gen d false; return .mul a b
      | 5 => do let a ← gen d false; let b ← gen d true; return .div a b
      | 6 => do
          let e : ℤ := ((← pick 5 : ℕ) : ℤ) - 2
          let a ← gen d (decide (e < 0))
          return .pow a e
      | _ => leaf false

/-- Checksum of strings, each followed by `;`, as `LeanCrossCheck` computes it. -/
def checksum (l : List String) : ℕ :=
  l.foldl (fun h s => ((s.foldl (fun h c => (h * 31 + c.toNat) % 1000000007) h) * 31 + 59)
    % 1000000007) 0

/-- `n` terms of depth `d` from seed `s0`, normalised under `A`: their forms. -/
def forms (A : Ax) (s0 n d : ℕ) : List String :=
  (((List.range n).mapM fun _ => gen d false).run' s0).map fun t => (nf A t).toForm

/-- `[n, checksum]`, as `run(s0, n, d)$LeanCrossCheck(A)` returns it. -/
def run (A : Ax) (s0 n d : ℕ) : List ℕ := [n, checksum (forms A s0 n d)]

end FricasSymbolic.CrossCheck
