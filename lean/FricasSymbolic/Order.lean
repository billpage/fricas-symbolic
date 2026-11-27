import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Order.Basic

/-!
# Part 2: the term order (spec §3.5, Prop. 4)

`Tree` models `InputForm` trees; `lt` mirrors `smaller?` of `SymbolicTermOrder`
(`src/algebra/gsexpr.spad`) clause by clause, with `numeralForm` and `kind` as in the
Spad code. Float numerals (decision 0010) are included: a float atom is modelled by its
exact value (`mantissa · 2^exponent`, as `numeralForm` computes it), a float literal
`(float m e b)` or `(($elt DoubleFloat float) m e b)` by its tree.

Modelling choices, each checked against FriCAS (runs `20261126-232443-order-probe`,
`…-232458-order-probe-2`) or stated as an assumption:

* `Symbol`'s `smaller?` and `String`'s `<` are the lexicographic order by character
  code, which is Lean's order on `String` (checked).
* A float atom is determined by its value: integral doubles convert to integer atoms,
  and `0.0`, `-0.0` both to the integer `0` (checked), so two distinct float atoms have
  distinct values.
* Any other atom is compared by `unparse`, so it is modelled by that string; this
  assumes `unparse` is injective on such atoms (assumption).
-/

namespace FricasSymbolic.Order

/-- `InputForm` trees: atoms, and compound forms `(head arg₁ … argₙ)`. -/
inductive Tree where
  | int : ℤ → Tree
  | flt : ℚ → Tree
  | sym : String → Tree
  | str : String → Tree
  | atom : String → Tree
  | node : Tree → List Tree → Tree
  deriving Repr, Inhabited

namespace Tree

/-- `floatHead?`: the symbol `float`, or `($elt D float)`. -/
def floatHead : Tree → Bool
  | sym s => s == "float"
  | node (sym e) [_, sym f] => e == "$elt" && f == "float"
  | _ => false

/-- `numeralForm`: `(float?, value)` for a numeral, `none` otherwise. -/
def numeralForm : Tree → Option (Bool × ℚ)
  | int n => some (false, n)
  | flt q => some (true, q)
  | node (sym h) [x] =>
      if h == "-" then (numeralForm x).map fun p => (p.1, -p.2) else none
  | node (sym h) [int a, int b] =>
      if h == "/" && b != 0 then some (false, (a : ℚ) / b) else none
  | node h [int m, int e, int b] =>
      if floatHead h && decide (2 ≤ b) then some (true, (m : ℚ) * (b : ℚ) ^ e) else none
  | _ => none

/-- `kind`: 0 exact numeral, 1 float numeral, 2 symbol, 3 string, 4 other atom,
5 compound. -/
def kind (t : Tree) : ℕ :=
  match numeralForm t with
  | some (f, _) => if f then 1 else 0
  | none =>
    match t with
    | sym _ => 2
    | str _ => 3
    | node _ _ => 5
    | _ => 4

/-- The value of a numeral (`0` for other trees, where it is not used). -/
def val (t : Tree) : ℚ := ((numeralForm t).map (·.2)).getD 0

/-- The comparisons of kinds 2–4: symbols, strings and other atoms by their strings;
`none` for two trees of another kind. -/
def atomLt : Tree → Tree → Option Bool
  | sym a, sym b => some (decide (a < b))
  | str a, str b => some (decide (a < b))
  | atom a, atom b => some (decide (a < b))
  | _, _ => none

mutual

/-- `smaller?` of `SymbolicTermOrder`. -/
def lt (s t : Tree) : Bool :=
  if kind s ≠ kind t then decide (kind s < kind t)
  else if kind s ≤ 1 then
    if val s ≠ val t then decide (val s < val t) else structural s t
  else (atomLt s t).getD (structural s t)
termination_by (sizeOf s + sizeOf t, 1)

/-- `structural?`: atoms before compounds; compounds by head, arity, arguments. -/
def structural (s t : Tree) : Bool :=
  match s, t with
  | node hs as, node ht bs =>
    if lt hs ht then true
    else if lt ht hs then false
    else if as.length ≠ bs.length then decide (as.length < bs.length)
    else ltList as bs
  | node _ _, _ => false
  | _, node _ _ => true
  | _, _ => false
termination_by (sizeOf s + sizeOf t, 0)

/-- The argument loop of `structural?`: the first difference decides. -/
def ltList (as bs : List Tree) : Bool :=
  match as, bs with
  | a :: as', b :: bs' =>
    if lt a b then true else if lt b a then false else ltList as' bs'
  | _, _ => false
termination_by (sizeOf as + sizeOf bs, 0)

end

end Tree

/-! ## Differential test against `SymbolicTermOrder` (with `lean/crosscheck/ordercheck.spad`) -/

namespace Check

open Tree

abbrev GenM := StateM ℕ

def nxt : GenM ℕ := modifyGet fun s =>
  let s' := (s * 1103515245 + 12345) % 2147483648
  (s', s')

def pick (n : ℕ) : GenM ℕ := do return (← nxt) / 65536 % n

def pickZ (n : ℕ) (off : ℤ) : GenM ℤ := do return ((← pick n : ℕ) : ℤ) - off

def syms : List String := ["x", "y", "X", "a", "float", "-"]
def heads : List String := ["+", "*", "-", "/", "sin", "f"]
def strs : List String := ["", "a", "B", "ab"]
def flts : List ℚ := [5/2, -3/4, 1/2, 3/2, -3/2]

def leaf : GenM Tree := do
  let j ← pick 9
  match j with
  | 0 => return int (← pickZ 7 3)
  | 1 => return int (← pick 3 : ℕ)
  | 2 => return flt (flts.getD (← pick 5) 0)
  | 3 | 4 => return sym (syms.getD (← pick 6) "x")
  | 5 => return str (strs.getD (← pick 4) "")
  | 6 => return int 2
  | 7 => return flt (1/2)
  | _ => return sym "x"

def gen : ℕ → GenM Tree
  | 0 => leaf
  | d + 1 => do
    let k ← pick 10
    match k with
    | 4 => do let a ← gen d; return node (sym "-") [a]
    | 5 => do
      let a ← pickZ 7 3; let b ← pickZ 5 2
      return node (sym "/") [int a, int b]
    | 6 => do
      let m ← pickZ 7 3; let e ← pickZ 5 2; let b ← pick 4
      return node (sym "float") [int m, int e, int b]
    | 7 => do
      let m ← pickZ 7 3; let e ← pickZ 5 2
      return node (node (sym "$elt") [sym "DoubleFloat", sym "float"]) [int m, int e, int 2]
    | 8 => do
      let h ← gen d; let n ← pick 3
      let args ← (List.range n).mapM fun _ => gen d
      return node h args
    | 9 => do
      let h := heads.getD (← pick 6) "f"; let n ← pick 3
      let args ← (List.range n).mapM fun _ => gen d
      return node (sym h) args
    | _ => leaf

/-- `[n, number of true comparisons, checksum]` over all ordered pairs of `n` trees of
depth `d` from seed `s0`, as `run(s0, n, d)$LeanOrderCheck` computes it. -/
def run (s0 n d : ℕ) : List ℕ :=
  let ts := ((List.range n).mapM fun _ => gen d).run' s0
  let bs := ts.flatMap fun a => ts.map fun b => lt a b
  [n, bs.count true, bs.foldl (fun h b => (h * 3 + (if b then 2 else 1)) % 1000000007) 0]

end Check

end FricasSymbolic.Order
