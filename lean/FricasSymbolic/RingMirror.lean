import FricasSymbolic.Order

/-!
# The Ring rung of `GeneralSymbolicExpression`, mirrored from the Spad code

Plan §5.3 (option 2) and §5.5. The Spad constructors of the rung `ring` are
`fromF ∘ op ∘ toF` (`ring1`, `ring2` in `src/algebra/gsexpr.spad`): the atoms of the
operands (`ratoms`) are read as variables, the operands as polynomials (`toF`), and
the result is rebuilt as a tree (`fromF`, which for the denominators of this rung is
`linOf`: `toLin`, then `linBuild`, with monomials from `prodBuild`).

This file mirrors that code on the trees of part 2 (`Order.Tree`, the `InputForm`
of a node). The polynomial arithmetic is naive (lists of terms); `linBuild` merges
equal monomials and drops zero coefficients as the Spad code does, so the tree it
builds depends only on the polynomial. The constructors mirror the clauses of `+`,
`-`, `*`, `/` and `^` that can fire for `A ⊇ ring` without `field` and `quotients`.
-/

namespace FricasSymbolic.RingMirror

open FricasSymbolic.Order Tree

/-! ## Trees as Spad nodes -/

mutual
/-- Identity of forms (`sameForm?`). -/
def teq : Tree → Tree → Bool
  | int a, int b => a == b
  | flt a, flt b => a == b
  | sym a, sym b => a == b
  | str a, str b => a == b
  | atom a, atom b => a == b
  | node h as, node g bs => teq h g && teqL as bs
  | _, _ => false
def teqL : List Tree → List Tree → Bool
  | [], [] => true
  | a :: as, b :: bs => teq a b && teqL as bs
  | _, _ => false
end

/-- `numeral?` (exact numerals only: `R = Integer`). -/
def isNum (t : Tree) : Bool := (numeralForm t).isSome

/-- The leaf of a numeral (`numNode`, decision 0010): `n`, `(/ p q)`, negated with `(- …)`. -/
def numNode (q : ℚ) : Tree :=
  let pos (r : ℚ) : Tree :=
    if r.den = 1 then int r.num else node (sym "/") [int r.num, int r.den]
  if q < 0 then node (sym "-") [pos (-q)] else pos q

/-- `intNode`, for integer exponents. -/
def intNode (n : ℤ) : Tree :=
  if n < 0 then node (sym "-") [int (-n)] else int n

def arith (s : String) (l : List Tree) : Tree := node (sym s) l

/-- `intExp`: the exponent of `(^ b e)` when `e` is an exact integer numeral. -/
def intExp : Tree → Option ℤ
  | node (sym "^") [_, e] =>
    match numeralForm e with
    | some (false, q) => if q.den = 1 then some q.num else none
    | _ => none
  | _ => none

/-- `rpow` without `field`: a power with exponent in `ℕ`. -/
def rpow (t : Tree) : Option ℕ :=
  match intExp t with
  | some n => if 0 ≤ n then some n.toNat else none
  | none => none

/-! ## Polynomials over the atoms -/

/-- A polynomial as a list of terms: (factors (atom index, exponent), coefficient). -/
abbrev Poly := List (List (ℕ × ℕ) × ℚ)

def pconst (q : ℚ) : Poly := [([], q)]
def pvar (i : ℕ) : Poly := [([(i, 1)], 1)]
def pneg (p : Poly) : Poly := p.map fun (m, c) => (m, -c)
def pscale (k : ℚ) (p : Poly) : Poly := p.map fun (m, c) => (m, k * c)
def pmul (p q : Poly) : Poly := p.flatMap fun (m, c) => q.map fun (n, d) => (m ++ n, c * d)
def ppow (p : Poly) : ℕ → Poly
  | 0 => pconst 1
  | n + 1 => pmul (ppow p n) p

def addAtom (l : List Tree) (t : Tree) : List Tree :=
  if l.any (teq · t) then l else l ++ [t]

/-- `ratoms`: the atoms of a normal form, in order of first appearance. -/
def ratoms (l : List Tree) (t : Tree) : List Tree :=
  if isNum t then l else
  match t with
  | node (sym "+") [a, b] => ratoms (ratoms l a) b
  | node (sym "-") [a] => ratoms l a
  | node (sym "-") [a, b] => ratoms (ratoms l a) b
  | node (sym "*") [a, b] => ratoms (ratoms l a) b
  | node (sym "/") [a, b] => if isNum b then ratoms (ratoms l a) b else addAtom l t
  | node (sym "^") [b, e] =>
    match rpow (node (sym "^") [b, e]) with
    | some _ => ratoms l b
    | none => addAtom l t
  | _ => addAtom l t

/-- The index of an atom in the atom list. -/
def atomIdx (al : List Tree) (t : Tree) : ℕ := (al.findIdx? (teq · t)).getD 0

/-- `toF`: a normal form as a polynomial in its atoms. -/
def toF (al : List Tree) (t : Tree) : Poly :=
  if isNum t then pconst (val t) else
  match t with
  | node (sym "+") [a, b] => toF al a ++ toF al b
  | node (sym "-") [a] => pneg (toF al a)
  | node (sym "-") [a, b] => toF al a ++ pneg (toF al b)
  | node (sym "*") [a, b] => pmul (toF al a) (toF al b)
  | node (sym "/") [a, b] =>
    if isNum b then pscale (val b)⁻¹ (toF al a) else pvar (atomIdx al t)
  | node (sym "^") [b, e] =>
    match rpow (node (sym "^") [b, e]) with
    | some n => ppow (toF al b) n
    | none => pvar (atomIdx al t)
  | _ => pvar (atomIdx al t)

/-! ## Read-back: `prodBuild`, `linBuild` -/

/-- Insertion of `a` into a list sorted by the term order. -/
def insertLt (a : Tree) : List Tree → List Tree
  | [] => [a]
  | b :: bs => if lt a b then a :: b :: bs else b :: insertLt a bs

def sortLt (l : List Tree) : List Tree := l.foldr insertLt []

/-- `mergeF`: factors with the same base merged, exponent sums `0` dropped. -/
def mergeF (fs : List (Tree × ℤ)) : List (Tree × ℤ) :=
  let ms := fs.foldl (fun acc (b, e) =>
    match acc.findIdx? (fun g => teq g.1 b) with
    | some i => acc.modify i (fun g => (g.1, g.2 + e))
    | none => acc ++ [(b, e)]) []
  ms.filter (·.2 ≠ 0)

/-- `facNode`. -/
def facNode (b : Tree) (e : ℤ) : Tree := if e = 1 then b else arith "^" [b, intNode e]

/-- `mulChain`: the numeral (left out if `1` and there are factors), then the factors. -/
def mulChain (c : ℚ) (l : List Tree) : Tree :=
  let l := if c ≠ 1 ∨ l = [] then numNode c :: l else l
  match l with
  | [] => numNode c
  | r :: rs => rs.foldl (fun acc t => arith "*" [acc, t]) r

/-- The sorted factor trees of a monomial (`prodBuild` with positive exponents). -/
def facTrees (al : List Tree) (m : List (ℕ × ℕ)) : List Tree :=
  sortLt ((mergeF (m.map fun (i, e) => (al.getD i (int 0), (e : ℤ)))).map
    fun (b, e) => facNode b e)

/-- `mergeT`: terms with the same monomial merged, coefficient sums `0` dropped. -/
def mergeT (ts : List (List Tree × ℚ)) : List (List Tree × ℚ) :=
  let key (fs : List Tree) : Tree := mulChain 1 fs
  let ms := ts.foldl (fun acc (fs, c) =>
    match acc.findIdx? (fun g => teq (key g.1) (key fs)) with
    | some i => acc.modify i (fun g => (g.1, g.2 + c))
    | none => acc ++ [(fs, c)]) []
  ms.filter (·.2 ≠ 0)

def insertTerm (a : List Tree × ℚ) : List (List Tree × ℚ) → List (List Tree × ℚ)
  | [] => [a]
  | b :: bs => if lt (mulChain 1 a.1) (mulChain 1 b.1) then a :: b :: bs else b :: insertTerm a bs

/-- `linBuild`: terms by monomial, the first negated if negative, the others added or
subtracted, the constant last. -/
def linBuild (c0 : ℚ) (ts : List (List Tree × ℚ)) : Tree :=
  let ms := (mergeT ts).foldr insertTerm []
  match ms with
  | [] => numNode c0
  | (fs, c) :: rest =>
    let trm (fs : List Tree) (c : ℚ) : Tree := if |c| = 1 then mulChain 1 fs else mulChain |c| fs
    let first := if 0 < c then trm fs c else arith "-" [trm fs c]
    let acc := rest.foldl (fun acc (fs, c) =>
      if 0 < c then arith "+" [acc, trm fs c] else arith "-" [acc, trm fs c]) first
    if c0 = 0 then acc
    else if 0 < c0 then arith "+" [acc, numNode |c0|] else arith "-" [acc, numNode |c0|]

/-- `linOf ∘ toLin`: the tree of a polynomial (the constant denominators of this rung). -/
def fromP (al : List Tree) (p : Poly) : Tree :=
  let c0 := (p.filter (·.1 = [])).foldl (fun s t => s + t.2) 0
  let ts := (p.filter (·.1 ≠ [])).map fun (m, c) => (facTrees al m, c)
  linBuild c0 ts

def ring1 (x : Tree) (f : Poly → Poly) : Tree :=
  let al := ratoms [] x
  fromP al (f (toF al x))

def ring2 (x y : Tree) (f : Poly → Poly → Poly) : Tree :=
  let al := ratoms (ratoms [] x) y
  fromP al (f (toF al x) (toF al y))

/-! ## The constructors of the rung `ring` -/

/-- The optional groups that change the Ring constructors' clauses. -/
structure RAx where
  ann : Bool := false
  inv : Bool := false

variable (A : RAx)

def lit (t : Tree) (q : ℚ) : Bool := isNum t && val t == q

def rAdd (x y : Tree) : Tree :=
  if isNum x && isNum y then numNode (val x + val y) else ring2 x y (· ++ ·)

def rSub (x y : Tree) : Tree :=
  if isNum x && isNum y then numNode (val x - val y) else ring2 x y (fun a b => a ++ pneg b)

def rNeg (x : Tree) : Tree :=
  if isNum x then numNode (- val x) else ring1 x pneg

def rMul (x y : Tree) : Tree :=
  if isNum x && isNum y then numNode (val x * val y)
  else if A.ann && (lit x 0 || lit y 0) then numNode 0
  else if lit x 1 then y
  else if lit y 1 then x
  else ring2 x y pmul

/-- `x / y`: by a numeral through the polynomial ring; otherwise an atom (no `quotients`). -/
def rDiv (x y : Tree) : Tree :=
  if isNum x && isNum y then numNode (val x / val y)
  else if isNum y then ring2 x y (fun a _ => pscale (val y)⁻¹ a)
  else if A.inv && lit x 1 then
    match y with
    | node (sym "/") [a, b] => if lit a 1 then b else arith "/" [x, y]
    | _ => arith "/" [x, y]
  else arith "/" [x, y]

def rPow (x : Tree) (n : ℤ) : Tree :=
  if isNum x then numNode (val x ^ n)
  else if n = 1 then x
  else if n = 0 then numNode 1
  else if 0 ≤ n then ring1 x (fun p => ppow p n.toNat)
  else arith "^" [x, intNode n]

/-! ## Printing and the differential test (with `lean/crosscheck/ringcheck.spad`) -/

mutual
/-- A tree as FriCAS prints an `InputForm` (`PRINC-TO-STRING`, on one line). -/
def str : Tree → String
  | int n => toString n
  | flt q => toString q
  | sym s => s
  | Tree.str s => "\"" ++ s ++ "\""
  | atom s => s
  | node h as => "(" ++ str h ++ strL as ++ ")"
def strL : List Tree → String
  | [] => ""
  | a :: as => " " ++ str a ++ strL as
end

namespace Check

abbrev GenM := StateM ℕ

def nxt : GenM ℕ := modifyGet fun s =>
  let s' := (s * 1103515245 + 12345) % 2147483648
  (s', s')

def pick (n : ℕ) : GenM ℕ := do return (← nxt) / 65536 % n

def leaf (safe : Bool) : GenM Tree := do
  let j ← pick 7
  return match j with
    | 0 => if safe then numNode 3 else numNode 0
    | 1 => numNode 1
    | 2 => numNode 2
    | 3 => numNode (-1)
    | 4 => sym "x"
    | 5 => sym "y"
    | _ => sym "z"

def gen : ℕ → Bool → GenM Tree
  | 0, safe => leaf safe
  | d + 1, true => do
    let k ← pick 4
    match k with
    | 1 => do let a ← gen d true; let b ← gen d true; return rMul A a b
    | 2 => do
      let e : ℤ := ((← pick 5 : ℕ) : ℤ) - 1
      let a ← gen d true
      return rPow a e
    | 3 => do let a ← gen d true; return rNeg a
    | _ => leaf true
  | d + 1, false => do
    let k ← pick 9
    match k with
    | 1 => do let a ← gen d false; let b ← gen d false; return rAdd a b
    | 2 => do let a ← gen d false; let b ← gen d false; return rSub a b
    | 3 => do let a ← gen d false; return rNeg a
    | 4 => do let a ← gen d false; let b ← gen d false; return rMul A a b
    | 5 => do
      let a ← gen d false; let c : ℚ := ((← pick 4 : ℕ) : ℚ) + 1
      return rDiv A a (numNode c)
    | 6 => do let a ← gen d false; let b ← gen d true; return rDiv A a b
    | 7 => do
      let e : ℤ := ((← pick 5 : ℕ) : ℤ) - 1
      let a ← gen d (decide (e < 0))
      return rPow a e
    | _ => leaf false

def checksum (l : List String) : ℕ :=
  l.foldl (fun h s => ((s.foldl (fun h c => (h * 31 + c.toNat) % 1000000007) h) * 31 + 59)
    % 1000000007) 0

def forms (s0 n d : ℕ) : List String :=
  (((List.range n).mapM fun _ => gen A d false).run' s0).map str

/-- `[n, checksum]`, as `run(s0, n, d)$LeanRingCheck(A)` returns it. -/
def run (s0 n d : ℕ) : List ℕ := [n, checksum (forms A s0 n d)]

end Check

end FricasSymbolic.RingMirror
