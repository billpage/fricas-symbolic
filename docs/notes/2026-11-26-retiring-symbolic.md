# Retiring the 2017 `Symbolic(R, A)`

*2026-11-26. Plan step 6 ([plan](../plans/symbolic-ladder.md)), decision [0008](../decisions/0008-ladder-of-normalisers.md).*

## What was removed

`src/algebra/sexpr.spad`, with the 2017 `Symbolic(R, A)`, its axiom categories and domains (`Squares`, `Inverse`, `Doubles`, …), `join`, `SINFunctions`, `SymbolicDistributedExpression` and `SymbolicFunctions1`; its tests `src/input/sexpr2.input` (Kurt Pagani's 2017 suite) and the session script `src/input/sexpr.input`; and the `make check-sexpr` target. The last commit with them is `b1c3820`. Before this repository they lived on branch `symbolic-expressions` of billpage/fricas-dev (formerly billpage/fricas), commit `933c5bb`, whose history was carried over here.

Design (II) is now `SymbolicTerm(R, A)`, and design (I) is `GeneralSymbolicExpression(R, A)`. Both share the normalisers of spec §3.4, which replace the 2017 axiom domains. Those rewrote binary trees by an order never shown to terminate (§4.2), and needed `)lib` to be run twice.

## The 2017 axiom set as groups

| 2017 axiom domain | Group |
|---|---|
| `Identities` (`LeftIdentity`, `RightIdentity`) | `identities` |
| `Annihilation` | `annihilation` |
| `Inverse` | `involutions` |
| `AssociativePlus`, `AssociativeTimes` | `associativity` |
| `CommutativePlus`, `CommutativeTimes` | `commutativity` |
| `Doubles`, `Cancels` | `linear` |
| `Squares` | `powers` |
| `Divides` | `quotients` |
| `Distributive` | `ring` |
| (numerals folded without an axiom) | `numerals` |
| `AntiCommutative` | none: unsound for `Expression` (§4.2) |

The groups apply to $`+`$ and $`\cdot`$ together, while some 2017 domains applied to one operator only. A group also needs the groups it requires (decision 0009). So `Symbolic(Integer, Doubles)` alone has no counterpart: P4 needs commutativity, associativity, identities and numerals.

## The tests of `sexpr2.input`

| 2017 test | Disposition |
|---|---|
| ex1: `1+1+1` kept, value 3 | Ported to `symterm.input`, "ported from sexpr2 ex1" |
| ex1: `simplify`, `retract` to `PositiveInteger` and `AlgebraicNumber` | Interface of `SymbolicTerm`, open (below) |
| ex2, ex3: the laws $`x+x=2x`$, $`x-x=0`$, C, A, $`x\cdot x=x^2`$, $`x/x=1`$, $`x(1/x)=1`$; no distributivity; $`(x+y)^2`$ by value; $`\sum_{n=1}^{10} n = 55`$ | Ported, "ported from sexpr2 ex2, ex3" |
| ex2: `smaller?` | The 2017 order is replaced by $`\prec`$ (§3.5), tested in gsexpr "Ord" |
| ex2: `factor`, `expand`, `variables`, `kernels`, `numer`/`denom` with boxed kernels, `tan` and inverse trig functions, `map(simplify, …)` | Interface of `SymbolicTerm`, open; all available in `GeneralSymbolicExpression`, which is an `AlgebraicallyClosedFunctionSpace` |
| ex3: `sum(x, 'x=1..10)`, `operator`, `D` | Design (I): gsexpr "summation and limits are correct"; for `SymbolicTerm`, open |
| ex3: `convert` to `InputForm`, `coerce` to `OutputForm` | `SymbolicTerm` exports both; (Disp) tests |
| ex4: rewrite rules (G4) | Design (I): gsexpr "rewrite rules act on the expression as written"; for `SymbolicTerm`, open (needs pattern matching) |
| Doubles: coefficient on either side | Ported, "ported from sexpr2: Doubles" |
| G3: no axioms keep the written form | Ported, "ported from sexpr2: G3", except `x^(2/3)`: `SymbolicTerm` exports `^` with `Integer` exponents only |

## Open: the interface of `SymbolicTerm`

`SymbolicTerm(R, A)` exports `SetCategory`, `ConvertibleTo InputForm`, the arithmetic, a few elementary functions, `form` and the value in `Expression R`. Which further operations and FriCAS categories it should have, possibly depending on $`A`$, is plan §4's question on categories. Examples: `AbelianMonoid` with Id at P3, `CommutativeRing` at Ring, kernels and pattern matching for rewrite rules, differentiation. The answer is a change to spec §3.2 and needs a decision record.
