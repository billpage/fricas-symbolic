# Commutativity and the hidden rewrites in `Symbolic(R, A)`

*2026-11-26. Analysis for design (II), spec §3.2 and §4.2. Not normative; proposals here become spec text through decision records. Runs: FriCAS 1.4.0 release binary, `src/algebra/sexpr.spad` at `main` 546710e…433c732 (unchanged since the port).*

Notation as in the spec (§0): $`T`$ the terms, $`=_A`$ equality modulo the axioms $`A`$, $`\mathrm{nf}`$ a normal form, $`\lvert t\rvert`$ the size. In addition:

| Symbol | Meaning |
|---|---|
| $`\mathrm{C}_\circ`$ | commutativity of $`\circ`$: $`x \circ y \approx y \circ x`$ |
| $`\mathrm{A}_\circ`$ | associativity of $`\circ`$: $`(x \circ y) \circ z \approx x \circ (y \circ z)`$ |
| $`\mathrm{AC}`$ | $`\mathrm{A}_\circ \cup \mathrm{C}_\circ`$ for $`\circ \in \{+, \cdot\}`$ |
| $`\prec`$ | a fixed strict total order on terms |
| $`=_{\mathrm{AC}}`$ | equality modulo AC |

## 1. Why commutativity cannot be a rewrite rule

A rewrite rule $`l \to r`$ needs a reduction order $`>`$ with $`l > r`$, closed under substitution (spec §2.4). For $`x+y \to y+x`$ this is impossible: if $`x + y > y + x`$, the substitution $`\sigma = \{x \mapsto y,\ y \mapsto x\}`$ gives $`y + x > x + y`$, and the two together contradict irreflexivity. Commutativity can only be *built into* equality. That is what "modulo AC" means: rewriting works on AC-equivalence classes,

```math
s \to_{R/\mathrm{AC}} t \iff s =_{\mathrm{AC}} s' \to_R t' =_{\mathrm{AC}} t \ \text{ for some } s', t' .
```

The 2017 code instead sorted operands with `smaller?` during rewriting, as if commutativity were a rule. Whether that terminates depends on `smaller?` being a total order compatible with the other rules, which was never shown, and Bill saw non-termination in 2017 (fricas-devel, "Symbolic (unevaluated) Expressions", 2017-02-10).

## 2. What AC rewriting needs, and what it means for the implementation

### 2.1 The general requirements

1. **Deciding $`=_{\mathrm{AC}}`$.** Flatten nested $`\circ`$ into one $`n`$-ary node (A) and sort its arguments by $`\prec`$ (C). Two terms are AC-equal iff their flattened, sorted forms are identical. Any strict total order $`\prec`$ works for this; it needs no further property.
2. **AC matching.** A rule $`l \to r`$ applies to $`t`$ if some substitution $`\sigma`$ has $`l\sigma =_{\mathrm{AC}} t`$. With flattened terms this means matching $`l`$'s arguments against a sub-multiset of $`t`$'s arguments. In general this is NP-complete (Benanav, Kapur & Narendran 1987), though finitary and cheap for small terms.
3. **Extended rules.** A rule whose root is AC must also apply inside a longer chain: $`x + x \to 2x`$ must rewrite $`a + x + x`$. Peterson & Stickel (1981) add the extension $`l + z \to r + z`$; with flattened terms this is matching against a sub-multiset, as in 2.
4. **Termination modulo AC.** This needs a reduction order compatible with AC: $`s' =_{\mathrm{AC}} s > t =_{\mathrm{AC}} t'`$ implies $`s' > t'`$. Two kinds are available:
   - AC-RPO (Rubio & Nieuwenhuis 1995), which is total on ground terms;
   - polynomial interpretations whose polynomials for $`+`$ and $`\cdot`$ are themselves associative and commutative, for example $`[x+y] = x+y+1`$.
5. **Confluence modulo AC.** Critical pairs are found with AC *unification*, which is finitary but can produce many unifiers (Stickel 1981), and the rule set must also be coherent with AC (Jouannaud & Kirchner 1986). Tools: Maude's Church–Rosser checker, CiME.

Building all of this as a general engine (AC matching, extended rules, a completion check) is a substantial project. Section 2.2 shows the fixed axiom sets of `Symbolic(R, A)` don't need it.

### 2.2 The practical route: normal forms of free structures

The rewrites the 2017 axiom categories apply to $`+`$ follow a pattern: Id ($`0`$), Num (fold numerals), Doubles (namely $`x+x \to 2x`$, more generally $`nx + mx \to (n+m)x`$) and Cancels (namely $`x + (-x) \to 0`$). Together with AC, these are the axioms of an abelian group with integer multiples, i.e. of the **free $`\mathbb{Z}`$-module** on the terms that are not sums. A canonical form of an element is a finite list of pairs (coefficient $`c \ne 0`$, term $`t`$), sorted by $`t`$ under $`\prec`$, plus one numeral for the constant part. Two sums are equal modulo these axioms iff their lists are identical.

The same holds for $`\cdot`$. With AC, $`1`$, Num and Squares (namely $`x \cdot x \to x^2`$, more generally $`x^n x^m \to x^{n+m}`$), a product is a free commutative monoid on its factors. With Divides/Cancels for $`\cdot`$ ($`x \cdot x^{-1} \to 1`$), it is a free abelian group with integer exponents. The canonical form is a sorted list of (factor, exponent $`\ne 0`$) pairs times one numeral.

So for these axiom sets, normalising is not rewriting: it is building the canonical element of a known free structure, as FriCAS's own `Polynomial` and `Expression` build theirs. This has three consequences:

- **AC matching is never needed for the built-in axioms.** After sorting, equal terms are neighbours, so "collect like terms" is a single linear pass.
- **Termination and confluence come for free.** Normalisation is a function into the canonical forms, and $`s =_A t \iff \mathrm{nf}(s) = \mathrm{nf}(t)`$ holds because the canonical forms of a free structure are unique. No reduction order or critical-pair computation is involved. The proof obligation becomes: the normaliser respects each axiom and fixes canonical forms. This is the same shape as the Lean plan for $`A_P`$ ([`docs/plans/lean-presentation-axioms.md`](../plans/lean-presentation-axioms.md)).
- **FriCAS already has the container.** `FreeModule(Integer, S)` (`FM`) holds integer linear combinations over any `SetCategory` `S`, kept in canonical order when `S` is `Comparable`. It serves for sums with coefficients and for products with exponents alike.

The axiom sets then form a ladder, each step adding structure to the canonical form:

| Axioms for $`+`$ | Canonical form of a sum | Known structure |
|---|---|---|
| none | binary tree as written | term algebra |
| C only | binary tree, operands of each node sorted | free commutative magma |
| A only | flat list in written order | free semigroup |
| AC | flat sorted list | free commutative semigroup |
| AC, Id, Num, Doubles | sorted (coefficient, term) list plus constant | free commutative monoid with integer multiples |
| … and Cancels | the same with coefficients in $`\mathbb{Z}`$ | free $`\mathbb{Z}`$-module |
| … with the same for $`\cdot`$, plus Distributive | polynomial in the non-arithmetic terms | polynomial ring, i.e. what `Expression` builds |

The last row shows why design (II) stops short of distributivity (spec §3.1): with it, the canonical form is a polynomial, and `Expression` already provides that.

### 2.3 What changes in the implementation

1. **Representation.** The 2017 `Symbolic` stores binary InputForm trees and rewrites them. For an AC operator it should instead store the canonical form of the row selected by $`A`$: a flat sorted list, or a `FreeModule(Integer, %)` of terms. `InputForm` stays the external form (`convert`, display), produced from the canonical form as n-ary `(+ a b c)` or `(* a b c)`, which FriCAS's `InputForm` supports.
2. **Subtraction and division.** In the module rows, $`x - y`$ is $`x + (-1)\,y`$ and $`x / y`$ is $`x \cdot y^{-1}`$. A sum is a list of signed terms and a product a list of signed exponents. This changes the written form, which is intended in design (II): equality must be decidable, and the display shows the canonical form, so (Disp) still holds.
3. **The order $`\prec`$.** It must be a strict total order, defined structurally: numerals before symbols before applications; numerals by value; symbols by name; applications by operator, then arity, then arguments lexicographically. It replaces the heuristic `smaller?` of `SINFunctions`. It plays no part in termination; it only fixes the representative.
4. **The axiom categories** (`CommutativePlus`, `Doubles`, …) become a choice of row per operator rather than rewrite procedures. Combinations off the ladder need a separate check before they are allowed, for example C without A, or Doubles without C.
5. **What stays out:** general AC matching, needed only for user `RewriteRule` patterns modulo AC (Q2 note §3.4). In design (II) `Symbolic` has no `FunctionSpace`, so `RewriteRule` does not apply to it anyway. A matcher of its own is a later, separate question.
6. **Size of the change.** This is a new core for `Symbolic` of a few hundred lines, replacing the ~800-line rewriting core, plus tests: per-row canonical forms, and exhaustive checks like the Assoc bracketing test.

## 3. The hidden rewrites, one by one

These are the rewrites `Symbolic(Integer, None)` applies although they belong to no axiom (spec §4.2). Rechecked 2026-11-26:

| Input | Result | Source in `sexpr.spad` |
|---|---|---|
| `0*x`, `x*0` | `0`, `0` | `times` |
| `0-y` | `-(y)` | `minus`: `x = 0 => minus1(y)` |
| `1/(x/y)` | `y/x` | `quotient` → `inv1` |
| `-(x-y)` | `y-x` | `minus1` |
| `-(x+y)` | `(-x)+(-y)` | `minus1` |
| `p*x`, `p : PositiveInteger` | `x+x` for $`p = 2`$, `x+(x+x)` for $`p = 3`$ | `*: (PositiveInteger, %)` → `RepeatedDoubling` unless Doubles |
| `n*x`, `n : Integer` | `2*x` | different signature, no doubling |
| `x^p`, `p : PositiveInteger` | `x*(x*x)` for $`p = 3`$ | `^: (%, PositiveInteger)` → `RepeatedSquaring` unless Squares |
| `x^n`, `n : Integer` | `x^2`; `x^(-2)` gives `1/(x^2)` | `^: (%, Integer)` |
| `x^(2/3)` | `nthRoot(x,3)^2` | `^: (%, Fraction Integer)` |

The criteria are those of the spec: soundness (S) in `Expression` where the left side is defined, termination (T), confluence (CR) with the axioms already present, and the cost to G1/G3.

| # | Rewrite | (S) | (T) | (CR) | Verdict | Effort |
|---|---|---|---|---|---|---|
| 1 | $`0\cdot x \to 0`$, $`x \cdot 0 \to 0`$ | yes | size $`3 \to 1`$ | joinable (§4.1) | **Axiom group Ann**, as in $`A_P`$; apply only when Ann is in $`A`$ | trivial |
| 2 | $`0 - y \to -y`$ | yes | size $`3 \to 2`$ | joinable (§4.1) | **Axiom group Id**; only when Id is in $`A`$ | trivial |
| 3 | $`1/(x/y) \to y/x`$ | yes: where the left side is defined, $`x, y \ne 0`$, and both sides are $`y/x`$ | size $`5 \to 3`$ | with Id: $`1/(x/1) \to 1/x`$ both ways; with Inv: $`1/(1/y) \to y/1 \to y`$, also by Inv directly | **Optional group "reciprocal"**; it contains Inv's $`1/(1/x) \to x`$ as the case $`x = 1`$ | easy |
| 4 | $`-(x-y) \to y-x`$ | yes | size $`4 \to 3`$ | with Id: $`-(x-0)`$ gives $`-x`$ both ways; $`-(0-y)`$ gives $`y`$ by Id then Inv, and by this rule then Id | **Optional group "negation"** | easy |
| 5 | $`-(x+y) \to (-x)+(-y)`$ | yes | size grows ($`4 \to 5`$), but terminates by the interpretation $`[-x] = 2x`$, $`[x \pm y] = x+y+1`$ over integers $`\ge 1`$: $`2x+2y+2 > 2x+2y+1`$ (it also orients 4 and Inv) | with Id: $`-(x+0)`$ gives $`-x`$, using Num on $`-0`$ | **Only as part of the signed-sum row of §2.2**, where it is one step towards the canonical form; as a separate group it expands what was written, against G1 | easy, but only meaningful with §2.2 |
| 6 | $`p \cdot x \mapsto`$ repeated doubling | yes | — | — | **Remove.** Not an axiom: an implementation shortcut that depends on which signature the interpreter picks (`p*x` and `n*x` differ). Make every integer multiple the product node $`n \cdot x`$; Doubles (namely $`x + x \to 2x`$) is the axiom that relates sums and multiples | trivial |
| 7 | $`x^p \mapsto`$ repeated squaring | yes | — | — | **Remove**, for the same reason; every integer power becomes the power node $`x^n`$; Squares (namely $`x \cdot x \to x^2`$) is the axiom | trivial |
| 8 | $`x^{-n} \to 1/x^n`$ | yes, where $`x \ne 0`$ | size grows by one | — | **Remove**: keep the power node $`x^{-n}`$. In the §2.2 product row, $`x^{-n}`$ is the canonical form anyway | trivial |
| 9 | $`x^{p/q} \to \mathrm{nthRoot}(x,q)^p`$ | yes: FriCAS defines rational powers this way | — | — | **Remove**: keep the power node $`x^{p/q}`$. The conversion to `Expression` applies FriCAS's definition | trivial |

In summary:
- Rewrites 1 and 2 already exist as axiom groups and only need to be made conditional.
- Rewrites 6–9 are not axioms at all and go away.
- Rewrites 3 and 4 are sound, terminating and confluent with $`A_P`$, and are cheap as optional groups.
- Rewrite 5 belongs to the commutative signed-sum normal form, not to a group of its own.

None needs AC matching.

## 4. Proposed order of work

1. **Done 2026-11-26** (decision [0007](../decisions/0007-symbolic-hidden-rewrites.md)), with 3–5 tied to `Inverse` for now. Remove rewrites 6–9 and make 1–2 conditional. These are small changes to the existing code, with tests that `Symbolic(R, None)` keeps every one of the inputs above as written (G3).
2. Decide the ladder of §2.2 as the design of `Symbolic(R, A)` (a decision record). Fix $`\prec`$ in the spec.
3. Rebuild the core of `Symbolic` on canonical forms, one row at a time, with exhaustive tests: all orders and groupings of small sums must give one form.
4. Groups 3 and 4 if wanted.

## References

- G. E. Peterson, M. E. Stickel, "Complete sets of reductions for some equational theories", *J. ACM* 28(2) (1981) 233–264.
- M. E. Stickel, "A unification algorithm for associative-commutative functions", *J. ACM* 28(3) (1981) 423–434.
- J.-P. Jouannaud, H. Kirchner, "Completion of a set of rules modulo a set of equations", *SIAM J. Comput.* 15(4) (1986) 1155–1194.
- D. Benanav, D. Kapur, P. Narendran, "Complexity of matching problems", *J. Symbolic Computation* 3 (1987) 203–216.
- A. Rubio, R. Nieuwenhuis, "A total AC-compatible ordering based on RPO", *Theoret. Comput. Sci.* 142 (1995) 209–227.
- F. Baader, T. Nipkow, *Term Rewriting and All That*, Cambridge University Press (1998), ch. 10–11 (equational unification; rewriting modulo).
