# Q2: should SymbolicExpression drop `FunctionSpace`? Implications and examples

> **Historical note.** Written in the FriCAS Claude project on 2026-11-25, before this repository existed. Branch and PR references are to `billpage/fricas-dev`; run names refer to runs on the project's FriCAS server and are not public. Not normative: where it differs from [`docs/spec/sexpr-spec.md`](../spec/sexpr-spec.md), the specification wins.

**Decision (Bill, 2026-11-25): Option (c)** — section 4's split. `Symbolic(R, A)` follows design (II); `SymbolicExpression(R)` follows design (I) through a pair representation. The prototype is in section 6.

*2026-11-25. Follows [the design review](2026-11-24-design-review.md) (Q2). All results below are from FriCAS 1.4.0 release runs, using the port's libraries (`ASUS-20261124-221331-addon-compile`, loaded with `)lib` twice). Run names are given with each table.*

## 1. The root cause: SEXPR mixes two notions of equality

Let $`T`$ be the set of InputForm trees. Let $`[\![\cdot]\!] : T \to \mathrm{EXPR}(R)`$ be the meaning map, and let $`=_A`$ be equality modulo SEXPR's rewrite axioms $`A`$. A FriCAS domain that claims `Ring` or `FunctionSpace` promises that all of its primitives use the *same* equality. SEXPR mixes the two (run `…-105531-sexpr-fs-contract`):

| Primitive | Behaves as | Example with $`a = (x+1)^2 - (x^2+2x+1)`$ |
|---|---|---|
| `=`@Boolean | semantic, $`[\![ a]\!] = 0`$ | `(a = 0)@Boolean` → `true` |
| `zero?` | syntactic, $`=_A`$ | `zero? a` → `false` |
| `numer`, `denom`, `kernels` | syntactic: every sum becomes a `%paren` kernel | `numer(x*(x-1)/2)` → `x*-(x, 1)` |
| `coerce: % -> OutputForm` | drops needed parentheses | `a` prints as `(1+x)^2-2*x+1+x^2`. Read literally, that is $`2x^2+2 \ne 0`$. |

Generic library code decides zero tests with `zero?` and reads structure from `numer`/`kernels`. It therefore computes in a structure that is not the one `=` describes, and gets wrong answers (run `…-105543-sexpr-fs-contract2`):

| Call on SEXPR | Result | Correct |
|---|---|---|
| `integrate((x+1)^2, 'x)` | `x*(x+1)^2`; its derivative is $`(x+1)(3x+1)`$ | $`\tfrac13 x^3 + x^2 + x`$ |
| `integrate(1/(x^2+1), 'x)` | `0` | $`\arctan x`$ |
| `sum(x, 'x=1..10)` | `100` | $`55`$ |
| `limit(sin(x)/x, x=0)` | error: `exprToUPS: neither a sum, product, power, nor kernel` | $`1`$ |
| `solve(x^2-1 = 0, 'x)` | error: `factor for this domain is unimplemented` | $`x = \pm 1`$ |
| `D((x+1)^2, 'x)` | `2*(1+x)` ✓ | |
| `determinant [[x,1],[1,x]]` | `(x-1/x)*x` ✓ (equal to $`x^2-1`$, in an awkward form) | |
| `rank`, `nullSpace` on a matrix with $`a`$ as an entry | correct ✓ | |

The worst outcome is a confident wrong answer like `0`; an error is the honest failure. Differentiation and the linear algebra above happen to work, because they make no zero decision on a hidden zero, or use `=` rather than `zero?`.

There are two consistent designs:

- **(I) Semantic.** `=`, `zero?`, `numer`, `denom` and `kernels` all mean $`[\![\cdot]\!]`$. SEXPR is then an honest `Ring`/`FunctionSpace`: it represents elements of EXPR(R), each in a chosen presentation. This is option (a) of the review.
- **(II) Syntactic.** Everything means $`=_A`$. `Symbolic(R, A)` is then the free algebra of the theory $`A`$: terms modulo $`A`$. This is option (b), the subject of this note.

## 2. What option (b) means for the type

The categories a domain may claim are those whose axioms hold for its equality. Under (II), the equality is $`=_A`$, so `Symbolic(R, A)` can claim exactly what $`A`$ proves:

| Axioms in $`A`$ | Honest category |
|---|---|
| assoc. + comm. of $`+`$ | `AbelianSemiGroup` |
| … + identity $`0`$ | `AbelianMonoid` |
| … + inverse $`x + (-x) = 0`$ | `AbelianGroup` |
| … + the same for $`\times`$ + distributivity | `CommutativeRing` |

The last row is where (II) ends. With distributivity in $`A`$, the normal form of $`(x+1)^2`$ must equal that of $`x^2+2x+1`$, so the normal forms are expanded polynomials, which is exactly what `Expression` already is. **An unevaluated domain cannot be an honest `Ring` under syntactic equality.** Option (b) therefore drops more than `FunctionSpace`: it also drops `Ring`, `Field`, `AlgebraicallyClosedFunctionSpace`, `TranscendentalFunctionCategory` and the rest of what `SymbolicCategory` adds under `if R has IntegralDomain`.

The operators keep their names as plain exports (`+`, `*`, `/`, `^`, `sin`, `exp`, …) that build terms. What changes is that the domain stops promising the ring laws to library code.

What remains:

- `SetCategory`, `ConvertibleTo InputForm` and `CoercibleTo OutputForm`;
- the algebraic categories in the table above that $`A`$ supports;
- `eval(f, x = g)` (substitution) and `D` (SEXPR's own rules), implemented directly rather than inherited from `FunctionSpace`;
- `coerce: % -> Expression R` and `coerce: Expression R -> %`.

## 3. What option (b) costs, with examples

**3.1 Library algorithms need explicit conversion.** Once SEXPR is not a `FunctionSpace`, the interpreter does not route `integrate(f, 'x)` through `Expression` by itself. I checked this with a minimal prototype that has the right `coerce` but no `FunctionSpace` (`TinySym`, runs `…-105658-tinysym-autocoerce` and `…-105707-tinysym-autocoerce2`): `integrate(f, 't)` → "no applicable operation". The user writes the conversion, or a package does it. The explicit route gives correct answers today:

```
integrate(((x+1)^2)::EXPR INT, 'x)::SEXPR INT     -- (3*x^2+3*x+x^3)/3
solve((x^2-1)::EXPR INT = 0, 'x)                  -- [x=1, x=-1]
expandTrigProducts((sin(x)*cos(x))::EXPR INT)::SEXPR INT   -- sin(2*x)/2
determinant(map(z +-> z::EXPR INT, m))::SEXPR INT -- -1+x^2
```

A package `SymbolicFunctions(R)` would make this seamless, with one line per operation:

```
integrate(f : SEXPR R, x : Symbol) : SEXPR R == (integrate(f::EXPR R, x)$FSINT)::SEXPR R
sum(f : SEXPR R, b : SegmentBinding SEXPR R) : SEXPR R == ...   -- likewise via EXPR
```

The list of operations to wrap is finite and known: `integrate`, `sum`, `product`, `limit`, `series`, `solve`, `factor`, `normalize`, the `TranscendentalManipulations` operations (`expand`, `simplify`, `htrigs`, `expandTrigProducts`, …) and `determinant`/`nullSpace` for matrices. SEXPR's `simplify` already works this way (sexpr.spad, line 1340).

**3.2 Results come back in EXPR's canonical form.** The user's own input stays unevaluated, but an algorithm's output is whatever EXPR produced. $`\int (x+1)^2\,dx`$ returns as $`\tfrac13(x^3+3x^2+3x)`$, not $`\tfrac13(x+1)^3`$. If a particular form is wanted, it has to be requested afterwards (`factor`, a rule).

**3.3 The EXPR → SEXPR conversion must be made structural.** Every result in 3.1 comes back through this conversion. Today it uses `interpret`, so it picks up interpreter variables (run `…-105720-sexpr-capture`):

```
z := 5
(('z)::EXPR INT + 1)::SEXPR INT     -- 6, not z+1
```

The SEXPR → EXPR direction is already protected: it substitutes fresh symbols before calling `interpret` (sexpr.spad, line 1072). The EXPR → SEXPR direction needs a structural walk over EXPR's `isPlus`/`isTimes`/`isPower`/kernels, building SEXPR terms without any interpreter call. This is a real bug today, independent of Q2.

**3.4 Rewrite rules are lost. This is the largest cost.** `RewriteRule`, `Ruleset` and `ApplyRules` (rule.spad) all require `F : Join(FunctionSpace R, PatternMatchable Base, ConvertibleTo Pattern Base)`. Under (b), `_rule(...)` on SEXPR stops compiling, and that includes the SandBoxSymbolicTrig showcase, which works now. The two ways to replace it are:

- **Apply rules in EXPR and convert back.** This loses the point. EXPR first rewrites $`t_1 = \cos x\,\sin y - \cos y\,\sin x`$ into its own canonical polynomial, and as Waldek noted in 2017, matching a minus sign there is unreliable.
- **Write a rule engine for `Symbolic`.** It would match patterns against InputForm trees modulo the AC axioms in $`A`$. That is natural here, since the axiom categories already rewrite InputForm, but AC matching is a substantial piece of work. In general it is NP-complete (Benanav, Kapur & Narendran 1987); for small terms it is cheap.

**3.5 Matrices.** `Matrix(R)` needs only `R : AbelianMonoid`, so `Matrix(SEXPR R)` still exists. `determinant`, `rank` and `nullSpace` need a commutative ring or field, so for Frangos' question they go through 3.1.

## 4. What this changes in my recommendation

In the review I recommended (b) for SEXPR. The `RewriteRule` dependency (3.4) changes that. Pattern rules over unevaluated expressions are the feature the trig example and Kurt's use cases depend on, and (b) would remove them until a new engine exists.

I now suggest **keeping both designs, one per constructor**, which is what the 2016 thread asked for:

- **`Symbolic(R, A)`: design (II).** Syntactic $`=_A`$; claims only the categories $`A`$ proves (section 2); no `FunctionSpace`. This is Kurt's domain for unification and term rewriting, where $`1+2 \ne 3`$. Algorithms run through explicit conversion (3.1).
- **`SymbolicExpression(R)`: design (I).** "Expression, but unevaluated": an honest `FunctionSpace`.

  A simple way to make (I) honest is a pair representation, `Rep := Record(form : InputForm, value : Expression R)`. Arithmetic builds both parts. `=`, `zero?`, `numer`, `denom` and `kernels` are taken from `value`; output, `isPlus`/`isTimes` (used by the pattern matcher) and `InputForm` are taken from `form`.

  It is like writing $`\tfrac{6}{8}`$ on paper while knowing it is $`\tfrac34`$: the page keeps the written form, and every decision uses the value.

  Then:
  - `RewriteRule` keeps working;
  - integration and summation decide zero correctly;
  - there are no `interpret` round trips, so neither 3.3 nor its performance cost applies.

  The price is that SEXPR does EXPR's arithmetic alongside its own, i.e. about EXPR's cost plus the presentation, and results come back in an algorithm-built form (e.g. `(x-1/x)*x`), correct but not always tidy.

Whether `Symbolic(R, A)` should also keep pattern rules can wait. It needs the AC rule engine of 3.4 in any case.

## 5. Examples to record as tests whichever way Q2 goes

These go into sexpr2.input as must-pass checks, the first two as `testTrue` of semantic equality:

- `integrate((x+1)^2,'x)`: its derivative must equal $`(x+1)^2`$.
- `integrate(1/(x^2+1),'x)`: its derivative must equal $`1/(x^2+1)`$.
- `sum(x,'x=1..10) = 55` (as an `Integer` after conversion).
- `zero?(a) = (a = 0)@Boolean` for $`a = (x+1)^2-(x^2+2x+1)`$, and the same for a non-zero $`a`$.
- `(('z)::EXPR INT + 1)::SEXPR INT` keeps `z` when `z` has a value in the interpreter.
- The printed form of `a` must denote $`0`$: parse the printed text back and compare.

## 6. Prototype of design (I): `SymbolicPair(R)` (2026-11-25)

The prototype is a separate domain, `SymbolicPair(R)` (`SYMPAIR`). It lives on branch `claude/sexpr-pair-prototype`, billpage/fricas-dev#9 into `dev`; it is not yet in the build or in sexpr.spad.

Each element is a node with five parts:

```math
x = (\text{form},\ \text{value},\ \text{head},\ \text{operator},\ \text{operands}),\qquad \text{value} = [\![\text{form}]\!] \in \mathrm{EXPR}(R).
```

**Two kinds of primitive.**

- *Semantic* primitives always read the value: `=`, `zero?`, `numer`, `denom`, `kernels`, `differentiate` and the retractions.
- *Structural* primitives read the written tree: `isPlus`, `isTimes`, `isPower`, and the kernel of an operator node. The pattern matcher and `ApplyRules` walk with exactly these four.

A node answers only the question that matches its written shape:

- a sum;
- a product (a/b counts as $`a\cdot b^{-1}`$);
- an integer power;
- a kernel, i.e. an operator node whose value is still that kernel.

Any other node answers like its value. So does a node whose value is a constant, and so does a result produced by a library algorithm. Each answer is a valid decomposition of the value, so the `FunctionSpace` contract holds: $`\sum \text{isPlus}(x) = x`$ and $`\prod \text{isTimes}(x) = x`$ in EXPR.

**Recorded run** `ASUS-20261125-112849-sympair-recorded2`:
- FriCAS 1.4.0 release;
- libraries compiled from `3e16e6ba` (sha256 `2ba389bf…`);
- tests `src/input/sympair.input` at `e565a1e5` (sha256 `7aa8d460…`).

**Result: 24 tests, unexpected failures 0, expected failures 6, unexpected passes 0.**

| Check | 2017 SEXPR | SymbolicPair |
|---|---|---|
| $`\int (x+1)^2\,dx`$, checked by $`D`$ | $`x(x+1)^2`$ ✗ | $`(x^3+3x^2+3x)/3`$ ✓ |
| $`\int dx/(x^2+1)`$ | $`0`$ ✗ | $`\arctan x`$ ✓ |
| $`\sum_{x=1}^{10} x`$ | $`100`$ ✗ | $`55`$ ✓ |
| $`\lim_{x\to0}\sin x/x`$ | error | $`1`$ ✓ |
| `zero? a` vs `(a = 0)@Boolean` | disagree | agree ✓ |
| `eval((x+1)^2, x = y+1)` | | `(y+1+1)^2` (form kept) ✓ |
| EXPR → pair with `z := 5` set | `6` ✗ | `z+1` ✓ |
| trig rules `rc rs expr` | worked | works ✓ (plain `Expression`: the rule does not fire) |

**Pitfalls found while building it.** These apply to any `FunctionSpace` built on `Expression`.

1. Operator `%eval` properties are global closures, so evaluation must happen through `Expression` (`elt(op, …)$E`). Otherwise `Expression`'s closure reads the pair `(form . value)` as its own `(numer . denom)`.
2. `FunctionSpaceAssertions` marks pattern variables (`optional`, …) on a *copy* of the operator, so `elt`/`kernel` must pass `op` through unchanged.
3. `operator(s)$CommonOperators` returns copies without `Expression`'s properties. Use `operator(op)$E`, or `ApplyRules` loops forever rebuilding new kernels.
4. `elt(op, args)$E` evaluates only operators that carry `%eval`; `sqrt`/`nthRoot` carry none. Rebuilding nodes therefore goes through the domain's own functions; otherwise `rootSimp` produced `sqrt(1)` inside $`\arctan`$.
5. Inside Spad, `(-1)::%` is unary minus applied to `1::%`, which made `isTimes` recurse forever.
6. `testsuite`/`testcase` clear macros as well as variables (skill PR claude-plugins #18).

Also confirmed: using the pair domain leaves `Expression` itself unaffected (run `…-112656-sympair-global-hazard`).

**Open points before it replaces sexpr.spad's SEXPR:**
- tidier forms for algorithm results (e.g. the closed form of the sum, `(-1)*x`);
- a `factor` export, so `solve` works;
- 2-D output (now the one-line `unparse` string);
- kernel identity is semantic, so a kernel's written operands are those of its first creation;
- cost: every operation also does EXPR's arithmetic;
- then rebuild `SymbolicExpression(R)` on this representation, and `Symbolic(R, A)` as design (II).

## References

- D. Benanav, D. Kapur, P. Narendran, "Complexity of matching problems", *J. Symbolic Computation* 3 (1987) 203–216.
- J.-P. Jouannaud, H. Kirchner, "Completion of a set of rules modulo a set of equations", *SIAM J. Comput.* 15(4) (1986) 1155–1194.
- FriCAS 1.4.0 sources: `rule.spad` (RewriteRule, ApplyRules, Ruleset), `matrix.spad` (Matrix), `integrat.spad` (FunctionSpaceIntegration), `combfunc.spad` (FunctionSpaceSum).
