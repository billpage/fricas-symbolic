# Symbolic expressions (sexpr.spad): design review, step 4

> **Historical note.** Written in the FriCAS Claude project on 2026-11-24, before this repository existed. Branch and PR references are to `billpage/fricas-dev`; run names refer to runs on the project's FriCAS server and are not public. Not normative: where it differs from [`docs/spec/sexpr-spec.md`](../spec/sexpr-spec.md), the specification wins.

*2026-11-24. Covers `sexpr.spad` as ported to FriCAS 1.4.0 (`dev` at 74b375b8, billpage/fricas-dev#8). This is for Bill to decide on; nothing here is meant for upstream yet.*

## 1. What was read

- fricas-devel, **"Symbolic (unevaluated) Expressions"**: 35 messages, 2016-11-14 to 2017-02-25. Writers: Bill Page, Qian Yun (oldk1331), Kurt Pagani, Ralf Hemmecke and Waldek Hebisch.
- The same subject, 2017-02, from **Constantine Frangos**: questions about using SEXPR in practice.
- fricas-devel, **"fricas: trigonometric simplification."**: 19 messages, 2017-01-25 to 2017-02-21. This is where `box`/`paren` were discussed, and it led to SandBoxSymbolicTrig.
- I searched for later threads on SEXPR, sexpr.spad or `Symbolic(`. There are none after February 2017.
- wiki.fricas.org **SandBoxSymbolicExpressions** (`/src`). This is the February 2017 version of the code, with names from before the renaming (`ASS+`, `COM+`, `/\` as `AND`), plus its test link. It has no user comments. Its tests already listed two known problems, "-- Wrong result !!" on `sum(x,'x=1..10)` and "need to handle %diff operator" (`D(x^n,'x)` was commented out). These are D1 and D2 below; neither was fixed after 2017. Open questions in its code comments:
  - "+0 is a hack to avoid premature conversion (do we need it?)";
  - "Do we want these even if R not a Ring, e.g. Symbol?";
  - "need to handle subscripted Symbol".
- wiki.fricas.org **SandBoxSymbolicTrig** (`/src`): the trigonometric `_rule` example with no prose. **It works on the port.** The run is `ASUS-20261124-224219-sexpr-trig-sandbox`:
  - `rs t1` → `sin(y-x)`, `rc t2` → `cos(y+x)`, and `rs` and `rc` leave the other term alone;
  - `rc rs expr` → `5+sin(y-x)*cos(y+x)*r3+cos(y+x)*w*cos(a)+sin(y-x)*cos(x3)+tan(w)*tan(q)`;
  - `test` against the hand-rewritten expression gives `true`.

## 2. What the 2016–17 discussion settled

| Point | Outcome |
|---|---|
| Representation | **InputForm** (Bill [5]). Bill's argument: an unevaluated expression is a labelled tree, and `interpret` gives it an operational meaning. The alternatives were dropped: a list of EXPR (Qian, withdrawn [3]); OutputForm (Kurt [2], but it loses semantics [6]); Bronstein's `ExpressionTree` in Aldor (Ralf [4], not pursued). |
| What `Symbolic(R)` contains | Everything `Expression(R)` contains, including `sin(x)` and `sqrt(x)`, only unevaluated (Bill [15]; Kurt agreed [16]). That is why `SymbolicExpression(R)` is a `FunctionSpace`. |
| OutputForm ≠ InputForm | Waldek [10]: code that treats InputForm as OutputForm via `pretend` is "bad". Bill rewrote `coerce: % -> OutputForm` (2016-11-17). Two `pretend OutputForm` uses remain: atoms (line 1023) and the "what is:" fallback (line 1069). |
| Axioms as parameters | `Symbolic(R, A)` takes an axiom set $`A`$, and `SEXPR(R)` is `Symbolic(R, all)`. Kurt's use case, syntactic unification where $`1+2 \ne 3`$, is `Symbolic(Integer, None)` [33]. |
| `_rule` | A function call, not the `rule` keyword (Waldek [20]). Bill used it to avoid the interpreter's coercion to `EXPR INT` [25]. |

Two items were left unresolved:

- **Termination of the rule set.** Bill reported non-termination while trying different term orderings [27]. He was reading Jouannaud & Marché and the Dershowitz survey.
- **Frangos' questions.** Should SEXPR be in a FriCAS release? Can it be used for matrices (determinant, nullspace)? Do other built-in functions work over SEXPR?

## 3. The design in one picture

Notation:

- $`\Sigma`$ is the operator signature ($`+,\ \times,\ \hat{}\ ,\ /,\ -,\ \sin,\ \dots`$).
- $`V`$ is the set of variables.
- $`T = T(\Sigma, V)`$ is the set of terms, i.e. InputForm trees.
- $`A`$ is the axiom set of `Symbolic(R, A)`.
- $`R_A`$ is the rewrite rules that the axiom categories (`DoublesAxiom`, `CancelsAxiom`, …) implement.
- $`[\![\cdot]\!] : T \to`$ `Expression(R)` is the meaning map (`interpret`, or the coercion to `EXPR`).

`Symbolic(R, A)` stands for the quotient $`T/{=_A}`$. Each class is stored by its normal form $`\mathrm{nf}_A(t)`$.

That works only if three properties hold:

1. **Soundness.** If $`s \to_{R_A} t`$, then $`[\![ s]\!] = [\![ t]\!]`$.
2. **Termination.** There must be a reduction order $`\succ`$ with $`l \succ r`$ for every rule $`l \to r`$. Because commutativity cannot be oriented, rewriting is done modulo AC, the associative–commutative equations. The order must then be AC-compatible: if $`s' =_{AC} s \succ t =_{AC} t'`$, then $`s' \succ t'`$.
3. **Confluence modulo AC.** Every AC critical pair must be joinable. Given 2 and 3, $`s =_A t \iff \mathrm{nf}_A(s) =_{AC} \mathrm{nf}_A(t)`$ (Peterson & Stickel 1981; Jouannaud & Kirchner 1986).

In the code, $`\succ`$ is `smaller?` in `SINFunctions`. Its own comment says it is "not yet proven" to be a total order, and it logs violations instead of raising an error. No AC critical-pair check has been done. Point Q4 below is about exactly this.

The code uses two different equalities:

- **syntactic modulo $`A`$:** $`s =_A t`$. This is `=` in `Symbolic(R, A)`; for example `(1+2 = 3)$Symbolic(Integer, None)` is false.
- **semantic:** $`[\![ s]\!] = [\![ t]\!]`$ in `Expression(R)`. This is `test(…)` on an Equation in SEXPR, e.g. `test(x*(y+z) = z*x+y*x)`.

The unit-test package's `testEquals` compares InputForms after construction, so it tests $`=_A`$ (with $`A`$ = all for SEXPR).

## 4. Questions for Bill to decide

**Q1. What does `=`@Boolean mean in `SEXPR(R)`?** It can be $`=_A`$ (decidable through normal forms) or semantic equality (decidable only as far as EXPR's zero test is). *Recommendation:* `=` is $`=_A`$, the same as in every `Symbolic(R, A)`. Semantic equality gets its own name: `test` is already that in practice, and an explicit `equivalent?(s, t) == zero?(s::EXPR R - t::EXPR R)` would make it clear. sexpr2.input already tests both kinds separately.

**Q2. Which algebra may SEXPR claim?** `SymbolicExpression(R)` exports `FunctionSpace(R)`. Generic library code (Gosper summation, `integrate`, `limit`, `solve`, matrices) then runs on SEXPR through `numer`/`denom`/kernels. Those operations do **not** return polynomials in the variables: every sum becomes an opaque `%paren` kernel (`makeKernel`, line 790). For example

```math
\mathrm{numer}\!\left(\tfrac{x(x-1)}{2}\right) = x\cdot k,\qquad k = \texttt{\%paren}(x-1),
```

which prints as `x*-(x, 1)`. The library then treats $`x`$ and $`k`$ as independent, so results can be wrong; see D1, where summation returns $`n^2`$ instead of $`n(n+1)/2`$.

There are two options:
- **(a)** Keep `FunctionSpace`, and compute `numer`/`denom`/`univariate` through `Expression(R)`, i.e. `numer(x) == map(...)(numer(x::EXPR R))` with kernels converted back.
- **(b)** Drop `FunctionSpace` (and the categories that depend on it). Export the unevaluated constructors plus explicit conversions, so that algorithms run in EXPR and the result is converted back.

*Recommendation:* (b) for Frangos-style computation (matrices, summation, solving). That matches Waldek's point [trig, 2017-01-27]: without automatic simplification, intermediate expressions grow. It also matches Bill's own description of SEXPR as "Expression, but unevaluated". (a) is more work and keeps a category promise that is hard to keep. **This is the main decision.** It affects which upstream categories SEXPR names, and it is the kind of change the project would take to fricas-devel before code, if it ever went upstream.

**Q3. Which rewrites are automatic in SEXPR?** Bill's first post said "no automatic simplifications". Today `SEXPR` sorts operands (commutativity), collects doubles (`x+(x+y)` → `2*x+y`) and folds constants. *Recommendation:* keep this, but document it. `SEXPR(R)` is "normal form modulo AC plus the listed axioms", and `Symbolic(R, None)` is the truly unevaluated domain. Every constructor's `++` description should name its axiom set.

**Q4. The term order `smaller?`.** *Recommendation:* replace it with a known AC-compatible total simplification order. AC-RPO (Rubio & Nieuwenhuis 1995) is the standard choice. Then:
- check AC critical pairs of the rule set for the full `SEXPR` axiom set (by hand, or with a small Spad completion loop);
- record a test that runs the 2017 non-terminating cases.

Until then, "not proven total" stays a known risk.

**Q5. `box` and `paren` in SEXPR.** In `Expression`, they are kernels that keep their content together, and `distribute` removes them (Waldek, trig thread). Bill's 2017 view was that they are "a hack at the wrong level", and that one (`paren`) would be enough. In the port:
- `paren` is the identity, so `paren(x+y)*(x+y)` → `(y+x)^2`;
- `box` is not handled at all: `box(m+1)*m` prints `%box(1+m)*m`.

*Recommendation:* in SEXPR, both are the identity, because SEXPR is already unevaluated. Converting EXPR → SEXPR strips them. The internal `%paren` wrapper in `makeKernel` goes away if Q2 is answered with (b). The pending `xftestEquals` on `%box` in sexpr2.input then becomes a plain test.

**Q6. Lisp property lists.** `rank` and the pattern-matching flags are stored on Lisp symbol plists via `MAKEPROP`/`GET`. Waldek [12]: FriCAS's algebra does not use Lisp plists; data goes into `BasicOperator` properties. *Recommendation:* move `rank` into a `Table(Symbol, Integer)` in `SINFunctions`, or into operator properties. This also removes the `FUNCALL('MAKEPROP…)` workaround from the port.

**Q8. Smaller points from the 2017 code comments.**
- Is the `+0` hack against premature conversion still needed?
- Should the arithmetic exports apply when `R` is not a ring, e.g. `Symbolic(Symbol)`?
- Subscripted symbols are not handled.

*Recommendation:* settle these after Q2, since the restructuring decides where conversion happens.

**Q7. Debug output.** The tracing on `$testingSystem` (`)set message testing on`) was Bill's own question in 2017 [31]. *Recommendation:* use a domain-local flag instead. `$testingSystem` belongs to the test harness, and turning it on changes the output of every library test.

## 5. Defects found in the port (checked by running)

All runs used FriCAS 1.4.0 release (SBCL 2.6.10), loading the libraries from `ASUS-20261124-221331-addon-compile` with `)lib` twice.

| # | Input | Got | Expected | Run |
|---|---|---|---|---|
| D1 | `sum(x,'x=1..10)` (marked "Wrong result" in 2017) | `100` | $`\sum_{x=1}^{10} x = 55`$ (EXPR gives 55) | `…-221718-sexpr-sum-power` |
| | `sum(k,'k=1..3)` | `9` | $`6`$ | same |
| | `sum(x,'x)` (Gosper chosen) | `-(x-1)/(-(x-1)+x-1-1)*(x-1)` $`=(x-1)^2`$ | $`F(x)=\tfrac{x(x-1)}{2}`$ | `…-221805-sexpr-sum-inputform` |
| D2 | `D(x^n,'x)` (known in 2017: "need to handle %diff"), `n:SEXPR INT` | no `^` for `Symbolic(Integer, join(…))` × `SEXPR(Integer)` | $`n\,x^{n-1}`$ | `…-221531-sexpr-known-problems` |
| D3 | `DoublesAxiom` guards | the `+` rules test `AssociativeAxiomTimes`, and one is misspelled `AssociativeActiomTimes` | `AssociativeAxiomPlus` | code, lines 319–323 |
| D4 | `box(m+1)*m` | `%box(1+m)*m` | `(m+1)*m`, or per Q5 | `…-221718-sexpr-sum-power` |
| D5 | local `hash` in `Symbolic` | dead code (`SetCategory` no longer exports `hash`) | remove | code |

**D1 in detail.** Let $`F`$ be an antidifference of $`f`$, i.e. $`\Delta F(x) = F(x+1)-F(x) = f(x)`$. Then $`\sum_{x=a}^{b} f(x) = F(b+1) - F(a)`$.

For $`f(x)=x`$, the correct antidifference is $`F(x) = x(x-1)/2`$. SEXPR returned $`G(x) = (x-1)^2`$, for which $`\Delta G(x) = x^2-(x-1)^2 = 2x-1 \ne x`$. So $`G(b+1)-G(1) = b^2`$, which matches both wrong values: $`10^2 = 100`$ and $`3^2 = 9`$.

The field arithmetic itself is right: in SEXPR, `simplify(eval(f, x=x+1) - f)` returns `x` for $`f = x(x-1)/2`$. The fault is the Gosper path running on SEXPR's `numer`/`denom` (Q2). Which `sum` the interpreter selects also varies: with `F := sum(x,'x)`, SEXPR's own `sum` is chosen and the result stays unevaluated. Fixed by Q2(b), or (a).

**D3.** In this run, `(x+y)+y` → `2*y+x` and `x+(x+y)` → `2*x+y` are correct anyway. Other rules (commutativity, then the first branch) probably reach them, but I have not traced it. The fix needs a test that must fail without associativity of $`+`$: in `Symbolic(Integer, Doubles)`, `(x+y)+y` must stay unchanged.

## 6. Suggested order

1. Bill decides Q1–Q3. Q2 decides most of the rest.
2. Small PRs into `dev`, one each, every one with a test in sexpr2.input:
   - D3 + D5 (trivial);
   - Q5/D4 (`box`/`paren`);
   - Q6 (plists);
   - Q7 (debug flag).
3. The Q2 restructuring, which also fixes D1 and probably D2.
4. Q4: AC-RPO and the critical-pair check. This is the research part, and it deserves its own write-up.
5. Then the `devel` build (Makefile.in, exposed.lsp).

## References

- G. E. Peterson, M. E. Stickel, "Complete sets of reductions for some equational theories", *J. ACM* 28(2) (1981) 233–264.
- J.-P. Jouannaud, H. Kirchner, "Completion of a set of rules modulo a set of equations", *SIAM J. Comput.* 15(4) (1986) 1155–1194.
- J.-P. Jouannaud, C. Marché, "Termination and completion modulo associativity, commutativity and identity", *Theoret. Comput. Sci.* 104 (1992) 29–51. (Cited by Bill, 2017-02-10.)
- N. Dershowitz, J.-P. Jouannaud, "Rewrite systems", in *Handbook of Theoretical Computer Science*, vol. B, Elsevier (1990) 243–320. (The "survey-draft" cited by Bill.)
- J. W. Klop, "Term rewriting systems", in *Handbook of Logic in Computer Science*, vol. 2, Oxford (1992). (Cited by Kurt.)
- A. Rubio, R. Nieuwenhuis, "A total AC-compatible ordering based on RPO", *Theoret. Comput. Sci.* 142 (1995) 209–227.
- R. W. Gosper, "Decision procedure for indefinite hypergeometric summation", *Proc. Natl. Acad. Sci. USA* 75 (1978) 40–42.
- fricas-devel threads (fricas-devel archive, Google Groups): "Symbolic (unevaluated) Expressions" (2016-11-14 to 2017-02-25); "fricas: trigonometric simplification." (2017-01-25 to 2017-02-21). Bracketed numbers [n] above are message indices in the first thread.
