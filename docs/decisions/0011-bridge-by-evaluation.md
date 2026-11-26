# 0011. The bridge: evaluation by the universal property

- Status: Proposed (Claude, 2026-11-26, at Bill's request: "Maybe we can provide conversions or other bridges?")
- Date: 2026-11-26
- Spec: §2.2 (evaluation), §3.2 (design (II): categories and conversions)

## Context

`SymbolicTerm(R, A)` exports `SetCategory`, `ConvertibleTo InputForm`, the arithmetic, a few elementary functions, `form` and the value in `Expression R`. The 2017 tests of `simplify`, `kernels`, `D`, rewrite rules and other interface were not ported for that reason ([note](../notes/2026-11-26-retiring-symbolic.md)). Spec §3.2 says the domain should have "exactly those categories whose axioms follow from $`A`$", for example `CommutativeRing` at the Ring rung.

That is not available in one constructor. FriCAS 1.4.0's Spad compiler stops with `System error: formatInfo` on an export that depends on the value of `A`, `if member?('ring, A) then CommutativeRing` (checked 2026-11-26). Separate constructors per rung would be needed. Bill: categories would be "nice in principle, but probably not necessary".

## The mathematics

Let $`\Sigma`$ be the signature of terms (§2.1): $`+, -, \cdot, /, \hat{}\,`$, the numerals, and the operators `sin`, `exp`, … Let $`X`$ be the symbols. `SymbolicTerm(R, A)` is $`T/{=_A}`$, which is the **free algebra over $`X`$ in the variety of $`\Sigma`$-algebras satisfying $`A`$** (Birkhoff). Its universal property:

> For every $`\Sigma`$-algebra $`D`$ in which the axioms $`A`$ hold, and every map $`\varphi : X \to D`$, there is exactly one $`\Sigma`$-homomorphism $`\mathrm{eval}_\varphi : T/{=_A} \to D`$ with $`\mathrm{eval}_\varphi(x) = \varphi(x)`$ for $`x \in X`$.

```
   X ──────────────▶ SymbolicTerm(R, A) = T/=_A
     \                       │
      φ                      │ eval_φ    (the unique homomorphism)
       \                     ▼
        └────────────▶       D           (any Σ-algebra satisfying A)
```

As a recursion, which is how it is computed:

```math
\mathrm{eval}_\varphi(x) = \varphi(x), \qquad \mathrm{eval}_\varphi(n) = n_D, \qquad \mathrm{eval}_\varphi(\omega(t_1, \ldots, t_k)) = \omega_D\big(\mathrm{eval}_\varphi(t_1), \ldots, \mathrm{eval}_\varphi(t_k)\big).
```

Well-definedness is exactly the condition "$`A`$ holds in $`D`$": equal classes in $`T/{=_A}`$ then have equal images, so evaluating a normal form gives the same result as evaluating any term of its class. Where $`D`$'s operations are partial (division), so is $`\mathrm{eval}_\varphi`$. The value map of §2.2 is the instance $`D = E`$, $`\varphi(x) = x`$, and soundness (S) is this condition for $`D = E`$.

Analogy: a polynomial ring $`K[x_1, \ldots, x_n]`$ is the free commutative $`K`$-algebra, and choosing values for the variables in any commutative $`K`$-algebra determines the value of every polynomial. `SymbolicTerm(R, A)` is "the polynomial ring of the theory $`A`$".

## Options

1. **Categories per rung.** Separate constructors, one per admissible set with a category of its own. Heavy, and it multiplies the domains a user must know.
2. **Bridges only (proposed).** `SymbolicTerm(R, A)` keeps a small interface: the arithmetic, operator application, `form`, `value`. Computation happens by crossing to a FriCAS domain that has the algebra, through $`\mathrm{eval}_\varphi`$. It needs no categories that depend on $`A`$.

## Decision (proposed)

Option 2:

- **`eval`**, in a package `SymbolicTermFunctions2(R, A, D)`: `eval(t, φ)` with `φ : Symbol -> D`, and a variant `eval(t, φ, ψ)` where `ψ : (BasicOperator, List D) -> D` interprets the operators other than the arithmetic. The default `ψ` uses `D`'s own `sin`, `exp`, … when `D` has `TranscendentalFunctionCategory`, and fails otherwise. Numerals map through `Fraction Integer` (decimals are rationals, decision 0010) or through `R` when `D` has `coerce : R -> D`.
- **The condition "$`A`$ holds in $`D`$" is checked where Spad can check it.** `eval` refuses at the call, as admissibility does (decision 0009), if `D` lacks the category that asserts a group's axioms: for example `commutativity` needs a commutative `D`, and `ring` needs `D has CommutativeRing`. Beyond that it is the user's statement about `D`, as soundness (S) is ours about `Expression`. For `Float` and other floating-point `D` the axioms hold only up to rounding, as in decision 0010.
- **Instances, with no extra code:**

  | `D`, `φ` | Gives |
  |---|---|
  | `Expression R`, `x ↦ x` | the present value map |
  | `Polynomial K`, `Fraction Polynomial K` | the Ring and Field rungs in FriCAS's own domains, with `factor`, `gcd` and `D` |
  | `Float`, `x ↦ ` a number | numerical evaluation |
  | `SymbolicTerm(R, B)` with $`B \supseteq A`$, `x ↦ x` | adding axioms: the quotient map $`T/{=_A} \to T/{=_B}`$, i.e. re-normalisation |
  | `GeneralSymbolicExpression(R, B)`, `x ↦ x` | moving to design (I), where every operation of `Expression` applies |

- **The other direction is a read-back, not a homomorphism.** A term is made from an `InputForm` (`parse`), or from an element of `GeneralSymbolicExpression` or `Expression` through its form. Dropping axioms, from `SymbolicTerm(R, B)` to `SymbolicTerm(R, A)` with $`A \subseteq B`$, chooses a representative (the normal form under $`B`$, read as a term) and is no homomorphism.
- **Spec §3.2**, "Categories", is replaced by this decision: no categories that depend on $`A`$; conversions by $`\mathrm{eval}`$.

## Consequences

- No category claims to verify per rung, and no extra constructors.
- Operations such as `simplify`, `factor`, `D` and rewrite rules are used on `SymbolicTerm` by crossing a bridge and, if wanted, reading back. The tests of 2017 that wait for an interface (note on retiring `Symbolic`) get their answer this way: for example, `D` through `GeneralSymbolicExpression` or `Polynomial`.
- `SymbolicTerm(R, A)` needs operator application (`elt(op, args)`) for terms with operators beyond its current `sqrt`, `exp`, `log`, `sin`, `cos`, `tan`, so that every term can be built and evaluated.
- To do once accepted: the package, the per-group category checks, and tests that `eval` respects $`=_A`$: random terms equal under $`A`$ evaluate equally in a `D` satisfying $`A`$. A must-fail test: a `D` that lacks a required category is refused.
- Open: whether `eval` should also accept a target `D` whose axioms hold only on a subset, such as `Float` for `field` (division by zero), with the partiality left to `D`.
