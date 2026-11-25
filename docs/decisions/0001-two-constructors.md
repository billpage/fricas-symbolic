# 0001. Two constructors, one equality each

- Status: Accepted
- Date: 2026-11-25
- Decided by: Bill Page ("Option (c)")
- Spec: §3

## Context

The 2017 `SymbolicExpression(R)` claimed `FunctionSpace R` while its `zero?`, `numer`, `denom` and `kernels` were syntactic and its `=` was semantic. FriCAS's integrator and summation, which rely on those primitives agreeing, returned wrong results: $`\int (x+1)^2\,dx = x(x+1)^2`$, $`\int dx/(x^2+1) = 0`$, $`\sum_{x=1}^{10} x = 100`$ ([design review](../notes/2026-11-24-design-review.md), D1; [Q2 note](../notes/2026-11-25-q2-functionspace.md) §1).

## Options

- **(a)** Keep `FunctionSpace` and compute `numer`/`denom` through `Expression`: equality becomes semantic, the display can stay unevaluated.
- **(b)** Drop `FunctionSpace`; algorithms run in `Expression` through explicit conversion. Loses `RewriteRule`, which needs a `FunctionSpace` (Q2 note §3.4).
- **(c)** Both, one per constructor: `Symbolic(R, A)` syntactic (b), `SymbolicExpression(R)` semantic (a) through a pair representation.

## Decision

(c). `Symbolic(R, A)` has equality $`=_A`$ and claims only the categories $`A`$ proves. `SymbolicExpression(R)` is an honest `FunctionSpace` whose elements are pairs (written form, value in `Expression R`).

## Consequences

- One equality per constructor (spec §3.1 shows one equality cannot serve both).
- `RewriteRule` keeps working on the pair domain, on the written form.
- `Symbolic(R, A)` loses `Ring`, `FunctionSpace` and the categories above them unless $`A`$ proves their axioms.
- The pair domain does `Expression`'s arithmetic alongside its own.
