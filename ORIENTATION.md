# Orientation

**A guide for a reader arriving with no context: what the package is for, which words mean what, and what is settled, open or withdrawn.** Current to 25 November 2026.

When this document and the specification disagree, the specification is right.

## 1. The problem

FriCAS's `Expression R` evaluates as it builds: $`(x+1)^2 - (x^2+2x+1)`$ becomes $`0`$ at once, and $`\cos x \sin y - \cos y \sin x`$ becomes FriCAS's canonical polynomial in its kernels. That makes it a reliable field to compute in, and a poor place to keep what someone wrote, or to apply a rewrite rule to the written structure.

The 2016–17 fricas-devel thread asked for expressions that stay unevaluated, yet can be simplified, compared, and converted to `Expression` when wanted. Its goals, with their sources, are G1–G8 in [spec §1](docs/spec/sexpr-spec.md#1-goals).

## 2. The central idea

Two of the goals cannot be met by one equality relation (spec §3.1):

- *display as written* and *purely syntactic work* (G1, G3) need equality of terms, where $`1+2 \ne 3`$;
- *correct library algorithms* (G2, G6) need equality of meaning, where $`(x+1)^2 - (x^2+2x+1) = 0`$.

The 2017 `SymbolicExpression` used both at once (`=` semantic, `zero?` syntactic), and FriCAS's integrator and summation then gave wrong answers. The specification therefore has two constructors, each with one equality:

| | `Symbolic(R, A)` — design (II) | `SymbolicPair(R, A)` — design (I) |
|---|---|---|
| An element is | a term, modulo the axioms $`A`$ | a pair (written form, value in `Expression R`) |
| Equality | $`=_A`$: same normal form | same value |
| May claim | only the categories $`A`$ proves | everything `Expression R` has, including `FunctionSpace` |
| Needs of $`A`$ | sound, terminating, confluent | sound and terminating |
| For | unification, term rewriting, $`1+2 \ne 3`$ | computing while keeping the written form |

An analogy: a pair is like writing $`\tfrac{6}{8}`$ on paper while knowing it is $`\tfrac34`$. The page keeps what was written; every decision is made with the value.

## 3. What is settled, open and withdrawn

| Item | Standing | Where |
|---|---|---|
| Two constructors, one equality each (Option (c)) | Decided by Bill Page, 2026-11-25 | [decision 0001](docs/decisions/0001-two-constructors.md) |
| Presentation axioms $`A_P`$ = identities, annihilation, involutions, numerals, the default for `SymbolicExpression(R)` | Decided by Bill Page, 2026-11-25; sound, terminating and confluent (spec Theorem 3); implemented in `SymbolicPair` | [decision 0002](docs/decisions/0002-presentation-axioms.md), spec §4.1 |
| The display shows the stored structure exactly, property (Disp) | Decided by Bill Page, 2026-11-26 | [decision 0004](docs/decisions/0004-display-shows-structure.md), spec §5 |
| Associativity: an optional axiom group, not in $`A_P`$ | Decided by Bill Page, 2026-11-26; specified, not yet implemented | [decision 0005](docs/decisions/0005-associativity-group.md), spec §4.1.1 |
| The 2017 axioms (commutativity, doubles, distributivity, …) in `Symbolic(R, A)` | Open: need AC-compatible ordering and a confluence check | spec §4.2 |
| Rewrites the 2017 code applies outside its axiom system | To be removed or made axioms | spec §4.2 |
| 2017 results `sum(x,'x=1..10) = 100`, $`\int (x+1)^2\,dx = x(x+1)^2`$, $`\int dx/(x^2+1) = 0`$ | Withdrawn (wrong); correct in `SymbolicPair` | [design review](docs/notes/2026-11-24-design-review.md) |

## 4. Where to start

1. [Spec §§1–3](docs/spec/sexpr-spec.md): goals, framework, the two constructors.
2. [`GLOSSARY.md`](GLOSSARY.md) for the words.
3. `make check`, then the tests in `src/input/sympair.input`, which read as worked examples.
4. The [notes](docs/notes/) for how the design got here.
