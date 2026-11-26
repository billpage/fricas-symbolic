# fricas-symbolic

Symbolic (unevaluated) expressions for [FriCAS](https://fricas.github.io): expressions that keep the form in which they were written, together with library algorithms (integration, summation, limits, rewrite rules) that still give correct answers.

The package is developed outside the FriCAS source tree, against an unmodified FriCAS release. Its code directories mirror FriCAS's own layout (`src/algebra/*.spad`, `src/input/*.input`), so that a finished piece can be proposed to [fricas/fricas](https://github.com/fricas/fricas) file for file.

## Status

Early development. The design is fixed by a mathematical specification, [`docs/spec/sexpr-spec.md`](docs/spec/sexpr-spec.md); the code is a prototype being brought into line with it.

| Constructor | File | What it is | State |
|---|---|---|---|
| `GeneralSymbolicExpression(R, A)` | `src/algebra/gsexpr.spad` | A presentation of `Expression R`: every element carries its written form and its value. Spec §3.3, design (I). | Prototype; passes its tests |
| `SymbolicExpression(R)` | `src/algebra/gsexpr.spad` | `GeneralSymbolicExpression(R, A)` with the default axioms $`A_P`$ (decision 0002) | Passes its tests |
| `SymbolicTerm(R, A)` | `src/algebra/symterm.spad` | Design (II): terms modulo the axiom groups $`A`$, equality by identity of normal forms (decisions 0008, 0009) | Groups of $`A_P`$, `associativity` and `commutativity` (plan steps 2–3); higher rungs to come |
| `Symbolic(R, A)` and the axiom domains | `src/algebra/sexpr.spad` | Bill Page's 2016–17 implementation, to be retired by `SymbolicTerm` (plan step 6), ported to FriCAS 1.4.0; equality modulo the axioms $`A`$. Spec §3.2, design (II), to be rebuilt on canonical forms ([note](docs/notes/2026-11-26-commutativity-and-hidden-rewrites.md)). | Ported; rewrites only by its axioms since 2026-11-26 |

[`ORIENTATION.md`](ORIENTATION.md) explains the goals, what is settled and what is open, and where to start reading.

## Quick start

Requires FriCAS 1.4.0 or later (the Linux binary from the [FriCAS releases](https://github.com/fricas/fricas/releases) is enough).

```
git clone https://github.com/billpage/fricas-symbolic.git
cd fricas-symbolic
make check            # compiles each package and runs its unit tests
```

In a FriCAS session started in the repository directory:

```
)compile src/algebra/gsexpr.spad
x : SymbolicExpression(Integer) := 'x   -- = GeneralSymbolicExpression(Integer, [identities, annihilation, involutions, numerals])
(x+1)^2 - (x^2+2*x+1)          -- displayed as written
zero? %                        -- true: equality is that of Expression Integer
sum(x, 'x=1..10)               -- 55
integrate(sin(x)*cos(x), 'x)   -- correct, unlike the 2017 domain
```

`sexpr.spad` (`Symbolic` and its axiom domains) defines many constructors. In a fresh session, load its compiled libraries with `)lib )dir <directory>` **twice**: FriCAS 1.4.0's `)lib` records constructor signatures in load order, and the second pass repairs them. A `)compile` in the same session needs no `)lib`.

## Layout

| Path | Contents |
|---|---|
| `docs/spec/` | The specification. **Normative**: the code follows it, and a design change is a change to it first. |
| `docs/decisions/` | Numbered decision records: what was decided, by whom, why, and what it rules out. |
| `docs/notes/` | Analyses and design notes. Not normative; the specification wins where they differ. |
| `docs/INDEX.md` | Every labelled goal, axiom and result in the specification, with its section, its standing and the tests that check it. |
| `src/algebra/` | Spad source, as in FriCAS: `gsexpr.spad` (`GeneralSymbolicExpression`, `SymbolicExpression`, `SymbolicAxiomGroups`, `SymbolicTermOrder`), `symterm.spad` (`SymbolicTerm`, needs `gsexpr.spad` compiled first), `sexpr.spad` (the 2017 `Symbolic`). |
| `src/input/` | Tests, written with FriCAS's unit-test package, as in FriCAS's `src/input`. |
| `references/` | Bibliography. |
| `tools/` | `check_summary.py` (judges a test log) and `check_md_math.py` (checks math in the markdown). |

## Contributing

See [`CONTRIBUTING.md`](CONTRIBUTING.md). In short: questions and ideas go to Issues or Discussions; a change of design starts as a pull request against the specification; an implementation pull request cites the specification labels it implements and adds tests named by them. Changes that would touch FriCAS's core algebra or language are discussed on [fricas-devel](https://groups.google.com/g/fricas-devel) first.

## History

The work began on fricas-devel in the thread "Symbolic (unevaluated) Expressions" (November 2016 to February 2017), with contributions from Kurt Pagani, Qian Yun, Ralf Hemmecke and Waldek Hebisch. Its git history, from the first commit of 14 November 2016, was carried over from the `symbolic-expressions` branch of [billpage/fricas-dev](https://github.com/billpage/fricas-dev) together with the 2026 port. `src/input/sexpr2.input` is Kurt Pagani's 2017 test suite, updated for FriCAS 1.4.0.

## Licence

- Code (`src/`, `tools/`, `Makefile`): BSD 3-clause, the same terms as FriCAS. See [`LICENSE`](LICENSE).
- Documentation: Creative Commons Attribution 4.0 International, or, at your option, the BSD terms of `LICENSE`, so that FriCAS can include any part of it under its own licence. See [`LICENSE-DOCS`](LICENSE-DOCS).

AI assistance in this repository is described in [`AI-USE.md`](AI-USE.md).
