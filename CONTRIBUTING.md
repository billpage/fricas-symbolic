# Contributing

Contributions of every size are welcome: a question, a counterexample, a test, a proof, a fix. The process below is light on purpose. Its one firm rule is that **the specification leads and the code follows**, so that the design does not drift.

## Where things go

| You have | Put it in |
|---|---|
| A question, an idea, a half-formed proposal | an Issue or a Discussion |
| A bug (wrong result, crash) | an Issue with the FriCAS input that shows it |
| An analysis or design argument | a pull request adding a note under `docs/notes/` |
| A change to what the package promises | a pull request against `docs/spec/`, with a decision record (below) |
| An implementation of something the spec already says | a pull request against `src/`, with tests |

## Kinds of change

**1. Design changes.** Anything that changes a goal, an axiom set, a constructor's equality or the categories it claims.

- The pull request edits `docs/spec/` and adds `docs/decisions/NNNN-<topic>.md` with status *Proposed* (see `docs/decisions/README.md`).
- It states the mathematical reason. For an axiom: soundness in `Expression`, termination, confluence (spec §2.3–2.4), and its effect on the written form (G1).
- The maintainer marks it *Accepted* or *Rejected* when merging or closing.
- A change that would touch FriCAS's core algebra or the language (as opposed to this package) is raised on [fricas-devel](https://groups.google.com/g/fricas-devel) before any code.

**2. Implementation.** Code that carries out what the specification already says.

- Name the specification labels it implements in the pull request (e.g. "spec §4.1, Num").
- Add tests in `src/input/` with FriCAS's unit-test package, and name each `testcase` by the label it checks. Include at least one test that must fail (`xftest…`), so that a check that cannot fail is noticed.
- Update `docs/INDEX.md` (the tests column).
- `make check` must pass. CI runs it on every pull request.

**3. Notes and examples.** Analyses, worked examples, background. These are not normative and need no decision record.

## Conventions

- **Spad** follows FriCAS's own style: `++` documentation on every export, upstream naming, no project-specific comments in code that may go upstream.
- **Tests** use `)expose UnittestCount UnittestAux Unittest`, `testsuite`/`testcase`/`testTrue`/`testEquals`, and end with `statistics()`. `testsuite` and `testcase` clear macros as well as variables, so write domain names in full inside each test case.
- **Math in markdown** uses GitHub's forms: inline $`…`$ in backtick-dollar form, display math in fenced `math` blocks. `make lint` checks it (needs `npm install --no-save katex mathjax-full` once for the rendering checks). CI runs it too.
- **Commits:** one topic per branch and pull request; messages say what and why.

## Review and merging

Bill Page maintains the repository and merges pull requests into `main`. `main` is protected: all changes arrive through pull requests.

## Licensing of contributions

By contributing you agree that your contribution is licensed under the repository's terms: code under the BSD 3-clause licence (`LICENSE`), documentation under CC BY 4.0 with the BSD option (`LICENSE-DOCS`). This keeps every part usable by FriCAS under its own licence.
