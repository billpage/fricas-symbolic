# Instructions for AI agents

Read [`README.md`](README.md), [`ORIENTATION.md`](ORIENTATION.md), [`CONTRIBUTING.md`](CONTRIBUTING.md) and [`AI-USE.md`](AI-USE.md) first. This file is the short version of the rules.

- **Delivery.** Never push to `main`. Push a branch named `claude/<topic>`; the maintainer opens and merges the pull request.
- **Specification first.** Do not change what a constructor promises (equality, categories, axioms) in code alone. Propose the change in `docs/spec/` with a decision record, and implement it after it is accepted.
- **Check behaviour by running FriCAS,** not from memory. Before committing code: `make check` (needs `fricas` on the PATH, or `FRICAS=...`).
- **Before committing markdown:** `make lint` (`npm install --no-save katex mathjax-full` once).
- **Tests:** FriCAS's unit-test package; `testcase` names cite the specification label; include must-fail tests.
- **Never commit:** build output (`build/`, `*.NRLIB`), copyrighted papers (link them in `references/bibliography.md`), private correspondence. Quote fricas-devel messages briefly and cite them by thread and date.
