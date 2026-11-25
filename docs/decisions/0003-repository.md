# 0003. A separate package repository, with the spec in it

- Status: Accepted
- Date: 2026-11-25
- Decided by: Bill Page

## Context

The specification and notes lived in a private Claude project; the code lived on the `dev` branch of `billpage/fricas-dev`, a fork of FriCAS. Collaborators need to read the documents and propose changes to them, next to the code.

## Options

1. Documents and code in `fricas-dev`: a collaborator must clone all of FriCAS; upstream's CI runs on the fork; `dev` mixes unrelated experiments; upstream has no place for design documents.
2. A separate repository for the package, modelled on Ralf Hemmecke's QEta (a FriCAS package developed outside the FriCAS tree), with the documentation conventions of `billpage/wpmw` and `billpage/oziewicz`.

## Decision

Option 2: `billpage/fricas-symbolic`.

- Code directories mirror FriCAS (`src/algebra`, `src/input`), and the code builds against an unmodified FriCAS release, so a finished piece can be proposed upstream file for file.
- Licences: code BSD 3-clause, as FriCAS; documentation CC BY 4.0 or, at the user's option, BSD 3-clause, so that FriCAS can take any part under its own licence.
- The git history of the files was carried over from `fricas-dev` (branch `symbolic-expressions`, 2016–17, then the 2026 port).
- `fricas-dev` remains the FriCAS fork: the upstream mirror, `dev` for work that needs a FriCAS rebuild, and branches for upstream pull requests.

## Consequences

- CI installs the FriCAS 1.4.0 release binary and runs `make check`, so the tests are checked on every pull request.
- The Claude project's documents become working notes; this repository is canonical.
