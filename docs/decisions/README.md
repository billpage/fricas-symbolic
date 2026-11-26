# Decision records

One file per decision, numbered in order: `NNNN-<topic>.md`. A record is short and is not rewritten after the decision; a later decision that changes it says so, and the earlier record's status becomes *Superseded by NNNN*.

## Template

```
# NNNN. Title

- Status: Proposed | Accepted | Rejected | Superseded by NNNN
- Date: YYYY-MM-DD
- Decided by: name (for Accepted or Rejected)
- Spec: the sections this decision changes or relies on

## Context
What question had to be answered, and why now.

## Options
Each option with its mathematical and practical consequences.

## Decision
What was chosen.

## Consequences
What this commits the package to, and what it rules out.
```

## Records

| No. | Title | Status |
|---|---|---|
| [0001](0001-two-constructors.md) | Two constructors, one equality each | Accepted, 2026-11-25 |
| [0002](0002-presentation-axioms.md) | Presentation axioms for `SymbolicPair` (now `GeneralSymbolicExpression`) | Accepted, 2026-11-25 |
| [0003](0003-repository.md) | A separate package repository, with the spec in it | Accepted, 2026-11-25 |
| [0004](0004-display-shows-structure.md) | The display shows the stored structure | Accepted, 2026-11-26 |
| [0005](0005-associativity-group.md) | Associativity is an optional axiom group, not in $`A_P`$ | Accepted, 2026-11-26 |
| [0006](0006-name.md) | The name `GeneralSymbolicExpression(R, A)` | Accepted, 2026-11-26 |
| [0007](0007-symbolic-hidden-rewrites.md) | `SymbolicExpression` is rebuilt; `Symbolic` rewrites only by its axioms | Accepted, 2026-11-26 |
| [0008](0008-ladder-of-normalisers.md) | One library of normalisers, the ladder of axiom sets, and the term order | Accepted, 2026-11-26 |
| [0009](0009-symbolic-term-groups.md) | `SymbolicTerm(R, A)`, with axiom groups named in a list | Accepted, 2026-11-26 |
| [0010](0010-float-numerals.md) | Floats are numerals | Accepted, 2026-11-26 |
| [0011](0011-bridge-by-evaluation.md) | The bridge: evaluation by the universal property | Accepted, 2026-11-26 |
