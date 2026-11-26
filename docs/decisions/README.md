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
| [0002](0002-presentation-axioms.md) | Presentation axioms for `SymbolicPair` | Accepted, 2026-11-25 |
| [0003](0003-repository.md) | A separate package repository, with the spec in it | Accepted, 2026-11-25 |
| [0004](0004-display-shows-structure.md) | The display shows the stored structure | Accepted, 2026-11-26 |
