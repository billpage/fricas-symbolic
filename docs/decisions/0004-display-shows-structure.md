# 0004. The display shows the stored structure

- Status: Accepted
- Date: 2026-11-26
- Decided by: Bill Page
- Spec: §1 (G1), §5 item 4 (Disp)

## Context

Spec §7 item 3 asked whether the display should flatten associative chains, for example print $`a+(b+c)`$ as `a+b+c`, while the stored tree keeps its grouping. A check of the display (2026-11-26) also found that it already lost grouping in three cases: $`a\cdot(b\cdot c)`$, $`a\cdot(b/c)`$ and $`a/(b/c)`$ were printed as `a*b*c`, `a*b/c` and `a/b/c`, which read back as different trees; the last also as a different value.

## Options

1. The display may simplify the presentation (flatten, drop parentheses) while the stored structure stays as built.
2. The display shows exactly the stored structure. Any change of structure, including flattening, is made by an axiom of the domain.

## Decision

Option 2. The user should have as much control as possible over the form of an expression, so what they see must be what they get. Made precise in the spec as property (Disp): the one-line display reads back (`parse$InputForm`) as the stored form.

## Consequences

- `coerce: % -> OutputForm` adds parentheses wherever the reading conventions would otherwise regroup; the three cases above are fixed and tested (28 shapes, `sympair.input`, test case "Disp").
- Spec §7 item 3 becomes: should an associativity axiom be part of the default set $`A_P`$? It is a question about axioms, not about display.
