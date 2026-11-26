# 0005. Associativity is an optional axiom group, not in $`A_P`$

- Status: Accepted
- Date: 2026-11-26
- Decided by: Bill Page
- Spec: §4.1.1; follows 0004

## Context

After 0004 (the display shows the stored structure), flattening chains such as $`a+(b+c)`$ can only come from an axiom. Should associativity be in the default axiom set $`A_P`$ of `SymbolicExpression(R)`?

## Options

1. Add associativity to $`A_P`$: every chain is stored left-nested and displayed flat.
2. Keep it out of $`A_P`$, and offer it as an axiom group `associativity` that a user adds to $`A`$.

## Decision

Option 2.

- $`A_P`$ is defined by a test: each rule removes something or folds numerals, and none reorders or regroups what was written. Associativity regroups, so in the default the user could not keep a grouping they typed.
- Rewrite rules gain nothing from it: `isPlus` already gives the pattern matcher all terms of a nested sum.
- As a group it costs nothing to those who want it. $`A_P \cup \mathrm{Assoc}`$ is sound, terminating (lexicographic order on size and the right-operand measure $`\mu`$) and confluent (spec §4.1.1).

## Consequences

- The spec gains §4.1.1 with the rules $`x \circ (y \circ z) \to (x \circ y) \circ z`$ for $`\circ \in \{+, \cdot\}`$, the termination proof and the critical pairs.
- The implementation adds the group `associativity`, as a recursion through the domain's own operations, with tests for each rule, for its absence from the default, and for (Disp) on flattened chains.
- Without commutativity, numeral folding stays incomplete under Assoc: $`(x+1)+2`$ is not folded.
