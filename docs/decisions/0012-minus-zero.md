# 0012. Id contains the rule −0 → 0

- Status: Accepted
- Date: 2026-11-26
- Decided by: Bill Page (option (a))
- Spec: §3.4 (the group `identities`), §4.1 (Id, proof of Theorem 3)

## Context

Spec Theorem 3 states that $`A_P`$ and every union of its groups is sound, terminating and confluent. Its proof joined the critical pair of $`0-0`$ only through Num: $`x-0\to x`$ gives $`0`$, and $`0-x\to -x`$ gives $`-0`$, which Num folds to $`0`$. Without Num the pair is not joinable.

The Lean formalisation found this (plan [`lean-presentation-axioms.md`](../plans/lean-presentation-axioms.md), part 1, theorem L10): with Id but without Num, $`0-0`$ rewrites to two different normal forms, $`0`$ and $`-0`$. FriCAS shows the same split, checked on `main` at `b3494b6` on 2026-11-26: in `GeneralSymbolicExpression(Integer, A)` with $`A`$ = `[identities]`, `[identities, annihilation]`, `[identities, involutions]` or `[identities, annihilation, involutions]`, `0 - 0` has the form `0` and `-0` the form `(- 0)`. With `numerals` both are `0`.

## Options

1. **(a) Add $`-0\to 0`$ to Id** (chosen). It is sound, it decreases size ($`2\to1`$), and it is the rule Knuth–Bendix completion adds for this pair. In the code it is one clause in unary minus.
2. Restrict Theorem 3 to unions containing Num. That leaves `[identities]` without unique normal forms, against (N2).
3. Drop $`0-x\to -x`$ from Id. That keeps `0 - y` as written, but Id would no longer remove the identity on that side.

## Decision

The group `identities` (Id) contains $`-0\to 0`$, with the other identity rules. Under Id, `-0` and `0 - 0` both normalise to `0`, with or without Num, Ann and Inv. In a floating-point domain (decision 0010) the zero numeral is `0.0`, so `-0.0` normalises to `0.0`.

## Consequences

- The proof of Theorem 3 joins $`0-0`$ by the new rule. The rule creates one new overlap, $`-(-0)`$, with Inv's $`-(-x)\to x`$; it is joinable (both sides give $`0`$).
- Lean: `Step` of part 1 gains the rule, since it is defined from the spec. L10 then holds for the old rule set only and becomes a regression test, like L7 for (AN).
- Forms change only for terms with a unary minus of zero, under Id without Num.
