# Glossary

Terms as used in this repository, with where each is defined. Section numbers refer to [`docs/spec/sexpr-spec.md`](docs/spec/sexpr-spec.md).

| Term | Meaning here | Defined |
|---|---|---|
| **term**, **form**, **written form** | An expression as a labelled tree, as the user wrote it; FriCAS `InputForm`. | §2.1 |
| **value** | The element of `Expression R` that a term denotes, $`[\![t]\!]`$. | §2.2 |
| **evaluation** $`[\![\cdot]\!]`$ | The homomorphism from terms to `Expression R`. Partial where `Expression` is (division by zero). | §2.2 |
| **semantic equality** $`\equiv`$ | Same value. | §2.2 |
| **axiom set** $`A`$ | Equations between terms that a constructor applies automatically. | §2.3 |
| $`=_A`$ | Equality of terms modulo $`A`$: the least congruence containing $`A`$. | §2.3 |
| **sound** (S) | Every instance of every axiom holds in `Expression` where defined. | §2.3 |
| **normal form** $`\mathrm{nf}_A`$ | The result of rewriting with $`A`$ oriented left to right until no rule applies. | §2.4 |
| **terminating** (T), **confluent** (CR) | Rewriting always stops; and the normal form does not depend on the order of rewriting. | §2.4 |
| **design (I)**, **presentation** | `GeneralSymbolicExpression(R, A)`: pairs (form, value); equality is semantic. | §3.3 |
| **design (II)** | `Symbolic(R, A)`: terms modulo $`A`$; equality is $`=_A`$. | §3.2 |
| **invariant (Val)** | In design (I), the stored value equals the evaluation of the stored form. `check(x)` tests it. | §3.3 |
| **structural / semantic primitives** | In design (I), `isPlus`, `isTimes`, `isPower` and operator kernels read the form; `=`, `zero?`, `numer`, `denom`, `kernels` read the value. | §3.3 |
| **root-collapsing rule** | A rule whose right side is a variable of its left side, a numeral or $`-x`$; normalising a new node then never restructures its children. | §3.3 |
| $`A_P`$, **presentation axioms** | Identities (Id), annihilation (Ann), involutions (Inv), numerals (Num). | §4.1 |
| **numeral** | A constant of $`\mathrm{Frac}(R)`$ written as a single leaf. | §0 |
| **2017 SEXPR** | `SymbolicExpression(R)` in `src/algebra/sexpr.spad` as written in 2016–17 and ported in 2026. | §4.2 |
