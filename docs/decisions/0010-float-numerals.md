# 0010. Floats are numerals

- Status: Accepted (Bill Page, 2026-11-26: "it is good to treat floats as numerals"; the details below are Claude's, accepted with the pull request)
- Date: 2026-11-26
- Decided by: Bill Page
- Spec: §3.4 (numerals in the rungs), §3.5 (term order), §4.1 (Num), §5 (Disp)

## Context

Plan §4 asked whether floats can be numerals, since `Float` has no exact arithmetic and so the group `numerals` is not exactly sound for them. Bill decided that they are numerals: "even though equivalence is not exact, floats are normally treated as real values in almost all applications".

Three facts, checked with FriCAS 1.4.0 on 2026-11-26, shape the details:

1. **`R = Float` was impossible.** Both constructors required `R` to have `PatternMatchable Integer`, `ConvertibleTo Pattern Integer`, `PolynomialFactorizationExplicit` and `LinearlyExplicitOver Integer`, and `Float` has none of them. `Expression Float` exists because `Expression` exports pattern matching over `Integer` or over `Float` as `R` allows. Rewrite rules work in `Expression Float`, with `Float` patterns, including patterns that name a float constant.
2. **A float's own forms do not read back.** `convert(0.1)@InputForm` is `(float 236118324143482260685 -71 2)`, the binary mantissa. Its display `0.1` parses to `(($elt (Float) float) 1 -1 10)`, a decimal literal. Large and small floats display as `0.1234 E 26`, which does not parse as a number. So (Disp) fails for any float numeral formed from `Float`'s own `InputForm`.
3. **Negative numerals do not read back either, exact ones included.** The parser reads `-3` as `(- 3)` and `-1/2` as `(- (/ 1 2))`, while the stored forms were the atom `-3` and `(/ -1 2)`. This (Disp) defect predates floats: the tests of (Disp) had no negative numeral standing alone.

## Decision

- **`R` may be a floating-point domain.** The requirements on `R` are `ComparableRepresentation`, `GcdDomain`, `CharacteristicZero`, `RetractableTo Integer` and `ConvertibleTo InputForm`. Pattern matching (`PatternMatchable` and `ConvertibleTo Pattern`) is exported over `Integer` if `R` has it, and over `Float` if `R` has it, as in `Expression R`.
- **In a floating-point domain every numeral is a float numeral**, as in `Expression Float`, where `2*x` is `2.0 x`. A float numeral is a decimal fraction $`m \cdot 10^{e}`$ with at most $`d`$ significant digits, $`d`$ being `digits()` of `R` when the numeral is made. In other domains the numerals are the rational numbers, as before. Exponents and root indices are integers or rationals, not numerals of the coefficient domain, and stay exact: `x^2`, `x^(1/3)`, `nthRoot(x, 3)`.
- **A float numeral is the decimal it shows.** Its display is a decimal literal, positional (`0.1`, `12500.0`) for moderate magnitudes and with an exponent (`1.234e25`) otherwise. Its form is the parse of that literal, `(($elt (Float) float) m e 10)`, and its value is that decimal in `R`. So (Disp) holds by construction, and form, display and value agree.
- **Negative numerals**, exact or float, have the form $`(-\ n)`$ with $`n`$ the positive numeral, as the parser reads them.
- **Arithmetic on numerals is exact, then rounded.** Numerals are combined in exact rational arithmetic, since decimals are rationals; in a floating-point domain each result is then rounded to $`d`$ significant digits. This holds wherever numerals are combined: Num, the coefficients of P4, M4 and M5, and the Ring and Field rungs, which compute over `Fraction Integer` and round the coefficients of the result.
- **Term order:** exact numerals, then float numerals, then symbols (spec §3.5); numerals of one kind are compared by value, and trees of equal value by shape.

## Options considered for floats

1. **Exactness per numeral:** exact numerals stay exact in a float domain and floats are contagious. Rejected after testing: with `1.0` the identity of Id, $`(2.0-1)\,y + y`$ became `2*y` while $`2.0\,y`$ stayed `2.0*y`, two normal forms for equal terms, against (N2). Keeping `1.0` and `0.0` apart from `1` and `0` instead gives two zeros and two units, which is not a ring, and the Ring and Field rungs need one.
2. **All numerals of a float domain are floats** (chosen). One zero and one unit, no exactness to track; the same convention as `Expression Float`.

## Consequences

- `GeneralSymbolicExpression(Float, A)` and `SymbolicTerm(Float, A)` work, as do `DoubleFloat` domains, with rewrite rules over `Float` patterns.
- **Soundness holds up to rounding.** With float numerals, (S), (N1) and (N3) hold for the reals the numerals denote only up to the rounding of each result, and (N2) holds where no rounding occurs. Terms equal as reals can have different normal forms when their numerals round differently. For example, `1/3` is `0.33333333333333333333`, so `y + 1/3.0 + 1/3.0 + 1/3.0` and `y + 1.0` differ. A pattern naming a float constant matches by equality of decimals.
- Because arithmetic on numerals is exact before rounding, sums of short decimals are exact: `y + 0.1 + 0.2` is `y + 0.3`, which binary `Float` arithmetic does not give. Ring and Field reduce exactly: $`(y^2 - 0.01)/(y - 0.1)`$ is $`y + 0.1`$.
- In a float domain the user's `2` is displayed `2.0`, as in `Expression Float`.
- The precision is the one in force when a numeral is made. A later change of `digits()` changes new results, not existing numerals, and equality compares the decimals as written.
- The fix of negative numerals changes the stored form of every negative numeral, from `-3` to `(- 3)`: `unparse` now gives `-(3)`, and the display is unchanged (`-3`).
- A new domain, `SymbolicNumeral(R)`, holds the numerals: their arithmetic, rounding, forms and display.
