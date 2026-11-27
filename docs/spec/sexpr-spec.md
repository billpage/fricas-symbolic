# Symbolic expressions in FriCAS: goals, mathematical specification and axiom selection

*Draft for review, 2026-11-25. Supersedes the informal design notes [`docs/notes/2026-11-24-design-review.md`](../notes/2026-11-24-design-review.md) and [`docs/notes/2026-11-25-q2-functionspace.md`](../notes/2026-11-25-q2-functionspace.md) wherever they differ. The implementation is to follow this document; a change of design is a change to this document first.*

## 0. Notation

| Symbol | Meaning |
|---|---|
| $`R`$ | coefficient domain (e.g. `Integer`) |
| $`K = \mathrm{Frac}(R)`$ | its field of fractions; the **numerals** are the elements of $`K`$. If $`R`$ is a floating-point domain, they are decimal fractions with at most `digits()` significant digits, and arithmetic on them is exact, then rounded (decision [0010](../decisions/0010-float-numerals.md)) |
| $`X`$ | the set of variables (FriCAS `Symbol`s) |
| $`\Sigma`$ | the signature: constants $`K`$; $`+,\ -,\ \cdot,\ /`$ and `^` (binary); $`-`$ (unary); and the named functions $`\Phi = \{\sin, \exp, \log, \ldots\}`$ with their arities |
| $`T = T_\Sigma(X)`$ | the terms over $`\Sigma`$ and $`X`$, i.e. labelled trees (FriCAS `InputForm`) |
| $`E = \mathrm{EXPR}(R)`$ | FriCAS `Expression(R)`, regarded as a (partial) $`\Sigma`$-algebra |
| $`[\![\,\cdot\,]\!] : T \rightharpoonup E`$ | evaluation (§2.2) |
| $`A`$ | a set of axioms, i.e. equations $`l \approx r`$ with $`l, r \in T`$ |
| $`=_A`$ | the least $`\Sigma`$-congruence on $`T`$ containing all instances of $`A`$ |
| $`\mathrm{nf}_A(t)`$ | the normal form of $`t`$ under the rules obtained by orienting $`A`$ |
| $`\lvert t\rvert`$ | the size of $`t`$: number of nodes, a numeral counting as one node |

Message numbers $`[n]`$ refer to the fricas-devel thread "Symbolic (unevaluated) Expressions" (2016-11-14 to 2017-02-25), as in the [design review](../notes/2026-11-24-design-review.md).

## 1. Goals

| # | Goal | Source |
|---|---|---|
| G1 | **Display as entered.** "Unevaluated … with no automatic simplifications"; keep "the similarity of its input form". What the user sees is the stored structure ("what you see is what you get"); any change of structure is made by an axiom, never by the display. Made precise as (Disp), §5. | Bill [0], Qian [3]; Bill, 2026-11-26 |
| G2 | **Same meaning as `Expression`.** Expressions "may be simplified, compared as and/or converted to fully evaluated expressions in the appropriate Expression domain"; `test(a = b)` decides equality of meaning. | Bill [0] |
| G3 | **Purely syntactic work without an autonomous simplifier**, e.g. syntactic unification, where $`1+2 \neq 3`$. | Kurt [2], [32]; Bill [33] |
| G4 | **Rewrite rules act on the written structure**, e.g. the SandBoxSymbolicTrig example. | Kurt (trig thread), Frangos |
| G5 | **Selectable automatic rewriting:** a domain is parameterised by the axioms it applies. | Bill's design, `Symbolic(R, A)` |
| G6 | **Library algorithms give correct results** (integration, summation, limits, linear algebra). | design review, defect D1 |
| G7 | **Automatic rewriting terminates and is deterministic.** | Bill [27] (non-termination observed) |
| G8 | **Formatting is decided by `coerce: % -> OutputForm`**, not by sharing representations with `OutputForm`. | Waldek [10] |

G1 and G3 constrain what the *form* may do automatically. G2 and G6 constrain what *equality* must mean. The two constraints are incompatible in one equality relation (§3.1). The design therefore keeps two constructors, each with one equality.

## 2. Mathematical framework

### 2.1 Terms

$`T`$ is the term algebra (absolutely free $`\Sigma`$-algebra) over $`X`$. A term is what the user wrote, as a labelled tree. Subtraction and division are kept as operators of their own rather than as $`+`$ and $`\cdot`$ with inverses, because the user writes them.

### 2.2 Evaluation

$`E`$ interprets every symbol of $`\Sigma`$, and every $`x \in X`$ is an element of $`E`$. Since $`T`$ is free, there is exactly one $`\Sigma`$-homomorphism extending $`x \mapsto x`$:

```math
[\![\,\cdot\,]\!] : T \rightharpoonup E, \qquad [\![\omega(t_1,\ldots,t_n)]\!] = \omega_E\big([\![t_1]\!],\ldots,[\![t_n]\!]\big).
```

It is partial only where $`E`$ is (division by an expression equal to $`0`$). Its kernel is the **semantic equality**

```math
s \equiv t \iff [\![s]\!] = [\![t]\!].
```

### 2.3 Axioms and soundness

An axiom set $`A`$ generates $`=_A`$, the equational theory of $`A`$ (Birkhoff). $`A`$ is **sound for $`E`$** if every instance of every axiom holds in $`E`$ wherever its left side is defined:

```math
\textbf{(S)}\qquad [\![l\sigma]\!] = [\![r\sigma]\!] \quad\text{for all } (l \approx r) \in A \text{ and all substitutions } \sigma \text{ with } [\![l\sigma]\!] \text{ defined}.
```

**Lemma 1 (soundness).** If (S) holds, then $`s =_A t`$ implies $`s \equiv t`$ (for defined terms).

*Proof.* $`\equiv`$ is a congruence, because $`[\![\cdot]\!]`$ is a homomorphism, and by (S) it contains every instance of $`A`$. Since $`=_A`$ is the least such congruence, $`=_A \subseteq \equiv`$. $`\square`$

### 2.4 Rewriting

Orienting each axiom $`l \approx r`$ as $`l \to r`$ gives a rewrite system $`\mathcal R_A`$. Three properties matter:

- **(T) Termination:** there is a well-founded order $`>`$, closed under contexts and substitutions, with $`l > r`$ for every rule. For the rule sets below, the size $`\lvert t\rvert`$ suffices: every rule strictly decreases it.
- **(CR) Confluence:** all critical pairs are joinable. For a terminating system this is equivalent to confluence (Knuth–Bendix critical pair lemma together with Newman's lemma). It then gives unique normal forms: $`s =_A t \iff \mathrm{nf}_A(s) = \mathrm{nf}_A(t)`$.
- **Modulo $`B`$:** axioms that cannot be oriented, such as commutativity, require rewriting modulo $`B`$. Confluence must then be checked with $`B`$-unification: Peterson–Stickel; Jouannaud–Kirchner. Termination needs a $`B`$-compatible order, e.g. AC-RPO (Rubio–Nieuwenhuis).

## 3. The two constructors

### 3.1 Why one equality cannot serve both G1/G3 and G2/G6

FriCAS's `Ring` and `FunctionSpace` promise that $`=`$, `zero?`, `numer`, `denom` and `kernels` describe the same structure. With syntactic equality $`=_A`$, a ring requires $`A`$ to prove distributivity, and then $`(x+1)^2 =_A x^2+2x+1`$. The normal forms are then expanded polynomials, which contradicts G1. Conversely, semantic equality cannot distinguish $`1+2`$ from $`3`$, which contradicts G3. The 2017 `SymbolicExpression` mixed the two equalities, and the wrong integrals and sums followed from that (design review, D1).

### 3.2 Design (II): `SymbolicTerm(R, A)`, the term algebra modulo $`A`$

*Named by decision [0009](../decisions/0009-symbolic-term-groups.md). It replaces the 2017 implementation `Symbolic(R, A)`, whose parameter was a `join` of axiom domains, retired in plan step 6 ([note](../notes/2026-11-26-retiring-symbolic.md)).*

- **Carrier:** $`T/{=_A}`$, represented by normal forms $`\mathrm{nf}_A`$.
- **Equality:** $`=_A`$, decided by comparing normal forms. This requires a normaliser with (N1) and (N2) (§3.4). A terminating and confluent rewrite system modulo $`B`$ is one way to obtain one (§2.4); the ladder of §3.4 builds canonical forms of free algebras directly.
- **Categories and conversions** (decision [0011](../decisions/0011-bridge-by-evaluation.md)): no categories that depend on $`A`$; Spad cannot export them from one constructor. Instead, $`T/{=_A}`$ is the free algebra over the symbols in the variety of $`\Sigma`$-algebras satisfying $`A`$, so for every $`\Sigma`$-algebra $`D`$ satisfying $`A`$ and every $`\varphi : X \to D`$ there is exactly one homomorphism $`\mathrm{eval}_\varphi : T/{=_A} \to D`$ extending $`\varphi`$. The value map of §2.2 is the case $`D = E`$. Implemented as `eval` in `SymbolicTermFunctions2(R, A, D)`, which refuses a `D` without the category asserting a group's axioms (a commutative ring for `commutativity`, `linear`, `powers`, `ring`; a field for `quotients`, `field`; `Fraction Integer` in `D` for `numerals`). The other direction is the read-back `convert : InputForm -> SymbolicTerm(R, A)`, which is the quotient map when it adds axioms. *(Until decision 0011: categories exactly those whose axioms follow from $`A`$, e.g. `AbelianMonoid` for `+` with assoc, comm and $`0`$; never `Ring` or `FunctionSpace` unless $`A`$ contains the ring axioms, §3.1.)*
- **Soundness for $`E`$** is required only for the conversion to `Expression`, i.e. for $`\mathrm{eval}`$ into $`D = E`$. $`A`$ may describe a different algebra, e.g. graded-commutative (§4.2); then no conversion to $`E`$ is offered, and $`\mathrm{eval}`$ goes to a $`D`$ that satisfies $`A`$.
- **G3:** `Symbolic(R, None)` applies no rewriting at all; $`=_\emptyset`$ is syntactic identity of terms.

### 3.3 Design (I): `GeneralSymbolicExpression(R, A)`, a presentation of `Expression`

*Named `SymbolicPair` until 2026-11-26 (decision [0006](../decisions/0006-name.md)); older records and notes use that name.*

**Carrier:**

```math
P_A = \{\, (t, v) : t \in \mathrm{NF}_A,\ v = [\![t]\!] \in E \,\}.
```

The **form** $`t`$ is what is displayed; the **value** $`v`$ is what is meant.

**Operations:** for $`\omega \in \Sigma`$,

```math
\omega\big((t_1,v_1),\ldots,(t_n,v_n)\big) = \big(\mathrm{nf}_A(\omega(t_1,\ldots,t_n)),\ \omega_E(v_1,\ldots,v_n)\big).
```

**Equality:** $`(t,v) = (t',v') \iff v = v'`$, i.e. $`\equiv`$.

**Invariant (Val):** $`v = [\![t]\!]`$.

**Proposition 2.** If $`A`$ is sound (S) and $`\mathcal R_A`$ terminates (T), then every operation preserves (Val), and the map $`\mathrm{val}: P_A \to E`$ is a $`\Sigma`$-homomorphism. With equality $`\equiv`$, $`P_A`$ is isomorphic to its image in $`E`$. Hence $`P_A`$ satisfies every equational law that $`E`$ satisfies, and may honestly claim every category $`E`$ has (`Field`, `FunctionSpace`, …).

*Proof.* $`\mathrm{nf}_A(\omega(\vec t))`$ exists by (T). It satisfies $`[\![\mathrm{nf}_A(\omega(\vec t))]\!] = [\![\omega(\vec t)]\!]`$ by Lemma 1, and the right side equals $`\omega_E(\vec v)`$ by (Val) for the arguments. Equality is the kernel of $`\mathrm{val}`$, so $`\mathrm{val}`$ is injective on the quotient. $`\square`$

Note that **(I) needs only (S) and (T), not (CR)**. Equality comes from the value, so different normal forms of the same term would merely be different presentations of one element. Confluence is still wanted, for G7 (deterministic display), but correctness does not depend on it.

**Primitives:**

- *Semantic* (`=`, `zero?`, `numer`, `denom`, `kernels`, `differentiate`, retractions) are defined through $`\mathrm{val}`$.
- *Structural* (`isPlus`, `isTimes`, `isPower`, the kernel of an operator node) read the form, for G4. The `FunctionSpace` contract only asks for a valid decomposition: $`\mathrm{isPlus}(p) = [p_1,\ldots,p_k] \Rightarrow \sum \mathrm{val}(p_i) = \mathrm{val}(p)`$. This holds because each $`p_i`$ is a subterm with value $`[\![p_i]\!]`$.
- Each node answers only the question matching its written shape; constants and results of library algorithms answer like their value. (Without this restriction, the 2026-11-25 prototype runs showed the integrator taking wrong paths.)

**Root-collapsing rules.** If every rule's right side is a variable of its left side, a numeral, or $`-x`$, then normalising a new node never restructures its children. Each node can therefore store its children together with their values, and no re-evaluation of subterms is needed. All the rules in $`A_P`$ (§4.1) have this property.

**Conversions:**
- $`E \to P_A`$: $`v \mapsto (\mathrm{nf}_A(\mathrm{form}(v)), v)`$, where $`\mathrm{form}(v)`$ is `Expression`'s own structural `convert(v)@InputForm` (no interpreter, fixing D7).
- $`P_A \to E`$ is $`\mathrm{val}`$.

### 3.4 One library of normalisers: the ladder of axiom sets

*Decision [0008](../decisions/0008-ladder-of-normalisers.md). This section and §3.5 replace, for design (II), the 2017 axiom categories, which rewrite binary trees with an order that was never shown to terminate (§4.2).*

**Normalisers.** For an admissible axiom set $`A`$ (defined below), a *normaliser* is a function $`N_A : T \to T`$ with

- **(N1) correct:** $`N_A(t) =_A t`$ for every term $`t`$;
- **(N2) canonical:** $`s =_A t \implies N_A(s) = N_A(t)`$ (identity of trees).

Together, $`s =_A t \iff N_A(s) = N_A(t)`$, and $`N_A`$ is idempotent: $`N_A(N_A(t)) = N_A(t)`$, since $`N_A(t) =_A t`$ by (N1). If $`A`$ is sound (S), then by Lemma 1 $`N_A`$ also preserves values where the term is defined:

- **(N3) value-preserving:** $`[\![t]\!]`$ defined $`\implies [\![N_A(t)]\!] = [\![t]\!]`$.

A normaliser need not come from a rewrite system. For the sets below it builds the canonical element of a known free algebra directly. (N2) then holds because canonical forms of a free algebra are unique, and no termination order or critical-pair check is involved.

**Both constructors use the same normalisers** and differ only in their equality:

| | `SymbolicTerm(R, A)`, design (II) | `GeneralSymbolicExpression(R, A)`, design (I) |
|---|---|---|
| Carrier | $`N_A(T)`$ | pairs $`(N_A(t), [\![t]\!])`$ |
| Operation $`\omega`$ | $`N_A(\omega(t_1, \ldots, t_n))`$ | form $`N_A(\omega(t_1, \ldots, t_n))`$, value $`\omega_E(v_1, \ldots, v_n)`$ |
| Equality | identity of normal forms, i.e. $`=_A`$ | equality of values, i.e. $`\equiv`$ |
| Needs | (N1), (N2) | (S) and (N1), hence (N3) and (Val) |
| Display | the normal form | the normal form of what was written |

So any sound admissible $`A`$ can serve as presentation axioms (Proposition 2). For example, `GeneralSymbolicExpression(R, [commutativity])` would display sums with sorted operands while keeping semantic equality. $`A_P`$ (§4.1) and Assoc (§4.1.1) are normalisers of this kind (Theorem 3).

**Atoms.** For a given $`A`$, an *atom* of an operator $`\circ`$ is a normal form whose head is not $`\circ`$, and not an operator that $`A`$ expresses through $`\circ`$ (below: $`-`$ through $`+`$, $`/`$ through $`\cdot`$). Numerals, symbols and applications $`f(t_1, \ldots, t_n)`$ are atoms of every operator. A power with a non-integer exponent, such as $`x^{1/2}`$, is an atom of $`\cdot`$.

**The rungs for $`+`$.** Each rung is the free algebra of its axioms over the atoms of $`+`$:

| Rung | Axioms for $`+`$ | Normal form of a sum | Free algebra | FriCAS container |
|---|---|---|---|---|
| P0 | none | binary tree as written | term algebra | `InputForm` |
| P1 | C | binary tree, the two operands of each node in $`\prec`$ order | free commutative magma | `InputForm` |
| P2 | A | flat list, written order | free semigroup | `List` |
| P3 | AC | flat list in $`\prec`$ order (a multiset) | free commutative semigroup | `List` |
| P4 | AC, Id ($`0`$), Num, Doubles, Cancels, with $`x-y \approx x + (-1)\,y`$ and $`-x \approx (-1)\,x`$ | a numeral $`c`$ plus a finite sum $`\sum_i c_i\, a_i`$ with distinct atoms $`a_1 \prec \cdots \prec a_k`$ and numerals $`c_i \ne 0`$ | free $`K`$-vector space on the atoms, plus constants | `FreeModule(K, S)` |

In the implementation the flat lists of P2/P3 (and M2/M3) are stored as left-nested chains, which display as `a+b+c` (Disp). Under P3/M3 with `numerals`, all numerals of a chain fold into one, since numerals come first in $`\prec`$ and so become neighbours; with `identities` the identity element is dropped, and with `annihilation` a product with a factor $`0`$ is $`0`$.

P4 takes Doubles and Cancels together: with numeral coefficients, a sum of coefficients can vanish, so one without the other is not closed under Num.

**The rungs for $`\cdot`$:**

| Rung | Axioms for $`\cdot`$ | Normal form of a product | Free algebra | FriCAS container |
|---|---|---|---|---|
| M0–M3 | as P0–P3 | as P0–P3 | as P0–P3 | as P0–P3 |
| M4 | AC, Id ($`1`$), Num, Squares | a numeral times $`\prod_i a_i^{e_i}`$, distinct atoms in $`\prec`$ order, integers $`e_i \ge 1`$ | free commutative monoid | `FreeModule(Integer, S)`, exponents $`\ge 1`$ |
| M5 | M4, Divides, with $`x/y \approx x \cdot y^{-1}`$ | the same with integers $`e_i \ne 0`$ | free abelian group | `FreeModule(Integer, S)` |

M5 is sound where defined: $`x \cdot x^{-1} \to 1`$ holds wherever $`x \ne 0`$, which is where the left side is defined.

**Trees of P4, M4 and M5.** The normal forms of the tables are stored as `InputForm` trees, built so that (Disp) holds:

- *Sums (P4).* The terms $`c_i\, a_i`$ in $`\prec`$ order of their atoms, then the constant $`c`$ if $`c \ne 0`$. A term is $`a_i`$ if $`c_i = 1`$, otherwise $`c_i \cdot a_i`$. The first term is negated with unary minus if $`c_i < 0`$; each later term is added, or subtracted with $`\lvert c_i\rvert`$ if $`c_i < 0`$. Examples: $`y - 2x + 1`$ has form `(-(2*x))+y+1`, and $`3 - x`$ has form `(-x)+3`. The constant comes last, unlike in P3, where numerals come first in $`\prec`$.
- *Products (M4, M5).* The factors with $`e_i > 0`$ in $`\prec`$ order form the numerator, $`a_i^{e_i}`$ or $`a_i`$ if $`e_i = 1`$; the numeral $`c`$ leads it if $`c \ne 1`$. If some $`e_i < 0`$, the factors $`a_i^{-e_i}`$ form a denominator and the tree is numerator `/` denominator. Examples: $`x/(2y)`$ has form `((1/2)*x)/y`, and $`x/(y x^2)`$ has form `1/(x*y)`. Under M4 alone a power with a negative exponent is an atom.
- *Both (P4 with M4 or M5).* The atoms of $`+`$ are the products. A numeral factor of a product is its coefficient, so $`2xy + 3yx`$ has form `5*x*y`.

- *Ring.* A polynomial is a P4 sum whose atoms are M4 monomials; the atoms of the polynomial are the normal forms whose head is none of $`+, -, \cdot`$, a division by a numeral, or a power with exponent in $`\mathbb{N}`$. Examples: $`x(x+1)`$ has form `x+x^2`, and $`(x+1)(x-1)`$ has form `x^2-1`.
- *Field.* A fraction $`p/q`$ with $`\gcd(p, q) = 1`$ (now also over divisions and powers with exponent in $`\mathbb{Z}`$). A constant $`q`$ is divided into $`p`$, which gives a Ring form. Otherwise $`p`$ and $`q`$ are scaled to integer coefficients with no common factor, and the first term of $`q`$ positive, as in `Fraction Polynomial Integer`; the tree is `p/q`, with a leading unary minus of $`p`$ in parentheses (Disp). Examples: $`(2x+2)/(4x-4)`$ has form `(x+1)/(2*x-2)`, and $`x/(2y)`$ has form `x/(2*y)`, where M5 gives `((1/2)*x)/y`.

The implementation computes Ring and Field in `Fraction Polynomial Fraction Integer`, with a fresh symbol for each atom, and rebuilds the result as above; (N2) for Field rests on FriCAS's polynomial gcd.

The order of terms and factors is $`\prec`$, which is not a degree order: $`(x-y)^3`$ has form `3*x*y^2-3*y*x^2+x^3-y^3`. A degree order is a possible later change, after wider review (plan §4).

In P4 a numeral times a sum is scalar multiplication, so $`2(x+y) = 2x + 2y`$ and $`0 \cdot x = 0`$ without `annihilation`. Other products of sums are distributivity, the Ring rung: $`x(y+1)`$ stays a product.

**Linking axioms**, which relate $`+`$ and $`\cdot`$:

| Axioms | Requires | Normal form | FriCAS container |
|---|---|---|---|
| Ann: $`0 \cdot x \approx 0`$ | any rungs | as the rungs, with products containing $`0`$ replaced by $`0`$ | |
| Ring: distributivity | P4 and M4 | polynomial over $`K`$ in the atoms of both | `SparseMultivariatePolynomial(K, S)` |
| Field: distributivity | P4 and M5 | reduced fraction $`p/q`$, $`\gcd(p, q) = 1`$, $`q`$ normalised | `Fraction` of the above |

The Ring and Field rungs are not `Expression`. Their equality is polynomial (rational-function) identity with the functions left uninterpreted. `Expression` identifies more, e.g. $`\sqrt2^{\,2} = 2`$, $`e^{\log x} = x`$, $`\sin 0 = 0`$ (run of 2026-11-26), so $`=_{\mathrm{Field}} \subsetneq \equiv`$.

**Axiom groups and admissible sets** (decision [0009](../decisions/0009-symbolic-term-groups.md)). Both constructors take $`A`$ as a list of group names, `List Symbol`, with one vocabulary:

| Group | Axioms | Requires | Rung |
|---|---|---|---|
| `identities` | Id: $`0+x,\ x+0,\ x-0,\ 0-x,\ -0,\ 1\cdot x,\ x \cdot 1,\ x/1,\ x^1,\ x^0`$ (§4.1) | — | |
| `annihilation` | Ann: $`0 \cdot x,\ x \cdot 0`$ | — | Ann |
| `involutions` | Inv: $`-(-x),\ 1/(1/x)`$ | — | |
| `numerals` | Num: fold operations on numerals | — | |
| `associativity` | A for $`+`$ and $`\cdot`$; with `numerals` also (AN) (§4.1.1) | — | P2, M2 |
| `commutativity` | C for $`+`$ and $`\cdot`$ | — | P1, M1; with `associativity` P3, M3 |
| `linear` | Doubles, Cancels, signed sums | `commutativity`, `associativity`, `identities`, `numerals` | P4 |
| `powers` | Squares: products as power products with exponents $`\ge 1`$ | `commutativity`, `associativity`, `identities`, `numerals` | M4 |
| `quotients` | Divides, $`x/y \approx x \cdot y^{-1}`$: exponents in $`\mathbb{Z}`$ | `powers` | M5 |
| `ring` | distributivity: polynomials in the atoms | `linear`, `powers` | Ring |
| `field` | reduced fractions | `ring`, `quotients` | Field |

$`A`$ is **admissible** if every name in it is a group of this table, and the groups it requires are in $`A`$ too; moreover `ring` and `quotients` together require `field` (decision 0009, amended: without `field`, $`(y+1)^{-1}(y+1)`$ would distribute to $`(y+1)^{-1}y + (y+1)^{-1}`$ instead of becoming $`1`$). Requirements are listed, not implied, so the list shows everything that applies. A constructor rejects an inadmissible $`A`$ when it is instantiated, with an error naming the unknown group or the missing requirement. Both constructors implement every group (plan steps 3–5). The empty list is rungs P0/M0: no rewriting. $`A_P`$, with or without `associativity`, is admissible (Theorem 3). AntiCommutative of 2017 is not a group: it is unsound for $`E`$ (§4.2) and has no rung yet.

### 3.5 The structural term order $`\prec`$

Rungs P1, P3, P4 and M1, M3–M5 sort atoms by a strict total order $`\prec`$ on normal forms. Any strict total order gives canonical forms: if the operands are canonical, their sorted list is canonical. The choice of $`\prec`$ therefore affects only the display, not correctness. It is defined on terms as `InputForm` trees, by structural recursion. Constants of $`R`$ enter as their `InputForm` conversion, so $`R`$'s own order is not used. *(Corrected 2026-11-26: the first version compared numerals with $`R`$'s `smaller?` and required $`R`$ to be `Comparable`; both were unnecessary, and comparing by value alone is not total on trees, e.g. `2/4` and `1/2`.)*

1. **Kinds**, in this order: exact numerals (integer atoms, quotients `(/ m n)` of integer atoms with $`n \ne 0`$, and their negations `(- n)`); float numerals (float literals `(($elt (Float) float) m e b)` and `(float m e b)`, float atoms, and their negations); symbols; strings; other atoms; compound terms.
2. **Numerals** of one kind by value in `Fraction Integer`; a float literal denotes $`m \cdot b^{e}`$ exactly. Ties between different trees of equal value, such as the atom `-3` and `(- 3)`, or `(/ 1 2)` and `(/ 2 4)`, by shape: an atom before a compound term, and compound terms as in step 5. This gives the earlier rule for exact numerals, an integer before a quotient and quotients by numerator, as a special case.
3. *(Merged into step 2 by decision 0010: float numerals, including the literals that floats written in the input parse to, are ordered by value.)*
4. **Symbols** by `smaller?$Symbol`, the order of the `OrderedSet` `Symbol`. **Strings** by `String`'s order. **Other atoms** by their `unparse` text.
5. **Compound terms** $`(h\ t_1 \ldots t_n)`$ and $`(h'\ u_1 \ldots u_m)`$ lexicographically by head, number of arguments, and argument list. Heads, usually operator symbols, and arguments are compared by $`\prec`$ recursively; the argument lists have equal length once the arities are equal.

**Proposition 4.** $`\prec`$ is a strict total order on $`T`$.

*Proof.* By induction on $`\max(\lvert s\rvert, \lvert t\rvert)`$ for a comparison of $`s`$ with $`t`$. Steps 1–4 order the kinds, and within each kind by strict total orders: for numerals, the lexicographic product of value and the shape order of step 5, which separates any two distinct trees (two distinct atoms of one kind of numeral have different values). Step 5 is the lexicographic product of the order on heads and arguments (by the induction hypothesis, since these are strictly smaller) with the order on arities. A lexicographic product of strict total orders is a strict total order: irreflexive, transitive and total. $`\square`$

Implemented as `SymbolicTermOrder` (`SYMORD`) in `src/algebra/gsexpr.spad`. Checked exhaustively on 37 terms, i.e. all pairs and all 50,653 triples, in `gsexpr.input`, test case "Ord".

**Remarks.**
- $`\prec`$ is not a reduction order and plays no part in termination; the normalisers of §3.4 terminate by structural recursion.
- Display conventions are separate from $`\prec`$: in a P4 sum the constant is shown last, and in an M4 product the numeral first, as in $`2x + y + 1`$.
- $`\prec`$ replaces `smaller?` of the 2017 `SINFunctions`, whose own comment said it was "not yet proven" to be a total order.

## 4. Axiom analysis

### 4.1 The presentation axioms $`A_P`$

The subscript stands for *presentation* (§3.3): these are the axioms a presentation of `Expression` may apply without changing the written form beyond recognition. Each rule removes something (an identity element, a double negation or reciprocal, a factor beside zero) or evaluates pure numerals; none reorders or regroups what was written, and each right side is a variable of its left side, a numeral or $`-x`$ (root-collapsing). Commutativity and collecting like terms are sound but fail this test.

$`n, m`$ denote numerals, $`x`$ a variable of the rule, and every rule is applied at the root of a newly built node.

| Group | Rules | Sound in $`E`$ | Size $`\lvert l\rvert \to \lvert r\rvert`$ |
|---|---|---|---|
| **Identities (Id)** | $`0+x\to x,\ x+0\to x,\ x-0\to x,\ 0-x\to -x,\ -0\to 0`$; $`1\cdot x\to x,\ x\cdot 1\to x,\ x/1\to x`$; $`x^1\to x,\ x^0\to 1`$ | yes ($`0^0=1`$ in FriCAS, run `…-162657-expr-zero-power`) | $`3\to1`$; $`0-x`$: $`3\to2`$; $`-0`$: $`2\to1`$ |
| **Annihilation (Ann)** | $`0\cdot x\to 0,\ x\cdot 0\to 0`$ | yes | $`3\to1`$ |
| **Involutions (Inv)** | $`-(-x)\to x,\ 1/(1/x)\to x`$ | yes where the left side is defined | $`3\to1`$, $`5\to1`$ |
| **Numerals (Num)** | $`\omega(n_1,\ldots,n_k)\to[\![\omega(n_1,\ldots,n_k)]\!]`$ for $`\omega\in\{+,-,\cdot,/,\hat{}\ \text{(integer exponent)},\text{unary }-\}`$, when defined | yes (it is evaluation) | $`\geq 2 \to 1`$ |

*Float numerals (decision [0010](../decisions/0010-float-numerals.md)).* If $`R`$ is a floating-point domain, every numeral is a decimal fraction with at most $`d`$ = `digits()` significant digits, and Num evaluates exactly, then rounds the result to $`d`$ digits. Num, and every rule that combines numerals (Doubles, Squares and the rungs of §3.4), is then sound for the reals the numerals denote only up to that rounding, and two terms equal as reals may have different normal forms when their numerals round differently. Theorem 3 and the properties (N1)–(N3) of §3.4 hold exactly for exact numerals, and for float numerals wherever no rounding occurs.

**Theorem 3.** $`A_P`$ (and every union of its groups) is sound, terminating and confluent.

*Proof.*
- *Soundness:* by the table.
- *Termination:* every rule strictly decreases $`\lvert t\rvert`$, and $`\lvert\cdot\rvert`$ is monotone under contexts.
- *Confluence:* all left sides are linear, so by the critical pair lemma it suffices to join the overlaps at the root. They are:
  - $`0+0`$, $`0\cdot 0`$, $`0\cdot 1`$, $`1\cdot 0`$, $`0^0`$, $`0^1`$, $`0/1`$: each rewrites to the same numeral by every applicable rule.
  - $`0-0`$: by $`x-0\to x`$ it gives $`0`$; by $`0-x\to -x`$ it gives $`-0`$, which $`-0\to 0`$ (and Num, if present) brings to $`0`$. Before decision [0012](../decisions/0012-minus-zero.md) only Num joined this pair, so unions of Id without Num were not confluent (Lean L10).
  - $`-(-0)`$: Inv gives $`0`$; $`-0\to 0`$ inside gives $`-0`$, then $`0`$. With Num, $`-0`$ is a numeral overlap: both give $`0`$.
  - Identities on numeral arguments, e.g. $`0+n`$: Id gives $`n`$, Num gives $`[\![0+n]\!]=n`$.
  - $`-(-n)`$ and $`1/(1/n)`$: Inv and Num agree.
  - $`1/(1/1)`$: Inv gives $`1`$, and $`x/1\to x`$ inside then outside also gives $`1`$.

  All are joinable, so by Newman's lemma the system is confluent. $`\square`$

**Effect on the open questions.**
- With $`A_P`$, `sum(x, 'x=1..10)` folds to `55`: the algorithm's arithmetic happens on numerals and on zero products.
- `1+2` becomes `3` under Num. The choice is per domain: `GeneralSymbolicExpression(R, Id)` keeps `1+2`, serving G1 and G3. `SymbolicExpression(R)` uses $`A_P`$ (decision 0002).
- No rule in $`A_P`$ reorders or regroups what the user wrote, so G1 holds up to the removal of identities and the evaluation of pure numerals.

### 4.1.1 The associativity group (Assoc), optional

Not part of $`A_P`$ (decision [0005](../decisions/0005-associativity-group.md)): it regroups what was written, which $`A_P`$ never does. It is available as the axiom group `associativity`, to be added to $`A`$ by a user who wants chains flattened. Under (Disp) a flattened chain is then *stored* left-nested and displayed as `a+b+c`; the display itself never regroups.

**Rules.** For $`\circ \in \{+, \cdot\}`$, applied at the root of a newly built node,

```math
\text{(A}_\circ\text{)}\qquad x \circ (y \circ z) \;\to\; (x \circ y) \circ z ,
```

```math
\text{(AN}_\circ\text{)}\qquad (x \circ n) \circ m \;\to\; x \circ k, \qquad k = [\![\, n \circ m \,]\!] ,
```

where $`n, m`$ are numerals. (AN) is the completion of (A) with Num (Knuth–Bendix): without it, $`x+(1+2)`$ has two normal forms, $`x+3`$ (Num inside first) and $`(x+1)+2`$ (A at the root first), which are equal under the axioms. The group `associativity` consists of (A) and, when Num is also present, (AN).

Only $`+`$ and $`\cdot`$ are associative; $`-`$, $`/`$ and $`\hat{}`$ get no rule, so $`a+(b-c)`$ and $`a\cdot(b/c)`$ keep their grouping.

**Soundness.** $`E`$ is a field, so (A) holds for all values, with no side condition (neither side divides); (AN) is (A) read right to left followed by Num.

**Termination.** The rules keep the size, so the size order of §4.1 does not apply. Let $`r(u)`$ be the right operand of a node $`u`$ and define

```math
\mu(t) \;=\; \sum_{u \in t,\ \mathrm{head}(u) \in \{+,\cdot\}} \lvert r(u) \rvert .
```

A step $`x \circ (y \circ z) \to (x \circ y) \circ z`$ changes only the root and its right child. Before, they contribute $`\lvert y \circ z\rvert + \lvert z\rvert = \lvert y\rvert + 2\lvert z\rvert + 1`$; after, the root and its new left child contribute $`\lvert z\rvert + \lvert y\rvert`$. So $`\mu`$ falls by $`\lvert z\rvert + 1 \ge 2`$, for every instance of $`x, y, z`$. The size is unchanged, so the contributions of all enclosing nodes are unchanged, and $`\mu`$ also falls in every context. Combined with §4.1, every rule of $`A_P \cup \mathrm{Assoc}`$ decreases the pair $`(\lvert t\rvert, \mu(t))`$ in the lexicographic order: the rules of $`A_P`$ and (AN) decrease $`\lvert t\rvert`$ (AN: from 5 to 3), and (A) keeps $`\lvert t\rvert`$ and decreases $`\mu`$. Every rule is linear and non-duplicating (each variable occurs once on each side), so this order is closed under contexts and substitutions and is well founded. Hence $`A_P \cup \mathrm{Assoc}`$ terminates.

**Critical pairs.** All left sides stay linear, so it suffices to join the overlaps.

| Overlap | One way | Other way |
|---|---|---|
| Assoc with itself: $`x \circ (y \circ (z \circ w))`$ | root first: $`(x \circ y) \circ (z \circ w) \to ((x \circ y) \circ z) \circ w`$ | inner first: $`x \circ ((y \circ z) \circ w) \to (x \circ (y \circ z)) \circ w \to ((x \circ y) \circ z) \circ w`$ |
| with Id at the root: $`0 + (y+z)`$ | Id: $`y+z`$ | Assoc: $`(0+y)+z \to y+z`$ |
| with Id inside: $`x + (0+z)`$, $`x+(y+0)`$ | Id: $`x+z`$, $`x+y`$ | Assoc: $`(x+0)+z \to x+z`$; $`(x+y)+0 \to x+y`$ |
| the same for $`1`$ and $`\cdot`$ | | |
| with Ann: $`0 \cdot (y \cdot z)`$, $`x \cdot (0 \cdot z)`$, $`x \cdot (y \cdot 0)`$ | Ann: $`0`$ | Assoc then Ann: $`(0\cdot y)\cdot z \to 0 \cdot z \to 0`$, and likewise |
| (A) with Num at the root: $`n + (m+z)`$ | Num cannot fire at the root | (A): $`(n+m)+z \to k+z`$ with $`k = n+m`$ |
| (A) with Num inside: $`x + (n+m)`$ | Num inside: $`x+k`$ | (A): $`(x+n)+m \to x+k`$ by (AN) — this pair is why (AN) is needed |
| (AN) with (A): $`w + ((x+n)+m)`$ | (AN) inside: $`w+(x+k) \to (w+x)+k`$ | (A): $`(w+(x+n))+m \to ((w+x)+n)+m \to (w+x)+k`$ |
| (AN) with itself: $`((x+p)+n)+m`$ | outer: $`(x+p)+k' \to x+k''`$ | inner: $`(x+k)+m \to x+k''`$, with $`k'' = p+n+m`$ either way |
| (AN) with Num: $`(p+n)+m`$ | Num inside: $`q+m \to k''`$ | (AN): $`p+k \to k''`$ |
| (AN) with Id: $`(x+0)+m`$, $`(x+n)+0`$ | Id: $`x+m`$, $`x+n`$ | (AN): $`x+m`$, $`x+n`$ |

The same pairs with $`\cdot`$, $`1`$ and Ann are joined in the same way. Inv rewrites unary $`-`$ and $`/`$, which Assoc never matches, so there is no overlap. All pairs are joinable, so $`A_P \cup \mathrm{Assoc}`$ is confluent (Newman's lemma), and so is every union of its groups.

**Remarks.**
- The rule is not root-collapsing (§3.3): it builds a new inner node $`x \circ y`$, which must itself be normalised. Since the right operand of a normal $`\circ`$-node is never a $`\circ`$-node, the implementation is the recursion $`x \circ (y_1 \circ y_2) := (x \circ y_1) \circ y_2`$ through the domain's own operations, and it terminates by the measure above.
- Numerals next to each other in a chain are folded, whatever the grouping: $`1+(2+x) \to 3+x`$, $`(x+1)+2 \to x+3`$. Numerals separated by another term, as in $`(1+x)+2`$, are not: joining them needs commutativity, which reorders what was written.
- Check: for chains of four leaves, every bracketing must give the same form (test case "Assoc: all bracketings agree").
- `isPlus` already gives the pattern matcher every term of a nested sum, so rewrite rules match either grouping with or without Assoc.

### 4.2 The 2017 axioms, assessed against (S), (T), (CR) and G1

*Kept as the record of why the ladder of §3.4 replaced them. `Symbolic(R, A)` and its axiom domains were retired on 2026-11-26 ([note](../notes/2026-11-26-retiring-symbolic.md)), which maps each axiom to its group.*

| Axiom (2017) | (S) in $`E`$ | (T) | (CR) | Presentation (G1) | Verdict |
|---|---|---|---|---|---|
| Commutative | yes | **cannot be oriented**; needs a total AC-compatible order. The 2017 `smaller?` is neither proven total nor AC-compatible, which explains the non-termination in [27] | modulo AC only | reorders input | (II) option only, modulo AC |
| Associative | yes | orients to flattening | joinable with C only modulo AC | regroups | (II) option; for (I) flattening n-ary $`+`$ and $`\cdot`$ is display-neutral and may be adopted |
| Doubles, Squares (collect like terms) | yes | $`x+x\to2x`$ does not decrease size; needs RPO | **fails as implemented:** results depend on term order ($`2x+3x \mapsto 3x+2x`$, run `…-160222-axioms-forms-table`); needs AC matching | merges terms | (II) only, after completion modulo AC |
| Cancels $`x-x\to0`$, Divides $`x/x\to1`$ | yes / only where $`x\ne0`$ | decreasing | joinable with Id, Num | hides what was written | (II) option; not in $`A_P`$ |
| Inverse, right ($`x+(-y)\to x-y`$, …) | yes | decreasing | — | rewrites notation | (II) option |
| Inverse, left ($`(-x)+y\to-(x-y)`$, …) | yes | **not decreasing**: size $`4\to4`$ | — | rewrites notation | drop or re-orient |
| Distributive | yes | expansion terminates only with a suitable RPO | interacts with all of the above | destroys factored forms | on request only (`expand`) |
| AntiCommutative (graded) | **no**: $`E`$ is commutative | — | — | — | (II) only, with a graded semantics and no conversion to $`E`$ |

**Rewrites outside the axiom system** (applied even in `Symbolic(R, None)`; rechecked 2026-11-26 on `main`, which corrected the 2026-11-25 list: `1/y` is *not* changed, and $`x^{-n}`$ was missing). Each must become an axiom or be removed, for G3; **done 2026-11-26** (decision [0007](../decisions/0007-symbolic-hidden-rewrites.md)): the doubling, squaring and power rewrites are removed, the others apply only with an axiom, and $`x^1 \to x`$, $`x^0 \to 1`$, also found hidden, apply only with `RightIdentity`. Their assessment is in [`docs/notes/2026-11-26-commutativity-and-hidden-rewrites.md`](../notes/2026-11-26-commutativity-and-hidden-rewrites.md) §3.

- $`0\cdot x\to0`$ and $`x \cdot 0 \to 0`$ (Ann);
- $`0-y\to-y`$ (Id);
- $`1/(x/y)\to y/x`$;
- $`-(x-y)\to y-x`$;
- $`-(x+y)\to(-x)+(-y)`$ (size-increasing);
- $`n\cdot x \mapsto`$ repeated doubling when $`n`$ is a `PositiveInteger` (`2*x` gives `x+x`, while an `Integer` 2 gives `2*x`);
- $`x^n\mapsto`$ repeated squaring when $`n`$ is a `PositiveInteger` (`x^3` gives `x*(x*x)`, while an `Integer` 3 gives `x^3`);
- $`x^{-n}\to 1/x^n`$;
- $`x^{p/q}\to \mathrm{nthRoot}(x,q)^p`$.

## 5. Specification summary

1. **`SymbolicTerm(R, A)`** (II) is the term algebra modulo $`A`$, with equality $`=_A`$, for an admissible $`A`$ on the ladder of §3.4, decided by a normaliser with (N1), (N2) and the term order of §3.5. It claims only the categories $`A`$ proves, offers conversion to `Expression` only when $`A`$ is sound for $`E`$, and applies no rewriting outside $`A`$.
2. **`GeneralSymbolicExpression(R, A)`** (I) is a presentation of `Expression(R)`, with equality $`\equiv`$. It requires $`A`$ sound and terminating, and keeps invariant (Val). Semantic primitives go through the value; structural primitives use the form, by class.
3. **`SymbolicExpression(R)` $`:=`$ `GeneralSymbolicExpression(R, A_P)`** (implemented in `src/algebra/gsexpr.spad`, decision 0007) with $`A_P = \mathrm{Id}\cup\mathrm{Ann}\cup\mathrm{Inv}\cup\mathrm{Num}`$ (Theorem 3).
4. **Display** is decided in `coerce: % -> OutputForm` from the form (G8). Structural results from library algorithms show `Expression`'s form of their value. The display must satisfy

   **(Disp)** for every element $`p`$ built by the domain's own operations, reading back the one-line display gives the stored form: $`\mathrm{parse}(\mathrm{display}_{1D}(p)) = \mathrm{form}(p)`$,

   where $`\mathrm{display}_{1D}`$ is the text the interpreter prints (`Format1D` after `precondition$OutputFormTools`) and $`\mathrm{parse}`$ is `parse$InputForm`. So the display may not regroup, drop or add structure: grouping that the reading conventions would not restore (e.g. $`a\cdot(b\cdot c)`$, $`a/(b/c)`$, $`a-(b+c)`$) is shown with parentheses, and flattening, if wanted, is an axiom (§4). Numerals are stored as the parser reads them (decision [0010](../decisions/0010-float-numerals.md)): a negative numeral as the negation `(- n)` of a positive one, which removed the earlier exception for negative literals, and a float numeral as the decimal literal it displays. The 2-D display is checked by eye against the same requirement.

## 6. Verification plan

| Level | What | How |
|---|---|---|
| V1 invariant | (Val) $`[\![\mathrm{form}(p)]\!] = \mathrm{val}(p)`$ for every result in the test suite | an exported `check(p)`, a structural evaluator $`T \to E`$ with no interpreter; called on every test result |
| V2 rules | each rule of $`A`$ fires where it should and nowhere else | `testEquals` on forms, plus `xftest…` for near misses |
| V3 algorithms | integrals verified by differentiating back, sums against closed forms, limits, linear algebra | as in `gsexpr.input` |
| V4 properties | for random terms $`t`$: $`[\![\mathrm{nf}_A t]\!] = [\![t]\!]`$, $`\mathrm{nf}_A(\mathrm{nf}_A t) = \mathrm{nf}_A t`$, and confluence (normal form independent of construction order) | a random term generator in a FriCAS `.input` file |
| V5 formal, (I) | Done (2026-11-26) as part 1 of [`docs/plans/lean-presentation-axioms.md`](../plans/lean-presentation-axioms.md), in Lean 4 with Mathlib in `lean/`: $`A_P`$ with Assoc and (AN) as a rewriting system, `Step` from this spec and `nf` mirroring the code (checked against FriCAS on 7,000 random terms); soundness by refinement of partial evaluation, (Val), termination, normal forms, confluence (L1–L9). Theorem 3 holds where Id comes with Num; L10 is a counterexample otherwise (plan §3.4–3.5) | Mathlib's total division ($`x/0 = 0`$) differs from $`E`$'s partiality, so soundness lemmas must carry side conditions (e.g. $`1/(1/x) = x`$ holds in Mathlib for all $`x`$, but Cancels' $`x/x = 1`$ needs $`x \ne 0`$). This makes the partiality explicit. |
| V5 formal, (II) | Planned in the same plan, parts 2–4 (revised 2026-11-26 for the ladder): Prop. 4 for $`\prec`$; each rung's $`T/{=_A}`$ isomorphic to a free algebra in Mathlib (`Multiset`, `Finsupp`, `MvPolynomial`, `FractionRing`), hence (N1) and (N2); soundness of every group, and `eval` of decision 0011 by the universal property | The ladder's normalisers build canonical forms directly, so no AC rewriting tools (Maude, AProVE, CeTA) are needed. Floats and (Disp) stay with the FriCAS tests |

## 7. Decisions for Bill

1. Accept the two-constructor specification (§5) as the reference design.
2. ~~$`A_P`$ as the default for `SymbolicExpression(R)`~~ Decided: yes, including Num (decision [0002](../decisions/0002-presentation-axioms.md)).
3. ~~Whether $`A_P`$ should include an associativity axiom~~ Decided: no; it is the optional group Assoc, §4.1.1 (decision [0005](../decisions/0005-associativity-group.md)).
4. ~~Formal verification: start with Lean for $`A_P`$ (V5-I)?~~ Decided: yes, in a separate conversation (Bill, 2026-11-26); the [plan](../plans/lean-presentation-axioms.md) was revised the same day to cover the ladder and the bridge.
5. ~~Clean-up of `Symbolic(R, A)` for (II)~~ Hidden rewrites done (decision 0007); AC strategy decided: canonical forms of free algebras, the ladder of §3.4 (decision 0008).

## 8. Implementation status (2026-11-25)

The runs named below were made on the project's FriCAS server before this repository had CI; `make check` (see the README) reproduces them.

| Item | Branch / run | Result |
|---|---|---|
| `GeneralSymbolicExpression(R, A)` with `A` any subset of `[identities, annihilation, involutions, numerals]`; `check` (V1); display from the tree | commit `f634bde`; run `ASUS-20261125-163109-sympair-axioms-recorded2` | 55 tests: 0 unexpected failures, 8 expected failures, 0 unexpected passes |
| `sum(x, 'x=1..10)` with $`A_P`$ | same | form `55` |
| `GeneralSymbolicExpression(Integer, [identities])` keeps `1+2`, `0*x`, `-(-x)` (G3) | same | as specified |
| Doubles: coefficient on either side (§4.2) | commit `b4dff36`; run `ASUS-20261125-163304-sexpr-doubles-recorded` | `2*x+3*x` → `5*x`; 53 tests, 0 unexpected failures |

Display (§5.4) needed explicit parentheses for two reasons. First, FriCAS 1.4.0's 1-D formatter prints `a-(b+c)` as `a-b+c` (run `ASUS-20261125-163021-format1d-minus-paren`); 2-D output is correct. Second, `OutputForm`'s unary minus cancels `-(-a)`, which would hide the written form in `GeneralSymbolicExpression(R, [identities])`.

The form of `sum(x, 'x)` is `(x-1)*(1/2+1/2*(x-1))`, the construction of FriCAS's summation algorithm. $`A_P`$ does not and should not tidy it further; its value is correct (`check` holds).

## References

- G. Birkhoff, "On the structure of abstract algebras", *Proc. Cambridge Phil. Soc.* 31 (1935) 433–454.
- D. E. Knuth, P. B. Bendix, "Simple word problems in universal algebras", in *Computational Problems in Abstract Algebra*, Pergamon (1970) 263–297.
- M. H. A. Newman, "On theories with a combinatorial definition of 'equivalence'", *Ann. of Math.* 43 (1942) 223–243.
- G. Huet, "Confluent reductions: abstract properties and applications to term rewriting systems", *J. ACM* 27(4) (1980) 797–821.
- G. E. Peterson, M. E. Stickel, "Complete sets of reductions for some equational theories", *J. ACM* 28(2) (1981) 233–264.
- J.-P. Jouannaud, H. Kirchner, "Completion of a set of rules modulo a set of equations", *SIAM J. Comput.* 15(4) (1986) 1155–1194.
- A. Rubio, R. Nieuwenhuis, "A total AC-compatible ordering based on RPO", *Theoret. Comput. Sci.* 142 (1995) 209–227.
- F. Baader, T. Nipkow, *Term Rewriting and All That*, Cambridge University Press (1998).
- fricas-devel, "Symbolic (unevaluated) Expressions", 2016-11-14 to 2017-02-25 (fricas-devel archive, Google Groups).
