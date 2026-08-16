# Scott Domains: A Catalogue of Examples

A worked list of Scott domains, from the two-element case up to D∞, with the
data one needs to check each claim: the carrier, the order, the set of compact
elements, the Scott topology, and which defining condition a near-miss violates.

The one example already formally verified in this repository is Sierpiński space
(§4); everything else here is mathematics, not Lean-checked. See §8 for the
formalization status.

---

## 1. Definitions used here

Fix a partial order (D, ⊑).

- **Directed** — S ⊆ D is directed when S ≠ ∅ and every pair in S has an upper
  bound in S.
- **Dcpo** — every directed S ⊆ D has a supremum ⊔S. **Pointed** — D has a least
  element ⊥. A pointed dcpo is a **cpo**.
- **Way-below** — x ≪ y when for every directed S with y ⊑ ⊔S there is s ∈ S with
  x ⊑ s. Read: any directed approximation of y already passes x.
- **Compact** (also *finite*, *isolated*) — k is compact when k ≪ k. Write K(D)
  for the set of compact elements.
- **Algebraic** — for every x ∈ D, the set ↡x = {k ∈ K(D) : k ⊑ x} is directed and
  x = ⊔↡x. **ω-algebraic** — algebraic with K(D) countable.
- **Continuous** — as above with ↡x = {y : y ≪ x} in place of the compacts. Every
  algebraic dcpo is continuous; §6.3 gives a continuous dcpo that is not
  algebraic.
- **Bounded complete** (= *consistently complete*) — every subset with an upper
  bound has a least upper bound. In a cpo it suffices to require this of pairs.

> **Scott domain** — a bounded-complete ω-algebraic cpo.

Variants in the literature: some authors drop ω (countability of the basis), some
require a top element (giving the **algebraic lattices**), and some say "domain"
for the continuous, non-algebraic case. Each example below is annotated with the
conditions it satisfies, so the reader can apply their own definition.

**Scott topology** σ(D): U ⊆ D is open when U is an up-set and is inaccessible by
directed suprema — S directed and ⊔S ∈ U imply s ∈ U for some s ∈ S. The
specialization order of σ(D) recovers ⊑: x ⊑ y iff every open containing x
contains y. That is exactly the definition of `leq` in
[LRSODInCIC.lean:111](../Domains/LRSODInCIC.lean).

---

## 2. Summary table

| # | Domain | \|D\| | K(D) | ω-alg. | bd. compl. | Scott domain | lattice |
|---|--------|------|------|--------|-----------|--------------|---------|
| 3.1 | one-point 𝟙 | 1 | 1 | yes | yes | yes | yes |
| 3.2 | Sierpiński 𝕊 | 2 | 2 | yes | yes | yes | yes |
| 3.3 | flat A⊥ | \|A\|+1 | all | iff A countable | yes | iff A countable | no (\|A\|≥2) |
| 3.4 | vertical ℕ<sup>∞</sup> = ω+1 | ℵ₀ | ℕ (not ∞) | yes | yes | yes | yes |
| 3.5 | finite bd.-compl. posets | finite | all | yes | yes | yes | sometimes |
| 3.6 | 𝒫(X), ⊆ | 2<sup>\|X\|</sup> | finite subsets | iff X countable | yes | iff X countable | yes |
| 3.7 | ℕ ⇀ ℕ, graph ⊆ | 2<sup>ℵ₀</sup> | finite partial fns | yes | yes | yes | no |
| 3.8 | streams A<sup>≤ω</sup>, prefix | ≤2<sup>ℵ₀</sup> | finite words | iff A countable | yes | iff A countable | no |
| 5.1 | [D → E] | — | joins of step fns | if D, E are | if E is | yes | if E is |
| 5.3 | Pω graph model | 2<sup>ℵ₀</sup> | finite subsets | yes | yes | yes | yes |
| 5.4 | term domain T<sup>∞</sup>(Σ) | ≤2<sup>ℵ₀</sup> | finite terms | iff Σ countable | yes | yes | no |
| 5.5 | D∞ | 2<sup>ℵ₀</sup> | see §5.5 | yes | yes | yes | no |
| 6.1 | two minimal upper bounds | 6 | all | yes | **no** | **no** | no |
| 6.2 | ℕ, usual ≤ | ℵ₀ | all | n/a | yes | **no** (not a dcpo) | no |
| 6.3 | interval domain I[0,1] | 2<sup>ℵ₀</sup> | {⊥} only | **no** | yes | **no** (not algebraic) | no |
| 6.4 | [0,1] ⊆ ℝ, ≤ | 2<sup>ℵ₀</sup> | {0} only | **no** | yes | **no** (not algebraic) | yes |

---

## 3. The obvious examples

### 3.1 The one-point domain 𝟙 = {⊥}

The terminal object. K(𝟙) = {⊥}. Scott topology: {∅, {⊥}} — two opens, the
indiscrete = discrete case. Every function into it is continuous. Degenerate, but
it is the base case of the inverse-limit tower and the unit for the coalesced sum.

### 3.2 The Sierpiński domain 𝕊 = {⊥ ⊑ ⊤}

The smallest non-degenerate Scott domain: two elements, both compact, a complete
lattice. Scott topology: **three** opens — ∅, {⊤}, {⊥,⊤} — because {⊤} is an
up-set and no directed set with supremum ⊤ avoids ⊤. See §4 for why this
two-element object carries the weight it does.

### 3.3 Flat domains A⊥

Take a set A, adjoin ⊥ below everything, and leave the elements of A pairwise
incomparable. Directed subsets are {⊥}, {a}, {⊥,a} — all have suprema, so A⊥ is a
cpo, and **every** element is compact, so A⊥ is algebraic with K(A⊥) = A⊥.
Bounded completeness holds because a set with an upper bound lies inside {⊥,a}
for a single a. For |A| ≥ 2 it is not a lattice: distinct a, b have no upper bound
at all.

Scott topology: an up-set containing ⊥ is everything, so the opens are exactly
𝒫(A) together with A⊥ itself — 2<sup>|A|</sup> + 1 opens. Every monotone function
out of a flat domain is Scott-continuous, since directed subsets are finite.

Standard instances: 𝔹⊥ = {⊥, tt, ff} (3 elements), ℕ⊥ (ω-algebraic), and the
value domains of a call-by-value language. 𝔹⊥ is the domain in which "strict"
acquires its precise meaning: f is strict iff f(⊥) = ⊥.

### 3.4 The vertical naturals ℕ<sup>∞</sup> = ω + 1

The chain 0 ⊑ 1 ⊑ 2 ⊑ … ⊑ ∞. A complete lattice, hence bounded complete.
K(ℕ<sup>∞</sup>) = ℕ: each finite n is compact, but **∞ is not**, since the
directed set ℕ has supremum ∞ with no member above ∞. So ∞ = ⊔ℕ is the first
genuinely non-compact element in this catalogue, and the smallest witness that
"algebraic" is not "all elements compact".

Scott topology: σ = {∅} ∪ {↑n : n ∈ ℕ}. Note {∞} is an up-set but is **not** open
— inaccessibility fails for S = ℕ. This is the domain of the lazy natural
numbers, and the object that makes "⊔ of an ω-chain" the standard test case.

### 3.5 Finite bounded-complete pointed posets

Any finite poset with ⊥ in which every bounded pair has a least upper bound. All
elements are compact (directed sets are finite), so algebraicity is automatic and
the only condition to check is bounded completeness. The four-element diamond
⊥ ⊑ a, b ⊑ ⊤ qualifies; §6.1 shows what a finite poset that fails looks like.

### 3.6 Powersets 𝒫(X) under ⊆

A complete lattice. K(𝒫(X)) = the finite subsets, and A = ⊔{F : F ⊆ A finite},
so 𝒫(X) is algebraic — an **algebraic lattice**. It is ω-algebraic iff X is
countable. Same shape, different content: the lattice of ideals of a ring, of
subgroups of a group, of subalgebras of an algebra; in each case the compact
elements are the finitely generated ones.

### 3.7 Partial functions ℕ ⇀ ℕ, ordered by graph inclusion

f ⊑ g iff the graph of f is contained in that of g. Directed unions of compatible
graphs are graphs, so this is a cpo with ⊥ the empty function. K = the **finite**
partial functions, countably many, so ω-algebraic. Bounded complete: a family with
an upper bound is pairwise compatible, and its union is the least upper bound. Not
a lattice — two functions disagreeing at a point have no upper bound.

This is the domain in which Kleene's first recursion theorem lives: a recursive
definition is a Scott-continuous functional and the least fixed point ⊔ₙ Fⁿ(⊥) is
its meaning.

### 3.8 Streams A<sup>≤ω</sup> = A\* ∪ A<sup>ω</sup> under the prefix order

Finite and infinite sequences, u ⊑ v iff u is a prefix of v. ⊥ = the empty word.
Directed sets are chains of prefixes with union as supremum. K = the finite words;
each infinite sequence is the supremum of its finite prefixes. Bounded complete
because two words with a common extension are prefix-comparable. Not a lattice.

Topological content worth noting: the **maximal** elements A<sup>ω</sup> with the
subspace Scott topology are exactly Cantor space (|A| = 2) or Baire space
(A = ℕ) with their usual topologies. The domain is a compactification of a
classical Polish space by its finite approximations.

---

## 4. Sierpiński space in depth

The two-element domain 𝕊 = {⊥ ⊑ ⊤} carries more structure than its size suggests.

**As a topological space.** The opens are the up-sets: ∅, {⊤}, {⊥,⊤}. This is the
Sierpiński space — T₀ but not T₁, sober, with generic point ⊥ and closed points
{⊥} = ↓⊥ and the whole space = ↓⊤.

**As the dualizing object.** For any dcpo D there is an order isomorphism

    [D → 𝕊]  ≅  σ(D)

between Scott-continuous maps into 𝕊 and Scott-open subsets of D: a continuous
map is exactly the characteristic function of an open set, and the pointwise
order on the left is inclusion on the right. This is the sense in which 𝕊
classifies opens, and it is why so many domain-theoretic statements can be tested
against a two-element object.

**As the smallest non-trivial case.** 𝕊 satisfies the axioms D1–D4 of
[LRSODInCIC.lean:133](../Domains/LRSODInCIC.lean) in full, and the file's witness `sierp`
(carrier `Bool`, `false = ⊥`, `true = ⊤`, `isOpen U := U false → U true`) is a
kernel-checked proof of that. Measured facts from that formalization:

- `#print axioms sierpTop` — depends on no axioms; layer O is constructive.
- `#print axioms sierp` — `[lem, propext, Quot.sound]`, all three entering through
  the `sober` field (D2) alone. Sobriety is the classical frontier here.
- Basis: `basis 0 = {⊥,⊤}`, `basis (n+1) = {⊤}` — two distinct compact opens,
  closed under intersection, generating all three opens.
- The enumeration "the opens are ∅, {⊤}, {⊥,⊤}" is itself checked, in
  [ScottDomainExamples.lean](../Domains/ScottDomainExamples.lean): `sierp_open_cases`
  puts every open into one of the three, and `sierp_empty_ne_top`,
  `sierp_top_ne_full`, `sierp_empty_ne_full` separate them, so the count is
  exactly three. Note where the axioms fall: the enumeration consumes
  `[lem, propext, Quot.sound]` and the three distinctness facts consume none.
  A subset here is a `Bool → Prop`, so `U ⊥` may be undecided and constructively
  there are more opens than three; excluded middle is what collapses them to
  three. This is the first result in the development whose *statement*, not only
  whose proof, is classical.

**Why `basisCap` is the topological shadow of bounded completeness.** For an
algebraic domain D the sets ↑k, k ∈ K(D), are compact-open and form a base. Given
compacts k, k′: if they have a least upper bound then ↑k ∩ ↑k′ = ↑(k ⊔ k′), again
a basic open; if they have upper bounds but no *least* one, the intersection is a
union of several ↑m and is not basic. So the base is closed under binary
intersection (allowing ∅ for the inconsistent case) exactly when bounded
completeness holds — which is what the `basisCap` field demands.

---

## 5. The more complicated examples

### 5.1 Function spaces [D → E]

Scott-continuous maps under the pointwise order. If D and E are Scott domains, so
is [D → E]; the compacts are the least upper bounds of finite bounded sets of
**step functions** (k ↘ e)(x) = e if k ⊑ x, else ⊥, for k ∈ K(D), e ∈ K(E). The
category of Scott domains and continuous maps is **cartesian closed** — the
property that makes it a model of the simply typed λ-calculus, and the reason
bounded completeness is imposed rather than plain algebraicity.

Concrete count: [𝔹⊥ → 𝔹⊥] has **11** elements — 9 strict maps (f(⊥) = ⊥, with
f(tt) and f(ff) arbitrary among 3 values), plus the two constants tt and ff. Any
f with f(⊥) ≠ ⊥ is constant, by monotonicity.

### 5.2 Parallel-or

In [𝔹⊥ × 𝔹⊥ → 𝔹⊥], define por(tt, x) = tt, por(x, tt) = tt, por(ff, ff) = ff. It
is monotone, hence continuous, hence an element of the function domain — yet it is
not definable in PCF (Plotkin 1977). The example marks the gap between the
domain-theoretic model and the operational one, and motivates stable domains and
game semantics.

### 5.3 The graph model Pω

𝒫(ℕ) as in §3.6, an ω-algebraic lattice. Using a pairing of ℕ with the finite
subsets of ℕ, one constructs continuous maps

    Fun : Pω → [Pω → Pω],    Graph : [Pω → Pω] → Pω,    Fun ∘ Graph = id

exhibiting [Pω → Pω] as a **retract** of Pω. That makes Pω a model of the
untyped λ-calculus without any inverse-limit construction: self-application is
interpretable because a function space embeds into the domain itself.

### 5.4 Term and tree domains

Fix a signature Σ and adjoin a symbol Ω for "undefined". The finite and infinite
Σ-terms, ordered by "less defined at every position", form a bounded-complete
ω-algebraic domain (ω-algebraic when Σ is countable) whose compacts are the
**finite** terms. This is the domain of infinite trees used for the semantics of
recursive program schemes; §3.8 is the special case of a signature with one unary
symbol per letter.

### 5.5 D∞

Start from any Scott domain D₀ with at least two elements and iterate
D<sub>n+1</sub> = [D<sub>n</sub> → D<sub>n</sub>], connected by embedding–projection
pairs (e<sub>n</sub>, p<sub>n</sub>) with p<sub>n</sub> ∘ e<sub>n</sub> = id and
e<sub>n</sub> ∘ p<sub>n</sub> ⊑ id. The inverse limit D∞ of that tower satisfies

    D∞  ≅  [D∞ → D∞]

as Scott domains, and is again bounded-complete and ω-algebraic when D₀ is. This
is Scott's 1969/1972 model of the untyped λ-calculus and the object this
repository's formalization is aimed at.

The distinction the Lean file is careful about: axioms D1–D4 characterize the
**class** of pointed ω-algebraic domains — 𝕊 satisfies all four — whereas D∞ is a
particular object in that class, obtained by a construction *on top of* D1–D4, not
a consequence of them.

### 5.6 The ideal completion, and why the catalogue is not arbitrary

For a poset P with least element, the ideal completion Idl(P) — directed lower
subsets of P ordered by ⊆ — is algebraic with compacts the principal ideals ↓p,
and every algebraic domain D satisfies

    D  ≅  Idl(K(D)).

So an ω-algebraic domain is *nothing but* the ideal completion of a countable
poset of finite approximations. Choosing a Scott domain is choosing a countable
poset of tokens; this is the content of Scott's information systems, and it means
every example above is determined by the finite data in the K(D) column of §2.

---

## 6. Near misses, and which condition fails

### 6.1 Bounded completeness fails: two minimal upper bounds

Take ⊥ ⊑ a, b, with a, b incomparable, and c, d incomparable, both above both a
and b. Six elements, all compact, a finite dcpo. But {a, b} has upper bounds c and
d and no least one, so the domain is **not** bounded complete. Topologically,
↑a ∩ ↑b = {c, d} is not of the form ↑k — the failure §4 predicts.

### 6.2 Directed completeness fails: ℕ under ≤

The whole of ℕ is directed and has no upper bound, so ℕ is not a dcpo. Adjoining
∞ repairs it and gives §3.4 — the standard illustration that "cpo" is a
completeness requirement, not a size requirement.

### 6.3 Algebraicity fails: the interval domain I[0,1]

Closed subintervals [a,b] ⊆ [0,1] ordered by **reverse inclusion** (more
information = smaller interval), with ⊥ = [0,1]. Directed suprema are
intersections, and it is bounded complete and **continuous** — [a,b] ≪ [c,d] iff
(c,d) ⊆ the interior of [a,b] appropriately — with the rational intervals as a
countable basis, so it is ω-continuous. But the only compact element is ⊥: for any
[a,b] ≠ [0,1] the directed family of slightly larger intervals has supremum [a,b]
with no member below it. Hence **not algebraic**, and not a Scott domain, though
it is a perfectly good domain for exact real arithmetic.

### 6.4 Algebraicity fails, lattice version: [0,1] ⊆ ℝ

The unit interval under ≤ is a complete lattice and a continuous lattice (x ≪ y
iff x < y or x = 0), but K = {0}, so it is not algebraic. Together with §6.3 this
is the standard demonstration that continuous ⊋ algebraic.

### 6.5 Outside the category: powerdomains

The Plotkin (convex) powerdomain of a Scott domain need not be bounded complete,
so the category of Scott domains is not closed under it. Repairing this is what
motivates the larger cartesian closed category of **bifinite (SFP) domains**. The
Hoare (lower) powerdomain, by contrast, stays inside the algebraic lattices.

---

## 7. Closure properties

Scott domains are closed under, and the constructions are computed pointwise or
componentwise:

| construction | notation | K of the result |
|---|---|---|
| finite and countable products | D × E | pairs of compacts |
| lifting | D<sub>⊥</sub> | ⊥ together with lifted compacts |
| separated and coalesced sums | D ⊕ E, D + E | ⊥ together with the summands' compacts |
| continuous function space | [D → E] | bounded finite joins of step functions |
| bilimits of e–p pairs | lim<sub>←</sub> D<sub>n</sub> | see §5.5 |

Products and function space give cartesian closure; bilimits give solutions to
recursive domain equations such as D ≅ [D → D], D ≅ 1 + (A × D) (streams, §3.8),
and D ≅ 1 + (D × D) (lazy binary trees).

---

## 8. Formalization status

Measured against [LRSODInCIC.lean](../Domains/LRSODInCIC.lean) and
[ScottDomainExamples.lean](../Domains/ScottDomainExamples.lean) as of this writing:

- **All 16 entries in §2 are settled**, all kernel-checked — twelve inhabited and
  four refuted, with **no outstanding scope limits**:

  | § | witness | carrier | axioms consumed |
  |---|---------|---------|-----------------|
  | 3.1 | `onePoint : DInfinityFoundations Unit` | `Unit` | `[propext, Quot.sound]` |
  | 3.2/4 | `sierp : DInfinityFoundations Bool` | `Bool` | `[lem, propext, Quot.sound]` |
  | 3.3 | `flatBool : DInfinityFoundations (Option Bool)` | `Option Bool` | `[lem, propext, Quot.sound]` |
  | 3.4 | `vertNat : DInfinityFoundations (Option Nat)` | `Option Nat` | `[lem, propext, Quot.sound]` |
  | 3.5 | `fbcDomain : FinBCPoset D → DInfinityFoundations D` | any `D` | `[lem, propext, Quot.sound]` |
  | 3.6 | `psetNat : DInfinityFoundations (Nat → Prop)` | `Nat → Prop` | `[lem, propext, Quot.sound]` |
  | 3.7 | `pfunNat : DInfinityFoundations PFun` | graphs, single-valued | `[lem, propext, Quot.sound]` |
  | 3.8 | `streamDomain : DInfinityFoundations BStream` | graphs, prefix-closed | `[lem, propext, Quot.sound]` |
  | 5.1 | `funSpace : TokenPoset → JoinTokens → DInfinityFoundations …` | ideals of step-function tokens | `[lem, propext, Quot.sound]` |
  | 5.3 | `psetNat` (domain) + `powApp_powGraph` (λ-model) | `Nat → Prop` | `[lem, propext, Quot.sound]` |
  | 5.4 | `treeDomain : TreeSig → DInfinityFoundations …` | ideals of finite terms | `[lem, propext, Quot.sound]` |
  | 6.1 | `six_no_lub`, `six_basisCap_fails` (refutations) | `Six` | `[propext]` |
  | 6.2 | `nat_not_dcpo` (refutation) | `Nat` | `[propext, Quot.sound]` |
  | 5.5 | `dInfinity : DInfinityFoundations (TokenIdeal dInfTokens)` | levelled tokens | `[lem, propext, Quot.sound]` |
  | 6.3 | `compact_iff_eq_bot` (refutation) | `Ival` | `[propext, Classical.choice, Quot.sound]` |
  | 6.4 | `ui_compact_iff` (refutation) | `UI` | `[propext, Classical.choice, Quot.sound]` |

  §3.5 is the first entry proved as a **class** rather than an object: `fbcDomain`
  takes any finite bounded-complete pointed poset to a witness, so the row covers
  every such poset at once, the four-element diamond included. `boolFinBC` and
  `sierpFromPoset` instantiate it, which keeps the theorem from being vacuous and
  recovers 𝕊 from its order rather than from a topology given by hand. Its
  topology is the Alexandrov one — on a finite poset that *is* the Scott topology,
  since every directed set is finite and so has a greatest element.

  Two things this entry isolates. Finiteness has to be made to produce **maximal**
  elements with no `Finset` machinery: `fbc_exists_maximal` scans the enumeration
  once, carrying the invariant that no index examined so far lies strictly above
  the current element, which survives replacement because the element only moves
  up. And `basisCap` is the **only** field that consumes bounded completeness —
  ↑a ∩ ↑b is ↑(a ⊔ b) when a and b are bounded and ∅ when they are not, so a pair
  with upper bounds but no least one leaves the intersection a union of several
  basic opens with no single index to name it. That is precisely §6.1.

  The fourth column is the informative one. `propext` with `Quot.sound` (the
  latter via `funext`) appears in all three, from the closure equation
  `C = clSingleton y` being an equality of predicates. `lem` is what varies: it
  enters through D2 alone, to decide of an arbitrary closed `C` which data it
  contains. 𝟙 has no datum to decide, so its sobriety proof is constructive and
  `lem` drops out; 𝕊 needs one such decision, 𝔹⊥ two. Every obligation for 𝟙 is
  discharged by definitional eta for structures — each `x : Unit` *is* `()` — so
  `t0` closes by `rfl` where the larger carriers need case splits.

  𝔹⊥ is where D2 stops being routine. In 𝟙 and 𝕊 every inhabited closed set is
  irreducible, so a generic point can simply be produced. In 𝔹⊥ the whole space
  is closed and inhabited but **reducible** — it is ↓tt ∪ ↓ff with neither part
  contained in the other — and has no generic point. The proof must therefore
  exclude that case by handing the `irreducible` hypothesis exactly that
  decomposition, which is the first use of the negative half of D2's statement.

  ℕ<sup>∞</sup> is where the infinite carrier changes both remaining fields. D2's
  generic point can no longer be exhibited: a closed set is an arbitrary bounded
  set of naturals, and its generic point is the **maximum**, constructed by
  induction on the bound (`vert_max_of_bounded`). D3's `basisCpt` acquires real
  content for the first time — a finite subcover has to be assembled one open at
  a time (`vert_finite_cover`), because turning `∀ m, ∃ i, U i m` into a function
  `m ↦ i` would need countable choice, and `lem` is the only classical principle
  this development admits. The induction is legitimate because the goal is a
  `Prop`, so each existential is eliminated inside the proof.

  Also checked, for 𝕊: the §4 enumeration, `sierp_open_cases` with the three
  distinctness lemmas — the opens are exactly ∅, {⊤}, {⊥,⊤}. For 𝔹⊥:
  `flat_incomparable`, that tt and ff have no order relation, which is what
  keeps it off the lattice column of §2. For ℕ<sup>∞</sup>:
  `vert_top_not_isOpen`, that {∞} is **not** open — the topological form of
  "∞ ∉ K(ℕ<sup>∞</sup>)", and the reason the base has one member per finite
  point and none for ∞.
  𝒫(ℕ) is the first uncountable carrier and the first with an infinite basis, and
  both land on D3. Because `basis` is `Nat`-indexed the finite subsets must be
  *enumerated*: `psetBits k` is the list of set bits of k, and `pset_exists_mask`
  produces a mask for any list, which is why this entry alone reaches into
  `Nat.testBit`. Its D2 is the deepest sobriety proof here — the generic point of
  an irreducible closed C is ⋃C, and ⋃C ∈ C needs three steps: C is a down-set,
  any two finite approximations drawn from C have a common extension **in** C
  (`pset_common_extension`, where irreducibility is used), and hence by induction
  every finite approximation of ⋃C already lies below one member (
  `pset_member_covering`).

  This also settles the *domain* half of §5.3: Pω is 𝒫(ℕ), so `psetNat` is its
  Scott-domain structure. The λ-model half is now done too — see below.
  §3.7 forced an encoding decision that is worth recording. A partial function is
  carried as its **graph plus a proof of single-valuedness**, not as
  `Nat → Option Nat`. With `Option`, D2's generic point — the union of C's graphs
  — would require *choosing* the value some member assigns at each argument, i.e.
  countable choice. With the graph encoding the union is a relation defined
  outright and single-valuedness is proved from the common-extension lemma, so
  `lem` remains the only classical principle in the development. The basis needs
  finite sets of *pairs*, supplied by `pairDecode`, a surjection ℕ ↠ ℕ × ℕ written
  as the structurally recursive Cantor walk so that surjectivity needs only
  ordinary induction rather than a closed form and its inverse.

  §3.8 makes the choice of base a **forced** one rather than a convenience. The
  obvious base — up-sets of finite sets of index/value pairs, as in §3.7 — fails
  `basisCpt` here: {(5,tt)} has no least stream above it, since indices 0–4 are
  unconstrained by prefix-closedness, so its up-set is not principal and
  compactness breaks. The compact opens are the up-sets of finite **words**, so
  the base is indexed by `pairDecode k = (length, bit-mask)` with index 0 reserved
  for ∅ — which `basisCap` needs, because two incompatible words have empty
  intersection and some index must name it. `basisGen` is where prefix-closure
  does its work: it fills in every index below the largest one a finite
  approximation mentions, and `stream_exists_mask` packs those values into a mask
  by induction, never extracting a function `i ↦ value` (that would be unique
  choice).

  The two non-examples are refutations rather than witnesses, and neither needs
  `lem`: §6.1 decides by case analysis on a five-constructor type, §6.2 by `omega`.
  §6.1 is the exact failure §4 predicts — `six_no_lub` is the order-theoretic form
  (a and b are bounded by c and d with no least bound) and `six_basisCap_fails`
  the topological one (↑a ∩ ↑b is not ↑k for any k), which is why `fbcDomain`
  consumes bounded completeness at `basisCap` and nowhere else.

  A discrepancy found while formalizing §6.1: the prose says "six elements", but
  the structure it describes — ⊥, a, b, c, d — has five, and its own claim
  ↑a ∩ ↑b = {c, d} is the five-element reading. Formalized as five.
- **§5.6 is proved as a general theorem**, though it is not one of §2's 16 rows:
  `idealDomain : (P : TokenPoset) → DInfinityFoundations (TokenIdeal P)` takes any
  countable poset of tokens with a least element and bounded joins to a witness.
  That is this section's own claim — an ω-algebraic domain is nothing but the ideal
  completion of a countable poset of finite approximations — and it is the pattern
  §3.6–§3.8 each carried out by hand.

  It is also **cheaper** than any of them, which is the measurement worth keeping:
  `idealTop` is axiom-free outright and `ideal_common_extension` needs `lem` alone,
  where the three concrete entries picked up `propext` and `Quot.sound` from the
  list lemmas their finite approximations required. The reason is that an ideal is
  directed, so any finite set of its tokens already lies below one of its members:
  the finite approximation is a **single token**, and the bit masks, `pairDecode`
  and `List.mem_append` all disappear. The basis is just `n ↦ ↑(enum n)`.
- **§5.1 is proved on top of §5.6**, as `funSpace : (P : TokenPoset) → (Q : JoinTokens)
  → DInfinityFoundations (TokenIdeal (funTokens P Q))`. The tokens of [D → E] are
  finite lists of step functions `(a,b)` ordered by entailment — b is below *every*
  upper bound of what the other list contributes at a, which says b ⊑ ⊔{…} without
  asserting the join exists — and `idealDomain` then discharges D1–D4. This is
  Scott's information-systems presentation, and §5.6 is what licenses it.

  **Both scope limits have now been addressed, and the first turned out not to be
  one.** `funTokens` and `funSpace` take *arbitrary* token posets on both sides.
  The earlier claim — that the value side needed total joins because only
  *consistent* step sets are legitimate tokens and consistency is undecidable — was
  wrong, and `stepEntails_of_unbounded` says why: a step set whose contributions at
  `a` have no upper bound entails **everything** at `a`, since the premise "v bounds
  the contributions" is unsatisfiable and the implication is vacuous. An
  inconsistent token is high in the order, not ill-formed; the carrier is all finite
  lists; no subtype and no decidability question arises. The construction never
  mentioned `Q.join` at all — the hypothesis was decoration, which a grep confirmed
  before the generalization was made.

  What total joins actually buy is the *reading* of the result: with them no token
  is inconsistent and the ideals are [D → E]; without them the inconsistent tokens
  sit above everything and the construction builds [D → E] with a top adjoined.
  §4's dualizing object [D → 𝕊] is the former case.

  The second limit is **closed**: the ideals of `funTokens P Q` are in **bijection
  with the continuous maps**, not merely a stand-in for them. With
  `IdealContinuous` as the finite-approximation form of Scott continuity — monotone,
  and every output token already produced by a single input token — the two
  directions are `funApply` (an ideal of step functions acts on ideals) and `ofFun`
  (a continuous map's graph), and they invert each other:

  | theorem | content |
  |---|---|
  | `funApply_ofFun` | Fun ∘ Graph = id — applying a map's graph recovers the map |
  | `ofFun_funApply` | Graph ∘ Fun = id — the graph of an ideal's action is that ideal |
  | `funApply_continuous` | every ideal's action is itself continuous, so `ofFun` needs no side hypothesis |

  Two lemmas carry the weight. `contributions_in` bounds a step-set's contributions
  inside the output ideal, by induction with `lem` deciding each comparison — that
  is what makes `ofFun`'s ideal down-closed and gives one half of each round trip.
  `stepEntails_of_stepLe` and `stepEntails_mono_arg` transfer entailment along the
  order on step-sets and along the argument, which is what lets the other half
  collect finitely many witnesses into one ideal member by induction rather than by
  choosing per element.

  **§5.1 therefore carries no remaining scope limit.**

  Building the tokens is `lem`-free (`funTokens` is `[propext, Quot.sound]`); only
  `idealDomain`'s D2 reintroduces excluded middle.

  Two interface weakenings to `TokenPoset` were needed and are worth recording,
  since both are facts about the ideal completion rather than conveniences.
  **Antisymmetry is never used** — a preorder of tokens suffices, which matters
  because step-function tokens genuinely are only preordered (`[(a,b)]` and
  `[(a,b),(a,b)]` entail each other without being equal). And **`enum_onto` needs
  only mutual entailment**, not equality, because ↑t depends only on t's ⊑-class;
  a bit-mask enumeration cannot reproduce a list's order or duplicates, so exact
  surjectivity was unattainable as well as unnecessary.
- **§5.3 is complete**: the domain half is `psetNat` (§3.6), and the λ-model half is
  `powApp_powGraph : powApp (powGraph f) B m ↔ f B m` for continuous f — **Fun ∘
  Graph = id**, so [Pω → Pω] is a retract of Pω. `powApp_continuous` shows `Fun A`
  really lands in the function space, and `powSelfApp A = A · A` is then definable:
  self-application is interpretable **with no inverse limit**, which is why §5.5 is
  needed only for Scott's original model and not for *a* model.

  One ingredient had to be added. `pairDecode` is a surjection ℕ ↠ ℕ×ℕ, enough for
  enumerating a basis, but reading k and m back out of ⟨k,m⟩ needs **injectivity** —
  a section. `cantor` is it, defined through triangular numbers so no division
  appears, with `pairDecode_cantor` proving it inverse to the walk on the nose. The
  whole λ-model layer is `lem`-free; `powApp_continuous` needs no axioms at all.
- **§5.4 is proved**, as `treeDomain : (S : TreeSig) → DInfinityFoundations
  (TokenIdeal (treeTokens S))` — T^∞(Σ) as the ideals of the finite Σ-terms, again
  via §5.6. The decisive choice is to make a finite partial term an **inductive
  type**, `FinTree := hole | node sym FinTree FinTree`, rather than a set of
  (position, symbol) pairs. A pair-set carries two side conditions — single-valued,
  and prefix-closed so that no position is labelled above an unlabelled one — and
  §3.8 already showed they cannot be dropped, since a basis element that is not
  prefix-closed has no least member and `basisCpt` fails. As an inductive type both
  hold by construction, and the undecidable validity predicate that would otherwise
  block `enum` without choice (the §5.1 obstruction) never arises.

  `treeLe_lub` is **axiom-free**: the least upper bound of two terms below a common
  one is built by recursion on that bound, so no total join function is needed.
  Countability comes from `treesUpTo n`, the trees of height ≤ n over the first n
  symbols, with monotonicity in n; the enumeration is that list indexed through
  `pairDecode`. Scope: binary signatures with countable symbols — any finite
  signature binarizes, and §3.8 is the unary case, one unary symbol per letter,
  exactly as this section says.
- **§5.5 is partially done, and the boundary is stated rather than papered over.**
  Built and checked: the tower `D₀ = 𝕊`, `Dₙ₊₁ = [Dₙ → Dₙ]` (`tower`), every level
  a Scott domain (`towerDomain n`), the embedding `e(x) = λy.x` as the one-element
  step function ⊥ ↦ t (`emb`), its monotonicity (`emb_mono`), and the iterated
  embedding into a later level with monotonicity (`liftTok`, `liftTok_mono`). The
  iteration is possible only because §5.1's function space closes on `JoinTokens`:
  the tokens of [D → D] join by concatenation, which is total, so `funJoin` carries
  a `JoinTokens` to a `JoinTokens`.

  **Not built: the bilimit.** D∞ is the colimit of the tower, its tokens
  `Σ n, (tower n).base.T`, ordered by lifting both sides to a common level:
  `⟨n,t⟩ ⊑ ⟨m,u⟩` iff `liftTok n k₁ t ⊑ liftTok m k₂ u` for some `k₁, k₂` with
  `n + k₁ = m + k₂`. `liftTok` is stated additively so each *single* step
  typechecks without transport, but that comparison cannot: the two sides live in
  `tower (n+k₁)` and `tower (m+k₂)`, types equal only *propositionally*. So the
  relation needs `h ▸ …`, and then transitivity, `bounded_lub` and `enum_onto` each
  have to compose transports and appeal to `Nat.add_assoc` as a propositional type
  equality. **The obstacle is that bookkeeping, not the mathematics.** The route
  around it is a redesign, not a continuation.

  **That redesign is now built, and the obstruction is gone.** Keep one **flat,
  unindexed** token type `DTok`, and carry the level in the *order* instead:
  `leAt : Nat → DTok → DTok → Prop`, the order of Dₙ, by recursion on n — level 0 is
  𝕊's order, level n+1 is §5.1's entailment between step-function sets phrased over
  `leAt n`. Comparing any two tokens at any level is then a `Prop` about two
  ordinary terms: no indices, no casts. The other half of the trick is `stepOf`,
  which reads *any* token as a finite set of step functions — ⊥ as the empty set
  (λy.⊥), ⊤ through one embedding (λy.⊤) — so a single recursion handles levels
  uniformly instead of by case analysis on which token is lower.

  Proved on it, each `[propext]` and nothing more: `leAt_refl`, `leAt_trans`,
  `leAt_bot_le`, and the one that matters — **`leAt_embTok`**, that e is an
  *order-embedding*: `leAt (n+1) (embTok x) (embTok y) ↔ leAt n x y`. That is the
  coherence the colimit runs on, and precisely the statement the indexed encoding
  could not express without transport.

  **D∞ is now built**: `dInfinity : DInfinityFoundations (TokenIdeal dInfTokens)`.
  A token is a pair `(n, x) : Nat × DTok` — a *declared level* and a token —
  compared after lifting both to the max of the declared levels (`cmpTok`), with
  `cmpTok_up`/`cmpTok_eq` showing any admissible comparison level gives the same
  answer. Nothing forces x to be well formed at level n and nothing needs to: a
  token declared too low is read through `isTopTok` and so is order-equivalent to ⊥,
  and extra copies of ⊥ change no ideal. That is what lets the carrier be a plain
  product rather than a subtype.

  Joins are total — inherited from D₀ = 𝕊 being a lattice — and are concatenation of
  step-sets; `joinLift` carries that through lifting by induction on the number of
  lifts, with the comparison level dropping alongside. Countability is `dtoksUpTo`,
  proved covering by a **mutual** recursion over `DTok` and its list, which is what
  the nested inductive calls for.

  `dInfinity` consumes exactly what every other witness does —
  `[lem, propext, Quot.sound]` — and in particular **no `Classical.choice`**. That
  took a measurement to secure: an earlier `dLe_lub` closed an impossible branch
  with a bare `omega` whose *goal was not arithmetic*, and omega discharges such a
  goal through `Classical.byContradiction`. It would have been the development's
  first use of choice outside the ℝ module. `absurd hN (by omega)` — omega proving
  the arithmetic fact, `absurd` doing the eliminating — removes it.

  Note also that `D₀ = 𝕊` is a lattice, which is Scott's own 1972 setting; §2's row
  saying D∞ is not a lattice refers to starting from a non-lattice D₀.
- **§6.3 is proved**, in its own module
  [IntervalDomain.lean](../Domains/IntervalDomain.lean):
  `compact_iff_eq_bot : IsCompactEl I ↔ I = ivalBot` — **K(I[0,1]) = {⊥}**, so the
  interval domain is not algebraic and not a Scott domain, which is this entry's
  claim. For any I ≠ ⊥ the refuting family is the widenings of I: same right
  endpoint and strictly smaller left endpoint (or the mirror image). Each family is
  *totally ordered*, so directedness needs no construction — the upper bound of two
  members is whichever is sharper — and its supremum is I, with no member above I.

  This is the **only** module that imports Mathlib, which it needs for ℝ.
  `LRSODInCIC.lean` and `ScottDomainExamples.lean` still import nothing, and the
  quarantine is the point: the audit here reads `[propext, Classical.choice,
  Quot.sound]`, and that `Classical.choice` is ℝ's, not the development's. The
  order-theoretic vocabulary — directed family, supremum, way-below, compact
  element — is defined locally, since the D1–D4 file is stated topologically and
  carries none of it.

  Note for other checkouts: the package now has a Mathlib dependency pinned to tag
  `v4.32.2`, matching `lean-toolchain` exactly, so no toolchain change is involved.
  A fresh checkout needs `lake exe cache get` before `lake build`.
- **§6.4 is proved** in the same module: `ui_compact_iff : IsCompactEl uiLe x ↔
  x = uiBot` — **K([0,1]) = {0}**, so the unit interval under ≤ is not algebraic
  either. It is the cleaner half of the pair: the refuting family is just
  "everything strictly below x", again totally ordered, with none of §6.3's
  interval bookkeeping. `ui_way_below_of_lt` supplies the *positive* half the
  catalogue asserts — x ≪ y whenever x < y — so what fails at §6.4 is algebraicity
  alone, and §6.3 together with §6.4 is the standard demonstration that continuous
  ⊋ algebraic. The order-theoretic vocabulary is shared with §6.3 rather than
  duplicated: `IsDirectedFam`, `IsLubFam`, `WayBelow` and `IsCompactEl` take the
  order as a parameter.
- **§6.5 is half proved, and the halves are not of the same kind.** The **Hoare
  (lower) powerdomain** is done: `hoarePowerdomain : (P : TokenPoset) →
  DInfinityFoundations (TokenIdeal (hoareTokens P))`. Its tokens are finite sets of
  tokens under "every member of A is below some member of B", and `hoare_join_total`
  shows joins are unions and are **total** — which is what puts it inside the
  algebraic *lattices*, as this section claims, rather than merely the domains.

  The **Plotkin (convex)** claim — that the convex powerdomain of a Scott domain
  need not be bounded complete — is **not** formalized, and the reason is worth
  recording. It is a refutation needing a *specific* Scott domain whose convex
  powerdomain has a bounded pair with no least bound, and the small cases do not
  supply one: over 𝔹⊥ the pair {⊥,tt}, {⊥,ff} is bounded by {tt,ff} and by
  {⊥,tt,ff}, and the second is below the first, so a least bound does exist there.
  A genuine counterexample is a piece of domain theory in its own right rather than
  a re-encoding of the catalogue, so `egliMilnerLe` is recorded for the statement's
  sake, with `egliMilner_le_hoare` showing the convex order is the lower order plus
  the upper condition — the half that costs bounded completeness — and the
  refutation is left open.
- **§5.2 is proved as far as this vocabulary reaches, and the boundary is exact.**
  Proved: por is **monotone in both arguments** (`por_mono_left`,
  `por_mono_right`), hence continuous — on a flat domain a directed subset is a
  chain with a greatest element, so preserving directed suprema *is* monotonicity —
  hence an element of the function domain, which is the section's first claim.

  Not proved, and not provable here: **undefinability in PCF**. Definability is a
  statement about a *syntax* and its operational semantics, needing a PCF term
  language and an adequacy theorem, neither of which the D1–D4 setting carries.

  What replaces it is the semantic hallmark that separates por from every
  sequential function: **`por_not_seq`, that por has no sequentiality index** — it
  is strict in neither argument, so evaluation cannot begin anywhere. `lor_seq`
  shows the notion is not vacuous (sequential left-strict or has one), and
  `por_lor_agree` shows the two agree on total data, so the whole difference is the
  behaviour at ⊥. That is exactly what "parallel" names.
- The D1–D4 axioms are stated purely in the vocabulary of layer O
  ([LRSODInCIC.lean:104](../Domains/LRSODInCIC.lean)), so each witness above is built by
  giving a topology and discharging four proof obligations — not by defining an
  order and deriving the topology.

## 9. Sources

- D. S. Scott, *Continuous Lattices*, Lecture Notes in Mathematics 274, 1972.
- D. S. Scott, "Data Types as Lattices", *SIAM J. Computing* 5(3), 1976 — Pω.
- C. Gunter and D. S. Scott, "Semantic Domains", *Handbook of Theoretical Computer
  Science* B, 1990 — the definition of Scott domain used here.
- G. Gierz et al., *Continuous Lattices and Domains*, 2003 — the standard
  reference for §1, §5.6, and the sobriety of the Scott topology.
- G. Plotkin, "LCF Considered as a Programming Language", *TCS* 5, 1977 —
  parallel-or, §5.2.
