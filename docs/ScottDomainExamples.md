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

- **2 of the 16 entries in §2 are formally verified**, both kernel-checked:

  | § | witness | carrier | axioms consumed |
  |---|---------|---------|-----------------|
  | 3.2/4 | `sierp : DInfinityFoundations Bool` | `Bool` | `[lem, propext, Quot.sound]` |
  | 3.1 | `onePoint : DInfinityFoundations Unit` | `Unit` | `[propext, Quot.sound]` |

  The difference in the third column is the point of the pair. `lem` enters
  `sierp` only through D2, to case split on `C ⊤`; 𝟙 has no second point to split
  on, so its sobriety proof is constructive and `lem` drops out. What remains in
  both is `propext` with `Quot.sound` (the latter via `funext`), from the closure
  equation `C = clSingleton ⊥` being an equality of predicates. Every obligation
  for 𝟙 is discharged by definitional eta for structures — each `x : Unit` *is*
  `()` — so `t0` closes by `rfl` where the `Bool` witness needed a case split.
- 0 non-examples are formalized. §6.1 is the cheapest next witness: a six-element
  finite poset, decidable throughout, so a refutation of bounded completeness
  should go through by `decide` with no classical axioms.
- §3.3 (flat 𝔹⊥) and §3.4 (ω + 1) are the natural next positive witnesses; the
  first is finite and decidable, the second is the first case where a
  non-compact element appears and `basisCpt` has real content.
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
