/- ================================================================
   §6.3 — the interval domain I[0,1]: algebraicity fails.

   Closed subintervals of [0,1] ordered by **reverse inclusion** — more
   information is a smaller interval — with ⊥ = [0,1]. The catalogue's
   claim is that this is a perfectly good *continuous* domain but is
   **not algebraic**, because its only compact element is ⊥: for any
   [a,b] ≠ [0,1] the directed family of slightly larger intervals has
   supremum [a,b] with no member below it.

   This is the one entry that needs the real numbers, so it is the one
   module that imports Mathlib. `LRSODInCIC.lean` and
   `ScottDomainExamples.lean` import nothing and must stay that way:
   the deep embedding's point is that layer S's restrictions cannot be
   bypassed via Lean's ambient library.

   The order-theoretic vocabulary is defined here rather than reused,
   because the D1–D4 file is stated topologically and carries no notion
   of directed set, supremum, or compact element.

   Both widening families are **totally ordered** — same right endpoint,
   varying left, or the mirror image — so directedness needs no
   construction at all: the upper bound of two members is whichever of
   the two is sharper.
   ================================================================ -/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-- A closed subinterval [lo, hi] ⊆ [0,1]. -/
structure Ival where
  lo        : ℝ
  hi        : ℝ
  lo_le_hi  : lo ≤ hi
  zero_le   : 0 ≤ lo
  hi_le_one : hi ≤ 1

theorem Ival.eq_of (I J : Ival) (h1 : I.lo = J.lo) (h2 : I.hi = J.hi) : I = J := by
  cases I; cases J; simp_all

/-- Reverse inclusion: `I ⊑ J` means J is the sharper interval, J ⊆ I. -/
def ivalLe (I J : Ival) : Prop := I.lo ≤ J.lo ∧ J.hi ≤ I.hi

def ivalBot : Ival := ⟨0, 1, by norm_num, le_refl 0, le_refl 1⟩

theorem ivalBot_le (I : Ival) : ivalLe ivalBot I := ⟨I.zero_le, I.hi_le_one⟩

/- The order-theoretic notions, in the vocabulary of §1 of the catalogue. -/

def IsDirectedFam {α : Type} (le : α → α → Prop) (S : α → Prop) : Prop :=
  (∃ x, S x) ∧ ∀ x y, S x → S y → ∃ z, S z ∧ le x z ∧ le y z

def IsLubFam {α : Type} (le : α → α → Prop) (S : α → Prop) (u : α) : Prop :=
  (∀ x, S x → le x u) ∧ ∀ v, (∀ x, S x → le x v) → le u v

/-- x ≪ y: every directed family whose supremum is above y already passes x. -/
def WayBelow {α : Type} (le : α → α → Prop) (x y : α) : Prop :=
  ∀ S u, IsDirectedFam le S → IsLubFam le S u → le y u → ∃ s, S s ∧ le x s

def IsCompactEl {α : Type} (le : α → α → Prop) (x : α) : Prop := WayBelow le x x

/-- ⊥ is compact: it is below every member, so any member of a nonempty family
    witnesses the condition. -/
theorem ivalBot_compact : IsCompactEl ivalLe ivalBot := by
  intro S _ hdir _ _
  obtain ⟨s, hs⟩ := hdir.1
  exact ⟨s, hs, ivalBot_le s⟩

/-- Widening on the left: same right endpoint, strictly smaller left endpoint. -/
def widenL (I : Ival) : Ival → Prop :=
  fun J => J.hi = I.hi ∧ J.lo < I.lo ∧ 0 ≤ J.lo

theorem widenL_directed (I : Ival) (h : 0 < I.lo) : IsDirectedFam ivalLe (widenL I) := by
  refine ⟨⟨⟨I.lo / 2, I.hi, by linarith [I.lo_le_hi], by linarith, I.hi_le_one⟩,
           rfl, by simp only; linarith, by simp only; linarith⟩, ?_⟩
  intro x y hx hy
  rcases le_total x.lo y.lo with hxy | hxy
  · exact ⟨y, hy, ⟨hxy, le_of_eq (hy.1.trans hx.1.symm)⟩, ⟨le_refl _, le_refl _⟩⟩
  · exact ⟨x, hx, ⟨le_refl _, le_refl _⟩, ⟨hxy, le_of_eq (hx.1.trans hy.1.symm)⟩⟩

theorem widenL_lub (I : Ival) (h : 0 < I.lo) : IsLubFam ivalLe (widenL I) I := by
  constructor
  · intro x hx
    exact ⟨le_of_lt hx.2.1, le_of_eq hx.1.symm⟩
  · intro v hv
    refine ⟨?_, ?_⟩
    · by_contra hcon
      have hlt : v.lo < I.lo := not_le.mp hcon
      have hc0 : 0 ≤ (v.lo + I.lo) / 2 := by linarith [v.zero_le]
      have hc1 : (v.lo + I.lo) / 2 < I.lo := by linarith
      have hcle : (v.lo + I.lo) / 2 ≤ I.hi := by linarith [I.lo_le_hi]
      have hmem : widenL I ⟨(v.lo + I.lo) / 2, I.hi, hcle, hc0, I.hi_le_one⟩ :=
        ⟨rfl, hc1, hc0⟩
      have hle := (hv _ hmem).1
      simp only at hle
      linarith
    · obtain ⟨x, hx⟩ := (widenL_directed I h).1
      have hle := (hv x hx).2
      rw [hx.1] at hle
      exact hle

/-- No member of the widening family is above I: that is exactly non-compactness. -/
theorem not_compact_of_lo_pos (I : Ival) (h : 0 < I.lo) : ¬ IsCompactEl ivalLe I := by
  intro hcomp
  obtain ⟨s, hs, hIs⟩ :=
    hcomp (widenL I) I (widenL_directed I h) (widenL_lub I h) ⟨le_refl _, le_refl _⟩
  have := hs.2.1
  have := hIs.1
  linarith

/-- Widening on the right, the mirror image. -/
def widenR (I : Ival) : Ival → Prop :=
  fun J => J.lo = I.lo ∧ I.hi < J.hi ∧ J.hi ≤ 1

theorem widenR_directed (I : Ival) (h : I.hi < 1) : IsDirectedFam ivalLe (widenR I) := by
  refine ⟨⟨⟨I.lo, (I.hi + 1) / 2, by linarith [I.lo_le_hi], I.zero_le, by linarith⟩,
           rfl, by simp only; linarith, by simp only; linarith⟩, ?_⟩
  intro x y hx hy
  rcases le_total x.hi y.hi with hxy | hxy
  · exact ⟨x, hx, ⟨le_refl _, le_refl _⟩, ⟨le_of_eq (hy.1.trans hx.1.symm), hxy⟩⟩
  · exact ⟨y, hy, ⟨le_of_eq (hx.1.trans hy.1.symm), hxy⟩, ⟨le_refl _, le_refl _⟩⟩

theorem widenR_lub (I : Ival) (h : I.hi < 1) : IsLubFam ivalLe (widenR I) I := by
  constructor
  · intro x hx
    exact ⟨le_of_eq hx.1, le_of_lt hx.2.1⟩
  · intro v hv
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := (widenR_directed I h).1
      have hle := (hv x hx).1
      rw [hx.1] at hle
      exact hle
    · by_contra hcon
      have hlt : I.hi < v.hi := not_le.mp hcon
      have hc1 : (I.hi + v.hi) / 2 ≤ 1 := by linarith [v.hi_le_one]
      have hc2 : I.hi < (I.hi + v.hi) / 2 := by linarith
      have hcle : I.lo ≤ (I.hi + v.hi) / 2 := by linarith [I.lo_le_hi]
      have hmem : widenR I ⟨I.lo, (I.hi + v.hi) / 2, hcle, I.zero_le, hc1⟩ :=
        ⟨rfl, hc2, hc1⟩
      have hle := (hv _ hmem).2
      simp only at hle
      linarith

theorem not_compact_of_hi_lt_one (I : Ival) (h : I.hi < 1) : ¬ IsCompactEl ivalLe I := by
  intro hcomp
  obtain ⟨s, hs, hIs⟩ :=
    hcomp (widenR I) I (widenR_directed I h) (widenR_lub I h) ⟨le_refl _, le_refl _⟩
  have := hs.2.1
  have := hIs.2
  linarith

/-- **K(I[0,1]) = {⊥}**: the interval domain is not algebraic, which is §6.3's
    claim and the reason it is not a Scott domain. -/
theorem compact_iff_eq_bot (I : Ival) : IsCompactEl ivalLe I ↔ I = ivalBot := by
  constructor
  · intro hcomp
    have hlo : I.lo = 0 := by
      by_contra hne
      exact not_compact_of_lo_pos I (lt_of_le_of_ne I.zero_le (Ne.symm hne)) hcomp
    have hhi : I.hi = 1 := by
      by_contra hne
      exact not_compact_of_hi_lt_one I (lt_of_le_of_ne I.hi_le_one hne) hcomp
    exact Ival.eq_of I ivalBot hlo hhi
  · intro h
    subst h
    exact ivalBot_compact

/- ================================================================
   §6.4 — [0,1] ⊆ ℝ under ≤: algebraicity fails, lattice version

   The unit interval under the usual order is a complete lattice and a
   *continuous* one — x ≪ y whenever x < y — but K = {0}, so it is not
   algebraic. Together with §6.3 this is the standard demonstration
   that continuous ⊋ algebraic, and it is the cleaner half: the same
   refutation with none of the interval bookkeeping, because the
   refuting family is just "everything strictly below x", which is
   totally ordered.
   ================================================================ -/

def UI : Type := {x : ℝ // 0 ≤ x ∧ x ≤ 1}

def uiLe (x y : UI) : Prop := x.val ≤ y.val

def uiBot : UI := ⟨0, le_refl 0, by norm_num⟩

theorem uiBot_le (x : UI) : uiLe uiBot x := x.2.1

theorem uiBot_compact : IsCompactEl uiLe uiBot := by
  intro S _ hdir _ _
  obtain ⟨s, hs⟩ := hdir.1
  exact ⟨s, hs, uiBot_le s⟩

/-- Everything strictly below x. -/
def belowFam (x : UI) : UI → Prop := fun y => y.val < x.val

theorem belowFam_directed (x : UI) (h : 0 < x.val) : IsDirectedFam uiLe (belowFam x) := by
  constructor
  · refine ⟨⟨x.val / 2, ⟨by linarith, by linarith [x.2.2]⟩⟩, ?_⟩
    show x.val / 2 < x.val
    linarith
  · intro y z hy hz
    rcases le_total y.val z.val with hyz | hyz
    · exact ⟨z, hz, hyz, le_refl _⟩
    · exact ⟨y, hy, le_refl _, hyz⟩

theorem belowFam_lub (x : UI) (h : 0 < x.val) : IsLubFam uiLe (belowFam x) x := by
  constructor
  · intro y hy
    exact le_of_lt hy
  · intro v hv
    by_contra hcon
    have hlt : v.val < x.val := not_le.mp hcon
    have hmem : belowFam x ⟨(v.val + x.val) / 2, ⟨by linarith [v.2.1], by linarith [x.2.2]⟩⟩ := by
      show (v.val + x.val) / 2 < x.val
      linarith
    have hle : (v.val + x.val) / 2 ≤ v.val := hv _ hmem
    linarith

/-- **K([0,1]) = {0}**: not algebraic, which is §6.4's claim. -/
theorem ui_not_compact_of_pos (x : UI) (h : 0 < x.val) : ¬ IsCompactEl uiLe x := by
  intro hcomp
  obtain ⟨s, hs, hxs⟩ :=
    hcomp (belowFam x) x (belowFam_directed x h) (belowFam_lub x h) (le_refl _)
  have h1 : s.val < x.val := hs
  have h2 : x.val ≤ s.val := hxs
  linarith

theorem ui_compact_iff (x : UI) : IsCompactEl uiLe x ↔ x = uiBot := by
  constructor
  · intro hcomp
    have hx : x.val = 0 := by
      by_contra hne
      exact ui_not_compact_of_pos x (lt_of_le_of_ne x.2.1 (Ne.symm hne)) hcomp
    exact Subtype.ext hx
  · intro h
    subst h
    exact uiBot_compact

/-- The positive half of the catalogue's claim: [0,1] *is* continuous — x ≪ y
    whenever x < y — so the failure at §6.4 is algebraicity alone. -/
theorem ui_way_below_of_lt (x y : UI) (h : x.val < y.val) : WayBelow uiLe x y := by
  intro S u hdir hlub hyu
  by_contra hcon
  have hub : ∀ s, S s → uiLe s x := by
    intro s hs
    have hns : ¬ uiLe x s := fun hxs => hcon ⟨s, hs, hxs⟩
    exact le_of_lt (not_le.mp hns)
  have hux : uiLe u x := hlub.2 x hub
  have h1 : y.val ≤ u.val := hyu
  have h2 : u.val ≤ x.val := hux
  linarith

-- Axiom audit. Mathlib's real numbers bring `Classical.choice` with them, which is
-- exactly why these two entries are quarantined in this module: the classical
-- content here is ℝ's, not the development's.
#print axioms ivalBot_compact
#print axioms not_compact_of_lo_pos
#print axioms compact_iff_eq_bot
#print axioms ui_compact_iff
#print axioms ui_way_below_of_lt
