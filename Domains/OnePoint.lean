/- ================================================================
   §3.1 — the one-point domain 𝟙.

   Part of the Scott domain catalogue; see ../docs/ScottDomainExamples.md
   and Domains/ScottDomainExamples.lean, which imports every part.
   ================================================================ -/

import Domains.LRSODInCIC

/- ----------------------------------------------------------------
   §3.1 — the one-point domain 𝟙 = {⊥}

   Carrier `Unit`. The catalogue records the Scott topology as
   {∅, {⊥}}: on a one-element poset every subset is an up-set and is
   trivially inaccessible by directed suprema, so every subset is
   open. With subsets rendered as `Unit → Prop` that is `isOpen _ :=
   True` — the degenerate case of `sierpTop`'s `U ⊥ → U ⊤`, with the
   implication carrying no content because there is no second point.

   What discharges the obligations is Lean's definitional eta for
   structures: `Unit` is a structure with one constructor, so every
   `x : Unit` is *definitionally* `()`. A statement about an arbitrary
   point is therefore already a statement about ⊥, and `rfl` closes
   goals that would need a case split on a larger carrier.

   𝟙 is a Scott domain: |D| = 1, K(𝟙) = {⊥}, ω-algebraic, bounded
   complete, and a lattice (catalogue §2, row 3.1).
   ---------------------------------------------------------------- -/

def onePointTop : TopologicalSpace Unit where
  isOpen _  := True
  openEmpty := trivial
  openFull  := trivial
  openUnion := by intros; trivial
  openInter := by intros; trivial

/-- The specialization order is the diagonal: ⊥ ⊑ ⊥ and nothing else to check. -/
theorem onePoint_leq (x y : Unit) : onePointTop.leq x y := fun _ _ h => h

def onePoint : DInfinityFoundations Unit where
  toTopologicalSpace := onePointTop

  -- D1: one point, so distinct points needing separation do not exist.
  t0 := by intro _ _ _; rfl

  -- D2: the only inhabited closed set is 𝟙 itself, with generic point ⊥.
  sober := by
    intro C _ hirr
    obtain ⟨w, hw⟩ := hirr.1
    refine ⟨(), ?_, ?_⟩
    · funext x
      exact propext ⟨fun _ => onePoint_leq x (), fun _ => hw⟩
    · intro _ _
      rfl

  -- D3: a constant basis — 𝟙 itself at every index — which is open, compact,
  -- generating, and closed under intersection.
  basis     := fun _ _ => True
  basisOpen := by intros; trivial
  basisCpt  := by
    intro _ _ U _ hcov
    obtain ⟨i, hi⟩ := hcov () trivial
    exact ⟨1, fun _ => i, fun _ _ => ⟨0, hi⟩⟩
  basisGen  := by
    intro _ _ _ hx
    exact ⟨0, trivial, fun _ _ => hx⟩
  basisCap  := by
    intro _ _
    exact ⟨0, fun _ => ⟨fun _ => trivial, fun _ => ⟨trivial, trivial⟩⟩⟩

  -- D4: ⊥ is the only point, hence vacuously the generic one.
  bot   := ()
  botAx := by intro _ _ h _; exact h

-- Axiom audit. Unlike `sierp`, this witness has **no classical frontier**: `lem`
-- is absent. `sierp` needed it to case split on `C ⊤` inside D2; here the carrier
-- has no second point to split on, so sobriety goes through constructively. What
-- remains is `propext` and `Quot.sound` (the latter via `funext`), both entering
-- through the same D2 field, where the closure equation `C = clSingleton ⊥` is an
-- equality of predicates.
#print axioms onePointTop     -- does not depend on any axioms
#print axioms onePoint_leq    -- does not depend on any axioms
#print axioms onePoint        -- [propext, Quot.sound]


