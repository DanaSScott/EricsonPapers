/- ================================================================
   §3.2 / §4 — the Sierpiński domain 𝕊, and its three opens.

   Part of the Scott domain catalogue; see ../docs/ScottDomainExamples.md
   and Domains/ScottDomainExamples.lean, which imports every part.
   ================================================================ -/

import Domains.LRSODInCIC

/- ----------------------------------------------------------------
   §3.2 / §4 — the Sierpiński domain 𝕊 = {⊥ ⊑ ⊤}

   The witness itself is `sierp : DInfinityFoundations Bool` in
   `LRSODInCIC.lean`; D1–D4 are discharged there. What §4 asserts and
   that file does not prove is the *enumeration*: the opens are
   **exactly** ∅, {⊤}, {⊥,⊤} — three of them, no more.

   That claim needs care in this encoding. A subset is a `Bool → Prop`,
   so an open is any `U` with `U ⊥ → U ⊤`, and `U ⊥` may be an
   undecided proposition. Constructively there are therefore more opens
   than three; the count of three is recovered only by deciding each
   truth value, which is what `lem` does. The enumeration below is thus
   the first result here whose *statement* is classical rather than
   only its proof — and the axiom audit measures exactly that.
   ---------------------------------------------------------------- -/

/-- Every open of 𝕊 is one of the three named sets. -/
theorem sierp_open_cases (U : Bool → Prop) (hU : sierpTop.isOpen U) :
    U = (fun _ => False) ∨ U = (fun b => b = true) ∨ U = (fun _ => True) := by
  cases lem (U false) with
  | inl hf =>
      -- ⊥ ∈ U forces ⊤ ∈ U by openness, so U is the whole space.
      refine Or.inr (Or.inr ?_)
      funext b
      exact propext ⟨fun _ => trivial, fun _ => sierp_up hU hf b⟩
  | inr hf =>
      cases lem (U true) with
      | inl ht =>
          refine Or.inr (Or.inl ?_)
          funext b
          cases b
          · exact propext ⟨fun h => absurd h hf, fun h => Bool.noConfusion h⟩
          · exact propext ⟨fun _ => rfl, fun _ => ht⟩
      | inr ht =>
          refine Or.inl ?_
          funext b
          cases b
          · exact propext ⟨fun h => absurd h hf, False.elim⟩
          · exact propext ⟨fun h => absurd h ht, False.elim⟩

/-- ∅ ≠ {⊤}. -/
theorem sierp_empty_ne_top : (fun _ => False) ≠ (fun b : Bool => b = true) := by
  intro h
  exact cast (congrFun h true).symm rfl

/-- {⊤} ≠ {⊥,⊤}. -/
theorem sierp_top_ne_full : (fun b : Bool => b = true) ≠ (fun _ => True) := by
  intro h
  exact Bool.noConfusion (cast (congrFun h false).symm trivial)

/-- ∅ ≠ {⊥,⊤}. -/
theorem sierp_empty_ne_full : (fun _ => False) ≠ (fun _ : Bool => True) := by
  intro h
  exact cast (congrFun h false).symm trivial

-- Axiom audit for the enumeration. `sierp_open_cases` consumes `lem` — the two
-- case splits on `U ⊥` and `U ⊤` — plus `propext` and `Quot.sound` from the
-- pointwise equalities. The three distinctness facts are constructive: each
-- exhibits a point where the two predicates differ, needing no excluded middle.
#print axioms sierp_open_cases     -- [lem, propext, Quot.sound]
#print axioms sierp_empty_ne_top   -- does not depend on any axioms
#print axioms sierp_top_ne_full    -- does not depend on any axioms
#print axioms sierp_empty_ne_full  -- does not depend on any axioms


