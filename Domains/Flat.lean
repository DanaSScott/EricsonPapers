/- ================================================================
   §3.3 — the flat domain 𝔹⊥.

   Part of the Scott domain catalogue; see ../docs/ScottDomainExamples.md
   and Domains/ScottDomainExamples.lean, which imports every part.
   ================================================================ -/

import Domains.LRSODInCIC

/- ----------------------------------------------------------------
   §3.3 — the flat domain 𝔹⊥ = {⊥, tt, ff}

   Carrier `Option Bool`: `none` is ⊥, `some b` is the datum b, and the
   two data are incomparable. The catalogue's description of the Scott
   topology — "an up-set containing ⊥ is everything, so the opens are
   exactly 𝒫(A) together with A⊥ itself" — is the definition used here:

       isOpen U  :=  U ⊥ → ∀ x, U x

   This is the first witness whose carrier has two incomparable points,
   and that is where the work is. In 𝟙 and 𝕊 every inhabited closed set
   was irreducible; here the whole space is **not**, since it splits as
   ↓tt ∪ ↓ff with neither part containing the other. So D2 cannot be
   proved by producing a generic point in every case — the proof must
   show that the one case with no generic point is excluded by the
   irreducibility hypothesis, by exhibiting that decomposition.
   ---------------------------------------------------------------- -/

def flatBoolTop : TopologicalSpace (Option Bool) where
  isOpen U  := U none → ∀ x, U x
  openEmpty := fun h _ => h
  openFull  := fun _ _ => trivial
  openUnion := by
    intro _ U hU h x
    obtain ⟨i, hi⟩ := h
    exact ⟨i, hU i hi x⟩
  openInter := by
    intro U W hU hW h x
    exact ⟨hU h.1 x, hW h.2 x⟩

/- The three impossible equations of the carrier, each concluding `False`. Stating
   them as named lemmas rather than inlining `Option.noConfusion` fixes its motive:
   applied inline the elaborator cannot tell the distinct-constructor case from the
   `some`/`some` case, whose continuation takes a `HEq`. -/

theorem flat_none_ne_some {b : Bool} (h : (none : Option Bool) = some b) : False := by
  cases h

theorem flat_some_ne_none {b : Bool} (h : (some b : Option Bool) = none) : False := by
  cases h

theorem flat_true_ne_false (h : (some true : Option Bool) = some false) : False :=
  Bool.noConfusion (Option.some.inj h)

theorem flat_false_ne_true (h : (some false : Option Bool) = some true) : False :=
  Bool.noConfusion (Option.some.inj h)

/-- Each datum's singleton is open: it does not contain ⊥, so openness is vacuous. -/
theorem flat_isOpen_singleton (b : Bool) : flatBoolTop.isOpen (fun z => z = some b) :=
  fun h => (flat_none_ne_some h).elim

/-- The "defined" set {tt, ff} is open, for the same reason. -/
theorem flat_isOpen_defined : flatBoolTop.isOpen (fun z => z ≠ none) :=
  fun h => absurd rfl h

/-- ⊥ is below everything: any open containing ⊥ is the whole space. -/
theorem flat_leq_none (x : Option Bool) : flatBoolTop.leq none x := fun _ hU h => hU h x

/-- A datum is below only itself — this is what makes tt and ff incomparable. -/
theorem flat_leq_some {b : Bool} {y : Option Bool} (h : flatBoolTop.leq (some b) y) :
    y = some b :=
  h (fun z => z = some b) (flat_isOpen_singleton b) rfl

theorem flat_leq_some_self (b : Bool) : flatBoolTop.leq (some b) (some b) := fun _ _ h => h

def flatBool : DInfinityFoundations (Option Bool) where
  toTopologicalSpace := flatBoolTop

  -- D1: {tt} and {ff} separate the data; the "defined" open separates each from ⊥.
  t0 := by
    intro x y h
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some c =>
            exact absurd rfl
              ((h _ flat_isOpen_defined).mpr (fun hc => flat_some_ne_none hc))
    | some b =>
        cases y with
        | none =>
            exact absurd rfl
              ((h _ flat_isOpen_defined).mp (fun hb => flat_some_ne_none hb))
        | some c =>
            exact ((h _ (flat_isOpen_singleton b)).mp rfl).symm

  -- D2: the irreducible closed sets are ↓⊥ = {⊥}, ↓tt = {⊥,tt} and ↓ff = {⊥,ff}.
  -- The whole space is closed and inhabited but reducible, and the proof below
  -- discharges that case by handing `irreducible` the split ↓tt ∪ ↓ff.
  sober := by
    intro C hC hirr
    obtain ⟨w, hw⟩ := hirr.1
    have hnone : C none := by
      cases lem (C none) with
      | inl h => exact h
      | inr h => exact absurd hw (hC h w)
    cases lem (C (some true)) with
    | inl hCt =>
        cases lem (C (some false)) with
        | inl hCf =>
            -- C is the whole space: reducible, contradicting the hypothesis.
            refine absurd ⟨flatBoolTop.clSingleton (some true),
                           flatBoolTop.clSingleton (some false), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hirr.2
            · exact fun h => absurd (flat_leq_none _) h
            · exact fun h => absurd (flat_leq_none _) h
            · intro x hx
              cases x with
              | none => exact hnone
              | some b => cases b with
                | true  => exact hCt
                | false => exact (flat_true_ne_false (flat_leq_some hx)).elim
            · intro x hx
              cases x with
              | none => exact hnone
              | some b => cases b with
                | true  => exact (flat_false_ne_true (flat_leq_some hx)).elim
                | false => exact hCf
            · intro x _
              cases x with
              | none => exact Or.inl (flat_leq_none _)
              | some b => cases b with
                | true  => exact Or.inl (flat_leq_some_self true)
                | false => exact Or.inr (flat_leq_some_self false)
            · exact ⟨some false, hCf, fun hx => flat_true_ne_false (flat_leq_some hx)⟩
            · exact ⟨some true, hCt, fun hx => flat_false_ne_true (flat_leq_some hx)⟩
        | inr hCf =>
            refine ⟨some true, ?_, ?_⟩
            · funext x
              cases x with
              | none => exact propext ⟨fun _ => flat_leq_none _, fun _ => hnone⟩
              | some b => cases b with
                | true  => exact propext ⟨fun _ => flat_leq_some_self true, fun _ => hCt⟩
                | false => exact propext ⟨fun h => absurd h hCf,
                             fun h => (flat_true_ne_false (flat_leq_some h)).elim⟩
            · intro y' hy'
              exact flat_leq_some (cast (congrFun hy' (some true)) hCt)
    | inr hCt =>
        cases lem (C (some false)) with
        | inl hCf =>
            refine ⟨some false, ?_, ?_⟩
            · funext x
              cases x with
              | none => exact propext ⟨fun _ => flat_leq_none _, fun _ => hnone⟩
              | some b => cases b with
                | true  => exact propext ⟨fun h => absurd h hCt,
                             fun h => (flat_false_ne_true (flat_leq_some h)).elim⟩
                | false => exact propext ⟨fun _ => flat_leq_some_self false, fun _ => hCf⟩
            · intro y' hy'
              exact flat_leq_some (cast (congrFun hy' (some false)) hCf)
        | inr hCf =>
            refine ⟨none, ?_, ?_⟩
            · funext x
              cases x with
              | none => exact propext ⟨fun _ => flat_leq_none _, fun _ => hnone⟩
              | some b => cases b with
                | true  => exact propext ⟨fun h => absurd h hCt,
                             fun h => (flat_none_ne_some (flat_leq_some h)).elim⟩
                | false => exact propext ⟨fun h => absurd h hCf,
                             fun h => (flat_none_ne_some (flat_leq_some h)).elim⟩
            · intro y' hy'
              cases y' with
              | none => rfl
              | some b =>
                  have hb : C (some b) :=
                    cast (congrFun hy' (some b)).symm (flat_leq_some_self b)
                  cases b with
                  | true  => exact absurd hb hCt
                  | false => exact absurd hb hCf

  -- D3: the base is {⊥,tt,ff}, {tt}, {ff}, ∅ — the compact opens, closed under
  -- binary intersection because tt and ff have no upper bound (see §4 on why
  -- `basisCap` is the topological form of bounded completeness).
  basis := fun n =>
    match n with
    | 0     => fun _ => True
    | 1     => fun z => z = some true
    | 2     => fun z => z = some false
    | _ + 3 => fun _ => False

  basisOpen := by
    intro n
    rcases n with _ | _ | _ | n
    · exact fun _ _ => trivial
    · exact flat_isOpen_singleton true
    · exact flat_isOpen_singleton false
    · exact fun h _ => h

  basisCpt := by
    intro n ι U hU hcov
    rcases n with _ | _ | _ | n
    · obtain ⟨i, hi⟩ := hcov none trivial
      exact ⟨1, fun _ => i, fun x _ => ⟨0, hU i hi x⟩⟩
    · obtain ⟨i, hi⟩ := hcov (some true) rfl
      refine ⟨1, fun _ => i, ?_⟩
      intro x hx
      subst hx
      exact ⟨0, hi⟩
    · obtain ⟨i, hi⟩ := hcov (some false) rfl
      refine ⟨1, fun _ => i, ?_⟩
      intro x hx
      subst hx
      exact ⟨0, hi⟩
    · exact ⟨0, Fin.elim0, fun _ hx => hx.elim⟩

  basisGen := by
    intro U hU x hx
    cases x with
    | none => exact ⟨0, trivial, fun y _ => hU hx y⟩
    | some b =>
        cases b with
        | true  =>
            refine ⟨1, rfl, ?_⟩
            intro y hy
            subst hy
            exact hx
        | false =>
            refine ⟨2, rfl, ?_⟩
            intro y hy
            subst hy
            exact hx

  basisCap := by
    intro m n
    rcases m with _ | _ | _ | m
    · rcases n with _ | _ | _ | n
      · exact ⟨0, fun _ => ⟨fun _ => trivial, fun _ => ⟨trivial, trivial⟩⟩⟩
      · exact ⟨1, fun _ => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩⟩
      · exact ⟨2, fun _ => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩⟩
      · exact ⟨3, fun _ => ⟨fun h => h.2, fun h => h.elim⟩⟩
    · rcases n with _ | _ | _ | n
      · exact ⟨1, fun _ => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩⟩
      · exact ⟨1, fun _ => ⟨fun h => h.1, fun h => ⟨h, h⟩⟩⟩
      · exact ⟨3, fun _ => ⟨fun h => flat_true_ne_false (h.1.symm.trans h.2),
                 fun h => h.elim⟩⟩
      · exact ⟨3, fun _ => ⟨fun h => h.2, fun h => h.elim⟩⟩
    · rcases n with _ | _ | _ | n
      · exact ⟨2, fun _ => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩⟩
      · exact ⟨3, fun _ => ⟨fun h => flat_false_ne_true (h.1.symm.trans h.2),
                 fun h => h.elim⟩⟩
      · exact ⟨2, fun _ => ⟨fun h => h.1, fun h => ⟨h, h⟩⟩⟩
      · exact ⟨3, fun _ => ⟨fun h => h.2, fun h => h.elim⟩⟩
    · rcases n with _ | _ | _ | n
      · exact ⟨3, fun _ => ⟨fun h => h.1, fun h => h.elim⟩⟩
      · exact ⟨3, fun _ => ⟨fun h => h.1, fun h => h.elim⟩⟩
      · exact ⟨3, fun _ => ⟨fun h => h.1, fun h => h.elim⟩⟩
      · exact ⟨3, fun _ => ⟨fun h => h.1, fun h => h.elim⟩⟩

  -- D4: ⊥ is the generic point — that is exactly the openness condition.
  bot   := none
  botAx := fun _ hU h x => hU h x

/-- tt and ff are incomparable: 𝔹⊥ is not a lattice, unlike 𝟙 and 𝕊. -/
theorem flat_incomparable : ¬ flatBoolTop.leq (some true) (some false) := by
  intro h
  exact flat_false_ne_true (flat_leq_some h)

-- Axiom audit. `lem` is back, and for the same reason it appeared in `sierp`: D2
-- needs to know, of an arbitrary closed C, whether it contains tt and whether it
-- contains ff, and the carrier gives no decision procedure for an arbitrary
-- predicate. Layer O and the incomparability of the two data are constructive.
#print axioms flatBoolTop         -- does not depend on any axioms
#print axioms flat_incomparable   -- does not depend on any axioms
#print axioms flatBool            -- [lem, propext, Quot.sound]


