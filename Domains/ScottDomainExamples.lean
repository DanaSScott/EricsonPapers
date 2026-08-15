/- ================================================================
   Scott domain examples.

   The witnesses go here. §3.1, the one-point domain, is below; the
   rest are Dana's work.

   The import below brings in the L, R, S, O, D layers, so the
   following are in scope without qualification:

     TopologicalSpace D        -- layer O, 3 axioms + openInter
     DInfinityFoundations D    -- D1 t0, D2 sober, D3 basis*, D4 bot
     sierpTop, sierp           -- the Sierpiński witness, already checked

   The mathematics to be formalized here is catalogued in
   ../docs/ScottDomainExamples.md.
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


/- ----------------------------------------------------------------
   §3.4 — the vertical naturals ℕ^∞ = ω + 1

   Carrier `Option Nat`: `some n` is the finite point n, `none` is ∞.
   The catalogue gives σ = {∅} ∪ {↑n : n ∈ ℕ}, and the content of that
   line is what {∞} is *not*: an up-set, but not open, because the
   directed set ℕ has supremum ∞ with no member above ∞. So openness
   is stated as three conditions — up-closed among the finite points,
   up-closed to ∞, and **inaccessible by the ω-chain**:

       isOpen U  :=  (a ≤ b → U a → U b) ∧ (U a → U ∞) ∧ (U ∞ → ∃ a, U a)

   The third conjunct is what excludes {∞}, and it is the first time
   in this file that openness says something a monotonicity condition
   would not.

   Two consequences for the proofs below. D2 no longer follows from a
   finite case split: a closed set is now an arbitrary bounded set of
   naturals, and the generic point is its maximum, which has to be
   *constructed* (`vert_max_of_bounded`, by induction on the bound).
   And D3's `basisCpt` has real content for the first time: extracting
   a finite subcover needs an induction that picks one covering open at
   a time (`vert_finite_cover`), because choosing one per point at once
   would need countable choice, which this development does not have —
   `lem` is the only classical principle in scope.
   ---------------------------------------------------------------- -/

def vertUp (n : Nat) : Option Nat → Prop
  | none   => True
  | some m => n ≤ m

def vertTop : TopologicalSpace (Option Nat) where
  isOpen U :=
    (∀ a b, a ≤ b → U (some a) → U (some b)) ∧
    (∀ a, U (some a) → U none) ∧
    (U none → ∃ a, U (some a))
  openEmpty := ⟨fun _ _ _ h => h, fun _ h => h, fun h => h.elim⟩
  openFull  := ⟨fun _ _ _ _ => trivial, fun _ _ => trivial, fun _ => ⟨0, trivial⟩⟩
  openUnion := by
    intro _ U hU
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab h
      obtain ⟨i, hi⟩ := h
      exact ⟨i, (hU i).1 a b hab hi⟩
    · intro a h
      obtain ⟨i, hi⟩ := h
      exact ⟨i, (hU i).2.1 a hi⟩
    · intro h
      obtain ⟨i, hi⟩ := h
      obtain ⟨a, ha⟩ := (hU i).2.2 hi
      exact ⟨a, i, ha⟩
  openInter := by
    intro U W hU hW
    refine ⟨?_, ?_, ?_⟩
    · exact fun a b hab h => ⟨hU.1 a b hab h.1, hW.1 a b hab h.2⟩
    · exact fun a h => ⟨hU.2.1 a h.1, hW.2.1 a h.2⟩
    · intro h
      obtain ⟨a, ha⟩ := hU.2.2 h.1
      obtain ⟨b, hb⟩ := hW.2.2 h.2
      rcases Nat.le_total a b with hab | hab
      · exact ⟨b, hU.1 a b hab ha, hb⟩
      · exact ⟨a, ha, hW.1 b a hab hb⟩

theorem vert_isOpen_up (n : Nat) : vertTop.isOpen (vertUp n) :=
  ⟨fun _ _ hab h => Nat.le_trans h hab, fun _ _ => trivial, fun _ => ⟨n, Nat.le_refl n⟩⟩

/-- {∞} is an up-set but **not open**: inaccessibility fails for the chain ℕ.
    This is the topological form of "∞ is not compact". -/
theorem vert_top_not_isOpen : ¬ vertTop.isOpen (fun z => z = none) := by
  intro h
  obtain ⟨a, ha⟩ := h.2.2 rfl
  cases ha

theorem vert_leq_some {a b : Nat} (h : vertTop.leq (some a) (some b)) : a ≤ b :=
  h (vertUp a) (vert_isOpen_up a) (Nat.le_refl a)

theorem vert_leq_of_le {a b : Nat} (hab : a ≤ b) : vertTop.leq (some a) (some b) :=
  fun _ hU h => hU.1 a b hab h

theorem vert_leq_some_none (a : Nat) : vertTop.leq (some a) none :=
  fun _ hU h => hU.2.1 a h

theorem vert_leq_none_none : vertTop.leq none none := fun _ _ h => h

theorem vert_not_leq_none_some (b : Nat) : ¬ vertTop.leq none (some b) := by
  intro h
  have hb : b + 1 ≤ b := h (vertUp (b + 1)) (vert_isOpen_up (b + 1)) trivial
  omega

/-- A bounded, inhabited set of naturals has a greatest element. Proved by
    induction on the bound; `lem` decides membership at each step. This is what
    supplies the generic point in D2 — unlike the finite carriers, the point is
    constructed rather than exhibited. -/
theorem vert_max_of_bounded (C : Nat → Prop) :
    ∀ n, (∀ m, C m → m < n) → ∀ w, C w → ∃ k, C k ∧ ∀ m, C m → m ≤ k := by
  intro n
  induction n with
  | zero => intro hb w hw; exact absurd (hb w hw) (Nat.not_lt_zero w)
  | succ n ih =>
      intro hb w hw
      cases lem (C n) with
      | inl h =>
          refine ⟨n, h, fun m hm => ?_⟩
          have := hb m hm
          omega
      | inr h =>
          refine ih (fun m hm => ?_) w hw
          have hlt := hb m hm
          rcases Nat.lt_or_ge m n with hmn | hmn
          · exact hmn
          · have hmn' : m = n := by omega
            subst hmn'
            exact absurd hm h

/-- A finite subcover for the finitely many points in `[n, k)`, built one open at
    a time. The induction is essential: `∀ m, ∃ i, U i m` cannot be turned into a
    function `m ↦ i` without countable choice, which is not available here. The
    goal being a `Prop` is what makes the step-by-step extraction legitimate. -/
theorem vert_finite_cover {ι : Type} (U : ι → Option Nat → Prop) (n : Nat) :
    ∀ k, (∀ m, n ≤ m → m < k → ∃ i, U i (some m)) →
      ∃ (p : Nat) (f : Fin p → ι), ∀ m, n ≤ m → m < k → ∃ j, U (f j) (some m) := by
  intro k
  induction k with
  | zero =>
      intro _
      exact ⟨0, Fin.elim0, fun m _ hm => absurd hm (Nat.not_lt_zero m)⟩
  | succ k ih =>
      intro hall
      obtain ⟨p, f, hf⟩ := ih (fun m hn hm => hall m hn (by omega))
      rcases Nat.lt_or_ge k n with hkn | hkn
      · exact ⟨p, f, fun m hn hm => hf m hn (by omega)⟩
      · obtain ⟨i, hi⟩ := hall k hkn (by omega)
        refine ⟨p + 1, fun j =>
          match j with
          | ⟨0, _⟩      => i
          | ⟨q + 1, hq⟩ => f ⟨q, by omega⟩, ?_⟩
        intro m hn hm
        rcases Nat.lt_or_ge m k with hlt | hge
        · obtain ⟨j, hj⟩ := hf m hn hlt
          exact ⟨⟨j.val + 1, by omega⟩, hj⟩
        · have hmk : m = k := by omega
          subst hmk
          exact ⟨⟨0, by omega⟩, hi⟩

def vertNat : DInfinityFoundations (Option Nat) where
  toTopologicalSpace := vertTop

  -- D1: ↑a separates a from every b it does not lie below; ↑(a+1) separates each
  -- finite point from ∞.
  t0 := by
    intro x y h
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some b =>
            have hb : b + 1 ≤ b := (h (vertUp (b + 1)) (vert_isOpen_up (b + 1))).mp trivial
            exact absurd hb (by omega)
    | some a =>
        cases y with
        | none =>
            have ha : a + 1 ≤ a := (h (vertUp (a + 1)) (vert_isOpen_up (a + 1))).mpr trivial
            exact absurd ha (by omega)
        | some b =>
            have h1 : a ≤ b := (h (vertUp a) (vert_isOpen_up a)).mp (Nat.le_refl a)
            have h2 : b ≤ a := (h (vertUp b) (vert_isOpen_up b)).mpr (Nat.le_refl b)
            have hab : a = b := by omega
            subst hab
            rfl

  -- D2: a closed set either contains ∞, and is then everything (generic point ∞),
  -- or is a bounded down-set of naturals, and is then ↓k for its maximum k.
  sober := by
    intro C hC hirr
    obtain ⟨w, hw⟩ := hirr.1
    cases lem (C none) with
    | inl hinf =>
        refine ⟨none, ?_, ?_⟩
        · funext x
          cases x with
          | none => exact propext ⟨fun _ => vert_leq_none_none, fun _ => hinf⟩
          | some a =>
              refine propext ⟨fun _ => vert_leq_some_none a, fun _ => ?_⟩
              cases lem (C (some a)) with
              | inl h => exact h
              | inr h => exact absurd hinf (hC.2.1 a h)
        · intro y' hy'
          have h1 : vertTop.leq none y' := cast (congrFun hy' none) hinf
          cases y' with
          | none => rfl
          | some b => exact absurd h1 (vert_not_leq_none_some b)
    | inr hinf =>
        -- the complement is open and contains ∞, so it contains a tail: C is bounded
        obtain ⟨a0, ha0⟩ := hC.2.2 hinf
        have hbound : ∀ m, C (some m) → m < a0 := by
          intro m hm
          rcases Nat.lt_or_ge m a0 with hlt | hge
          · exact hlt
          · exact absurd hm (hC.1 a0 m hge ha0)
        have hw' : ∃ m, C (some m) := by
          cases w with
          | none => exact absurd hw hinf
          | some m => exact ⟨m, hw⟩
        obtain ⟨w0, hw0⟩ := hw'
        obtain ⟨k, hk, hmax⟩ :=
          vert_max_of_bounded (fun m => C (some m)) a0 hbound w0 hw0
        refine ⟨some k, ?_, ?_⟩
        · funext x
          cases x with
          | none =>
              exact propext ⟨fun h => absurd h hinf,
                             fun h => absurd h (vert_not_leq_none_some k)⟩
          | some m =>
              refine propext ⟨fun h => vert_leq_of_le (hmax m h), fun h => ?_⟩
              cases lem (C (some m)) with
              | inl hm => exact hm
              | inr hm => exact absurd hk (hC.1 m k (vert_leq_some h) hm)
        · intro y' hy'
          cases y' with
          | none =>
              have : C none := cast (congrFun hy' none).symm vert_leq_none_none
              exact absurd this hinf
          | some b =>
              have hkb : k ≤ b := vert_leq_some (cast (congrFun hy' (some k)) hk)
              have hbC : C (some b) :=
                cast (congrFun hy' (some b)).symm (vert_leq_of_le (Nat.le_refl b))
              have hbk : b ≤ k := hmax b hbC
              have : b = k := by omega
              subst this
              rfl

  -- D3: the base is {↑n : n ∈ ℕ} — one basic open per compact element, and none
  -- for ∞, which is exactly K(ℕ^∞) = ℕ.
  basis     := vertUp
  basisOpen := vert_isOpen_up

  basisCpt := by
    intro n ι U hU hcov
    obtain ⟨i0, h0⟩ := hcov none trivial
    obtain ⟨j, hj⟩ := (hU i0).2.2 h0
    obtain ⟨p, f, hf⟩ := vert_finite_cover U n j (fun m hn _ => hcov (some m) hn)
    refine ⟨p + 1, fun q =>
      match q with
      | ⟨0, _⟩      => i0
      | ⟨q' + 1, hq⟩ => f ⟨q', by omega⟩, ?_⟩
    intro x hx
    cases x with
    | none => exact ⟨⟨0, by omega⟩, h0⟩
    | some m =>
        rcases Nat.lt_or_ge m j with hlt | hge
        · obtain ⟨jj, hjj⟩ := hf m hx hlt
          exact ⟨⟨jj.val + 1, by omega⟩, hjj⟩
        · exact ⟨⟨0, by omega⟩, (hU i0).1 j m hge hj⟩

  basisGen := by
    intro U hU x hx
    cases x with
    | none =>
        obtain ⟨a, ha⟩ := hU.2.2 hx
        refine ⟨a, trivial, ?_⟩
        intro y hy
        cases y with
        | none   => exact hU.2.1 a ha
        | some m => exact hU.1 a m hy ha
    | some a =>
        refine ⟨a, Nat.le_refl a, ?_⟩
        intro y hy
        cases y with
        | none   => exact hU.2.1 a hx
        | some m => exact hU.1 a m hy hx

  basisCap := by
    intro m n
    rcases Nat.le_total m n with h | h
    · refine ⟨n, ?_⟩
      intro x
      cases x with
      | none   => exact ⟨fun _ => trivial, fun _ => ⟨trivial, trivial⟩⟩
      | some q => exact ⟨fun hh => hh.2, fun hh => ⟨Nat.le_trans h hh, hh⟩⟩
    · refine ⟨m, ?_⟩
      intro x
      cases x with
      | none   => exact ⟨fun _ => trivial, fun _ => ⟨trivial, trivial⟩⟩
      | some q => exact ⟨fun hh => hh.1, fun hh => ⟨hh, Nat.le_trans h hh⟩⟩

  -- D4: 0 is the least element.
  bot   := some 0
  botAx := by
    intro U hU h x
    cases x with
    | none   => exact hU.2.1 0 h
    | some m => exact hU.1 0 m (Nat.zero_le m) h

/-- ∞ is above every finite point, and no finite point is above ∞: the chain
    really is ω + 1 and not ω. -/
theorem vert_le_top (a : Nat) : vertTop.leq (some a) none := vert_leq_some_none a

-- Axiom audit. `lem` again enters through D2 only, here via `vert_max_of_bounded`,
-- which decides membership at each step of the induction. Note `vert_finite_cover`
-- is classical-free in the sense that matters — no `lem` — but is not axiom-free:
-- `omega` discharges its arithmetic side conditions and reports `propext` and
-- `Quot.sound`. Layer O and the non-openness of {∞} are axiom-free outright.
#print axioms vertTop               -- does not depend on any axioms
#print axioms vert_top_not_isOpen   -- does not depend on any axioms
#print axioms vert_finite_cover     -- [propext, Quot.sound]
#print axioms vert_max_of_bounded   -- [lem, propext, Quot.sound]
#print axioms vertNat               -- [lem, propext, Quot.sound]


/- ----------------------------------------------------------------
   §3.5 — finite bounded-complete pointed posets

   Unlike §3.1–§3.4 this entry is a **class**, not an object, so the
   result is a function from such a poset to a `DInfinityFoundations`.
   `FinBCPoset D` packages exactly the catalogue's hypotheses: a
   partial order, a least element, finiteness (as a surjective
   enumeration bounded by `size`), and bounded completeness (every
   pair with an upper bound has a least one).

   The topology is the **Alexandrov** one — U is open iff it is an
   up-set. On a finite poset that *is* the Scott topology: every
   directed set is finite, hence has a greatest element, so
   inaccessibility by directed suprema is automatic and adds nothing.

   Three things the finite carrier changes:

   - Finiteness must be made to yield **maximal elements**, with no
     `Finset` machinery available. `fbc_exists_maximal` scans the
     enumeration once, carrying the invariant "no index examined so
     far lies strictly above the current element"; the invariant
     survives a replacement because the element only moves up.
   - Sobriety needs *maximum*, not maximal. Irreducibility is what
     upgrades it: a maximal m that is not a maximum splits C into
     ↓m ∩ C and the down-closure of the part of C not below m, both
     closed and both proper — the decomposition D2 forbids.
   - `basisCap` is where **bounded completeness is consumed**, and it
     is the only place. ↑a ∩ ↑b is ↑(a ⊔ b) when a and b are bounded
     and ∅ when they are not; without a *least* upper bound the
     intersection is a union of several basic opens and no single
     index works. §6.1 is exactly that failure.
   ---------------------------------------------------------------- -/

structure FinBCPoset (D : Type) where
  le          : D → D → Prop
  le_refl     : ∀ x, le x x
  le_trans    : ∀ x y z, le x y → le y z → le x z
  le_antisymm : ∀ x y, le x y → le y x → x = y
  bot         : D
  bot_le      : ∀ x, le bot x
  size        : Nat
  enum        : Nat → D
  enum_onto   : ∀ x, ∃ n, n < size ∧ enum n = x
  bounded_lub : ∀ x y, (∃ z, le x z ∧ le y z) →
                  ∃ u, le x u ∧ le y u ∧ ∀ v, le x v → le y v → le u v

variable {D : Type}

def fbcTop (P : FinBCPoset D) : TopologicalSpace D where
  isOpen U  := ∀ x y, P.le x y → U x → U y
  openEmpty := fun _ _ _ h => h
  openFull  := fun _ _ _ _ => trivial
  openUnion := by
    intro _ U hU x y hxy h
    obtain ⟨i, hi⟩ := h
    exact ⟨i, hU i x y hxy hi⟩
  openInter := by
    intro U W hU hW x y hxy h
    exact ⟨hU x y hxy h.1, hW x y hxy h.2⟩

/-- The principal up-set ↑a, the basic open of an algebraic domain. -/
def fbcUp (P : FinBCPoset D) (a : D) : D → Prop := fun z => P.le a z

theorem fbc_isOpen_up (P : FinBCPoset D) (a : D) : (fbcTop P).isOpen (fbcUp P a) :=
  fun _ _ hxy h => P.le_trans a _ _ h hxy

/-- The specialization order of the Alexandrov topology is the poset order. -/
theorem fbc_leq_of_le (P : FinBCPoset D) {x y : D} (h : P.le x y) : (fbcTop P).leq x y :=
  fun _ hU hx => hU x y h hx

theorem fbc_le_of_leq (P : FinBCPoset D) {x y : D} (h : (fbcTop P).leq x y) : P.le x y :=
  h (fbcUp P x) (fbc_isOpen_up P x) (P.le_refl x)

/-- A closed set is a down-set. -/
theorem fbc_down_closed (P : FinBCPoset D) {C : D → Prop}
    (hC : (fbcTop P).isClosed C) {x y : D} (hxy : P.le x y) (hy : C y) : C x := by
  cases lem (C x) with
  | inl h => exact h
  | inr h => exact absurd hy (hC x y hxy h)

/-- Finiteness yields maximal elements. One pass over the enumeration suffices:
    the current element only ever moves up, so an index rejected earlier cannot
    lie strictly above the final element. -/
theorem fbc_exists_maximal (P : FinBCPoset D) (S : D → Prop) :
    ∀ n, ∀ x, S x → ∃ m, S m ∧ P.le x m ∧
      ∀ j, j < n → S (P.enum j) → P.le m (P.enum j) → P.enum j = m := by
  intro n
  induction n with
  | zero =>
      intro x hx
      exact ⟨x, hx, P.le_refl x, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ n ih =>
      intro x hx
      obtain ⟨m, hm, hxm, hmax⟩ := ih x hx
      cases lem (S (P.enum n) ∧ P.le m (P.enum n) ∧ P.enum n ≠ m) with
      | inl hnew =>
          obtain ⟨hSn, hmn, hne⟩ := hnew
          refine ⟨P.enum n, hSn, P.le_trans x m _ hxm hmn, ?_⟩
          intro j hj hSj hlej
          rcases Nat.lt_or_ge j n with hjn | hjn
          · have hmj : P.le m (P.enum j) := P.le_trans m _ _ hmn hlej
            have hjm : P.enum j = m := hmax j hjn hSj hmj
            have : P.enum n = m := P.le_antisymm _ _ (hjm ▸ hlej) hmn
            exact absurd this hne
          · have : j = n := by omega
            subst this
            rfl
      | inr hnew =>
          refine ⟨m, hm, hxm, ?_⟩
          intro j hj hSj hlej
          rcases Nat.lt_or_ge j n with hjn | hjn
          · exact hmax j hjn hSj hlej
          · have hjn' : j = n := by omega
            subst hjn'
            cases lem (P.enum j = m) with
            | inl h => exact h
            | inr h => exact absurd ⟨hSj, hlej, h⟩ hnew

def fbcDomain (P : FinBCPoset D) : DInfinityFoundations D where
  toTopologicalSpace := fbcTop P

  -- D1: ↑x and ↑y separate x from y unless each lies below the other.
  t0 := by
    intro x y h
    exact P.le_antisymm x y
      (h (fbcUp P x) (fbc_isOpen_up P x) |>.mp (P.le_refl x))
      (h (fbcUp P y) (fbc_isOpen_up P y) |>.mpr (P.le_refl y))

  -- D2: an inhabited closed set has a maximal element by finiteness, and
  -- irreducibility upgrades it to a maximum, which is the generic point.
  sober := by
    intro C hC hirr
    obtain ⟨w, hw⟩ := hirr.1
    obtain ⟨m, hm, _, hmax⟩ := fbc_exists_maximal P C P.size w hw
    -- `hmax` is maximality over the enumeration; `enum_onto` makes it maximality.
    have hmaximal : ∀ z, C z → P.le m z → z = m := by
      intro z hz hmz
      obtain ⟨j, hj, hje⟩ := P.enum_onto z
      exact hje ▸ hmax j hj (hje ▸ hz) (hje ▸ hmz)
    -- irreducibility: m is not merely maximal but a maximum
    have hmaximum : ∀ z, C z → P.le z m := by
      intro z hz
      cases lem (P.le z m) with
      | inl h => exact h
      | inr h =>
          refine absurd ⟨fun q => C q ∧ P.le q m,
                         fun q => ∃ w', C w' ∧ ¬ P.le w' m ∧ P.le q w',
                         ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hirr.2
          · intro a b hab hna hb
            exact hna ⟨fbc_down_closed P hC hab hb.1, P.le_trans a b m hab hb.2⟩
          · intro a b hab hna hb
            obtain ⟨w', hw', hnw', hbw'⟩ := hb
            exact hna ⟨w', hw', hnw', P.le_trans a b w' hab hbw'⟩
          · exact fun q hq => hq.1
          · intro q hq
            obtain ⟨w', hw', _, hqw'⟩ := hq
            exact fbc_down_closed P hC hqw' hw'
          · intro q hq
            cases lem (P.le q m) with
            | inl hqm => exact Or.inl ⟨hq, hqm⟩
            | inr hqm => exact Or.inr ⟨q, hq, hqm, P.le_refl q⟩
          · exact ⟨z, hz, fun hc => h hc.2⟩
          · refine ⟨m, hm, ?_⟩
            intro hc
            obtain ⟨w', hw', hnw', hmw'⟩ := hc
            exact absurd (hmaximal w' hw' hmw' ▸ P.le_refl m) hnw'
    refine ⟨m, ?_, ?_⟩
    · funext z
      exact propext ⟨fun hz => fbc_leq_of_le P (hmaximum z hz),
                     fun hz => fbc_down_closed P hC (fbc_le_of_leq P hz) hm⟩
    · intro y' hy'
      have hy'C : C y' := cast (congrFun hy' y').symm (fbc_leq_of_le P (P.le_refl y'))
      have h1 : P.le y' m := hmaximum y' hy'C
      have h2 : P.le m y' := fbc_le_of_leq P (cast (congrFun hy' m) hm)
      exact P.le_antisymm y' m h1 h2

  -- D3: one basic open ↑(enum n) per element, plus ∅ at index 0.
  basis := fun n =>
    match n with
    | 0     => fun _ => False
    | n + 1 => fbcUp P (P.enum n)

  basisOpen := by
    intro n
    rcases n with _ | n
    · exact fun _ _ _ h => h
    · exact fbc_isOpen_up P (P.enum n)

  -- Every up-set is compact in the Alexandrov topology: whichever open covers
  -- the generator already contains the whole up-set.
  basisCpt := by
    intro n ι U hU hcov
    rcases n with _ | n
    · exact ⟨0, Fin.elim0, fun _ hx => hx.elim⟩
    · obtain ⟨i, hi⟩ := hcov (P.enum n) (P.le_refl (P.enum n))
      exact ⟨1, fun _ => i, fun x hx => ⟨0, hU i (P.enum n) x hx hi⟩⟩

  basisGen := by
    intro U hU x hx
    obtain ⟨n, _, hne⟩ := P.enum_onto x
    refine ⟨n + 1, ?_, ?_⟩
    · exact hne ▸ P.le_refl x
    · intro y hy
      exact hU (P.enum n) y hy (hne ▸ hx)

  -- The only field that consumes bounded completeness.
  basisCap := by
    intro m n
    rcases m with _ | m
    · exact ⟨0, fun _ => ⟨fun h => h.1, fun h => h.elim⟩⟩
    · rcases n with _ | n
      · exact ⟨0, fun _ => ⟨fun h => h.2, fun h => h.elim⟩⟩
      · cases lem (∃ z, P.le (P.enum m) z ∧ P.le (P.enum n) z) with
        | inl hbdd =>
            obtain ⟨u, hu1, hu2, hulub⟩ := P.bounded_lub _ _ hbdd
            obtain ⟨p, _, hpe⟩ := P.enum_onto u
            subst hpe
            refine ⟨p + 1, fun x => ⟨fun h => hulub x h.1 h.2, fun h => ?_⟩⟩
            exact ⟨P.le_trans _ _ x hu1 h, P.le_trans _ _ x hu2 h⟩
        | inr hbdd =>
            exact ⟨0, fun x => ⟨fun h => hbdd ⟨x, h.1, h.2⟩, fun h => h.elim⟩⟩

  -- D4: the least element of the poset.
  bot   := P.bot
  botAx := fun _ hU h x => hU P.bot x (P.bot_le x) h

/- A witness that the hypotheses are satisfiable, so the theorem above is not
   vacuous: `Bool` under ⊥ = false ⊑ true = ⊤, which is 𝕊 again — reached this
   time from the order rather than by giving the topology directly. -/
def boolFinBC : FinBCPoset Bool where
  le x y      := x = true → y = true
  le_refl _   := fun h => h
  le_trans _ _ _ h1 h2 := fun h => h2 (h1 h)
  le_antisymm := by
    intro x y h1 h2
    cases x <;> cases y
    · rfl
    · exact absurd (h2 rfl) (fun hh => Bool.noConfusion hh)
    · exact absurd (h1 rfl) (fun hh => Bool.noConfusion hh)
    · rfl
  bot         := false
  bot_le _    := fun h => Bool.noConfusion h
  size        := 2
  enum n      := match n with
                 | 0 => false
                 | _ => true
  enum_onto   := by
    intro x
    cases x
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, by omega, rfl⟩
  bounded_lub := by
    intro x y _
    cases x <;> cases y
    · exact ⟨false, fun h => h, fun h => h, fun _ h _ => h⟩
    · exact ⟨true, fun h => Bool.noConfusion h, fun h => h, fun _ _ h => h⟩
    · exact ⟨true, fun h => h, fun h => Bool.noConfusion h, fun _ h _ => h⟩
    · exact ⟨true, fun h => h, fun h => h, fun _ h _ => h⟩

def sierpFromPoset : DInfinityFoundations Bool := fbcDomain boolFinBC

-- Axiom audit. `lem` is used three times over: to make a closed set a down-set,
-- to decide membership while scanning for a maximal element, and to decide
-- whether a pair of basis generators is bounded. Layer O is still axiom-free.
#print axioms fbcTop              -- does not depend on any axioms
#print axioms fbc_isOpen_up       -- does not depend on any axioms
#print axioms fbc_exists_maximal  -- [lem, propext, Quot.sound]
#print axioms fbcDomain           -- [lem, propext, Quot.sound]
#print axioms sierpFromPoset      -- [lem, propext, Quot.sound]


/- ----------------------------------------------------------------
   §3.6 — the powerset 𝒫(X) under ⊆, for X = ℕ

   Carrier `Nat → Prop`, ordered by inclusion. This is the first
   uncountable carrier and the first with a genuinely infinite basis,
   and both facts land on D3.

   K(𝒫(ℕ)) is the finite subsets, so openness is stated as an up-set
   condition plus "every member has a finite sub-approximation whose
   up-set stays inside U":

       isOpen U := (A ⊆ B → U A → U B) ∧ (U A → ∃ l, l ⊆ A ∧ ↑l ⊆ U)

   with finite subsets represented as `List Nat`. The second conjunct
   is inaccessibility by directed unions and the statement that the
   ↑l generate, in one clause.

   `basis` is indexed by `Nat`, so the finite subsets have to be
   *enumerated*. They are, as bit masks: `psetBits k` is the list of
   set bits of k, and `pset_exists_mask` produces a mask for any list.
   That is why this entry, alone among the positive ones, reaches into
   `Nat.testBit` — the alternative, a hand-rolled pairing function,
   would cost more and prove less.

   D2 is the deepest sobriety proof in the file. The generic point of
   an irreducible closed C is ⋃C, and showing ⋃C ∈ C needs three
   steps: C is a down-set; any two finite approximations drawn from C
   have a common extension *in* C (this is where irreducibility is
   used, via the same two-closed-sets decomposition as §3.5); and
   hence, by induction on the list, every finite approximation of ⋃C
   is already below a single member of C.
   ---------------------------------------------------------------- -/

def psetUpList (l : List Nat) : (Nat → Prop) → Prop := fun A => ∀ n, n ∈ l → A n

def psetTop : TopologicalSpace (Nat → Prop) where
  isOpen U :=
    (∀ A B, (∀ n, A n → B n) → U A → U B) ∧
    (∀ A, U A → ∃ l : List Nat, (∀ n, n ∈ l → A n) ∧ ∀ B, (∀ n, n ∈ l → B n) → U B)
  openEmpty := ⟨fun _ _ _ h => h, fun _ h => h.elim⟩
  openFull  := ⟨fun _ _ _ _ => trivial,
                fun _ _ => ⟨[], (fun _ hn => by cases hn), fun _ _ => trivial⟩⟩
  openUnion := by
    intro _ U hU
    refine ⟨?_, ?_⟩
    · intro A B hAB h
      obtain ⟨i, hi⟩ := h
      exact ⟨i, (hU i).1 A B hAB hi⟩
    · intro A h
      obtain ⟨i, hi⟩ := h
      obtain ⟨l, hl, hup⟩ := (hU i).2 A hi
      exact ⟨l, hl, fun B hB => ⟨i, hup B hB⟩⟩
  openInter := by
    intro U W hU hW
    refine ⟨?_, ?_⟩
    · intro A B hAB h
      exact ⟨hU.1 A B hAB h.1, hW.1 A B hAB h.2⟩
    · intro A h
      obtain ⟨l1, hl1, hup1⟩ := hU.2 A h.1
      obtain ⟨l2, hl2, hup2⟩ := hW.2 A h.2
      refine ⟨l1 ++ l2, ?_, ?_⟩
      · intro n hn
        rcases List.mem_append.mp hn with h' | h'
        · exact hl1 n h'
        · exact hl2 n h'
      · intro B hB
        exact ⟨hup1 B (fun n hn => hB n (List.mem_append.mpr (Or.inl hn))),
               hup2 B (fun n hn => hB n (List.mem_append.mpr (Or.inr hn)))⟩

theorem pset_isOpen_upList (l : List Nat) : psetTop.isOpen (psetUpList l) :=
  ⟨fun _ _ hAB h n hn => hAB n (h n hn), fun _ h => ⟨l, h, fun _ hB => hB⟩⟩

theorem pset_single {A : Nat → Prop} {n : Nat} (hn : A n) : psetUpList [n] A := by
  intro m hm
  cases hm with
  | head => exact hn
  | tail _ h => cases h

/-- Set extensionality, via `funext` and `propext`. -/
theorem pset_ext {A B : Nat → Prop} (h1 : ∀ n, A n → B n) (h2 : ∀ n, B n → A n) : A = B := by
  funext n
  exact propext ⟨h1 n, h2 n⟩

/-- The specialization order is inclusion. -/
theorem pset_leq_of_sub {A B : Nat → Prop} (h : ∀ n, A n → B n) : psetTop.leq A B :=
  fun _ hU hA => hU.1 A B h hA

theorem pset_sub_of_leq {A B : Nat → Prop} (h : psetTop.leq A B) (n : Nat) (hn : A n) : B n :=
  h (psetUpList [n]) (pset_isOpen_upList [n]) (pset_single hn) n (List.Mem.head _)

theorem pset_down_closed {C : (Nat → Prop) → Prop} (hC : psetTop.isClosed C)
    {A B : Nat → Prop} (hAB : ∀ n, A n → B n) (hB : C B) : C A := by
  cases lem (C A) with
  | inl h => exact h
  | inr h => exact absurd hB (hC.1 A B hAB h)

/- The finite subsets of ℕ enumerated as bit masks. Every set bit of k is below
   k+1 — `2 ^ i ≤ k` and `i < 2 ^ i` — so the list of set bits is a filter of
   `List.range (k+1)`, with no recursion needed. -/

def psetBits (k : Nat) : List Nat := (List.range (k + 1)).filter (fun i => k.testBit i)

theorem pset_mem_bits {k n : Nat} : n ∈ psetBits k ↔ k.testBit n = true := by
  constructor
  · intro h
    exact (List.mem_filter.mp h).2
  · intro h
    refine List.mem_filter.mpr ⟨List.mem_range.mpr ?_, h⟩
    have h2 : 2 ^ n ≤ k := Nat.ge_two_pow_of_testBit h
    have h3 : n < 2 ^ n := Nat.lt_two_pow_self
    omega

theorem pset_exists_mask (l : List Nat) : ∃ k : Nat, ∀ n, k.testBit n = true ↔ n ∈ l := by
  induction l with
  | nil =>
      refine ⟨0, fun n => ⟨fun h => ?_, fun h => ?_⟩⟩
      · rw [Nat.zero_testBit] at h
        exact Bool.noConfusion h
      · cases h
  | cons a t ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨k ||| 2 ^ a, fun n => ?_⟩
      rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_iff,
          hk n, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl h.symm
      · rintro (h | h)
        · exact Or.inr h.symm
        · exact Or.inl h

/-- `C ∩ ↑l`-complement, closed. Used to feed D2's `irreducible` hypothesis. -/
theorem pset_isClosed_and_not_up {C : (Nat → Prop) → Prop} (hC : psetTop.isClosed C)
    (l : List Nat) : psetTop.isClosed (fun z => C z ∧ ¬ psetUpList l z) := by
  constructor
  · intro A B hAB hA hB
    exact hA ⟨pset_down_closed hC hAB hB.1,
              fun hup => hB.2 ((pset_isOpen_upList l).1 A B hAB hup)⟩
  · intro A hA
    cases lem (C A) with
    | inl hc =>
        have hup1 : psetUpList l A := by
          cases lem (psetUpList l A) with
          | inl h => exact h
          | inr h => exact absurd ⟨hc, h⟩ hA
        exact ⟨l, hup1, fun _ hB hcb => hcb.2 hB⟩
    | inr hnc =>
        obtain ⟨l', hl', hup⟩ := hC.2 A hnc
        exact ⟨l', hl', fun B hB hcb => hup B hB hcb.1⟩

/-- Irreducibility, in the form actually needed: two finite approximations drawn
    from C have a common extension **inside** C. -/
theorem pset_common_extension {C : (Nat → Prop) → Prop} (hC : psetTop.isClosed C)
    (hirr : psetTop.irreducible C) {A B : Nat → Prop} (hA : C A) (hB : C B)
    (l1 l2 : List Nat) (h1 : psetUpList l1 A) (h2 : psetUpList l2 B) :
    ∃ z, C z ∧ psetUpList l1 z ∧ psetUpList l2 z := by
  cases lem (∃ z, C z ∧ psetUpList l1 z ∧ psetUpList l2 z) with
  | inl h => exact h
  | inr h =>
      refine absurd ⟨fun z => C z ∧ ¬ psetUpList l1 z, fun z => C z ∧ ¬ psetUpList l2 z,
                     pset_isClosed_and_not_up hC l1, pset_isClosed_and_not_up hC l2,
                     fun _ hq => hq.1, fun _ hq => hq.1, ?_,
                     ⟨A, hA, fun hc => hc.2 h1⟩, ⟨B, hB, fun hc => hc.2 h2⟩⟩ hirr.2
      intro q hq
      cases lem (psetUpList l1 q) with
      | inr hq1 => exact Or.inl ⟨hq, hq1⟩
      | inl hq1 =>
          cases lem (psetUpList l2 q) with
          | inr hq2 => exact Or.inr ⟨hq, hq2⟩
          | inl hq2 => exact absurd ⟨q, hq, hq1, hq2⟩ h

/-- Every finite approximation drawn from C lies below a single member of C. -/
theorem pset_member_covering {C : (Nat → Prop) → Prop} (hC : psetTop.isClosed C)
    (hirr : psetTop.irreducible C) {w : Nat → Prop} (hw : C w) :
    ∀ l : List Nat, (∀ n, n ∈ l → ∃ A, C A ∧ A n) → ∃ z, C z ∧ psetUpList l z := by
  intro l
  induction l with
  | nil => intro _; exact ⟨w, hw, (fun _ hn => by cases hn)⟩
  | cons a t ih =>
      intro hall
      obtain ⟨z1, hz1, hup1⟩ := ih (fun n hn => hall n (List.Mem.tail _ hn))
      obtain ⟨A, hA, hAa⟩ := hall a (List.Mem.head _)
      obtain ⟨z, hz, hzt, hza⟩ :=
        pset_common_extension hC hirr hz1 hA t [a] hup1 (pset_single hAa)
      refine ⟨z, hz, ?_⟩
      intro n hn
      cases hn with
      | head       => exact hza a (List.Mem.head _)
      | tail _ hn' => exact hzt n hn'

def psetNat : DInfinityFoundations (Nat → Prop) where
  toTopologicalSpace := psetTop

  -- D1: the singleton up-set ↑{n} detects membership of n, for every n.
  t0 := by
    intro A B h
    refine pset_ext ?_ ?_
    · intro n hn
      exact (h (psetUpList [n]) (pset_isOpen_upList [n])).mp (pset_single hn) n (List.Mem.head _)
    · intro n hn
      exact (h (psetUpList [n]) (pset_isOpen_upList [n])).mpr (pset_single hn) n (List.Mem.head _)

  -- D2: the generic point of an irreducible closed C is ⋃C.
  sober := by
    intro C hC hirr
    obtain ⟨w, hw⟩ := hirr.1
    have hWC : C (fun n => ∃ A, C A ∧ A n) := by
      cases lem (C (fun n => ∃ A, C A ∧ A n)) with
      | inl h => exact h
      | inr h =>
          obtain ⟨l, hl, hup⟩ := hC.2 _ h
          obtain ⟨z, hz, hzl⟩ := pset_member_covering hC hirr hw l hl
          exact absurd hz (hup z hzl)
    refine ⟨fun n => ∃ A, C A ∧ A n, ?_, ?_⟩
    · funext A
      refine propext ⟨fun hA => pset_leq_of_sub (fun n hn => ⟨A, hA, hn⟩), fun hA => ?_⟩
      exact pset_down_closed hC (fun n hn => pset_sub_of_leq hA n hn) hWC
    · intro y' hy'
      have hy'C : C y' := cast (congrFun hy' y').symm (pset_leq_of_sub (fun _ h => h))
      refine pset_ext (fun n hn => ⟨y', hy'C, hn⟩) ?_
      exact fun n hn => pset_sub_of_leq (cast (congrFun hy' _) hWC) n hn

  -- D3: one basic open per finite subset, the finite subsets enumerated as the
  -- bit masks of a natural number.
  basis     := fun k => psetUpList (psetBits k)
  basisOpen := fun k => pset_isOpen_upList (psetBits k)

  -- ↑l is compact: the open covering the generating set l already contains all
  -- of ↑l, since opens are up-sets. One member of the cover suffices.
  basisCpt := by
    intro k ι U hU hcov
    obtain ⟨i, hi⟩ := hcov (fun n => n ∈ psetBits k) (fun _ hn => hn)
    exact ⟨1, fun _ => i, fun B hB => ⟨0, (hU i).1 _ B (fun n hn => hB n hn) hi⟩⟩

  basisGen := by
    intro U hU A hA
    obtain ⟨l, hl, hup⟩ := hU.2 A hA
    obtain ⟨k, hk⟩ := pset_exists_mask l
    refine ⟨k, ?_, ?_⟩
    · exact fun n hn => hl n ((hk n).mp (pset_mem_bits.mp hn))
    · exact fun B hB => hup B (fun n hn => hB n (pset_mem_bits.mpr ((hk n).mpr hn)))

  -- The base is closed under intersection because the finite subsets are: the
  -- mask of the union is the bitwise or.
  basisCap := by
    intro k1 k2
    refine ⟨k1 ||| k2, fun B => ⟨fun h n hn => ?_, fun h => ⟨fun n hn => ?_, fun n hn => ?_⟩⟩⟩
    · have hb : (k1 ||| k2).testBit n = true := pset_mem_bits.mp hn
      rw [Nat.testBit_or, Bool.or_eq_true] at hb
      cases hb with
      | inl hb1 => exact h.1 n (pset_mem_bits.mpr hb1)
      | inr hb2 => exact h.2 n (pset_mem_bits.mpr hb2)
    · refine h n (pset_mem_bits.mpr ?_)
      rw [Nat.testBit_or, Bool.or_eq_true]
      exact Or.inl (pset_mem_bits.mp hn)
    · refine h n (pset_mem_bits.mpr ?_)
      rw [Nat.testBit_or, Bool.or_eq_true]
      exact Or.inr (pset_mem_bits.mp hn)

  -- D4: the empty set.
  bot   := fun _ => False
  botAx := fun _ hU h A => hU.1 _ A (fun _ hn => hn.elim) h

/-- ∅ ⊑ every set, and 𝒫(ℕ) is a complete lattice, unlike 𝔹⊥. -/
theorem pset_bot_le (A : Nat → Prop) : psetTop.leq (fun _ => False) A :=
  pset_leq_of_sub (fun _ h => h.elim)

-- Axiom audit. Same three axioms, but note where they enter: `lem` is used in
-- three separate places in D2 alone — down-closure, the common-extension
-- argument, and the decision whether ⋃C is already a member.
#print axioms psetTop               -- [propext]
#print axioms pset_exists_mask      -- [propext, Quot.sound]
#print axioms pset_common_extension -- [lem, propext]
#print axioms psetNat               -- [lem, propext, Quot.sound]


/- ----------------------------------------------------------------
   §6.1 — bounded completeness fails: two minimal upper bounds

   The first **non**-example. Everything before this inhabited
   `DInfinityFoundations`; here the content is a refutation, and the
   two results below are the two faces of the same failure:

   - order-theoretic: {a, b} has upper bounds c and d and no least
     one, so the poset is not bounded complete;
   - topological: ↑a ∩ ↑b = {c, d} is not ↑k for any k, so the
     compact-open base is not closed under intersection and `basisCap`
     (D3) cannot be discharged.

   §4 predicted exactly this — `basisCap` is the topological form of
   bounded completeness — and §3.5's `fbcDomain` consumes the
   hypothesis at exactly that field. This poset satisfies every other
   `FinBCPoset` field; `bounded_lub` is the one it fails.

   Note on the count: the catalogue says "six elements", but the
   structure it describes — ⊥, a, b, c, d — has five, and its own
   claim ↑a ∩ ↑b = {c, d} is the five-element reading. Formalized as
   five.
   ---------------------------------------------------------------- -/

inductive Six where
  | bot | a | b | c | d
  deriving DecidableEq

/-- ⊥ ⊑ a, b ⊑ c, d, with a ∦ b and c ∦ d. -/
def sixLe : Six → Six → Bool
  | .bot, _  => true
  | .a,   .a => true
  | .a,   .c => true
  | .a,   .d => true
  | .b,   .b => true
  | .b,   .c => true
  | .b,   .d => true
  | .c,   .c => true
  | .d,   .d => true
  | _,    _  => false

def sixUp (x : Six) : Six → Prop := fun z => sixLe x z = true

/-- Bounded completeness fails: a and b are bounded, with no least upper bound. -/
theorem six_no_lub :
    ¬ ∃ u, sixLe .a u = true ∧ sixLe .b u = true ∧
        ∀ v, sixLe .a v = true → sixLe .b v = true → sixLe u v = true := by
  rintro ⟨u, hau, hbu, hlub⟩
  cases u with
  | bot => exact Bool.noConfusion hau
  | a   => exact Bool.noConfusion hbu
  | b   => exact Bool.noConfusion hau
  | c   => exact Bool.noConfusion (hlub .d rfl rfl)
  | d   => exact Bool.noConfusion (hlub .c rfl rfl)

/-- The pair *is* bounded — c and d are both upper bounds. What fails is leastness. -/
theorem six_bounded : sixLe .a .c = true ∧ sixLe .b .c = true := ⟨rfl, rfl⟩

/-- D3 fails topologically: ↑a ∩ ↑b is not a principal up-set. -/
theorem six_basisCap_fails :
    ¬ ∃ k, ∀ z, (sixUp .a z ∧ sixUp .b z) ↔ sixUp k z := by
  rintro ⟨k, hk⟩
  have hc : sixUp k .c := (hk .c).mp ⟨rfl, rfl⟩
  have hd : sixUp k .d := (hk .d).mp ⟨rfl, rfl⟩
  cases k with
  | bot => exact Bool.noConfusion ((hk .a).mpr rfl).2
  | a   => exact Bool.noConfusion ((hk .a).mpr rfl).2
  | b   => exact Bool.noConfusion ((hk .b).mpr rfl).1
  | c   => exact Bool.noConfusion hd
  | d   => exact Bool.noConfusion hc


/- ----------------------------------------------------------------
   §6.2 — directed completeness fails: ℕ under ≤

   ℕ is directed — any two naturals have an upper bound — and has no
   upper bound at all, so it is not a dcpo. Adjoining ∞ repairs it and
   gives §3.4's `vertNat`, which is the point of the pair: "cpo" is a
   completeness requirement, not a size requirement.
   ---------------------------------------------------------------- -/

theorem nat_directed (n m : Nat) : ∃ k, n ≤ k ∧ m ≤ k := ⟨n + m, by omega, by omega⟩

theorem nat_not_dcpo : ¬ ∃ m : Nat, ∀ n : Nat, n ≤ m := by
  rintro ⟨m, hm⟩
  exact absurd (hm (m + 1)) (by omega)

-- Axiom audit for the two non-examples. Both are refutations of finite or
-- arithmetic facts, so neither needs `lem`: §6.1 decides by case analysis on a
-- five-constructor type, §6.2 by `omega`.
#print axioms six_no_lub          -- [propext]
#print axioms six_basisCap_fails  -- [propext]
#print axioms nat_not_dcpo        -- [propext, Quot.sound]


/- ----------------------------------------------------------------
   §3.7 — partial functions ℕ ⇀ ℕ, ordered by graph inclusion

   A partial function is carried as its **graph together with a proof
   of single-valuedness** — a subtype of `Nat → Nat → Prop` — not as
   `Nat → Option Nat`. The reason is D2. The generic point of an
   irreducible closed C is the union of C's graphs, and reading a
   value out of `Option` at each argument would require *choosing* the
   value some member assigns, which is countable choice. With the
   graph encoding the union is a relation defined outright, and
   single-valuedness is *proved* from the common-extension lemma. No
   choice is used, and `lem` remains the only classical principle.

   The finite approximations are lists of pairs, so the basis needs an
   enumeration of finite sets of pairs. `pairDecode` supplies the
   missing ingredient — a surjection ℕ ↠ ℕ × ℕ, the Cantor walk

       (0,0), (1,0), (0,1), (2,0), (1,1), (0,2), …

   written as a structural recursion, so surjectivity needs only
   ordinary induction (outer on the antidiagonal, inner on the second
   coordinate) rather than a closed form and its inverse.
   ---------------------------------------------------------------- -/

def pairDecode : Nat → Nat × Nat
  | 0     => (0, 0)
  | k + 1 =>
    match pairDecode k with
    | (0,     v) => (v + 1, 0)
    | (n + 1, v) => (n, v + 1)

theorem pairDecode_hits : ∀ s v n, n + v = s → ∃ k, pairDecode k = (n, v) := by
  intro s
  induction s with
  | zero =>
      intro v n hn
      have hv : v = 0 := by omega
      have hnn : n = 0 := by omega
      subst hv
      subst hnn
      exact ⟨0, rfl⟩
  | succ s ih =>
      intro v
      induction v with
      | zero =>
          intro n hn
          have hns : n = s + 1 := by omega
          subst hns
          obtain ⟨k, hk⟩ := ih s 0 (by omega)
          exact ⟨k + 1, by simp [pairDecode, hk]⟩
      | succ w ihv =>
          intro n hn
          obtain ⟨k, hk⟩ := ihv (n + 1) (by omega)
          exact ⟨k + 1, by simp [pairDecode, hk]⟩

/-- A partial function ℕ ⇀ ℕ: a graph that is single-valued. -/
def PFun : Type := {G : Nat → Nat → Prop // ∀ n v w, G n v → G n w → v = w}

def pfunUpList (l : List (Nat × Nat)) : PFun → Prop := fun f => ∀ p, p ∈ l → f.val p.1 p.2

def pfunTop : TopologicalSpace PFun where
  isOpen U :=
    (∀ f g : PFun, (∀ n v, f.val n v → g.val n v) → U f → U g) ∧
    (∀ f, U f → ∃ l : List (Nat × Nat), (∀ p, p ∈ l → f.val p.1 p.2) ∧
       ∀ g : PFun, (∀ p, p ∈ l → g.val p.1 p.2) → U g)
  openEmpty := ⟨fun _ _ _ h => h, fun _ h => h.elim⟩
  openFull  := ⟨fun _ _ _ _ => trivial,
                fun _ _ => ⟨[], (fun _ hp => by cases hp), fun _ _ => trivial⟩⟩
  openUnion := by
    intro _ U hU
    refine ⟨?_, ?_⟩
    · intro f g hfg h
      obtain ⟨i, hi⟩ := h
      exact ⟨i, (hU i).1 f g hfg hi⟩
    · intro f h
      obtain ⟨i, hi⟩ := h
      obtain ⟨l, hl, hup⟩ := (hU i).2 f hi
      exact ⟨l, hl, fun g hg => ⟨i, hup g hg⟩⟩
  openInter := by
    intro U W hU hW
    refine ⟨?_, ?_⟩
    · intro f g hfg h
      exact ⟨hU.1 f g hfg h.1, hW.1 f g hfg h.2⟩
    · intro f h
      obtain ⟨l1, hl1, hup1⟩ := hU.2 f h.1
      obtain ⟨l2, hl2, hup2⟩ := hW.2 f h.2
      refine ⟨l1 ++ l2, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.mp hp with h' | h'
        · exact hl1 p h'
        · exact hl2 p h'
      · intro g hg
        exact ⟨hup1 g (fun p hp => hg p (List.mem_append.mpr (Or.inl hp))),
               hup2 g (fun p hp => hg p (List.mem_append.mpr (Or.inr hp)))⟩

theorem pfun_isOpen_upList (l : List (Nat × Nat)) : pfunTop.isOpen (pfunUpList l) :=
  ⟨fun _ _ hfg h p hp => hfg p.1 p.2 (h p hp), fun _ h => ⟨l, h, fun _ hg => hg⟩⟩

theorem pfun_single {f : PFun} {n v : Nat} (h : f.val n v) : pfunUpList [(n, v)] f := by
  intro p hp
  cases hp with
  | head        => exact h
  | tail _ hh   => cases hh

theorem pfun_leq_of_sub {f g : PFun} (h : ∀ n v, f.val n v → g.val n v) : pfunTop.leq f g :=
  fun _ hU hf => hU.1 f g h hf

theorem pfun_sub_of_leq {f g : PFun} (h : pfunTop.leq f g) (n v : Nat) (hv : f.val n v) :
    g.val n v :=
  h (pfunUpList [(n, v)]) (pfun_isOpen_upList [(n, v)]) (pfun_single hv) (n, v) (List.Mem.head _)

theorem pfun_down_closed {C : PFun → Prop} (hC : pfunTop.isClosed C)
    {f g : PFun} (hfg : ∀ n v, f.val n v → g.val n v) (hg : C g) : C f := by
  cases lem (C f) with
  | inl h => exact h
  | inr h => exact absurd hg (hC.1 f g hfg h)

theorem pfun_isClosed_and_not_up {C : PFun → Prop} (hC : pfunTop.isClosed C)
    (l : List (Nat × Nat)) : pfunTop.isClosed (fun z => C z ∧ ¬ pfunUpList l z) := by
  constructor
  · intro f g hfg hf hg
    exact hf ⟨pfun_down_closed hC hfg hg.1,
              fun hup => hg.2 ((pfun_isOpen_upList l).1 f g hfg hup)⟩
  · intro f hf
    cases lem (C f) with
    | inl hc =>
        have hup1 : pfunUpList l f := by
          cases lem (pfunUpList l f) with
          | inl h => exact h
          | inr h => exact absurd ⟨hc, h⟩ hf
        exact ⟨l, hup1, fun _ hg hcg => hcg.2 hg⟩
    | inr hnc =>
        obtain ⟨l', hl', hup⟩ := hC.2 f hnc
        exact ⟨l', hl', fun g hg hcg => hup g hg hcg.1⟩

theorem pfun_common_extension {C : PFun → Prop} (hC : pfunTop.isClosed C)
    (hirr : pfunTop.irreducible C) {f g : PFun} (hf : C f) (hg : C g)
    (l1 l2 : List (Nat × Nat)) (h1 : pfunUpList l1 f) (h2 : pfunUpList l2 g) :
    ∃ z, C z ∧ pfunUpList l1 z ∧ pfunUpList l2 z := by
  cases lem (∃ z, C z ∧ pfunUpList l1 z ∧ pfunUpList l2 z) with
  | inl h => exact h
  | inr h =>
      refine absurd ⟨fun z => C z ∧ ¬ pfunUpList l1 z, fun z => C z ∧ ¬ pfunUpList l2 z,
                     pfun_isClosed_and_not_up hC l1, pfun_isClosed_and_not_up hC l2,
                     fun _ hq => hq.1, fun _ hq => hq.1, ?_,
                     ⟨f, hf, fun hc => hc.2 h1⟩, ⟨g, hg, fun hc => hc.2 h2⟩⟩ hirr.2
      intro q hq
      cases lem (pfunUpList l1 q) with
      | inr hq1 => exact Or.inl ⟨hq, hq1⟩
      | inl hq1 =>
          cases lem (pfunUpList l2 q) with
          | inr hq2 => exact Or.inr ⟨hq, hq2⟩
          | inl hq2 => exact absurd ⟨q, hq, hq1, hq2⟩ h

theorem pfun_member_covering {C : PFun → Prop} (hC : pfunTop.isClosed C)
    (hirr : pfunTop.irreducible C) {w : PFun} (hw : C w) :
    ∀ l : List (Nat × Nat), (∀ p, p ∈ l → ∃ f, C f ∧ f.val p.1 p.2) →
      ∃ z, C z ∧ pfunUpList l z := by
  intro l
  induction l with
  | nil => intro _; exact ⟨w, hw, (fun _ hp => by cases hp)⟩
  | cons a t ih =>
      intro hall
      obtain ⟨z1, hz1, hup1⟩ := ih (fun p hp => hall p (List.Mem.tail _ hp))
      obtain ⟨f, hf, hfa⟩ := hall a (List.Mem.head _)
      obtain ⟨z, hz, hzt, hza⟩ :=
        pfun_common_extension hC hirr hz1 hf t [a] hup1
          (by intro p hp; cases hp with
              | head      => exact hfa
              | tail _ hh => cases hh)
      refine ⟨z, hz, ?_⟩
      intro p hp
      cases hp with
      | head       => exact hza a (List.Mem.head _)
      | tail _ hp' => exact hzt p hp'

/-- Every finite set of pairs is the decoding of a finite set of codes. -/
theorem pfun_exists_codes (l : List (Nat × Nat)) :
    ∃ codes : List Nat, ∀ p, (∃ i, i ∈ codes ∧ pairDecode i = p) ↔ p ∈ l := by
  induction l with
  | nil =>
      refine ⟨[], fun p => ⟨?_, ?_⟩⟩
      · rintro ⟨i, hi, _⟩
        cases hi
      · intro h
        cases h
  | cons a t ih =>
      obtain ⟨codes, hcodes⟩ := ih
      obtain ⟨k, hk⟩ := pairDecode_hits (a.1 + a.2) a.2 a.1 rfl
      refine ⟨k :: codes, fun p => ⟨?_, ?_⟩⟩
      · rintro ⟨i, hi, hdec⟩
        cases hi with
        | head =>
            have hpa : p = a := by rw [← hdec, hk]
            subst hpa
            exact List.Mem.head _
        | tail _ hi' => exact List.Mem.tail _ ((hcodes p).mp ⟨i, hi', hdec⟩)
      · intro hp
        cases hp with
        | head => exact ⟨k, List.Mem.head _, hk⟩
        | tail _ hp' =>
            obtain ⟨i, hi, hdec⟩ := (hcodes p).mpr hp'
            exact ⟨i, List.Mem.tail _ hi, hdec⟩

/-- The basic open generated by the finite set of pairs coded by k's bits. -/
def pfunBasis (k : Nat) : PFun → Prop :=
  fun f => ∀ i, i ∈ psetBits k → f.val (pairDecode i).1 (pairDecode i).2

theorem pfun_isOpen_basis (k : Nat) : pfunTop.isOpen (pfunBasis k) := by
  constructor
  · intro f g hfg h i hi
    exact hfg _ _ (h i hi)
  · intro f h
    refine ⟨(psetBits k).map pairDecode, ?_, ?_⟩
    · intro p hp
      obtain ⟨i, hi, hdec⟩ := List.mem_map.mp hp
      subst hdec
      exact h i hi
    · intro g hg i hi
      exact hg (pairDecode i) (List.mem_map.mpr ⟨i, hi, rfl⟩)

/-- The nowhere-defined partial function, ⊥ of ℕ ⇀ ℕ. -/
def pfunBot : PFun := ⟨fun _ _ => False, fun _ _ _ h => h.elim⟩

def pfunNat : DInfinityFoundations PFun where
  toTopologicalSpace := pfunTop

  -- D1: the open ↑{(n,v)} detects whether f sends n to v.
  t0 := by
    intro f g h
    apply Subtype.ext
    funext n
    funext v
    exact propext
      ⟨fun hf => (h _ (pfun_isOpen_upList [(n, v)])).mp (pfun_single hf) (n, v) (List.Mem.head _),
       fun hg => (h _ (pfun_isOpen_upList [(n, v)])).mpr (pfun_single hg) (n, v) (List.Mem.head _)⟩

  -- D2: the generic point is the union of the graphs. Single-valuedness of that
  -- union is *proved*, from the common-extension lemma — no value is chosen.
  sober := by
    intro C hC hirr
    obtain ⟨w, hw⟩ := hirr.1
    have hsv : ∀ n v v', (∃ f, C f ∧ f.val n v) → (∃ f, C f ∧ f.val n v') → v = v' := by
      rintro n v v' ⟨f1, hf1, hv1⟩ ⟨f2, hf2, hv2⟩
      obtain ⟨z, _, hz1, hz2⟩ :=
        pfun_common_extension hC hirr hf1 hf2 [(n, v)] [(n, v')]
          (pfun_single hv1) (pfun_single hv2)
      exact z.2 n v v' (hz1 (n, v) (List.Mem.head _)) (hz2 (n, v') (List.Mem.head _))
    have hWC : C ⟨fun n v => ∃ f, C f ∧ f.val n v, fun n v w' h1 h2 => hsv n v w' h1 h2⟩ := by
      cases lem (C ⟨fun n v => ∃ f, C f ∧ f.val n v, fun n v w' h1 h2 => hsv n v w' h1 h2⟩) with
      | inl h => exact h
      | inr h =>
          obtain ⟨l, hl, hup⟩ := hC.2 _ h
          obtain ⟨z, hz, hzl⟩ := pfun_member_covering hC hirr hw l hl
          exact absurd hz (hup z hzl)
    refine ⟨⟨fun n v => ∃ f, C f ∧ f.val n v, fun n v w' h1 h2 => hsv n v w' h1 h2⟩, ?_, ?_⟩
    · funext f
      exact propext ⟨fun hf => pfun_leq_of_sub (fun n v hv => ⟨f, hf, hv⟩),
                     fun hf => pfun_down_closed hC (fun n v hv => pfun_sub_of_leq hf n v hv) hWC⟩
    · intro y' hy'
      have hy'C : C y' := cast (congrFun hy' y').symm (pfun_leq_of_sub (fun _ _ h => h))
      apply Subtype.ext
      funext n
      funext v
      refine propext ⟨fun hv => ⟨y', hy'C, hv⟩, fun hv => ?_⟩
      exact pfun_sub_of_leq (cast (congrFun hy' _) hWC) n v hv

  -- D3: one basic open per finite set of pairs, coded as bits decoded by the
  -- Cantor walk.
  basis     := pfunBasis
  basisOpen := pfun_isOpen_basis

  -- A basic open is compact: either it is empty, or the finite set of pairs
  -- coding it is itself consistent, hence a partial function, hence the least
  -- member — and the open covering it covers the whole up-set.
  basisCpt := by
    intro k ι U hU hcov
    cases lem (∃ f : PFun, pfunBasis k f) with
    | inr hempty => exact ⟨0, Fin.elim0, fun f hf => absurd ⟨f, hf⟩ hempty⟩
    | inl hinh =>
        obtain ⟨f0, hf0⟩ := hinh
        have hGsv : ∀ n v w', (∃ i, i ∈ psetBits k ∧ pairDecode i = (n, v)) →
            (∃ i, i ∈ psetBits k ∧ pairDecode i = (n, w')) → v = w' := by
          rintro n v w' ⟨i, hi, hdi⟩ ⟨j, hj, hdj⟩
          have h1 := hf0 i hi
          have h2 := hf0 j hj
          rw [hdi] at h1
          rw [hdj] at h2
          exact f0.2 n v w' h1 h2
        obtain ⟨j, hj⟩ :=
          hcov ⟨fun n v => ∃ i, i ∈ psetBits k ∧ pairDecode i = (n, v), hGsv⟩
            (fun i hi => ⟨i, hi, rfl⟩)
        refine ⟨1, fun _ => j, fun f hf => ⟨0, ?_⟩⟩
        refine (hU j).1 _ f ?_ hj
        rintro n v ⟨i, hi, hdec⟩
        have h1 := hf i hi
        rw [hdec] at h1
        exact h1

  basisGen := by
    intro U hU f hf
    obtain ⟨l, hl, hup⟩ := hU.2 f hf
    obtain ⟨codes, hcodes⟩ := pfun_exists_codes l
    obtain ⟨k, hk⟩ := pset_exists_mask codes
    refine ⟨k, ?_, ?_⟩
    · intro i hi
      exact hl (pairDecode i) ((hcodes (pairDecode i)).mp ⟨i, (hk i).mp (pset_mem_bits.mp hi), rfl⟩)
    · intro g hg
      refine hup g ?_
      intro p hp
      obtain ⟨i, hic, hdec⟩ := (hcodes p).mpr hp
      have h2 := hg i (pset_mem_bits.mpr ((hk i).mpr hic))
      rw [hdec] at h2
      exact h2

  basisCap := by
    intro k1 k2
    refine ⟨k1 ||| k2, fun g => ⟨fun h i hi => ?_, fun h => ⟨fun i hi => ?_, fun i hi => ?_⟩⟩⟩
    · have hb : (k1 ||| k2).testBit i = true := pset_mem_bits.mp hi
      rw [Nat.testBit_or, Bool.or_eq_true] at hb
      cases hb with
      | inl hb1 => exact h.1 i (pset_mem_bits.mpr hb1)
      | inr hb2 => exact h.2 i (pset_mem_bits.mpr hb2)
    · refine h i (pset_mem_bits.mpr ?_)
      rw [Nat.testBit_or, Bool.or_eq_true]
      exact Or.inl (pset_mem_bits.mp hi)
    · refine h i (pset_mem_bits.mpr ?_)
      rw [Nat.testBit_or, Bool.or_eq_true]
      exact Or.inr (pset_mem_bits.mp hi)

  -- D4: the nowhere-defined partial function.
  bot   := pfunBot
  botAx := fun _ hU h f => hU.1 pfunBot f (fun _ _ hv => False.elim hv) h

/-- ℕ ⇀ ℕ is not a lattice: two partial functions disagreeing at a point have no
    upper bound at all, since an upper bound would send 0 to both 0 and 1. -/
theorem pfun_not_lattice :
    ¬ ∃ h : PFun, (∀ n v, (n = 0 ∧ v = 0) → h.val n v) ∧ (∀ n v, (n = 0 ∧ v = 1) → h.val n v) := by
  rintro ⟨h, h0, h1⟩
  exact Nat.noConfusion (h.2 0 0 1 (h0 0 0 ⟨rfl, rfl⟩) (h1 0 1 ⟨rfl, rfl⟩))

-- Axiom audit.
#print axioms pairDecode_hits   -- [propext, Quot.sound]
#print axioms pfunTop           -- [propext]
#print axioms pfunNat           -- [lem, propext, Quot.sound]
#print axioms pfun_not_lattice  -- does not depend on any axioms


/- ----------------------------------------------------------------
   §3.8 — streams 𝔹^≤ω = 𝔹* ∪ 𝔹^ω under the prefix order

   A stream is a graph `Nat → Bool → Prop` that is single-valued and
   **prefix-closed**: defined at n+1 implies defined at n. So the
   defined indices form an initial segment, finite (a word) or all of
   ℕ (an infinite stream), and graph inclusion *is* the prefix order.
   The graph encoding is kept for the §3.7 reason — D2's generic point
   is a union, and `Option` would require choosing values.

   The basis is where this differs from §3.7, and the difference is
   forced. The obvious base — up-sets of finite sets of index/value
   pairs — **fails `basisCpt`**: {(5,tt)} has no least stream above it,
   since indices 0–4 are unconstrained, so its up-set is not a
   principal open and compactness breaks. The compact opens here are
   the up-sets of finite **words**, so `basis (k+1)` is the word of
   length `(pairDecode k).1` whose i-th letter is bit i of
   `(pairDecode k).2`, and `basis 0` is ∅ — needed because two
   incompatible words have empty intersection and `basisCap` must name
   an index for it.
   ---------------------------------------------------------------- -/

def BStream : Type :=
  {G : Nat → Bool → Prop //
    (∀ n b c, G n b → G n c → b = c) ∧ (∀ n b, G (n + 1) b → ∃ c, G n c)}

/-- Prefix-closedness, propagated downward: defined at j implies defined at every i ≤ j. -/
theorem stream_defined_below (s : BStream) :
    ∀ j i, i ≤ j → (∃ b, s.val j b) → ∃ c, s.val i c := by
  intro j
  induction j with
  | zero =>
      intro i hi h
      have : i = 0 := by omega
      subst this
      exact h
  | succ j ih =>
      intro i hi h
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · obtain ⟨b, hb⟩ := h
        obtain ⟨c, hc⟩ := s.2.2 j b hb
        exact ih i (by omega) ⟨c, hc⟩
      · have : i = j + 1 := by omega
        subst this
        exact h

/-- A stream defined below n is captured by a bit mask: the values it assigns on
    `[0, n)` are the low bits of some natural. Built by induction rather than by
    extracting a function `i ↦ value`, which would need unique choice. -/
theorem stream_exists_mask (s : BStream) :
    ∀ n, (∀ i, i < n → ∃ b, s.val i b) →
      ∃ m : Nat, (∀ i, i < n → s.val i (m.testBit i)) ∧ (∀ i, n ≤ i → m.testBit i = false) := by
  intro n
  induction n with
  | zero =>
      intro _
      exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero i), fun i _ => Nat.zero_testBit i⟩
  | succ n ih =>
      intro hall
      obtain ⟨m, hm, hzero⟩ := ih (fun i hi => hall i (by omega))
      obtain ⟨b, hb⟩ := hall n (by omega)
      cases b with
      | true =>
          refine ⟨m ||| 2 ^ n, ?_, ?_⟩
          · intro i hi
            rcases Nat.lt_or_ge i n with h | h
            · have hbit : (m ||| 2 ^ n).testBit i = m.testBit i := by
                rw [Nat.testBit_or, Nat.testBit_two_pow]
                have hne : ¬ (n = i) := by omega
                simp [hne]
              rw [hbit]
              exact hm i h
            · have hin : i = n := by omega
              subst hin
              have hbit : (m ||| 2 ^ i).testBit i = true := by
                rw [Nat.testBit_or, Nat.testBit_two_pow]
                simp
              rw [hbit]
              exact hb
          · intro i hi
            rw [Nat.testBit_or, Nat.testBit_two_pow]
            have h1 : m.testBit i = false := hzero i (by omega)
            have h2 : ¬ (n = i) := by omega
            simp [h1, h2]
      | false =>
          refine ⟨m, ?_, ?_⟩
          · intro i hi
            rcases Nat.lt_or_ge i n with h | h
            · exact hm i h
            · have hin : i = n := by omega
              subst hin
              have hbit : m.testBit i = false := hzero i (Nat.le_refl i)
              rw [hbit]
              exact hb
          · intro i hi
            exact hzero i (by omega)

def streamTop : TopologicalSpace BStream where
  isOpen U :=
    (∀ f g : BStream, (∀ n b, f.val n b → g.val n b) → U f → U g) ∧
    (∀ f, U f → ∃ l : List (Nat × Bool), (∀ p, p ∈ l → f.val p.1 p.2) ∧
       ∀ g : BStream, (∀ p, p ∈ l → g.val p.1 p.2) → U g)
  openEmpty := ⟨fun _ _ _ h => h, fun _ h => h.elim⟩
  openFull  := ⟨fun _ _ _ _ => trivial,
                fun _ _ => ⟨[], (fun _ hp => by cases hp), fun _ _ => trivial⟩⟩
  openUnion := by
    intro _ U hU
    refine ⟨?_, ?_⟩
    · intro f g hfg h
      obtain ⟨i, hi⟩ := h
      exact ⟨i, (hU i).1 f g hfg hi⟩
    · intro f h
      obtain ⟨i, hi⟩ := h
      obtain ⟨l, hl, hup⟩ := (hU i).2 f hi
      exact ⟨l, hl, fun g hg => ⟨i, hup g hg⟩⟩
  openInter := by
    intro U W hU hW
    refine ⟨?_, ?_⟩
    · intro f g hfg h
      exact ⟨hU.1 f g hfg h.1, hW.1 f g hfg h.2⟩
    · intro f h
      obtain ⟨l1, hl1, hup1⟩ := hU.2 f h.1
      obtain ⟨l2, hl2, hup2⟩ := hW.2 f h.2
      refine ⟨l1 ++ l2, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.mp hp with h' | h'
        · exact hl1 p h'
        · exact hl2 p h'
      · intro g hg
        exact ⟨hup1 g (fun p hp => hg p (List.mem_append.mpr (Or.inl hp))),
               hup2 g (fun p hp => hg p (List.mem_append.mpr (Or.inr hp)))⟩

def streamUpList (l : List (Nat × Bool)) : BStream → Prop := fun f => ∀ p, p ∈ l → f.val p.1 p.2

theorem stream_isOpen_upList (l : List (Nat × Bool)) : streamTop.isOpen (streamUpList l) :=
  ⟨fun _ _ hfg h p hp => hfg p.1 p.2 (h p hp), fun _ h => ⟨l, h, fun _ hg => hg⟩⟩

theorem stream_single {f : BStream} {n : Nat} {b : Bool} (h : f.val n b) :
    streamUpList [(n, b)] f := by
  intro p hp
  cases hp with
  | head      => exact h
  | tail _ hh => cases hh

theorem stream_leq_of_sub {f g : BStream} (h : ∀ n b, f.val n b → g.val n b) :
    streamTop.leq f g :=
  fun _ hU hf => hU.1 f g h hf

theorem stream_sub_of_leq {f g : BStream} (h : streamTop.leq f g) (n : Nat) (b : Bool)
    (hv : f.val n b) : g.val n b :=
  h (streamUpList [(n, b)]) (stream_isOpen_upList [(n, b)]) (stream_single hv) (n, b)
    (List.Mem.head _)

theorem stream_down_closed {C : BStream → Prop} (hC : streamTop.isClosed C)
    {f g : BStream} (hfg : ∀ n b, f.val n b → g.val n b) (hg : C g) : C f := by
  cases lem (C f) with
  | inl h => exact h
  | inr h => exact absurd hg (hC.1 f g hfg h)

theorem stream_isClosed_and_not_up {C : BStream → Prop} (hC : streamTop.isClosed C)
    (l : List (Nat × Bool)) : streamTop.isClosed (fun z => C z ∧ ¬ streamUpList l z) := by
  constructor
  · intro f g hfg hf hg
    exact hf ⟨stream_down_closed hC hfg hg.1,
              fun hup => hg.2 ((stream_isOpen_upList l).1 f g hfg hup)⟩
  · intro f hf
    cases lem (C f) with
    | inl hc =>
        have hup1 : streamUpList l f := by
          cases lem (streamUpList l f) with
          | inl h => exact h
          | inr h => exact absurd ⟨hc, h⟩ hf
        exact ⟨l, hup1, fun _ hg hcg => hcg.2 hg⟩
    | inr hnc =>
        obtain ⟨l', hl', hup⟩ := hC.2 f hnc
        exact ⟨l', hl', fun g hg hcg => hup g hg hcg.1⟩

theorem stream_common_extension {C : BStream → Prop} (hC : streamTop.isClosed C)
    (hirr : streamTop.irreducible C) {f g : BStream} (hf : C f) (hg : C g)
    (l1 l2 : List (Nat × Bool)) (h1 : streamUpList l1 f) (h2 : streamUpList l2 g) :
    ∃ z, C z ∧ streamUpList l1 z ∧ streamUpList l2 z := by
  cases lem (∃ z, C z ∧ streamUpList l1 z ∧ streamUpList l2 z) with
  | inl h => exact h
  | inr h =>
      refine absurd ⟨fun z => C z ∧ ¬ streamUpList l1 z, fun z => C z ∧ ¬ streamUpList l2 z,
                     stream_isClosed_and_not_up hC l1, stream_isClosed_and_not_up hC l2,
                     fun _ hq => hq.1, fun _ hq => hq.1, ?_,
                     ⟨f, hf, fun hc => hc.2 h1⟩, ⟨g, hg, fun hc => hc.2 h2⟩⟩ hirr.2
      intro q hq
      cases lem (streamUpList l1 q) with
      | inr hq1 => exact Or.inl ⟨hq, hq1⟩
      | inl hq1 =>
          cases lem (streamUpList l2 q) with
          | inr hq2 => exact Or.inr ⟨hq, hq2⟩
          | inl hq2 => exact absurd ⟨q, hq, hq1, hq2⟩ h

theorem stream_member_covering {C : BStream → Prop} (hC : streamTop.isClosed C)
    (hirr : streamTop.irreducible C) {w : BStream} (hw : C w) :
    ∀ l : List (Nat × Bool), (∀ p, p ∈ l → ∃ f, C f ∧ f.val p.1 p.2) →
      ∃ z, C z ∧ streamUpList l z := by
  intro l
  induction l with
  | nil => intro _; exact ⟨w, hw, (fun _ hp => by cases hp)⟩
  | cons a t ih =>
      intro hall
      obtain ⟨z1, hz1, hup1⟩ := ih (fun p hp => hall p (List.Mem.tail _ hp))
      obtain ⟨f, hf, hfa⟩ := hall a (List.Mem.head _)
      obtain ⟨z, hz, hzt, hza⟩ :=
        stream_common_extension hC hirr hz1 hf t [a] hup1
          (by intro p hp; cases hp with
              | head      => exact hfa
              | tail _ hh => cases hh)
      refine ⟨z, hz, ?_⟩
      intro p hp
      cases hp with
      | head       => exact hza a (List.Mem.head _)
      | tail _ hp' => exact hzt p hp'

/-- The word of length n whose i-th letter is bit i of m — the least stream in its
    own basic open, and the reason words rather than pair-sets are the base. -/
def wordStream (n m : Nat) : BStream :=
  ⟨fun i b => i < n ∧ b = m.testBit i,
   ⟨fun _ b c hb hc => by rw [hb.2, hc.2],
    fun i b h => ⟨m.testBit i, by omega, rfl⟩⟩⟩

def streamBasis : Nat → BStream → Prop
  | 0     => fun _ => False
  | k + 1 => fun s => ∀ i, i < (pairDecode k).1 → s.val i ((pairDecode k).2.testBit i)

def streamBot : BStream := ⟨fun _ _ => False, ⟨fun _ _ _ h => h.elim, fun _ _ h => h.elim⟩⟩

/-- The index bound of a finite approximation. -/
def maxIdx : List (Nat × Bool) → Nat
  | []     => 0
  | p :: t => max (p.1 + 1) (maxIdx t)

theorem maxIdx_bound : ∀ (l : List (Nat × Bool)) p, p ∈ l → p.1 < maxIdx l := by
  intro l
  induction l with
  | nil => intro p hp; cases hp
  | cons a t ih =>
      intro p hp
      cases hp with
      | head =>
          show a.1 < max (a.1 + 1) (maxIdx t)
          omega
      | tail _ hp' =>
          have := ih p hp'
          show p.1 < max (a.1 + 1) (maxIdx t)
          omega

def streamDomain : DInfinityFoundations BStream where
  toTopologicalSpace := streamTop

  t0 := by
    intro f g h
    apply Subtype.ext
    funext n
    funext b
    exact propext
      ⟨fun hf => (h _ (stream_isOpen_upList [(n, b)])).mp (stream_single hf) (n, b)
                   (List.Mem.head _),
       fun hg => (h _ (stream_isOpen_upList [(n, b)])).mpr (stream_single hg) (n, b)
                   (List.Mem.head _)⟩

  -- D2: the generic point is the union of the graphs; single-valuedness comes from
  -- the common-extension lemma and prefix-closedness is inherited memberwise.
  sober := by
    intro C hC hirr
    obtain ⟨w, hw⟩ := hirr.1
    have hsv : ∀ n b c, (∃ f, C f ∧ f.val n b) → (∃ f, C f ∧ f.val n c) → b = c := by
      rintro n b c ⟨f1, hf1, hv1⟩ ⟨f2, hf2, hv2⟩
      obtain ⟨z, _, hz1, hz2⟩ :=
        stream_common_extension hC hirr hf1 hf2 [(n, b)] [(n, c)]
          (stream_single hv1) (stream_single hv2)
      exact z.2.1 n b c (hz1 (n, b) (List.Mem.head _)) (hz2 (n, c) (List.Mem.head _))
    have hpc : ∀ n b, (∃ f, C f ∧ f.val (n + 1) b) → ∃ c, ∃ f, C f ∧ f.val n c := by
      rintro n b ⟨f, hf, hv⟩
      obtain ⟨c, hc⟩ := f.2.2 n b hv
      exact ⟨c, f, hf, hc⟩
    have hWC : C ⟨fun n b => ∃ f, C f ∧ f.val n b, ⟨hsv, hpc⟩⟩ := by
      cases lem (C ⟨fun n b => ∃ f, C f ∧ f.val n b, ⟨hsv, hpc⟩⟩) with
      | inl h => exact h
      | inr h =>
          obtain ⟨l, hl, hup⟩ := hC.2 _ h
          obtain ⟨z, hz, hzl⟩ := stream_member_covering hC hirr hw l hl
          exact absurd hz (hup z hzl)
    refine ⟨⟨fun n b => ∃ f, C f ∧ f.val n b, ⟨hsv, hpc⟩⟩, ?_, ?_⟩
    · funext f
      exact propext ⟨fun hf => stream_leq_of_sub (fun n b hv => ⟨f, hf, hv⟩),
                     fun hf => stream_down_closed hC
                       (fun n b hv => stream_sub_of_leq hf n b hv) hWC⟩
    · intro y' hy'
      have hy'C : C y' := cast (congrFun hy' y').symm (stream_leq_of_sub (fun _ _ h => h))
      apply Subtype.ext
      funext n
      funext b
      refine propext ⟨fun hv => ⟨y', hy'C, hv⟩, fun hv => ?_⟩
      exact stream_sub_of_leq (cast (congrFun hy' _) hWC) n b hv

  basis := streamBasis

  basisOpen := by
    intro k
    cases k with
    | zero => exact ⟨fun _ _ _ h => h, fun _ h => h.elim⟩
    | succ k =>
        refine ⟨fun f g hfg h i hi => hfg i _ (h i hi), ?_⟩
        intro f h
        refine ⟨(List.range (pairDecode k).1).map (fun i => (i, (pairDecode k).2.testBit i)),
                ?_, ?_⟩
        · intro p hp
          obtain ⟨i, hi, hdec⟩ := List.mem_map.mp hp
          subst hdec
          exact h i (List.mem_range.mp hi)
        · intro g hg i hi
          exact hg (i, (pairDecode k).2.testBit i)
            (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

  -- Each basic open is the up-set of a word, whose least member is the word
  -- itself, so one member of any cover already covers the whole basic open.
  basisCpt := by
    intro k ι U hU hcov
    cases k with
    | zero => exact ⟨0, Fin.elim0, fun _ hx => hx.elim⟩
    | succ k =>
        obtain ⟨j, hj⟩ :=
          hcov (wordStream (pairDecode k).1 (pairDecode k).2) (fun i hi => ⟨hi, rfl⟩)
        refine ⟨1, fun _ => j, fun f hf => ⟨0, ?_⟩⟩
        refine (hU j).1 _ f ?_ hj
        rintro i b ⟨hlt, hb⟩
        rw [hb]
        exact hf i hlt

  -- Every finite approximation of a stream is dominated by a word: prefix-closure
  -- fills in the indices below the largest one mentioned, and `stream_exists_mask`
  -- packs the values into a bit mask.
  basisGen := by
    intro U hU f hf
    obtain ⟨l, hl, hup⟩ := hU.2 f hf
    have hdef : ∀ i, i < maxIdx l → ∃ b, f.val i b := by
      intro i hi
      cases lem (∃ p, p ∈ l ∧ i ≤ p.1) with
      | inl h =>
          obtain ⟨p, hp, hip⟩ := h
          exact stream_defined_below f p.1 i hip ⟨p.2, hl p hp⟩
      | inr h =>
          -- every index in l is below i, so maxIdx l ≤ i, contradicting hi
          exfalso
          revert hi
          have : maxIdx l ≤ i := by
            clear hup
            induction l with
            | nil => simp [maxIdx]
            | cons a t ih =>
                have ha : ¬ (i ≤ a.1) := fun hle => h ⟨a, List.Mem.head _, hle⟩
                have hrest : maxIdx t ≤ i :=
                  ih (fun p hp => hl p (List.Mem.tail _ hp))
                    (fun hh => h (by obtain ⟨p, hp, hip⟩ := hh
                                     exact ⟨p, List.Mem.tail _ hp, hip⟩))
                show max (a.1 + 1) (maxIdx t) ≤ i
                omega
          omega
    obtain ⟨m, hm, _⟩ := stream_exists_mask f (maxIdx l) hdef
    obtain ⟨k, hk⟩ := pairDecode_hits (maxIdx l + m) m (maxIdx l) rfl
    refine ⟨k + 1, ?_, ?_⟩
    · show ∀ i, i < (pairDecode k).1 → f.val i ((pairDecode k).2.testBit i)
      rw [hk]
      exact hm
    · intro g hg
      refine hup g ?_
      intro p hp
      have hlt : p.1 < maxIdx l := maxIdx_bound l p hp
      have hgv : g.val p.1 (m.testBit p.1) := by
        have := hg p.1
        rw [hk] at this
        exact this hlt
      have hfv : f.val p.1 (m.testBit p.1) := hm p.1 hlt
      have : p.2 = m.testBit p.1 := f.2.1 p.1 p.2 (m.testBit p.1) (hl p hp) hfv
      rw [this]
      exact hgv

  -- Two words either extend one another — and the intersection is the longer —
  -- or are incompatible, and the intersection is ∅ at index 0.
  basisCap := by
    intro k1 k2
    cases k1 with
    | zero => exact ⟨0, fun _ => ⟨fun h => h.1, fun h => h.elim⟩⟩
    | succ k1 =>
        cases k2 with
        | zero => exact ⟨0, fun _ => ⟨fun h => h.2, fun h => h.elim⟩⟩
        | succ k2 =>
            cases lem (∃ s : BStream, streamBasis (k1 + 1) s ∧ streamBasis (k2 + 1) s) with
            | inr hempty =>
                exact ⟨0, fun s => ⟨fun h => hempty ⟨s, h.1, h.2⟩, fun h => h.elim⟩⟩
            | inl hinh =>
                obtain ⟨s0, hs1, hs2⟩ := hinh
                rcases Nat.le_total (pairDecode k1).1 (pairDecode k2).1 with hle | hle
                · refine ⟨k2 + 1, fun t => ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩⟩
                  intro i hi
                  have hagree : (pairDecode k1).2.testBit i = (pairDecode k2).2.testBit i :=
                    s0.2.1 i _ _ (hs1 i hi) (hs2 i (by omega))
                  rw [hagree]
                  exact h i (by omega)
                · refine ⟨k1 + 1, fun t => ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩⟩
                  intro i hi
                  have hagree : (pairDecode k2).2.testBit i = (pairDecode k1).2.testBit i :=
                    s0.2.1 i _ _ (hs2 i hi) (hs1 i (by omega))
                  rw [hagree]
                  exact h i (by omega)

  bot   := streamBot
  botAx := fun _ hU h f => hU.1 streamBot f (fun _ _ hv => False.elim hv) h

/-- The empty word is ⊥, and every stream extends it. -/
theorem stream_bot_le (s : BStream) : streamTop.leq streamBot s :=
  stream_leq_of_sub (fun _ _ h => False.elim h)

-- Axiom audit.
#print axioms streamTop           -- [propext]
#print axioms stream_exists_mask  -- [propext, Quot.sound]
#print axioms streamDomain        -- [lem, propext, Quot.sound]


/- ----------------------------------------------------------------
   §5.6 — the ideal completion Idl(P)

   The general theorem the catalogue's last section states: a countable
   poset of tokens with a least element, in which every bounded pair has
   a least upper bound, has an ideal completion satisfying D1–D4. Since
   every ω-algebraic domain is Idl(K(D)), this is the statement that
   *choosing a Scott domain is choosing a countable poset of tokens*.

   It is also the pattern §3.6–§3.8 were each doing by hand. Here the
   finite approximation is a **single token**, not a list, because an
   ideal is directed: any finite set of its tokens is already below one
   of its members. That collapses the list machinery those three
   entries needed — no masks, no `pairDecode`, no `List.mem_append` —
   and the basis is just `n ↦ ↑(enum n)`.

   `basis 0` is ∅ for the same reason as §3.8: two tokens with no upper
   bound generate disjoint basic opens, and `basisCap` must name an
   index for the empty intersection.
   ---------------------------------------------------------------- -/

/- Two deliberate weakenings against the textbook statement, each of which the
   proof below shows is all that is needed, and each of which §5.1 requires:

   - **no antisymmetry**. A *preorder* of tokens suffices. Ideals are sets of
     tokens, so two ideals with the same tokens are equal outright and D1 never
     needs the order to separate tokens. Step-function tokens (§5.1) are only
     preordered — `[(a,b)]` and `[(a,b),(a,b)]` entail each other without being
     equal — so requiring antisymmetry would force a quotient for no gain.
   - **enumeration up to mutual entailment**, not equality. `↑t` depends only on
     t's ⊑-class, since an ideal is down-closed: if `enum n ⊑ t ⊑ enum n` then an
     ideal contains one iff it contains the other. A bit-mask enumeration of
     finite token sets cannot reproduce a list's order or duplicates, so exact
     surjectivity is unattainable there and unnecessary here. -/
structure TokenPoset where
  T           : Type
  le          : T → T → Prop
  le_refl     : ∀ a, le a a
  le_trans    : ∀ a b c, le a b → le b c → le a c
  bot         : T
  bot_le      : ∀ a, le bot a
  enum        : Nat → T
  enum_onto   : ∀ a, ∃ n, le (enum n) a ∧ le a (enum n)
  bounded_lub : ∀ a b, (∃ c, le a c ∧ le b c) →
                  ∃ u, le a u ∧ le b u ∧ ∀ v, le a v → le b v → le u v

/-- A directed lower subset containing ⊥. -/
def TokenIdeal (P : TokenPoset) : Type :=
  {I : P.T → Prop //
    (∀ a b, P.le a b → I b → I a) ∧
    (∀ a b, I a → I b → ∃ c, I c ∧ P.le a c ∧ P.le b c) ∧
    I P.bot}

def idealTop (P : TokenPoset) : TopologicalSpace (TokenIdeal P) where
  isOpen U :=
    (∀ I J : TokenIdeal P, (∀ t, I.val t → J.val t) → U I → U J) ∧
    (∀ I, U I → ∃ t, I.val t ∧ ∀ J : TokenIdeal P, J.val t → U J)
  openEmpty := ⟨fun _ _ _ h => h, fun _ h => h.elim⟩
  openFull  := ⟨fun _ _ _ _ => trivial, fun I _ => ⟨P.bot, I.2.2.2, fun _ _ => trivial⟩⟩
  openUnion := by
    intro _ U hU
    refine ⟨?_, ?_⟩
    · intro I J hIJ h
      obtain ⟨i, hi⟩ := h
      exact ⟨i, (hU i).1 I J hIJ hi⟩
    · intro I h
      obtain ⟨i, hi⟩ := h
      obtain ⟨t, ht, hup⟩ := (hU i).2 I hi
      exact ⟨t, ht, fun J hJ => ⟨i, hup J hJ⟩⟩
  openInter := by
    intro U W hU hW
    refine ⟨?_, ?_⟩
    · intro I J hIJ h
      exact ⟨hU.1 I J hIJ h.1, hW.1 I J hIJ h.2⟩
    · intro I h
      obtain ⟨t1, ht1, hup1⟩ := hU.2 I h.1
      obtain ⟨t2, ht2, hup2⟩ := hW.2 I h.2
      obtain ⟨c, hc, hc1, hc2⟩ := I.2.2.1 t1 t2 ht1 ht2
      exact ⟨c, hc, fun J hJ => ⟨hup1 J (J.2.1 t1 c hc1 hJ), hup2 J (J.2.1 t2 c hc2 hJ)⟩⟩

def idealUp (P : TokenPoset) (t : P.T) : TokenIdeal P → Prop := fun I => I.val t

theorem ideal_isOpen_up (P : TokenPoset) (t : P.T) : (idealTop P).isOpen (idealUp P t) :=
  ⟨fun _ _ hIJ h => hIJ t h, fun _ h => ⟨t, h, fun _ hJ => hJ⟩⟩

/-- The principal ideal ↓t: the least member of the basic open ↑t, and the reason
    each basic open is compact. -/
def principalIdeal (P : TokenPoset) (t : P.T) : TokenIdeal P :=
  ⟨fun a => P.le a t,
   ⟨fun a b hab hb => P.le_trans a b t hab hb,
    fun a b ha hb => ⟨t, P.le_refl t, ha, hb⟩,
    P.bot_le t⟩⟩

theorem ideal_leq_of_sub {P : TokenPoset} {I J : TokenIdeal P}
    (h : ∀ t, I.val t → J.val t) : (idealTop P).leq I J :=
  fun _ hU hI => hU.1 I J h hI

theorem ideal_sub_of_leq {P : TokenPoset} {I J : TokenIdeal P}
    (h : (idealTop P).leq I J) (t : P.T) (ht : I.val t) : J.val t :=
  h (idealUp P t) (ideal_isOpen_up P t) ht

theorem ideal_down_closed {P : TokenPoset} {C : TokenIdeal P → Prop}
    (hC : (idealTop P).isClosed C) {I J : TokenIdeal P}
    (hIJ : ∀ t, I.val t → J.val t) (hJ : C J) : C I := by
  cases lem (C I) with
  | inl h => exact h
  | inr h => exact absurd hJ (hC.1 I J hIJ h)

theorem ideal_isClosed_and_not_up {P : TokenPoset} {C : TokenIdeal P → Prop}
    (hC : (idealTop P).isClosed C) (t : P.T) :
    (idealTop P).isClosed (fun Z => C Z ∧ ¬ idealUp P t Z) := by
  constructor
  · intro I J hIJ hI hJ
    exact hI ⟨ideal_down_closed hC hIJ hJ.1, fun hup => hJ.2 (hIJ t hup)⟩
  · intro I hI
    cases lem (C I) with
    | inl hc =>
        have hup1 : idealUp P t I := by
          cases lem (idealUp P t I) with
          | inl h => exact h
          | inr h => exact absurd ⟨hc, h⟩ hI
        exact ⟨t, hup1, fun _ hJ hcj => hcj.2 hJ⟩
    | inr hnc =>
        obtain ⟨t', ht', hup⟩ := hC.2 I hnc
        exact ⟨t', ht', fun J hJ hcj => hup J hJ hcj.1⟩

theorem ideal_common_extension {P : TokenPoset} {C : TokenIdeal P → Prop}
    (hC : (idealTop P).isClosed C) (hirr : (idealTop P).irreducible C)
    {I J : TokenIdeal P} (hI : C I) (hJ : C J) (t1 t2 : P.T)
    (h1 : I.val t1) (h2 : J.val t2) :
    ∃ Z, C Z ∧ Z.val t1 ∧ Z.val t2 := by
  cases lem (∃ Z, C Z ∧ Z.val t1 ∧ Z.val t2) with
  | inl h => exact h
  | inr h =>
      refine absurd ⟨fun Z => C Z ∧ ¬ idealUp P t1 Z, fun Z => C Z ∧ ¬ idealUp P t2 Z,
                     ideal_isClosed_and_not_up hC t1, ideal_isClosed_and_not_up hC t2,
                     fun _ hq => hq.1, fun _ hq => hq.1, ?_,
                     ⟨I, hI, fun hc => hc.2 h1⟩, ⟨J, hJ, fun hc => hc.2 h2⟩⟩ hirr.2
      intro Q hQ
      cases lem (idealUp P t1 Q) with
      | inr hq1 => exact Or.inl ⟨hQ, hq1⟩
      | inl hq1 =>
          cases lem (idealUp P t2 Q) with
          | inr hq2 => exact Or.inr ⟨hQ, hq2⟩
          | inl hq2 => exact absurd ⟨Q, hQ, hq1, hq2⟩ h

def idealDomain (P : TokenPoset) : DInfinityFoundations (TokenIdeal P) where
  toTopologicalSpace := idealTop P

  -- D1: ↑t detects membership of the token t, for every t.
  t0 := by
    intro I J h
    apply Subtype.ext
    funext t
    exact propext ⟨fun hI => (h _ (ideal_isOpen_up P t)).mp hI,
                   fun hJ => (h _ (ideal_isOpen_up P t)).mpr hJ⟩

  -- D2: the generic point is the union of C. Directedness of that union is where
  -- irreducibility is used — two tokens drawn from C sit in a common member,
  -- which is itself directed.
  sober := by
    intro C hC hirr
    obtain ⟨w, hw⟩ := hirr.1
    have hdown : ∀ a b, P.le a b → (∃ I, C I ∧ I.val b) → ∃ I, C I ∧ I.val a := by
      rintro a b hab ⟨I, hI, hb⟩
      exact ⟨I, hI, I.2.1 a b hab hb⟩
    have hdir : ∀ a b, (∃ I, C I ∧ I.val a) → (∃ I, C I ∧ I.val b) →
        ∃ c, (∃ I, C I ∧ I.val c) ∧ P.le a c ∧ P.le b c := by
      rintro a b ⟨I1, hI1, ha⟩ ⟨I2, hI2, hb⟩
      obtain ⟨Z, hZ, hZa, hZb⟩ := ideal_common_extension hC hirr hI1 hI2 a b ha hb
      obtain ⟨c, hc, hac, hbc⟩ := Z.2.2.1 a b hZa hZb
      exact ⟨c, ⟨Z, hZ, hc⟩, hac, hbc⟩
    have hbot : ∃ I, C I ∧ I.val P.bot := ⟨w, hw, w.2.2.2⟩
    have hWC : C ⟨fun t => ∃ I, C I ∧ I.val t, ⟨hdown, hdir, hbot⟩⟩ := by
      cases lem (C ⟨fun t => ∃ I, C I ∧ I.val t, ⟨hdown, hdir, hbot⟩⟩) with
      | inl h => exact h
      | inr h =>
          obtain ⟨t, ht, hup⟩ := hC.2 _ h
          obtain ⟨I, hI, hIt⟩ := ht
          exact absurd hI (hup I hIt)
    refine ⟨⟨fun t => ∃ I, C I ∧ I.val t, ⟨hdown, hdir, hbot⟩⟩, ?_, ?_⟩
    · funext I
      exact propext ⟨fun hI => ideal_leq_of_sub (fun t ht => ⟨I, hI, ht⟩),
                     fun hI => ideal_down_closed hC (fun t ht => ideal_sub_of_leq hI t ht) hWC⟩
    · intro y' hy'
      have hy'C : C y' := cast (congrFun hy' y').symm (ideal_leq_of_sub (fun _ h => h))
      apply Subtype.ext
      funext t
      refine propext ⟨fun ht => ⟨y', hy'C, ht⟩, fun ht => ?_⟩
      exact ideal_sub_of_leq (cast (congrFun hy' _) hWC) t ht

  -- D3: one basic open per token, plus ∅.
  basis := fun n =>
    match n with
    | 0     => fun _ => False
    | n + 1 => idealUp P (P.enum n)

  basisOpen := by
    intro n
    cases n with
    | zero   => exact ⟨fun _ _ _ h => h, fun _ h => h.elim⟩
    | succ n => exact ideal_isOpen_up P (P.enum n)

  basisCpt := by
    intro n ι U hU hcov
    cases n with
    | zero => exact ⟨0, Fin.elim0, fun _ hx => hx.elim⟩
    | succ n =>
        obtain ⟨i, hi⟩ := hcov (principalIdeal P (P.enum n)) (P.le_refl (P.enum n))
        refine ⟨1, fun _ => i, fun I hI => ⟨0, ?_⟩⟩
        exact (hU i).1 _ I (fun a ha => I.2.1 a (P.enum n) ha hI) hi

  basisGen := by
    intro U hU I hI
    obtain ⟨t, ht, hup⟩ := hU.2 I hI
    obtain ⟨n, hn1, hn2⟩ := P.enum_onto t
    refine ⟨n + 1, ?_, ?_⟩
    · exact I.2.1 (P.enum n) t hn1 ht
    · intro J hJ
      exact hup J (J.2.1 t (P.enum n) hn2 hJ)

  -- Two tokens bounded in some ideal have a least upper bound, and ↑a ∩ ↑b = ↑(a ⊔ b);
  -- unbounded tokens generate disjoint basic opens.
  basisCap := by
    intro m n
    cases m with
    | zero => exact ⟨0, fun _ => ⟨fun h => h.1, fun h => h.elim⟩⟩
    | succ m =>
        cases n with
        | zero => exact ⟨0, fun _ => ⟨fun h => h.2, fun h => h.elim⟩⟩
        | succ n =>
            cases lem (∃ c, P.le (P.enum m) c ∧ P.le (P.enum n) c) with
            | inr hunb =>
                refine ⟨0, fun I => ⟨fun h => ?_, fun h => h.elim⟩⟩
                obtain ⟨c, _, hmc, hnc⟩ := I.2.2.1 _ _ h.1 h.2
                exact hunb ⟨c, hmc, hnc⟩
            | inl hbdd =>
                obtain ⟨u, hu1, hu2, hulub⟩ := P.bounded_lub _ _ hbdd
                obtain ⟨p, hp1, hp2⟩ := P.enum_onto u
                refine ⟨p + 1, fun I => ⟨fun h => ?_, fun h => ?_⟩⟩
                · obtain ⟨c, hc, hmc, hnc⟩ := I.2.2.1 _ _ h.1 h.2
                  exact I.2.1 (P.enum p) c (P.le_trans _ u c hp1 (hulub c hmc hnc)) hc
                · have hu : I.val u := I.2.1 u (P.enum p) hp2 h
                  exact ⟨I.2.1 _ u hu1 hu, I.2.1 _ u hu2 hu⟩

  -- D4: the least ideal, ↓⊥.
  bot   := principalIdeal P P.bot
  botAx := by
    intro U hU h I
    exact hU.1 _ I (fun a ha => I.2.1 a P.bot ha I.2.2.2) h

/-- Compact elements of Idl(P) are exactly the principal ideals — the ↑t are the
    basic opens, so the tokens are the finite approximations. -/
theorem ideal_principal_mem (P : TokenPoset) (t : P.T) :
    (principalIdeal P t).val t := P.le_refl t

-- Axiom audit. Leaner than §3.6–§3.8: `idealTop` is axiom-free outright and the
-- common-extension argument needs `lem` alone, where the three concrete entries
-- picked up `propext` and `Quot.sound` from the list lemmas their finite
-- approximations required. Working with a single token instead of a list is what
-- removes them.
#print axioms idealTop               -- does not depend on any axioms
#print axioms ideal_common_extension -- [lem]
#print axioms idealDomain            -- [lem, propext, Quot.sound]


/- ----------------------------------------------------------------
   §5.1 — the function space [D → E], via step-function tokens

   Built on §5.6 rather than topologically: give the *tokens* of the
   function space and hand them to `idealDomain`. This is Scott's
   information-systems presentation, and §5.6's own claim — choosing a
   Scott domain is choosing a countable poset of tokens — is what makes
   it legitimate.

   A token is a finite list of step functions `(a, b)`, read as "sends
   anything above a to at least b". The order is entailment:

       l ⊑ m  ⇔  for every (a,b) ∈ l, b is below **every** upper bound
                 of what m contributes at a

   which says b ⊑ ⊔{b' | (a',b') ∈ m, a' ⊑ a} without having to assert
   that the join exists. That formulation is what keeps the definition
   first-order and join-free.

   **Scope, stated exactly.** The value side is required to have
   *total* binary joins (`JoinTokens`). For a general value domain a
   finite set of step functions is a legitimate token only when it is
   *consistent*, and consistency is not decidable from a bare
   `TokenPoset` — so the carrier would be a subtype with an undecidable
   predicate, and `enum` could not be constructed without choice, which
   this development does not admit. Carrying joins as data removes the
   condition: every finite list is consistent, bounded by the fold of
   the joins. §4's dualizing object [D → 𝕊] is covered, since 𝕊's
   tokens carry `or` as their join.

   Not proved here: that these ideals are in bijection with the
   Scott-continuous maps D → E. That is the information-systems
   *definition* of the function space; identifying it with the space of
   actual functions needs a notion of continuous map, which the D1–D4
   vocabulary does not yet carry.
   ---------------------------------------------------------------- -/

structure JoinTokens where
  base          : TokenPoset
  join          : base.T → base.T → base.T
  le_join_left  : ∀ a b, base.le a (join a b)
  le_join_right : ∀ a b, base.le b (join a b)
  join_least    : ∀ a b v, base.le a v → base.le b v → base.le (join a b) v

/-- b is below every upper bound of what l contributes at a. -/
def stepEntails (P : TokenPoset) (Q : JoinTokens) (l : List (P.T × Q.base.T))
    (a : P.T) (b : Q.base.T) : Prop :=
  ∀ v, (∀ a' b', (a', b') ∈ l → P.le a' a → Q.base.le b' v) → Q.base.le b v

def stepLe (P : TokenPoset) (Q : JoinTokens) (l m : List (P.T × Q.base.T)) : Prop :=
  ∀ a b, (a, b) ∈ l → stepEntails P Q m a b

theorem stepEntails_of_mem {P : TokenPoset} {Q : JoinTokens} {m : List (P.T × Q.base.T)}
    {a a' : P.T} {b b' : Q.base.T} (hmem : (a', b') ∈ m) (ha : P.le a' a)
    (hb : Q.base.le b b') : stepEntails P Q m a b :=
  fun v hv => Q.base.le_trans b b' v hb (hv a' b' hmem ha)

theorem stepEntails_mono {P : TokenPoset} {Q : JoinTokens} {m m' : List (P.T × Q.base.T)}
    {a : P.T} {b : Q.base.T} (hsub : ∀ q, q ∈ m → q ∈ m')
    (h : stepEntails P Q m a b) : stepEntails P Q m' a b :=
  fun v hv => h v (fun a' b' hmem ha => hv a' b' (hsub (a', b') hmem) ha)

/-- The enumeration of finite step-function sets: k's bits, decoded as index pairs. -/
def stepEnum (P : TokenPoset) (Q : JoinTokens) (k : Nat) : List (P.T × Q.base.T) :=
  (psetBits k).map (fun i => (P.enum (pairDecode i).1, Q.base.enum (pairDecode i).2))

theorem mem_bits_or {k i j : Nat} : j ∈ psetBits (k ||| 2 ^ i) ↔ (j ∈ psetBits k ∨ j = i) := by
  rw [pset_mem_bits, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_iff,
      pset_mem_bits]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr h.symm

def funTokens (P : TokenPoset) (Q : JoinTokens) : TokenPoset where
  T  := List (P.T × Q.base.T)
  le := stepLe P Q

  le_refl := by
    intro l a b hab v hv
    exact hv a b hab (P.le_refl a)

  le_trans := by
    intro l m n hlm hmn a b hab v hv
    refine hlm a b hab v ?_
    intro a' b' hmem ha'
    refine hmn a' b' hmem v ?_
    intro a'' b'' hmem'' ha''
    exact hv a'' b'' hmem'' (P.le_trans a'' a' a ha'' ha')

  bot    := []
  bot_le := by
    intro _ a b hab
    cases hab

  enum := stepEnum P Q

  enum_onto := by
    intro l
    induction l with
    | nil =>
        refine ⟨0, ?_, ?_⟩
        · intro a b hab
          rw [show stepEnum P Q 0 = [] from rfl] at hab
          cases hab
        · intro a b hab
          cases hab
    | cons p t ih =>
        obtain ⟨kt, ht1, ht2⟩ := ih
        obtain ⟨n, hn1, hn2⟩ := P.enum_onto p.1
        obtain ⟨m, hm1, hm2⟩ := Q.base.enum_onto p.2
        obtain ⟨i, hi⟩ := pairDecode_hits (n + m) m n rfl
        have hnew : (P.enum n, Q.base.enum m) ∈ stepEnum P Q (kt ||| 2 ^ i) := by
          refine List.mem_map.mpr ⟨i, mem_bits_or.mpr (Or.inr rfl), ?_⟩
          rw [hi]
        have hold : ∀ q, q ∈ stepEnum P Q kt → q ∈ stepEnum P Q (kt ||| 2 ^ i) := by
          intro q hq
          obtain ⟨j, hj, hqj⟩ := List.mem_map.mp hq
          exact List.mem_map.mpr ⟨j, mem_bits_or.mpr (Or.inl hj), hqj⟩
        refine ⟨kt ||| 2 ^ i, ?_, ?_⟩
        · -- the enumerated list is below p :: t
          intro a b hab
          obtain ⟨j, hj, hqj⟩ := List.mem_map.mp hab
          rcases mem_bits_or.mp hj with hjk | hji
          · refine stepEntails_mono (m := t) (fun q hq => List.Mem.tail _ hq) ?_
            exact ht1 a b (List.mem_map.mpr ⟨j, hjk, hqj⟩)
          · subst hji
            rw [hi] at hqj
            injection hqj with h1 h2
            subst h1
            subst h2
            exact stepEntails_of_mem (List.Mem.head _) hn2 hm1
        · -- p :: t is below the enumerated list
          intro a b hab
          cases hab with
          | head =>
              exact stepEntails_of_mem hnew hn1 hm2
          | tail _ hmem =>
              exact stepEntails_mono hold (ht2 a b hmem)

  bounded_lub := by
    intro l m _
    refine ⟨l ++ m, ?_, ?_, ?_⟩
    · intro a b hab v hv
      exact hv a b (List.mem_append.mpr (Or.inl hab)) (P.le_refl a)
    · intro a b hab v hv
      exact hv a b (List.mem_append.mpr (Or.inr hab)) (P.le_refl a)
    · intro z hlz hmz a b hab
      rcases List.mem_append.mp hab with h | h
      · exact hlz a b h
      · exact hmz a b h

/-- [D → E] as a Scott domain: the ideals of the step-function tokens. -/
def funSpace (P : TokenPoset) (Q : JoinTokens) :
    DInfinityFoundations (TokenIdeal (funTokens P Q)) :=
  idealDomain (funTokens P Q)

/-- 𝕊's tokens: ⊥ ⊑ ⊤ with `or` as the join, so [D → 𝕊] is covered. -/
def sierpTokens : JoinTokens where
  base :=
    { T           := Bool
      le          := fun x y => x = true → y = true
      le_refl     := fun _ h => h
      le_trans    := fun _ _ _ h1 h2 h => h2 (h1 h)
      bot         := false
      bot_le      := fun _ h => Bool.noConfusion h
      enum        := fun n => match n with | 0 => false | _ => true
      enum_onto   := by
        intro a
        cases a
        · exact ⟨0, fun h => h, fun h => h⟩
        · exact ⟨1, fun h => h, fun h => h⟩
      bounded_lub := by
        intro a b _
        cases a <;> cases b
        · exact ⟨false, fun h => h, fun h => h, fun _ h _ => h⟩
        · exact ⟨true, fun h => Bool.noConfusion h, fun h => h, fun _ _ h => h⟩
        · exact ⟨true, fun h => h, fun h => Bool.noConfusion h, fun _ h _ => h⟩
        · exact ⟨true, fun h => h, fun h => h, fun _ h _ => h⟩ }
  join          := fun a b => a || b
  le_join_left  := by intro a b h; cases a <;> simp_all
  le_join_right := by intro a b h; cases b <;> simp_all
  join_least    := by intro a b v h1 h2 h; cases a <;> cases b <;> simp_all

-- Axiom audit. The token construction itself is `lem`-free — building the tokens
-- of [D → E] is constructive; only passing them through `idealDomain`, whose D2
-- decides membership of a closed set, brings excluded middle back.
#print axioms funTokens  -- [propext, Quot.sound]
#print axioms funSpace   -- [lem, propext, Quot.sound]
