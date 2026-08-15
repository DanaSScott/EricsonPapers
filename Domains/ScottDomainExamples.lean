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
