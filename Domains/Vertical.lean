/- ================================================================
   §3.4 — the vertical naturals ω + 1.

   Part of the Scott domain catalogue; see ../docs/ScottDomainExamples.md
   and Domains/ScottDomainExamples.lean, which imports every part.
   ================================================================ -/

import Domains.LRSODInCIC

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


