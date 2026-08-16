/- ================================================================
   §3.5 — finite bounded-complete pointed posets, as a class.

   Part of the Scott domain catalogue; see ../docs/ScottDomainExamples.md
   and Domains/ScottDomainExamples.lean, which imports every part.
   ================================================================ -/

import Domains.LRSODInCIC

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


