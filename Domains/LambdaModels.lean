/- ================================================================
   §5.2 parallel-or and §5.3 the Pω λ-model.

   Part of the Scott domain catalogue; see ../docs/ScottDomainExamples.md
   and Domains/ScottDomainExamples.lean, which imports every part.
   ================================================================ -/

import Domains.Infinite

/- ----------------------------------------------------------------
   §5.2 — parallel-or

   por(tt, x) = tt, por(x, tt) = tt, por(ff, ff) = ff, on 𝔹⊥ from §3.3.
   The catalogue makes two claims about it, and again they are not the
   same kind of claim.

   **It is monotone, hence continuous, hence an element of the function
   domain** — proved here, in both arguments. On a flat domain monotone
   *is* continuous: a directed subset of 𝔹⊥ is a chain with a greatest
   element, so preservation of directed suprema is monotonicity.

   **It is not definable in PCF (Plotkin 1977)** — not proved here, and
   not provable in this vocabulary: definability is a statement about a
   *syntax* and its operational semantics, so it needs a PCF term
   language and an adequacy theorem, neither of which the D1–D4 setting
   carries.

   What *is* provable here is the semantic hallmark that separates por
   from every sequential function: it has **no sequentiality index**.
   A function of two flat arguments is sequential when some argument
   position is strict — evaluating it must begin somewhere — and
   `por_not_seq` shows por is strict in neither, while `lor_seq` shows
   the notion is not vacuous. That is exactly what "parallel" names.
   ---------------------------------------------------------------- -/

def por : Option Bool → Option Bool → Option Bool
  | some true,  _          => some true
  | _,          some true  => some true
  | some false, some false => some false
  | _,          _          => none

theorem por_tt_left (x : Option Bool) : por (some true) x = some true := rfl

theorem por_tt_right (x : Option Bool) : por x (some true) = some true := by
  cases x with
  | none   => rfl
  | some b => cases b with
    | true  => rfl
    | false => rfl

theorem por_ff : por (some false) (some false) = some false := rfl

/-- The flat order on 𝔹⊥: ⊥ below everything, data incomparable. -/
def flatLe (x y : Option Bool) : Prop := x = none ∨ x = y

theorem por_mono_left : ∀ x x' y, flatLe x x' → flatLe (por x y) (por x' y) := by
  intro x x' y h
  rcases h with h | h
  · subst h
    cases y with
    | none   => exact Or.inl rfl
    | some b => cases b with
      | true  => exact Or.inr (by rw [por_tt_right, por_tt_right])
      | false => exact Or.inl rfl
  · subst h
    exact Or.inr rfl

theorem por_mono_right : ∀ x y y', flatLe y y' → flatLe (por x y) (por x y') := by
  intro x y y' h
  rcases h with h | h
  · subst h
    cases x with
    | none   => exact Or.inl rfl
    | some b => cases b with
      | true  => exact Or.inr (by rw [por_tt_left, por_tt_left])
      | false => exact Or.inl rfl
  · subst h
    exact Or.inr rfl

/-- A function of two flat arguments is sequential when some argument position is
    strict: evaluation has to begin somewhere. -/
def StrictFirst (f : Option Bool → Option Bool → Option Bool) : Prop := ∀ y, f none y = none

def StrictSecond (f : Option Bool → Option Bool → Option Bool) : Prop := ∀ x, f x none = none

def HasSeqIndex (f : Option Bool → Option Bool → Option Bool) : Prop :=
  StrictFirst f ∨ StrictSecond f

/-- **por has no sequentiality index** — it is strict in neither argument. This is
    the semantic content of "parallel". -/
theorem por_not_seq : ¬ HasSeqIndex por := by
  rintro (h | h)
  · have h2 : (some true : Option Bool) = none := h (some true)
    cases h2
  · have h2 : (some true : Option Bool) = none := h (some true)
    cases h2

/-- Sequential (left-strict) or, to show the notion is not vacuous. -/
def lor : Option Bool → Option Bool → Option Bool
  | none,       _ => none
  | some true,  _ => some true
  | some false, y => y

theorem lor_seq : HasSeqIndex lor := Or.inl (fun _ => rfl)

/-- por and sequential or agree wherever both are defined on total data, so the
    difference is exactly the behaviour at ⊥. -/
theorem por_lor_agree (b c : Bool) : por (some b) (some c) = lor (some b) (some c) := by
  cases b <;> cases c <;> rfl

-- Axiom audit. The whole entry is `lem`-free; `propext` enters only through
-- `rintro`'s case analysis.
#print axioms por_mono_left   -- [propext]
#print axioms por_mono_right  -- [propext]
#print axioms por_not_seq     -- [propext]
#print axioms lor_seq         -- does not depend on any axioms
/- ----------------------------------------------------------------
   §5.3 — Pω as a λ-model: [Pω → Pω] is a retract of Pω

   The *domain* is §3.6: Pω is 𝒫(ℕ), already a Scott domain as
   `psetNat`. What this entry adds is the λ-model structure — Scott's
   1976 "Data Types as Lattices" construction:

       A · B  =  { m | ∃ k, ⟨k,m⟩ ∈ A and e_k ⊆ B }
       Graph f = { ⟨k,m⟩ | m ∈ f(e_k) }
       Fun (Graph f) = f     for continuous f

   with `e_k` the finite set coded by k's bits, already available as
   the §3.6 basis. Because the function space embeds into the domain
   itself, self-application `A · A` is interpretable and Pω models the
   untyped λ-calculus **with no inverse limit** — which is why §5.5 is
   not needed for a model, only for Scott's original one.

   One ingredient is missing and is supplied first. `pairDecode` is a
   surjection ℕ ↠ ℕ×ℕ, which was enough for enumerating a basis, but a
   *coding* needs a section: `Fun (Graph f) = f` reads back k and m
   from ⟨k,m⟩ and so needs **injectivity**. `cantor` is that section,
   defined through triangular numbers so that no division appears, and
   `pairDecode_cantor` proves it inverse to the walk on the nose.
   ---------------------------------------------------------------- -/

def tri : Nat → Nat
  | 0     => 0
  | n + 1 => tri n + (n + 1)

/-- The Cantor pairing, as a section of `pairDecode`. -/
def cantor (n m : Nat) : Nat := tri (n + m) + m

theorem pairDecode_cantor : ∀ s m n, n + m = s → pairDecode (cantor n m) = (n, m) := by
  intro s
  induction s with
  | zero =>
      intro m n h
      have hn : n = 0 := by omega
      have hm : m = 0 := by omega
      subst hn
      subst hm
      rfl
  | succ s ih =>
      intro m
      induction m with
      | zero =>
          intro n h
          have hn : n = s + 1 := by omega
          subst hn
          have hc : cantor (s + 1) 0 = cantor 0 s + 1 := by
            show tri ((s + 1) + 0) + 0 = tri (0 + s) + s + 1
            rw [Nat.add_zero, Nat.zero_add, tri]
            omega
          rw [hc, pairDecode, ih s 0 (by omega)]
      | succ m ihm =>
          intro n h
          have hidx : n + (m + 1) = (n + 1) + m := by omega
          have hc : cantor n (m + 1) = cantor (n + 1) m + 1 := by
            show tri (n + (m + 1)) + (m + 1) = tri ((n + 1) + m) + m + 1
            rw [hidx]
            omega
          rw [hc, pairDecode, ihm (n + 1) (by omega)]

theorem cantor_injective {n m n' m' : Nat} (h : cantor n m = cantor n' m') :
    n = n' ∧ m = m' := by
  have h1 : pairDecode (cantor n m) = (n, m) := pairDecode_cantor (n + m) m n rfl
  have h2 : pairDecode (cantor n' m') = (n', m') := pairDecode_cantor (n' + m') m' n' rfl
  rw [h, h2] at h1
  injection h1 with e1 e2
  exact ⟨e1.symm, e2.symm⟩

/-- `e_k`, the finite set coded by the bits of k — the §3.6 basis, as a predicate. -/
def eSet (k : Nat) : Nat → Prop := fun n => k.testBit n = true

/-- Application: A · B. -/
def powApp (A B : Nat → Prop) : Nat → Prop :=
  fun m => ∃ k, A (cantor k m) ∧ ∀ n, eSet k n → B n

/-- Graph: the code of a function as a set. -/
def powGraph (f : (Nat → Prop) → (Nat → Prop)) : Nat → Prop :=
  fun j => ∃ k m, j = cantor k m ∧ f (eSet k) m

/-- Continuity in the form §3.6's topology already uses: monotone, and every
    element of an output is already produced by a finite part of the input. -/
structure PowContinuous (f : (Nat → Prop) → (Nat → Prop)) : Prop where
  mono   : ∀ A B, (∀ n, A n → B n) → ∀ m, f A m → f B m
  finite : ∀ B m, f B m → ∃ k, (∀ n, eSet k n → B n) ∧ f (eSet k) m

/-- **Fun ∘ Graph = id**: the retraction, and with it §5.3's claim that
    [Pω → Pω] is a retract of Pω. -/
theorem powApp_powGraph (f : (Nat → Prop) → (Nat → Prop)) (hf : PowContinuous f)
    (B : Nat → Prop) (m : Nat) : powApp (powGraph f) B m ↔ f B m := by
  constructor
  · rintro ⟨k, ⟨k', m', heq, hfk⟩, hsub⟩
    obtain ⟨hk, hm⟩ := cantor_injective heq
    subst hk
    subst hm
    exact hf.mono _ B hsub m hfk
  · intro h
    obtain ⟨k, hsub, hfk⟩ := hf.finite B m h
    exact ⟨k, ⟨k, m, rfl, hfk⟩, hsub⟩

/-- Every `Fun A` is itself continuous, so `Fun` really lands in [Pω → Pω]. -/
theorem powApp_continuous (A : Nat → Prop) : PowContinuous (powApp A) where
  mono := by
    rintro B C hBC m ⟨k, hA, hsub⟩
    exact ⟨k, hA, fun n hn => hBC n (hsub n hn)⟩
  finite := by
    rintro B m ⟨k, hA, hsub⟩
    exact ⟨k, hsub, ⟨k, hA, fun _ hn => hn⟩⟩

/-- Self-application is interpretable: this is what a λ-model needs and what the
    retraction buys, with no inverse limit anywhere. -/
def powSelfApp (A : Nat → Prop) : Nat → Prop := powApp A A

-- Axiom audit. The whole λ-model layer is constructive: no `lem`, and the two
-- remaining axioms come from `omega`'s arithmetic reasoning inside the pairing.
#print axioms pairDecode_cantor  -- [propext, Quot.sound]
#print axioms cantor_injective   -- [propext, Quot.sound]
#print axioms powApp_powGraph    -- [propext, Quot.sound]
#print axioms powApp_continuous  -- does not depend on any axioms


