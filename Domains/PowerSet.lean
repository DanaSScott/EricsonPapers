/- ================================================================
   §3.6 — the powerset 𝒫(ℕ). Also `psetBits` and `pset_exists_mask`, the
   bit-mask enumeration of finite sets that later sections reuse.

   Part of the Scott domain catalogue; see ../docs/ScottDomainExamples.md
   and Domains/ScottDomainExamples.lean, which imports every part.
   ================================================================ -/

import Domains.LRSODInCIC

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


