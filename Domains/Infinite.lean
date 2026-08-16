/- ================================================================
   Infinite carriers: §3.6–§3.8.  Also the bit-mask and pairing machinery
   (`psetBits`, `pairDecode`) that later sections enumerate with.

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


