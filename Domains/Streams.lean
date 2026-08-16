/- ================================================================
   §3.8 — streams under the prefix order.

   Part of the Scott domain catalogue; see ../docs/ScottDomainExamples.md
   and Domains/ScottDomainExamples.lean, which imports every part.
   ================================================================ -/

import Domains.PartialFunctions

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


