/- ================================================================
   §3.7 — partial functions ℕ ⇀ ℕ. Also `pairDecode`, the surjection
   ℕ ↠ ℕ×ℕ that later sections enumerate pairs with.

   Part of the Scott domain catalogue; see ../docs/ScottDomainExamples.md
   and Domains/ScottDomainExamples.lean, which imports every part.
   ================================================================ -/

import Domains.PowerSet

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


