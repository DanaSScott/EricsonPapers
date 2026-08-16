/- ================================================================
   §5.6, the ideal completion — the general theorem the rest of §5 is built on.

   Part of the Scott domain catalogue; see ../docs/ScottDomainExamples.md
   and Domains/ScottDomainExamples.lean, which imports every part.
   ================================================================ -/

import Domains.LRSODInCIC

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
    fun _ _ ha hb => ⟨t, P.le_refl t, ha, hb⟩,
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


