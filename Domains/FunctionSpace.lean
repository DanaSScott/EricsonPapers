/- ================================================================
   §5.1, the function space, and its bijection with the continuous maps.

   Part of the Scott domain catalogue; see ../docs/ScottDomainExamples.md
   and Domains/ScottDomainExamples.lean, which imports every part.
   ================================================================ -/

import Domains.Infinite
import Domains.IdealCompletion

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

   **Scope.** `funTokens` and `funSpace` take *arbitrary* token posets
   on both sides. An earlier version of this comment claimed the value
   side needed total joins, on the grounds that only *consistent* step
   sets are legitimate tokens and consistency is undecidable; that was
   wrong, and the reason is `stepEntails_of_unbounded` below. A step
   set whose contributions at `a` have no upper bound entails
   everything at `a` — the premise "v bounds the contributions" is
   unsatisfiable, so the implication is vacuous. An inconsistent token
   is therefore high in the order rather than ill-formed, the carrier
   can be all finite lists, and no subtype and no decidability question
   arises.

   What total joins on the value side actually buy is the reading of
   the result: with them no token is inconsistent, so the ideals are
   [D → E]; without them the inconsistent tokens sit above everything
   and the construction builds [D → E] with a top adjoined. §4's
   dualizing object [D → 𝕊] is the former case, 𝕊's tokens carrying
   `or` as their join.

   **The bijection with continuous maps is now proved.** With
   `IdealContinuous` as the finite-approximation form of Scott
   continuity — monotone, and every output token already produced by a
   single input token — the two directions are

       funApply  : ideal of step functions → map on ideals
       ofFun     : continuous map → ideal of step functions (its graph)

   and they invert each other: `funApply_ofFun` gives Fun ∘ Graph = id
   and `ofFun_funApply` gives Graph ∘ Fun = id. So the ideals of
   `funTokens P Q` *are* the continuous maps, not merely a stand-in for
   them, and §5.1 carries no remaining scope limit.

   `funApply_continuous` closes the loop by showing every ideal's action
   is itself continuous, so `ofFun` may be applied to it without a side
   hypothesis.
   ---------------------------------------------------------------- -/

structure JoinTokens where
  base          : TokenPoset
  join          : base.T → base.T → base.T
  le_join_left  : ∀ a b, base.le a (join a b)
  le_join_right : ∀ a b, base.le b (join a b)
  join_least    : ∀ a b v, base.le a v → base.le b v → base.le (join a b) v

/-- b is below every upper bound of what l contributes at a. -/
def stepEntails (P : TokenPoset) (Q : TokenPoset) (l : List (P.T × Q.T))
    (a : P.T) (b : Q.T) : Prop :=
  ∀ v, (∀ a' b', (a', b') ∈ l → P.le a' a → Q.le b' v) → Q.le b v

def stepLe (P : TokenPoset) (Q : TokenPoset) (l m : List (P.T × Q.T)) : Prop :=
  ∀ a b, (a, b) ∈ l → stepEntails P Q m a b

theorem stepEntails_of_mem {P : TokenPoset} {Q : TokenPoset} {m : List (P.T × Q.T)}
    {a a' : P.T} {b b' : Q.T} (hmem : (a', b') ∈ m) (ha : P.le a' a)
    (hb : Q.le b b') : stepEntails P Q m a b :=
  fun v hv => Q.le_trans b b' v hb (hv a' b' hmem ha)

theorem stepEntails_mono {P : TokenPoset} {Q : TokenPoset} {m m' : List (P.T × Q.T)}
    {a : P.T} {b : Q.T} (hsub : ∀ q, q ∈ m → q ∈ m')
    (h : stepEntails P Q m a b) : stepEntails P Q m' a b :=
  fun v hv => h v (fun a' b' hmem ha => hv a' b' (hsub (a', b') hmem) ha)

/-- The enumeration of finite step-function sets: k's bits, decoded as index pairs. -/
def stepEnum (P : TokenPoset) (Q : TokenPoset) (k : Nat) : List (P.T × Q.T) :=
  (psetBits k).map (fun i => (P.enum (pairDecode i).1, Q.enum (pairDecode i).2))

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

def funTokens (P : TokenPoset) (Q : TokenPoset) : TokenPoset where
  T  := List (P.T × Q.T)
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
        obtain ⟨m, hm1, hm2⟩ := Q.enum_onto p.2
        obtain ⟨i, hi⟩ := pairDecode_hits (n + m) m n rfl
        have hnew : (P.enum n, Q.enum m) ∈ stepEnum P Q (kt ||| 2 ^ i) := by
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
def funSpace (P : TokenPoset) (Q : TokenPoset) :
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
/-- **Why no consistency side-condition is needed.** A finite step-set whose
    contributions at `a` have no upper bound entails *everything* at `a`: the
    premise "v bounds the contributions" is unsatisfiable, so the implication is
    vacuous. An inconsistent token therefore sits high in the order rather than
    being ill-formed, which is why the carrier can be all finite lists — no
    subtype, and so no undecidable predicate blocking `enum`. -/
theorem stepEntails_of_unbounded {P Q : TokenPoset} {m : List (P.T × Q.T)}
    {a : P.T} (h : ¬ ∃ v, ∀ a' b', (a', b') ∈ m → P.le a' a → Q.le b' v) (b : Q.T) :
    stepEntails P Q m a b :=
  fun v hv => absurd ⟨v, hv⟩ h

/-- The least upper bound of what `l` contributes at `a`. Built by induction with
    `lem` deciding each `a' ⊑ a`, so no decidability of the order is needed. Total
    joins on the value side are what make it exist. -/
theorem contributions_lub (P : TokenPoset) (Q : JoinTokens) (l : List (P.T × Q.base.T))
    (a : P.T) :
    ∃ c, (∀ a' b', (a', b') ∈ l → P.le a' a → Q.base.le b' c) ∧
         (∀ v, (∀ a' b', (a', b') ∈ l → P.le a' a → Q.base.le b' v) → Q.base.le c v) := by
  induction l with
  | nil =>
      refine ⟨Q.base.bot, ?_, ?_⟩
      · intro a' b' hmem
        cases hmem
      · intro v _
        exact Q.base.bot_le v
  | cons p t ih =>
      obtain ⟨c, hbound, hleast⟩ := ih
      cases lem (P.le p.1 a) with
      | inl hpa =>
          refine ⟨Q.join p.2 c, ?_, ?_⟩
          · intro a' b' hmem ha'
            cases hmem with
            | head       => exact Q.le_join_left _ _
            | tail _ hm  => exact Q.base.le_trans b' c _ (hbound a' b' hm ha') (Q.le_join_right _ _)
          · intro v hv
            refine Q.join_least _ _ v (hv p.1 p.2 (List.Mem.head _) hpa) ?_
            exact hleast v (fun a' b' hm ha' => hv a' b' (List.Mem.tail _ hm) ha')
      | inr hpa =>
          refine ⟨c, ?_, ?_⟩
          · intro a' b' hmem ha'
            cases hmem with
            | head      => exact absurd ha' hpa
            | tail _ hm => exact hbound a' b' hm ha'
          · intro v hv
            exact hleast v (fun a' b' hm ha' => hv a' b' (List.Mem.tail _ hm) ha')

/-- **Applying an ideal of step functions to an ideal of arguments.** This is the
    operative half of "the ideals of [D → E] *are* the continuous maps": each ideal
    acts on ideals, monotonically. The full bijection with Scott-continuous maps is
    still not proved — that needs a notion of continuous map between ideal
    completions — but the action itself is here. -/
def funApply (P : TokenPoset) (Q : JoinTokens)
    (F : TokenIdeal (funTokens P Q.base)) (X : TokenIdeal P) : TokenIdeal Q.base :=
  ⟨fun b => ∃ l a, F.val l ∧ X.val a ∧ stepEntails P Q.base l a b,
   ⟨by
      rintro b b' hbb ⟨l, a, hF, hX, hent⟩
      exact ⟨l, a, hF, hX, fun v hv => Q.base.le_trans b b' v hbb (hent v hv)⟩,
    by
      rintro b1 b2 ⟨l1, a1, hF1, hX1, hent1⟩ ⟨l2, a2, hF2, hX2, hent2⟩
      obtain ⟨l, hFl, hl1, hl2⟩ := F.2.2.1 l1 l2 hF1 hF2
      obtain ⟨a, hXa, ha1, ha2⟩ := X.2.2.1 a1 a2 hX1 hX2
      obtain ⟨c, hcb, hcl⟩ := contributions_lub P Q l a
      have key : ∀ (l0 : List (P.T × Q.base.T)) (a0 : P.T),
          (funTokens P Q.base).le l0 l → P.le a0 a →
          ∀ a' b', (a', b') ∈ l0 → P.le a' a0 → Q.base.le b' c := by
        intro l0 a0 hl0 ha0 a' b' hmem ha'
        refine hl0 a' b' hmem c ?_
        intro a'' b'' hmem'' ha''
        exact hcb a'' b'' hmem''
          (P.le_trans a'' a' a ha'' (P.le_trans a' a0 a ha' ha0))
      refine ⟨c, ⟨l, a, hFl, hXa, fun v hv => hcl v hv⟩, ?_, ?_⟩
      · exact hent1 c (key l1 a1 hl1 ha1)
      · exact hent2 c (key l2 a2 hl2 ha2),
    ⟨[], P.bot, F.2.2.2, X.2.2.2, fun v _ => Q.base.bot_le v⟩⟩⟩

theorem funApply_mono_left (P : TokenPoset) (Q : JoinTokens)
    (F G : TokenIdeal (funTokens P Q.base)) (X : TokenIdeal P)
    (h : ∀ l, F.val l → G.val l) :
    ∀ b, (funApply P Q F X).val b → (funApply P Q G X).val b := by
  rintro b ⟨l, a, hF, hX, hent⟩
  exact ⟨l, a, h l hF, hX, hent⟩

theorem funApply_mono_right (P : TokenPoset) (Q : JoinTokens)
    (F : TokenIdeal (funTokens P Q.base)) (X Y : TokenIdeal P)
    (h : ∀ a, X.val a → Y.val a) :
    ∀ b, (funApply P Q F X).val b → (funApply P Q F Y).val b := by
  rintro b ⟨l, a, hF, hX, hent⟩
  exact ⟨l, a, hF, h a hX, hent⟩

/-- Entailment is monotone in the argument: a larger argument admits more
    contributions, so any bound for it bounds the smaller argument's. -/
theorem stepEntails_mono_arg {P Q : TokenPoset} {m : List (P.T × Q.T)} {a a' : P.T}
    {b : Q.T} (h : stepEntails P Q m a' b) (hle : P.le a' a) : stepEntails P Q m a b :=
  fun v hv => h v (fun a'' b'' hmem ha'' => hv a'' b'' hmem (P.le_trans a'' a' a ha'' hle))

/-- An ideal contains an upper bound of any finite set of its members: directedness,
    iterated. -/
theorem ideal_finite_bound (P : TokenPoset) (I : TokenIdeal P) :
    ∀ l : List P.T, (∀ a, a ∈ l → I.val a) → ∃ c, I.val c ∧ ∀ a, a ∈ l → P.le a c := by
  intro l
  induction l with
  | nil => intro _; exact ⟨P.bot, I.2.2.2, (by intro a ha; cases ha)⟩
  | cons a t ih =>
      intro h
      obtain ⟨c, hc, hbound⟩ := ih (fun x hx => h x (List.Mem.tail _ hx))
      obtain ⟨d, hd, hac, hcd⟩ := I.2.2.1 a c (h a (List.Mem.head _)) hc
      refine ⟨d, hd, ?_⟩
      intro x hx
      cases hx with
      | head       => exact hac
      | tail _ hx' => exact P.le_trans x c d (hbound x hx') hcd

/-- Continuity of a map between ideal completions, in the finite-approximation form
    the algebraic setting uses: monotone, and every output token is already produced
    by a single input token. -/
structure IdealContinuous (P : TokenPoset) (Q : JoinTokens)
    (F : TokenIdeal P → TokenIdeal Q.base) : Prop where
  mono     : ∀ X Y, (∀ a, X.val a → Y.val a) → ∀ b, (F X).val b → (F Y).val b
  finitary : ∀ X b, (F X).val b → ∃ a, X.val a ∧ (F (principalIdeal P a)).val b

/-- The contributions of a step-set at an argument are jointly bounded inside the
    output ideal. Induction with `lem` deciding each comparison; the value-side
    joins are not needed, because the bound is taken inside `F X` by directedness. -/
theorem contributions_in (P : TokenPoset) (Q : JoinTokens)
    (F : TokenIdeal P → TokenIdeal Q.base) (hF : IdealContinuous P Q F)
    (X : TokenIdeal P) (a : P.T) (haX : X.val a) :
    ∀ l : List (P.T × Q.base.T), (∀ p, p ∈ l → (F (principalIdeal P p.1)).val p.2) →
      ∃ c, (F X).val c ∧ ∀ a' b', (a', b') ∈ l → P.le a' a → Q.base.le b' c := by
  intro l
  induction l with
  | nil =>
      intro _
      exact ⟨Q.base.bot, (F X).2.2.2, (by intro a' b' hmem; cases hmem)⟩
  | cons p t ih =>
      intro hl
      obtain ⟨c, hc, hbound⟩ := ih (fun q hq => hl q (List.Mem.tail _ hq))
      cases lem (P.le p.1 a) with
      | inl hpa =>
          have hp : (F X).val p.2 :=
            hF.mono (principalIdeal P p.1) X
              (fun x hx => X.2.1 x a (P.le_trans x p.1 a hx hpa) haX) p.2
              (hl p (List.Mem.head _))
          obtain ⟨d, hd, hpd, hcd⟩ := (F X).2.2.1 p.2 c hp hc
          refine ⟨d, hd, ?_⟩
          intro a' b' hmem ha'
          cases hmem with
          | head       => exact hpd
          | tail _ hm  => exact Q.base.le_trans b' c d (hbound a' b' hm ha') hcd
      | inr hpa =>
          refine ⟨c, hc, ?_⟩
          intro a' b' hmem ha'
          cases hmem with
          | head      => exact absurd ha' hpa
          | tail _ hm => exact hbound a' b' hm ha'

#print axioms funTokens              -- [propext, Quot.sound]
#print axioms funSpace               -- [lem, propext, Quot.sound]
#print axioms stepEntails_of_unbounded
#print axioms contributions_lub
#print axioms funApply
/-- Entailment transfers along the order on step-sets. -/
theorem stepEntails_of_stepLe {P Q : TokenPoset} {l m : List (P.T × Q.T)} {a : P.T} {b : Q.T}
    (hlm : stepLe P Q l m) (h : stepEntails P Q l a b) : stepEntails P Q m a b :=
  fun v hv => h v (fun a' b' hmem ha' => hlm a' b' hmem v
    (fun a'' b'' hmem'' ha'' => hv a'' b'' hmem'' (P.le_trans a'' a' a ha'' ha')))

theorem funApply_continuous (P : TokenPoset) (Q : JoinTokens)
    (F : TokenIdeal (funTokens P Q.base)) : IdealContinuous P Q (funApply P Q F) where
  mono     := fun X Y h b hb => funApply_mono_right P Q F X Y h b hb
  finitary := by
    rintro X b ⟨l, a, hF, hX, hent⟩
    exact ⟨a, hX, ⟨l, a, hF, P.le_refl a, hent⟩⟩

/-- **Graph**: the step-function tokens a continuous map validates. -/
def ofFun (P : TokenPoset) (Q : JoinTokens) (F : TokenIdeal P → TokenIdeal Q.base)
    (hF : IdealContinuous P Q F) : TokenIdeal (funTokens P Q.base) :=
  ⟨fun (l : List (P.T × Q.base.T)) => ∀ p, p ∈ l → (F (principalIdeal P p.1)).val p.2,
   ⟨by
      intro m l hml hl p hp
      obtain ⟨c, hc, hbound⟩ :=
        contributions_in P Q F hF (principalIdeal P p.1) p.1 (P.le_refl p.1) l hl
      exact (F (principalIdeal P p.1)).2.1 p.2 c (hml p.1 p.2 hp c hbound) hc,
    by
      intro l1 l2 h1 h2
      refine ⟨List.append l1 l2, ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.mp hp with h | h
        · exact h1 p h
        · exact h2 p h
      · intro a b hab v hv
        exact hv a b (List.mem_append.mpr (Or.inl hab)) (P.le_refl a)
      · intro a b hab v hv
        exact hv a b (List.mem_append.mpr (Or.inr hab)) (P.le_refl a),
    by intro p hp; cases hp⟩⟩

/-- **Fun ∘ Graph = id**: applying the graph of a continuous map recovers the map. -/
theorem funApply_ofFun (P : TokenPoset) (Q : JoinTokens)
    (F : TokenIdeal P → TokenIdeal Q.base) (hF : IdealContinuous P Q F) (X : TokenIdeal P) :
    funApply P Q (ofFun P Q F hF) X = F X := by
  apply Subtype.ext
  funext b
  refine propext ⟨?_, ?_⟩
  · rintro ⟨l, a, hl, ha, hent⟩
    obtain ⟨c, hc, hbound⟩ := contributions_in P Q F hF X a ha l hl
    exact (F X).2.1 b c (hent c hbound) hc
  · intro hb
    obtain ⟨a, haX, hb'⟩ := hF.finitary X b hb
    refine ⟨[(a, b)], a, ?_, haX, ?_⟩
    · intro p hp
      cases hp with
      | head      => exact hb'
      | tail _ hh => cases hh
    · intro v hv
      exact hv a b (List.Mem.head _) (P.le_refl a)

/-- **Graph ∘ Fun = id**: the graph of an ideal's action is that ideal. -/
theorem ofFun_funApply (P : TokenPoset) (Q : JoinTokens)
    (F : TokenIdeal (funTokens P Q.base)) :
    ofFun P Q (funApply P Q F) (funApply_continuous P Q F) = F := by
  have key : ∀ (m : List (P.T × Q.base.T)),
      (∀ p, p ∈ m → (funApply P Q F (principalIdeal P p.1)).val p.2) →
      ∃ L, F.val L ∧ ∀ p, p ∈ m → stepEntails P Q.base L p.1 p.2 := by
    intro m
    induction m with
    | nil => intro _; exact ⟨[], F.2.2.2, (by intro p hp; cases hp)⟩
    | cons p t ih =>
        intro hm
        obtain ⟨L, hL, hall⟩ := ih (fun q hq => hm q (List.Mem.tail _ hq))
        obtain ⟨l', a', hl', ha', hent'⟩ := hm p (List.Mem.head _)
        obtain ⟨M, hM, hLM, hlM⟩ := F.2.2.1 L l' hL hl'
        refine ⟨M, hM, ?_⟩
        intro q hq
        cases hq with
        | head       => exact stepEntails_mono_arg (stepEntails_of_stepLe hlM hent') ha'
        | tail _ hq' => exact stepEntails_of_stepLe hLM (hall q hq')
  apply Subtype.ext
  funext l
  refine propext ⟨?_, ?_⟩
  · intro hl
    obtain ⟨L, hL, hall⟩ := key l hl
    exact F.2.1 l L (fun a b hab => hall (a, b) hab) hL
  · intro hl p hp
    exact ⟨l, p.1, hl, P.le_refl p.1,
           stepEntails_of_mem hp (P.le_refl p.1) (Q.base.le_refl p.2)⟩

#print axioms ideal_finite_bound
#print axioms contributions_in
#print axioms ofFun
#print axioms funApply_ofFun
#print axioms ofFun_funApply


