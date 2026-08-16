/- ================================================================
   §5.4, term and tree domains.

   Part of the Scott domain catalogue; see ../docs/ScottDomainExamples.md
   and Domains/ScottDomainExamples.lean, which imports every part.
   ================================================================ -/

import Domains.Infinite
import Domains.IdealCompletion

/- ----------------------------------------------------------------
   §5.4 — term and tree domains T^∞(Σ)

   The finite Σ-terms with Ω for "undefined", ordered by "less defined
   at every position", are the compacts; the domain is their ideal
   completion, so §5.6 again supplies D1–D4 and only the tokens have to
   be built.

   The decisive choice is to make a finite partial term an **inductive
   type** rather than a set of (position, symbol) pairs:

       FinTree := hole | node (s : sym) (l r : FinTree)

   A labelling given as a set of pairs would have to carry two side
   conditions — single-valued, and prefix-closed so that no position is
   labelled above an unlabelled one — and §3.8 showed why they cannot be
   dropped: a basis element that is not prefix-closed has no least
   member and `basisCpt` fails. As an inductive type both conditions
   hold by construction, and the undecidability that a validity
   predicate would introduce (blocking `enum` without choice, as in
   §5.1) never arises.

   Signature scope: binary, with symbols countable. Any finite
   signature binarizes, and §3.8 is the unary case — one unary symbol
   per letter — as the catalogue says.
   ---------------------------------------------------------------- -/

structure TreeSig where
  sym       : Type
  enum      : Nat → sym
  enum_onto : ∀ s, ∃ n, enum n = s

inductive FinTree (S : TreeSig) where
  | hole : FinTree S
  | node : S.sym → FinTree S → FinTree S → FinTree S

/-- "Less defined at every position": Ω is below everything, and nodes compare
    only under equal symbols, componentwise. -/
def treeLe {S : TreeSig} : FinTree S → FinTree S → Prop
  | .hole,       _           => True
  | .node _ _ _, .hole       => False
  | .node s a b, .node t c d => s = t ∧ treeLe a c ∧ treeLe b d

theorem treeLe_refl {S : TreeSig} (t : FinTree S) : treeLe t t := by
  induction t with
  | hole => trivial
  | node s a b iha ihb => exact ⟨rfl, iha, ihb⟩

theorem treeLe_trans {S : TreeSig} :
    ∀ t u v : FinTree S, treeLe t u → treeLe u v → treeLe t v := by
  intro t
  induction t with
  | hole => intro _ _ _ _; trivial
  | node s a b iha ihb =>
      intro u v htu huv
      cases u with
      | hole => exact htu.elim
      | node s' a' b' =>
          cases v with
          | hole => exact huv.elim
          | node s'' a'' b'' =>
              exact ⟨htu.1.trans huv.1, iha a' a'' htu.2.1 huv.2.1,
                     ihb b' b'' htu.2.2 huv.2.2⟩

/-- Two terms below a common one have a least upper bound: built by recursion on
    the bound, so no total join function is needed. -/
theorem treeLe_lub {S : TreeSig} :
    ∀ c t u : FinTree S, treeLe t c → treeLe u c →
      ∃ w, treeLe t w ∧ treeLe u w ∧ ∀ v, treeLe t v → treeLe u v → treeLe w v := by
  intro c
  induction c with
  | hole =>
      intro t u htc huc
      cases t with
      | hole =>
          cases u with
          | hole => exact ⟨.hole, trivial, trivial, fun _ _ _ => trivial⟩
          | node _ _ _ => exact huc.elim
      | node _ _ _ => exact htc.elim
  | node s c1 c2 ih1 ih2 =>
      intro t u htc huc
      cases t with
      | hole =>
          exact ⟨u, trivial, treeLe_refl u, fun v _ hv => hv⟩
      | node ts t1 t2 =>
          cases u with
          | hole => exact ⟨.node ts t1 t2, treeLe_refl _, trivial, fun v hv _ => hv⟩
          | node us u1 u2 =>
              obtain ⟨w1, hw1t, hw1u, hw1l⟩ := ih1 t1 u1 htc.2.1 huc.2.1
              obtain ⟨w2, hw2t, hw2u, hw2l⟩ := ih2 t2 u2 htc.2.2 huc.2.2
              refine ⟨.node ts w1 w2, ⟨rfl, hw1t, hw2t⟩,
                      ⟨huc.1.trans htc.1.symm, hw1u, hw2u⟩, ?_⟩
              intro v hv1 hv2
              cases v with
              | hole => exact hv1.elim
              | node vs v1 v2 =>
                  exact ⟨hv1.1, hw1l v1 hv1.2.1 hv2.2.1, hw2l v2 hv1.2.2 hv2.2.2⟩

/-- All trees of height ≤ n using symbols among the first n of the enumeration. -/
def treesUpTo (S : TreeSig) : Nat → List (FinTree S)
  | 0     => [FinTree.hole]
  | n + 1 =>
      FinTree.hole ::
        (List.range (n + 1)).flatMap (fun i =>
          (treesUpTo S n).flatMap (fun l =>
            (treesUpTo S n).map (fun r => FinTree.node (S.enum i) l r)))

theorem treesUpTo_mono (S : TreeSig) :
    ∀ n t, t ∈ treesUpTo S n → t ∈ treesUpTo S (n + 1) := by
  intro n t ht
  cases n with
  | zero =>
      have : t = FinTree.hole := by
        cases ht with
        | head => rfl
        | tail _ h => cases h
      subst this
      exact List.Mem.head _
  | succ n =>
      -- `treesUpTo (n+2)` starts with hole and then ranges over a superset
      cases ht with
      | head => exact List.Mem.head _
      | tail _ hmem =>
          refine List.Mem.tail _ ?_
          obtain ⟨i, hi, hrest⟩ := List.mem_flatMap.mp hmem
          obtain ⟨l, hl, hrest2⟩ := List.mem_flatMap.mp hrest
          obtain ⟨r, hr, heq⟩ := List.mem_map.mp hrest2
          refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr (by
            have := List.mem_range.mp hi; omega), ?_⟩
          exact List.mem_flatMap.mpr ⟨l, treesUpTo_mono S n l hl,
            List.mem_map.mpr ⟨r, treesUpTo_mono S n r hr, heq⟩⟩

theorem treesUpTo_le (S : TreeSig) :
    ∀ n m t, n ≤ m → t ∈ treesUpTo S n → t ∈ treesUpTo S m := by
  intro n m
  induction m with
  | zero => intro t hnm ht; have : n = 0 := by omega
            subst this; exact ht
  | succ m ih =>
      intro t hnm ht
      rcases Nat.lt_or_ge n (m + 1) with h | h
      · exact treesUpTo_mono S m t (ih t (by omega) ht)
      · have : n = m + 1 := by omega
        subst this
        exact ht

theorem treesUpTo_covers (S : TreeSig) : ∀ t : FinTree S, ∃ n, t ∈ treesUpTo S n := by
  intro t
  induction t with
  | hole => exact ⟨0, List.Mem.head _⟩
  | node s a b iha ihb =>
      obtain ⟨na, hna⟩ := iha
      obtain ⟨nb, hnb⟩ := ihb
      obtain ⟨i, hi⟩ := S.enum_onto s
      refine ⟨max (max na nb) i + 1, ?_⟩
      refine List.Mem.tail _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr (by omega), ?_⟩)
      refine List.mem_flatMap.mpr
        ⟨a, treesUpTo_le S na (max (max na nb) i) a (by omega) hna, ?_⟩
      refine List.mem_map.mpr
        ⟨b, treesUpTo_le S nb (max (max na nb) i) b (by omega) hnb, ?_⟩
      rw [hi]

def treeTokens (S : TreeSig) : TokenPoset where
  T  := FinTree S
  le := treeLe

  le_refl  := treeLe_refl
  le_trans := treeLe_trans

  bot    := FinTree.hole
  bot_le := fun _ => trivial

  enum := fun k => (treesUpTo S (pairDecode k).1).getD (pairDecode k).2 FinTree.hole

  enum_onto := by
    intro t
    obtain ⟨n, hn⟩ := treesUpTo_covers S t
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hn
    obtain ⟨k, hk⟩ := pairDecode_hits (n + j) j n rfl
    refine ⟨k, ?_, ?_⟩
    · rw [hk]
      show treeLe ((treesUpTo S n).getD j FinTree.hole) t
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, hget]
      exact treeLe_refl t
    · rw [hk]
      show treeLe t ((treesUpTo S n).getD j FinTree.hole)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, hget]
      exact treeLe_refl t

  bounded_lub := by
    rintro t u ⟨c, htc, huc⟩
    exact treeLe_lub c t u htc huc

/-- T^∞(Σ): the infinite Σ-terms, as ideals of finite ones. -/
def treeDomain (S : TreeSig) : DInfinityFoundations (TokenIdeal (treeTokens S)) :=
  idealDomain (treeTokens S)

-- Axiom audit.
#print axioms treeLe_lub  -- does not depend on any axioms
#print axioms treeTokens  -- [propext, Quot.sound]
#print axioms treeDomain  -- [lem, propext, Quot.sound]


