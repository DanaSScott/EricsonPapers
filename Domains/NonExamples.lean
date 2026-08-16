/- ================================================================
   §6.1, §6.2 and §6.5 — the refutations and the powerdomains.

   Part of the Scott domain catalogue; see ../docs/ScottDomainExamples.md
   and Domains/ScottDomainExamples.lean, which imports every part.
   ================================================================ -/

import Domains.IdealCompletion
import Domains.Infinite
import Domains.Enumeration

/- ----------------------------------------------------------------
   §6.1 — bounded completeness fails: two minimal upper bounds

   The first **non**-example. Everything before this inhabited
   `DInfinityFoundations`; here the content is a refutation, and the
   two results below are the two faces of the same failure:

   - order-theoretic: {a, b} has upper bounds c and d and no least
     one, so the poset is not bounded complete;
   - topological: ↑a ∩ ↑b = {c, d} is not ↑k for any k, so the
     compact-open base is not closed under intersection and `basisCap`
     (D3) cannot be discharged.

   §4 predicted exactly this — `basisCap` is the topological form of
   bounded completeness — and §3.5's `fbcDomain` consumes the
   hypothesis at exactly that field. This poset satisfies every other
   `FinBCPoset` field; `bounded_lub` is the one it fails.

   Note on the count: the catalogue says "six elements", but the
   structure it describes — ⊥, a, b, c, d — has five, and its own
   claim ↑a ∩ ↑b = {c, d} is the five-element reading. Formalized as
   five.
   ---------------------------------------------------------------- -/

inductive Six where
  | bot | a | b | c | d
  deriving DecidableEq

/-- ⊥ ⊑ a, b ⊑ c, d, with a ∦ b and c ∦ d. -/
def sixLe : Six → Six → Bool
  | .bot, _  => true
  | .a,   .a => true
  | .a,   .c => true
  | .a,   .d => true
  | .b,   .b => true
  | .b,   .c => true
  | .b,   .d => true
  | .c,   .c => true
  | .d,   .d => true
  | _,    _  => false

def sixUp (x : Six) : Six → Prop := fun z => sixLe x z = true

/-- Bounded completeness fails: a and b are bounded, with no least upper bound. -/
theorem six_no_lub :
    ¬ ∃ u, sixLe .a u = true ∧ sixLe .b u = true ∧
        ∀ v, sixLe .a v = true → sixLe .b v = true → sixLe u v = true := by
  rintro ⟨u, hau, hbu, hlub⟩
  cases u with
  | bot => exact Bool.noConfusion hau
  | a   => exact Bool.noConfusion hbu
  | b   => exact Bool.noConfusion hau
  | c   => exact Bool.noConfusion (hlub .d rfl rfl)
  | d   => exact Bool.noConfusion (hlub .c rfl rfl)

/-- The pair *is* bounded — c and d are both upper bounds. What fails is leastness. -/
theorem six_bounded : sixLe .a .c = true ∧ sixLe .b .c = true := ⟨rfl, rfl⟩

/-- D3 fails topologically: ↑a ∩ ↑b is not a principal up-set. -/
theorem six_basisCap_fails :
    ¬ ∃ k, ∀ z, (sixUp .a z ∧ sixUp .b z) ↔ sixUp k z := by
  rintro ⟨k, hk⟩
  have hc : sixUp k .c := (hk .c).mp ⟨rfl, rfl⟩
  have hd : sixUp k .d := (hk .d).mp ⟨rfl, rfl⟩
  cases k with
  | bot => exact Bool.noConfusion ((hk .a).mpr rfl).2
  | a   => exact Bool.noConfusion ((hk .a).mpr rfl).2
  | b   => exact Bool.noConfusion ((hk .b).mpr rfl).1
  | c   => exact Bool.noConfusion hd
  | d   => exact Bool.noConfusion hc


/- ----------------------------------------------------------------
   §6.2 — directed completeness fails: ℕ under ≤

   ℕ is directed — any two naturals have an upper bound — and has no
   upper bound at all, so it is not a dcpo. Adjoining ∞ repairs it and
   gives §3.4's `vertNat`, which is the point of the pair: "cpo" is a
   completeness requirement, not a size requirement.
   ---------------------------------------------------------------- -/

theorem nat_directed (n m : Nat) : ∃ k, n ≤ k ∧ m ≤ k := ⟨n + m, by omega, by omega⟩

theorem nat_not_dcpo : ¬ ∃ m : Nat, ∀ n : Nat, n ≤ m := by
  rintro ⟨m, hm⟩
  exact absurd (hm (m + 1)) (by omega)

-- Axiom audit for the two non-examples. Both are refutations of finite or
-- arithmetic facts, so neither needs `lem`: §6.1 decides by case analysis on a
-- five-constructor type, §6.2 by `omega`.
#print axioms six_no_lub          -- [propext]
#print axioms six_basisCap_fails  -- [propext]
#print axioms nat_not_dcpo        -- [propext, Quot.sound]


/- ----------------------------------------------------------------
   §6.5 — powerdomains

   The section makes two claims, and they are not of the same kind.

   **The Hoare (lower) powerdomain stays inside the algebraic
   lattices** — proved here. Its tokens are finite sets of tokens under
   the lower preorder "every member of A is below some member of B",
   joins are unions and are **total**, so `idealDomain` yields a Scott
   domain that is moreover a lattice.

   **The Plotkin (convex) powerdomain of a Scott domain need not be
   bounded complete** — *not* proved here, and the reason is worth
   stating. This is a refutation needing a *specific* Scott domain
   whose convex powerdomain has a bounded pair with no least bound. The
   small cases do not work: over 𝔹⊥ the pair {⊥,tt}, {⊥,ff} is bounded
   by {tt,ff} and by {⊥,tt,ff}, and the latter is below the former, so
   a least bound does exist there. A genuine counterexample is a piece
   of domain theory in its own right, not a re-encoding of what the
   catalogue asserts, so `egliMilnerLe` is recorded below for the
   statement's sake and the refutation is left open.
   ---------------------------------------------------------------- -/

/-- Every list of naturals is bounded in length and in entries. -/
theorem natList_bound : ∀ l : List Nat, ∃ n, l.length ≤ n ∧ ∀ x, x ∈ l → x < n := by
  intro l
  induction l with
  | nil => exact ⟨0, by simp, (by intro x hx; cases hx)⟩
  | cons a t ih =>
      obtain ⟨n, h1, h2⟩ := ih
      refine ⟨max (n + 1) (a + 1), ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · intro x hx
        cases hx with
        | head        => omega
        | tail _ hx'  => have := h2 x hx'; omega

def natListsUpTo (n : Nat) : List (List Nat) := listsUpTo (List.range n) n

theorem natListsUpTo_covers : ∀ l : List Nat, ∃ n, l ∈ natListsUpTo n := by
  intro l
  obtain ⟨n, h1, h2⟩ := natList_bound l
  exact ⟨n, mem_listsUpTo _ n l h1 (fun x hx => List.mem_range.mpr (h2 x hx))⟩

/-- The Hoare (lower) preorder on finite sets of tokens. -/
def hoareLe (P : TokenPoset) (A B : List P.T) : Prop :=
  ∀ a, a ∈ A → ∃ b, b ∈ B ∧ P.le a b

/-- Joins in the Hoare powerdomain are unions, and they are **total** — which is
    what puts it inside the algebraic lattices rather than merely the domains. -/
theorem hoare_join_total (P : TokenPoset) (A B : List P.T) :
    hoareLe P A (A ++ B) ∧ hoareLe P B (A ++ B) ∧
      ∀ C, hoareLe P A C → hoareLe P B C → hoareLe P (A ++ B) C := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    exact ⟨a, List.mem_append.mpr (Or.inl ha), P.le_refl a⟩
  · intro a ha
    exact ⟨a, List.mem_append.mpr (Or.inr ha), P.le_refl a⟩
  · intro C hAC hBC a ha
    rcases List.mem_append.mp ha with h | h
    · exact hAC a h
    · exact hBC a h

def hoareEnum (P : TokenPoset) (k : Nat) : List P.T :=
  ((natListsUpTo (pairDecode k).1).getD (pairDecode k).2 []).map P.enum

/-- Every finite set of tokens is Hoare-equivalent to one built from enumerated
    tokens: the replacement is elementwise, so it is an induction, not a choice. -/
theorem hoare_enum_approx (P : TokenPoset) : ∀ A : List P.T,
    ∃ l : List Nat, hoareLe P A (l.map P.enum) ∧ hoareLe P (l.map P.enum) A := by
  intro A
  induction A with
  | nil => exact ⟨[], (by intro a ha; cases ha), (by intro a ha; cases ha)⟩
  | cons a t ih =>
      obtain ⟨l, h1, h2⟩ := ih
      obtain ⟨k, hk1, hk2⟩ := P.enum_onto a
      refine ⟨k :: l, ?_, ?_⟩
      · intro x hx
        cases hx with
        | head => exact ⟨P.enum k, List.Mem.head _, hk2⟩
        | tail _ hx' =>
            obtain ⟨b, hb, hab⟩ := h1 x hx'
            exact ⟨b, List.Mem.tail _ hb, hab⟩
      · intro x hx
        cases hx with
        | head => exact ⟨a, List.Mem.head _, hk1⟩
        | tail _ hx' =>
            obtain ⟨b, hb, hab⟩ := h2 x hx'
            exact ⟨b, List.Mem.tail _ hb, hab⟩

def hoareTokens (P : TokenPoset) : TokenPoset where
  T  := List P.T
  le := hoareLe P

  le_refl := fun _ a ha => ⟨a, ha, P.le_refl a⟩

  le_trans := by
    intro A B C hAB hBC a ha
    obtain ⟨b, hb, hab⟩ := hAB a ha
    obtain ⟨c, hc, hbc⟩ := hBC b hb
    exact ⟨c, hc, P.le_trans a b c hab hbc⟩

  bot    := []
  bot_le := by intro _ a ha; cases ha

  enum := hoareEnum P

  enum_onto := by
    intro A
    obtain ⟨l, h1, h2⟩ := hoare_enum_approx P A
    obtain ⟨n, hn⟩ := natListsUpTo_covers l
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hn
    obtain ⟨k, hk⟩ := pairDecode_hits (n + i) i n rfl
    have heq : hoareEnum P k = l.map P.enum := by
      show ((natListsUpTo (pairDecode k).1).getD (pairDecode k).2 []).map P.enum
        = l.map P.enum
      rw [hk]
      show ((natListsUpTo n).getD i []).map P.enum = l.map P.enum
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hget]
      rfl
    exact ⟨k, by rw [heq]; exact h2, by rw [heq]; exact h1⟩

  bounded_lub := by
    intro A B _
    obtain ⟨h1, h2, h3⟩ := hoare_join_total P A B
    exact ⟨A ++ B, h1, h2, h3⟩

/-- The Hoare powerdomain of a Scott domain, as a Scott domain. -/
def hoarePowerdomain (P : TokenPoset) :
    DInfinityFoundations (TokenIdeal (hoareTokens P)) :=
  idealDomain (hoareTokens P)

/-- The Egli–Milner (Plotkin) preorder, recorded for the statement's sake. The
    refutation of bounded completeness for the convex powerdomain is **not**
    formalized — see the note above. -/
def egliMilnerLe (P : TokenPoset) (A B : List P.T) : Prop :=
  (∀ a, a ∈ A → ∃ b, b ∈ B ∧ P.le a b) ∧ (∀ b, b ∈ B → ∃ a, a ∈ A ∧ P.le a b)

/-- Egli–Milner refines Hoare: the convex order is the lower order plus the upper
    condition, which is the half that costs bounded completeness. -/
theorem egliMilner_le_hoare (P : TokenPoset) (A B : List P.T)
    (h : egliMilnerLe P A B) : hoareLe P A B := h.1

-- Axiom audit.
#print axioms hoare_join_total   -- [propext]
#print axioms hoareTokens        -- [propext, Quot.sound]
#print axioms hoarePowerdomain   -- [lem, propext, Quot.sound]


