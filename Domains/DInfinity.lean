/- ================================================================
   §5.5, the D∞ tower and the bilimit.

   Part of the Scott domain catalogue; see ../docs/ScottDomainExamples.md
   and Domains/ScottDomainExamples.lean, which imports every part.
   ================================================================ -/

import Domains.FunctionSpace
import Domains.Enumeration

/- ----------------------------------------------------------------
   §5.5 — the D∞ tower

   `D₀ = 𝕊`, `Dₙ₊₁ = [Dₙ → Dₙ]`, with the embeddings that connect them.
   Each level is a Scott domain by `towerDomain`.

   The step is available because §5.1's function space closes on
   `JoinTokens`: the tokens of [D → D] are lists of step functions and
   their join is concatenation, which is total, so `funJoin` carries a
   `JoinTokens` to a `JoinTokens` and the tower can be iterated. `D₀`
   is 𝕊, a lattice, which is Scott's own 1972 setting; starting from a
   non-lattice D₀ is what makes the catalogue's §2 row say D∞ is not a
   lattice.

   The embedding is the token-level `e(x) = λy.x`: the one-element step
   function ⊥ ↦ t, which `emb_mono` shows is monotone.

   **Not built: the bilimit itself.** See the note after `emb_mono`.
   ---------------------------------------------------------------- -/

/-- [Q → Q] again carries total joins — concatenation — so the tower can iterate. -/
def funJoin (Q : JoinTokens) : JoinTokens where
  base := funTokens Q.base Q.base
  join := fun l m => List.append l m
  le_join_left := by
    intro l m a b hab v hv
    exact hv a b (List.mem_append.mpr (Or.inl hab)) (Q.base.le_refl a)
  le_join_right := by
    intro l m a b hab v hv
    exact hv a b (List.mem_append.mpr (Or.inr hab)) (Q.base.le_refl a)
  join_least := by
    intro l m z hlz hmz a b hab
    rcases List.mem_append.mp hab with h | h
    · exact hlz a b h
    · exact hmz a b h

/-- The tower `D₀ = 𝕊`, `Dₙ₊₁ = [Dₙ → Dₙ]`. -/
def tower : Nat → JoinTokens
  | 0     => sierpTokens
  | n + 1 => funJoin (tower n)

/-- Every level is a Scott domain. -/
def towerDomain (n : Nat) : DInfinityFoundations (TokenIdeal (tower n).base) :=
  idealDomain (tower n).base

/-- The embedding `e(x) = λy.x`, at token level the step function ⊥ ↦ t. -/
def emb (n : Nat) (t : (tower n).base.T) : (tower (n + 1)).base.T :=
  [((tower n).base.bot, t)]

theorem emb_mono (n : Nat) (t u : (tower n).base.T) (h : (tower n).base.le t u) :
    (tower (n + 1)).base.le (emb n t) (emb n u) := by
  intro a b hab v hv
  cases hab with
  | head =>
      exact (tower n).base.le_trans t u v h
        (hv (tower n).base.bot u (List.Mem.head _) ((tower n).base.le_refl _))
  | tail _ hh => cases hh

/-- Iterated embedding into a later level. Stated as `n + k` rather than with a
    `n ≤ m` hypothesis, so that `tower (n + (k+1))` and `tower ((n+k) + 1)` are the
    *same* type definitionally and no transport is needed. -/
def liftTok (n : Nat) : (k : Nat) → (tower n).base.T → (tower (n + k)).base.T
  | 0,     t => t
  | k + 1, t => emb (n + k) (liftTok n k t)

theorem liftTok_mono (n : Nat) :
    ∀ (k : Nat) (t u : (tower n).base.T), (tower n).base.le t u →
      (tower (n + k)).base.le (liftTok n k t) (liftTok n k u) := by
  intro k
  induction k with
  | zero => intro t u h; exact h
  | succ k ih =>
      intro t u h
      exact emb_mono (n + k) _ _ (ih t u h)

/- ----------------------------------------------------------------
   Where this stops, and why.

   D∞ is the colimit of the tower along these embeddings. Its tokens
   are `Σ n, (tower n).base.T`, and the order compares two tokens after
   lifting both to a common level:

       ⟨n, t⟩ ⊑ ⟨m, u⟩   iff   liftTok n k₁ t ⊑ liftTok m k₂ u
                               for some k₁, k₂ with n + k₁ = m + k₂.

   `liftTok` is stated additively precisely so that each single step
   typechecks without transport. The comparison above cannot be: the
   two sides live in `tower (n + k₁)` and `tower (m + k₂)`, which are
   equal only *propositionally*, via `n + k₁ = m + k₂`. So the relation
   needs `h ▸ …`, and then every law — reflexivity is fine, but
   transitivity, `bounded_lub`, and `enum_onto` — has to compose
   transports and appeal to `Nat.add_assoc` as a propositional type
   equality. That bookkeeping, not the mathematics, is the obstacle.

   The route that avoids it is a redesign rather than a continuation:
   give the tower a *level-indexed inductive token type*, so that a
   single type carries all levels and cross-level comparison is
   structural recursion instead of transport. That is the next step,
   and it is a substantial one — this is the boundary reached, stated
   rather than papered over.
   ---------------------------------------------------------------- -/

-- Axiom audit.
#print axioms funJoin      -- [propext, Quot.sound]
#print axioms tower        -- [propext, Quot.sound]
#print axioms emb_mono     -- [propext, Quot.sound]
#print axioms liftTok_mono -- [propext, Quot.sound]
#print axioms towerDomain  -- [lem, propext, Quot.sound]


/- ----------------------------------------------------------------
   §5.5 revisited — the flat encoding that unblocks the bilimit

   The tower above stopped at the colimit for a type-theoretic reason,
   not a mathematical one: tokens at levels n and m live in *different
   types*, `tower (n+k₁)` and `tower (m+k₂)`, equal only propositionally,
   so every law had to compose transports.

   This is the redesign that removes it. Keep **one flat token type**,
   with the level carried not by the type but by the *order*:

       DTok            — one type, all levels
       leAt : Nat → DTok → DTok → Prop

   `leAt n` is the order of Dₙ, defined by recursion on n, so the
   comparison of any two tokens at any level is a `Prop` about two
   ordinary terms. No indices, no casts.

   The other half of the trick is `stepOf`, which reads *any* token as
   a finite set of step functions — a base token through one
   application of e(x) = λy.x, with ⊥ read as the empty set, which is
   λy.⊥. That is what lets a single recursion handle levels uniformly
   rather than by case analysis on which token is "lower".
   ---------------------------------------------------------------- -/

inductive DTok where
  | bot  : DTok
  | top  : DTok
  | step : List (DTok × DTok) → DTok

def isTopTok : DTok → Bool
  | .top => true
  | _    => false

/-- Any token read as a finite set of step functions: ⊥ as the empty set (λy.⊥),
    ⊤ through one embedding (λy.⊤), a step set as itself. -/
def stepOf : DTok → List (DTok × DTok)
  | .bot    => []
  | .top    => [(.bot, .top)]
  | .step l => l

/-- The order of Dₙ. At level 0 it is 𝕊's; at level n+1 it is §5.1's entailment
    between step-function sets, phrased over `leAt n`. -/
def leAt : Nat → DTok → DTok → Prop
  | 0,     x, y => isTopTok x = true → isTopTok y = true
  | n + 1, x, y =>
      ∀ a b, (a, b) ∈ stepOf x →
        ∀ v, (∀ a' b', (a', b') ∈ stepOf y → leAt n a' a → leAt n b' v) → leAt n b v

theorem leAt_refl : ∀ (n : Nat) (x : DTok), leAt n x x := by
  intro n
  induction n with
  | zero => intro x h; exact h
  | succ n ih =>
      intro x a b hab v hv
      exact hv a b hab (ih a)

theorem leAt_trans : ∀ (n : Nat) (x y z : DTok), leAt n x y → leAt n y z → leAt n x z := by
  intro n
  induction n with
  | zero => intro x y z hxy hyz h; exact hyz (hxy h)
  | succ n ih =>
      intro x y z hxy hyz a b hab v hv
      refine hxy a b hab v ?_
      intro a' b' hmem ha'
      refine hyz a' b' hmem v ?_
      intro a'' b'' hmem'' ha''
      exact hv a'' b'' hmem'' (ih a'' a' a ha'' ha')

/-- The embedding e(x) = λy.x, in the flat encoding. -/
def embTok (x : DTok) : DTok := .step [(.bot, x)]

/-- **e is an order-embedding**: comparing at level n+1 after embedding is exactly
    comparing at level n. This is the coherence the colimit runs on, and in the
    indexed encoding it was the statement that could not be written without
    transport. -/
theorem leAt_embTok (n : Nat) (x y : DTok) :
    leAt (n + 1) (embTok x) (embTok y) ↔ leAt n x y := by
  constructor
  · intro h
    refine h .bot x (List.Mem.head _) y ?_
    intro a' b' hmem ha'
    cases hmem with
    | head      => exact leAt_refl n y
    | tail _ hh => cases hh
  · intro h a b hab v hv
    cases hab with
    | head =>
        refine leAt_trans n x y v h ?_
        exact hv .bot y (List.Mem.head _) (leAt_refl n .bot)
    | tail _ hh => cases hh

/-- ⊥ is below everything at every level: at level 0 the implication is vacuous,
    at level n+1 `stepOf ⊥` is empty. -/
theorem leAt_bot_le : ∀ (n : Nat) (v : DTok), leAt n .bot v := by
  intro n
  cases n with
  | zero   => intro v h; exact Bool.noConfusion h
  | succ n => intro v a b hab; cases hab

/- ----------------------------------------------------------------
   D∞ itself.

   A token is a pair `(n, x) : Nat × DTok` — a **declared level** and a
   token — compared after lifting both to the max of the declared
   levels. No subtype and no dependent type, so every law is ordinary
   `Prop` work.

   Nothing forces `x` to be well formed at level n. It need not: a
   token declared too low is compared at that low level, where `leAt`
   reads it through `isTopTok`, making it order-equivalent to ⊥. Extra
   copies of ⊥ change no ideal, so the completion is unaffected — and
   this is what lets the carrier be a plain product.
   ---------------------------------------------------------------- -/

def embIter : Nat → DTok → DTok
  | 0,     x => x
  | k + 1, x => embTok (embIter k x)

theorem embIter_add : ∀ (a b : Nat) (x : DTok),
    embIter (a + b) x = embIter a (embIter b x) := by
  intro a
  induction a with
  | zero =>
      intro b x
      show embIter (0 + b) x = embIter b x
      rw [Nat.zero_add]
  | succ a ih =>
      intro b x
      rw [Nat.succ_add]
      show embTok (embIter (a + b) x) = embTok (embIter a (embIter b x))
      rw [ih b x]

theorem leAt_embIter_bot : ∀ (N k : Nat) (v : DTok), leAt N (embIter k .bot) v := by
  intro N
  induction N with
  | zero =>
      intro k v h
      cases k with
      | zero   => exact Bool.noConfusion h
      | succ _ => exact Bool.noConfusion h
  | succ N ih =>
      intro k v a b hab
      cases k with
      | zero => cases hab
      | succ k =>
          cases hab with
          | head =>
              intro w _
              exact ih k w
          | tail _ hh => cases hh

/-- Comparison of two tokens at a level above both declared levels. -/
def cmpTok (N n m : Nat) (x y : DTok) : Prop :=
  leAt N (embIter (N - n) x) (embIter (N - m) y)

/-- **Stability**: raising the comparison level by one changes nothing. This is
    `leAt_embTok` with the arithmetic that the extra lift is exactly one more
    embedding on each side. -/
theorem cmpTok_up (N n m : Nat) (x y : DTok) (hn : n ≤ N) (hm : m ≤ N) :
    cmpTok N n m x y ↔ cmpTok (N + 1) n m x y := by
  have h1 : N + 1 - n = (N - n) + 1 := by omega
  have h2 : N + 1 - m = (N - m) + 1 := by omega
  show leAt N (embIter (N - n) x) (embIter (N - m) y) ↔
       leAt (N + 1) (embIter (N + 1 - n) x) (embIter (N + 1 - m) y)
  rw [h1, h2]
  exact (leAt_embTok N _ _).symm

theorem cmpTok_add (n m : Nat) (x y : DTok) :
    ∀ (d N : Nat), n ≤ N → m ≤ N → (cmpTok N n m x y ↔ cmpTok (N + d) n m x y) := by
  intro d
  induction d with
  | zero => intro N _ _; exact Iff.rfl
  | succ d ih =>
      intro N hn hm
      refine (ih N hn hm).trans ?_
      have : N + (d + 1) = (N + d) + 1 := by omega
      rw [this]
      exact cmpTok_up (N + d) n m x y (by omega) (by omega)

/-- Any two admissible comparison levels agree. -/
theorem cmpTok_eq (n m : Nat) (x y : DTok) (N M : Nat)
    (hnN : n ≤ N) (hmN : m ≤ N) (hnM : n ≤ M) (hmM : m ≤ M) :
    cmpTok N n m x y ↔ cmpTok M n m x y := by
  rcases Nat.le_total N M with h | h
  · have : M = N + (M - N) := by omega
    rw [this]
    exact cmpTok_add n m x y (M - N) N hnN hmN
  · have : N = M + (N - M) := by omega
    rw [this]
    exact (cmpTok_add n m x y (N - M) M hnM hmM).symm

/-- The order on D∞ tokens. -/
def dLe (p q : Nat × DTok) : Prop := cmpTok (max p.1 q.1) p.1 q.1 p.2 q.2

theorem dLe_refl (p : Nat × DTok) : dLe p p := by
  show leAt (max p.1 p.1) (embIter (max p.1 p.1 - p.1) p.2) (embIter (max p.1 p.1 - p.1) p.2)
  exact leAt_refl _ _

theorem dLe_trans (p q r : Nat × DTok) (hpq : dLe p q) (hqr : dLe q r) : dLe p r := by
  have h1 : cmpTok (max (max p.1 q.1) (max q.1 r.1)) p.1 q.1 p.2 q.2 :=
    (cmpTok_eq p.1 q.1 p.2 q.2 (max p.1 q.1) _ (by omega) (by omega)
      (by omega) (by omega)).mp hpq
  have h2 : cmpTok (max (max p.1 q.1) (max q.1 r.1)) q.1 r.1 q.2 r.2 :=
    (cmpTok_eq q.1 r.1 q.2 r.2 (max q.1 r.1) _ (by omega) (by omega)
      (by omega) (by omega)).mp hqr
  have h3 : cmpTok (max (max p.1 q.1) (max q.1 r.1)) p.1 r.1 p.2 r.2 :=
    leAt_trans _ _ _ _ h1 h2
  exact (cmpTok_eq p.1 r.1 p.2 r.2 _ (max p.1 r.1) (by omega) (by omega)
    (by omega) (by omega)).mp h3

theorem dLe_bot (p : Nat × DTok) : dLe (0, DTok.bot) p := by
  show leAt (max 0 p.1) (embIter (max 0 p.1 - 0) DTok.bot) (embIter (max 0 p.1 - p.1) p.2)
  exact leAt_embIter_bot _ _ _

/-- The join is concatenation of step-sets, and it survives lifting: the induction
    is on the number of lifts, with the comparison level dropping alongside. -/
theorem joinLift : ∀ (k L : Nat) (x y z : DTok),
    leAt L (embIter k x) z → leAt L (embIter k y) z →
    leAt L (embIter k (.step (stepOf x ++ stepOf y))) z := by
  intro k
  induction k with
  | zero =>
      intro L x y z hx hy
      cases L with
      | zero => intro h; exact Bool.noConfusion h
      | succ L =>
          intro a b hab v hv
          rcases List.mem_append.mp hab with h | h
          · exact hx a b h v hv
          · exact hy a b h v hv
  | succ k ih =>
      intro L x y z hx hy
      cases L with
      | zero => intro h; exact Bool.noConfusion h
      | succ L =>
          intro a b hab v hv
          cases hab with
          | head =>
              refine ih L x y v ?_ ?_
              · exact hx .bot (embIter k x) (List.Mem.head _) v hv
              · exact hy .bot (embIter k y) (List.Mem.head _) v hv
          | tail _ hh => cases hh

/-- Every pair of tokens has a least upper bound, so D∞'s tokens have total joins —
    inherited from `D₀ = 𝕊` being a lattice. -/
theorem dLe_lub (p q : Nat × DTok) :
    ∃ u, dLe p u ∧ dLe q u ∧ ∀ w, dLe p w → dLe q w → dLe u w := by
  rcases Nat.eq_zero_or_pos (max p.1 q.1) with hN | hN
  · -- both declared at level 0: `leAt 0` reads them through `isTopTok`
    have hp1 : p.1 = 0 := by omega
    have hq1 : q.1 = 0 := by omega
    cases hp : isTopTok p.2 with
    | true =>
        refine ⟨p, dLe_refl p, ?_, fun w hw _ => hw⟩
        show leAt (max q.1 p.1) (embIter (max q.1 p.1 - q.1) q.2)
               (embIter (max q.1 p.1 - p.1) p.2)
        rw [hp1, hq1]
        show leAt 0 q.2 p.2
        intro _
        exact hp
    | false =>
        refine ⟨q, ?_, dLe_refl q, fun w _ hw => hw⟩
        show leAt (max p.1 q.1) (embIter (max p.1 q.1 - p.1) p.2)
               (embIter (max p.1 q.1 - q.1) q.2)
        rw [hp1, hq1]
        show leAt 0 p.2 q.2
        intro h
        rw [hp] at h
        exact Bool.noConfusion h
  · -- at a positive level the join is the concatenation of the step-sets
    refine ⟨(max p.1 q.1,
             .step (stepOf (embIter (max p.1 q.1 - p.1) p.2) ++
                    stepOf (embIter (max p.1 q.1 - q.1) q.2))), ?_, ?_, ?_⟩
    · show leAt (max p.1 (max p.1 q.1))
             (embIter (max p.1 (max p.1 q.1) - p.1) p.2)
             (embIter (max p.1 (max p.1 q.1) - max p.1 q.1) _)
      have he : max p.1 (max p.1 q.1) = max p.1 q.1 := by omega
      rw [he]
      have hz : max p.1 q.1 - max p.1 q.1 = 0 := by omega
      rw [hz]
      cases hK : max p.1 q.1 with
      | zero => exact absurd hN (by omega)
      | succ K =>
          intro a b hab v hv
          exact hv a b (List.mem_append.mpr (Or.inl hab)) (leAt_refl K a)
    · show leAt (max q.1 (max p.1 q.1))
             (embIter (max q.1 (max p.1 q.1) - q.1) q.2)
             (embIter (max q.1 (max p.1 q.1) - max p.1 q.1) _)
      have he : max q.1 (max p.1 q.1) = max p.1 q.1 := by omega
      rw [he]
      have hz : max p.1 q.1 - max p.1 q.1 = 0 := by omega
      rw [hz]
      cases hK : max p.1 q.1 with
      | zero => exact absurd hN (by omega)
      | succ K =>
          intro a b hab v hv
          exact hv a b (List.mem_append.mpr (Or.inr hab)) (leAt_refl K a)
    · intro w hpw hqw
      have hL1 : cmpTok (max (max p.1 q.1) w.1) p.1 w.1 p.2 w.2 :=
        (cmpTok_eq p.1 w.1 p.2 w.2 (max p.1 w.1) _ (by omega) (by omega)
          (by omega) (by omega)).mp hpw
      have hL2 : cmpTok (max (max p.1 q.1) w.1) q.1 w.1 q.2 w.2 :=
        (cmpTok_eq q.1 w.1 q.2 w.2 (max q.1 w.1) _ (by omega) (by omega)
          (by omega) (by omega)).mp hqw
      have hsplit1 : max (max p.1 q.1) w.1 - p.1
          = (max (max p.1 q.1) w.1 - max p.1 q.1) + (max p.1 q.1 - p.1) := by omega
      have hsplit2 : max (max p.1 q.1) w.1 - q.1
          = (max (max p.1 q.1) w.1 - max p.1 q.1) + (max p.1 q.1 - q.1) := by omega
      rw [cmpTok, hsplit1, embIter_add] at hL1
      rw [cmpTok, hsplit2, embIter_add] at hL2
      show leAt (max (max p.1 q.1) w.1)
             (embIter (max (max p.1 q.1) w.1 - max p.1 q.1) _)
             (embIter (max (max p.1 q.1) w.1 - w.1) w.2)
      exact joinLift _ _ _ _ _ hL1 hL2


def dtokPairs (prev : List DTok) : List (DTok × DTok) :=
  prev.flatMap (fun a => prev.map (fun b => (a, b)))

def dtoksUpTo : Nat → List DTok
  | 0     => [DTok.bot, DTok.top]
  | n + 1 => dtoksUpTo n ++ (listsUpTo (dtokPairs (dtoksUpTo n)) (n + 1)).map DTok.step

theorem dtoksUpTo_mono : ∀ (n m : Nat) (x : DTok),
    n ≤ m → x ∈ dtoksUpTo n → x ∈ dtoksUpTo m := by
  intro n m
  induction m with
  | zero => intro x h hx; have : n = 0 := by omega
            subst this; exact hx
  | succ m ih =>
      intro x h hx
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · exact List.mem_append.mpr (Or.inl (ih x (by omega) hx))
      · have : n = m + 1 := by omega
        subst this
        exact hx

mutual

theorem dtoksUpTo_covers : ∀ x : DTok, ∃ n, x ∈ dtoksUpTo n
  | .bot    => ⟨0, List.Mem.head _⟩
  | .top    => ⟨0, List.Mem.tail _ (List.Mem.head _)⟩
  | .step l => by
      obtain ⟨n, hpairs, hlen⟩ := dtoksUpTo_covers_list l
      refine ⟨n + 1, List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨l, ?_, rfl⟩))⟩
      refine mem_listsUpTo _ (n + 1) l (by omega) ?_
      intro p hp
      obtain ⟨h1, h2⟩ := hpairs p hp
      exact List.mem_flatMap.mpr ⟨p.1, h1, List.mem_map.mpr ⟨p.2, h2, rfl⟩⟩

theorem dtoksUpTo_covers_list : ∀ l : List (DTok × DTok),
    ∃ n, (∀ p, p ∈ l → p.1 ∈ dtoksUpTo n ∧ p.2 ∈ dtoksUpTo n) ∧ l.length ≤ n
  | []     => ⟨0, (by intro p hp; cases hp), by simp⟩
  | p :: t => by
      obtain ⟨n1, h1⟩ := dtoksUpTo_covers p.1
      obtain ⟨n2, h2⟩ := dtoksUpTo_covers p.2
      obtain ⟨n3, h3, h4⟩ := dtoksUpTo_covers_list t
      refine ⟨max (max n1 n2) (n3 + 1), ?_, ?_⟩
      · intro q hq
        cases hq with
        | head =>
            exact ⟨dtoksUpTo_mono n1 _ p.1 (by omega) h1,
                   dtoksUpTo_mono n2 _ p.2 (by omega) h2⟩
        | tail _ hq' =>
            obtain ⟨g1, g2⟩ := h3 q hq'
            exact ⟨dtoksUpTo_mono n3 _ q.1 (by omega) g1,
                   dtoksUpTo_mono n3 _ q.2 (by omega) g2⟩
      · simp only [List.length_cons]
        omega

end

/-- The enumeration: k codes a level, a height bound, and an index into the tokens
    of that height. -/
def dInfEnum (k : Nat) : Nat × DTok :=
  ((pairDecode k).1,
   (dtoksUpTo (pairDecode (pairDecode k).2).1).getD (pairDecode (pairDecode k).2).2 DTok.bot)

/-- D∞'s tokens: a declared level and a token, ordered by comparison at the max of
    the declared levels. -/
def dInfTokens : TokenPoset where
  T           := Nat × DTok
  le          := dLe
  le_refl     := dLe_refl
  le_trans    := dLe_trans
  bot         := (0, DTok.bot)
  bot_le      := dLe_bot
  enum        := dInfEnum
  bounded_lub := fun a b _ => dLe_lub a b
  enum_onto   := by
    intro a
    obtain ⟨n, hn⟩ := dtoksUpTo_covers a.2
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hn
    obtain ⟨rest, hrest⟩ := pairDecode_hits (n + i) i n rfl
    obtain ⟨k, hk⟩ := pairDecode_hits (a.1 + rest) rest a.1 rfl
    have heq : dInfEnum k = a := by
      show ((pairDecode k).1,
        (dtoksUpTo (pairDecode (pairDecode k).2).1).getD
          (pairDecode (pairDecode k).2).2 DTok.bot) = a
      rw [hk]
      show (a.1, (dtoksUpTo (pairDecode rest).1).getD (pairDecode rest).2 DTok.bot) = a
      rw [hrest]
      show (a.1, (dtoksUpTo n).getD i DTok.bot) = a
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hget]
      rfl
    refine ⟨k, ?_, ?_⟩
    · rw [show dInfEnum k = a from heq]
      exact dLe_refl a
    · rw [show dInfEnum k = a from heq]
      exact dLe_refl a

/-- **D∞**, at last: the ideal completion of the tokens of the tower
    `D₀ = 𝕊`, `Dₙ₊₁ = [Dₙ → Dₙ]`, satisfying D1–D4. -/
def dInfinity : DInfinityFoundations (TokenIdeal dInfTokens) := idealDomain dInfTokens

/- Axiom audit for the flat encoding and the bilimit. `dInfinity` consumes exactly
   what every other witness here does — `[lem, propext, Quot.sound]`, the `lem`
   entering through `idealDomain`'s D2 — and in particular **no `Classical.choice`**.

   That last point took a measurement to secure. An earlier version of `dLe_lub`
   discharged an impossible branch with a bare `omega` whose *goal was not
   arithmetic*; omega closes such a goal through `Classical.byContradiction`, which
   pulled choice into D∞ and from there into nothing else — but it would have been
   the development's first use. Replacing it with `absurd hN (by omega)`, where
   omega proves the arithmetic fact and `absurd` does the eliminating, removes it. -/
#print axioms leAt_refl     -- [propext]
#print axioms leAt_trans    -- [propext]
#print axioms leAt_embTok   -- [propext]
#print axioms leAt_bot_le   -- [propext]
#print axioms joinLift      -- [propext]
#print axioms dLe_lub       -- [propext, Quot.sound]
#print axioms dtoksUpTo_covers -- [propext, Quot.sound]
#print axioms dInfTokens    -- [propext, Quot.sound]
#print axioms dInfinity     -- [lem, propext, Quot.sound]


