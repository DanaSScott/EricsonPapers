/- ================================================================
   Shared enumeration machinery: lists of bounded length.

   Part of the Scott domain catalogue; see ../docs/ScottDomainExamples.md
   and Domains/ScottDomainExamples.lean, which imports every part.
   ================================================================ -/

/- Countability. `dtoksUpTo n` holds every token of height ≤ n whose step-sets have
   length ≤ n over tokens already listed; `listsUpTo` is the list-of-length-≤-k
   construction it needs. The covering proof is a **mutual** recursion over `DTok`
   and its list, which is what the nested inductive calls for. -/

def listsUpTo {α : Type} (xs : List α) : Nat → List (List α)
  | 0     => [[]]
  | k + 1 => listsUpTo xs k ++ xs.flatMap (fun a => (listsUpTo xs k).map (fun l => a :: l))

theorem nil_mem_listsUpTo {α : Type} (xs : List α) :
    ∀ k, [] ∈ listsUpTo xs k := by
  intro k
  induction k with
  | zero   => exact List.Mem.head _
  | succ k ih => exact List.mem_append.mpr (Or.inl ih)

theorem mem_listsUpTo {α : Type} (xs : List α) :
    ∀ (k : Nat) (l : List α), l.length ≤ k → (∀ a, a ∈ l → a ∈ xs) → l ∈ listsUpTo xs k := by
  intro k
  induction k with
  | zero =>
      intro l hlen _
      cases l with
      | nil       => exact List.Mem.head _
      | cons _ _  => exact absurd hlen (by simp)
  | succ k ih =>
      intro l hlen hmem
      cases l with
      | nil => exact nil_mem_listsUpTo xs (k + 1)
      | cons a t =>
          refine List.mem_append.mpr (Or.inr ?_)
          refine List.mem_flatMap.mpr ⟨a, hmem a (List.Mem.head _), ?_⟩
          refine List.mem_map.mpr ⟨t, ih t (by simp at hlen; omega) ?_, rfl⟩
          intro b hb
          exact hmem b (List.Mem.tail _ hb)
