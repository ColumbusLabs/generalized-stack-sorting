import InfiniteFamily

/-! The literal unequal-width obstruction family, zero-based.

Adding one to every entry of `family r s m` gives the one-based
`R_(r,s,m)` of `docs/infinite-basis-unequal-draft.md` (Section 2). These
definitions do not assume the family is forbidden. -/
namespace StackSorting.Generalized
namespace Unequal

/-- `Q_0,1,Q_1,2,...,Q_(r-2),r-1` (one-based) as zero-based values. -/
def lowPairs (r s : Nat) : List Nat :=
  (List.range (r-1)).flatMap (fun i => [s+1+2*i, i])

/-- The ordinary relay steps `A_j,E_j`, `0 <= j < m`, zero-based. -/
def relayPairs (r s m : Nat) : List Nat :=
  (List.range m).flatMap (fun j => [s+2*r-1+2*j, s+2*j])

/-- The relays `E_m,...,E_(m+r-2)` output after the permanent token. -/
def lateRelays (r s m : Nat) : List Nat :=
  (List.range (r-1)).map (fun j => s+2*(m+j))

/-- Zero-based `R_(r,s,m)`: the permanent token is `r-1`, the final record is
`2s+r+2m-1`, and the length is `2s+r+2m`. -/
def family (r s m : Nat) : List Nat :=
  lowPairs r s ++ List.range' r (s-r) ++ relayPairs r s m ++
    [2*s+r+2*m-1, r-1] ++ lateRelays r s m ++ List.range' (s+2*r-2+2*m) (s-r+1)

theorem lowPairs_succ (s k : Nat) :
    (List.range (k+1)).flatMap (fun i => [s+1+2*i, i]) =
      (List.range k).flatMap (fun i => [s+1+2*i, i]) ++ [s+1+2*k, k] := by
  simp [List.range_succ, List.flatMap_append]

theorem relayPairs_succ (r s m : Nat) :
    relayPairs r s (m+1) = relayPairs r s m ++ [s+2*r-1+2*m, s+2*m] := by
  simp [relayPairs, List.range_succ, List.flatMap_append]

theorem flatMap_pair_length (f g : Nat → Nat) (k : Nat) :
    ((List.range k).flatMap (fun i => [f i, g i])).length = 2*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.range_succ, List.flatMap_append, ih]; omega

theorem family_length (r s m : Nat) (hr : 1 ≤ r) (hrs : r ≤ s) :
    (family r s m).length = 2*s+r+2*m := by
  have h₁ := flatMap_pair_length (fun i => s+1+2*i) (fun i => i) (r-1)
  have h₂ := flatMap_pair_length (fun j => s+2*r-1+2*j) (fun j => s+2*j) m
  simp only [family, lowPairs, relayPairs, lateRelays, List.length_append,
    List.length_range', List.length_map, List.length_range, List.length_cons,
    List.length_nil] at h₁ h₂ ⊢
  rw [h₁, h₂]
  omega

/-- Pigeonhole for `range`: a list of length `n` containing every `x < n`
is a permutation of `range n`. -/
theorem perm_range_of_mem (n : Nat) (l : List Nat) (hl : l.length = n)
    (hm : ∀ x, x < n → x ∈ l) : l.Perm (List.range n) := by
  induction n generalizing l with
  | zero =>
    have : l = [] := List.eq_nil_of_length_eq_zero hl
    subst this
    exact List.Perm.refl _
  | succ n ih =>
    have hn : n ∈ l := hm n (by omega)
    have hlen : (l.erase n).length = n := by
      rw [List.length_erase_of_mem hn, hl]; rfl
    have hsub : ∀ x, x < n → x ∈ l.erase n := by
      intro x hx
      exact (List.mem_erase_of_ne (by omega)).mpr (hm x (by omega))
    have hp := ih (l.erase n) hlen hsub
    have h₁ := List.perm_cons_erase hn
    have h₂ : (n :: l.erase n).Perm (n :: List.range n) := List.Perm.cons n hp
    have h₃ : (n :: List.range n).Perm (List.range (n+1)) := by
      rw [List.range_succ]
      exact (List.perm_append_singleton n (List.range n)).symm
    exact h₁.trans (h₂.trans h₃)

theorem mem_lowPairs_record (r s k : Nat) (hk : k < r-1) :
    s+1+2*k ∈ lowPairs r s := by
  simp only [lowPairs, List.mem_flatMap, List.mem_range]
  exact ⟨k, hk, by simp⟩

theorem mem_lowPairs_low (r s k : Nat) (hk : k < r-1) : k ∈ lowPairs r s := by
  simp only [lowPairs, List.mem_flatMap, List.mem_range]
  exact ⟨k, hk, by simp⟩

theorem mem_relayPairs_record (r s m j : Nat) (hj : j < m) :
    s+2*r-1+2*j ∈ relayPairs r s m := by
  simp only [relayPairs, List.mem_flatMap, List.mem_range]
  exact ⟨j, hj, by simp⟩

theorem mem_relayPairs_relay (r s m j : Nat) (hj : j < m) :
    s+2*j ∈ relayPairs r s m := by
  simp only [relayPairs, List.mem_flatMap, List.mem_range]
  exact ⟨j, hj, by simp⟩

theorem mem_lateRelays (r s m j : Nat) (hj : j < r-1) :
    s+2*(m+j) ∈ lateRelays r s m := by
  simp only [lateRelays, List.mem_map, List.mem_range]
  exact ⟨j, hj, rfl⟩

theorem family_cover (r s m : Nat) (hr : 2 ≤ r) (hrs : r < s) (x : Nat)
    (hx : x < 2*s+r+2*m) : x ∈ family r s m := by
  simp only [family, List.mem_append, List.mem_cons, List.mem_range', List.not_mem_nil]
  by_cases h₀ : x < r-1
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (mem_lowPairs_low r s x h₀)))))
  by_cases h₁ : x = r-1
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h₁))))
  by_cases h₂ : x < s
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x-r, by omega, by omega⟩))))
  by_cases h₃ : x < s+2*r-2+2*m
  · rcases Nat.mod_two_eq_zero_or_one (x-s) with he | ho
    · -- an E relay, s + 2j
      have hx' : x = s+2*((x-s)/2) := by omega
      by_cases hj : (x-s)/2 < m
      · rw [hx']
        exact Or.inl (Or.inl (Or.inl (Or.inr (mem_relayPairs_relay r s m _ hj))))
      · have hx'' : x = s+2*(m+((x-s)/2-m)) := by omega
        rw [hx'']
        exact Or.inl (Or.inr (mem_lateRelays r s m _ (by omega)))
    · -- a record, s + 1 + 2k
      by_cases hk : (x-s)/2 < r-1
      · have hx' : x = s+1+2*((x-s)/2) := by omega
        rw [hx']
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (mem_lowPairs_record r s _ hk)))))
      · have hx' : x = s+2*r-1+2*((x-s)/2-(r-1)) := by omega
        rw [hx']
        exact Or.inl (Or.inl (Or.inl (Or.inr (mem_relayPairs_record r s m _ (by omega)))))
  by_cases h₄ : x = 2*s+r+2*m-1
  · exact Or.inl (Or.inl (Or.inr (Or.inl h₄)))
  · exact Or.inr ⟨x-(s+2*r-2+2*m), by omega, by omega⟩

theorem family_perm (r s m : Nat) (hr : 2 ≤ r) (hrs : r < s) :
    (family r s m).Perm (List.range (2*s+r+2*m)) :=
  perm_range_of_mem _ _ (family_length r s m (by omega) (by omega))
    (family_cover r s m hr hrs)

theorem family_nodup (r s m : Nat) (hr : 2 ≤ r) (hrs : r < s) :
    (family r s m).Nodup :=
  (family_perm r s m hr hrs).nodup_iff.mpr List.nodup_range

theorem family_injective (r s : Nat) (hr : 2 ≤ r) (hrs : r < s) :
    Function.Injective (family r s) := by
  intro m k he
  have hl := congrArg List.length he
  rw [family_length r s m (by omega) (by omega),
    family_length r s k (by omega) (by omega)] at hl
  omega

/-- At push width two the family is literally the earlier `(2,s)` family. -/
theorem family_two (s m : Nat) (hs : 2 ≤ s) : family 2 s m = BasisFamily.rho s m := by
  have hf : (fun j => [s+2*2-1+2*j, s+2*j]) = (fun j => [s+3+2*j, s+2*j]) := by
    funext j
    have he : s+2*2-1+2*j = s+3+2*j := by omega
    rw [he]
  have hp : relayPairs 2 s m = BasisFamily.pairs s m := by
    simp only [relayPairs, BasisFamily.pairs, hf]
  simp [family, lowPairs, hp, lateRelays, BasisFamily.rho, List.append_assoc]
  omega

/-- Zero-based form of the draft's displayed `(3,4)` examples. -/
example : family 3 4 0 = [5,0,7,1,3,10,2,4,6,8,9] := by decide
example : family 3 4 1 = [5,0,7,1,3,9,4,12,2,6,8,10,11] := by decide

#print axioms family_length
#print axioms family_perm
#print axioms family_injective
#print axioms family_two
end Unequal
end StackSorting.Generalized
