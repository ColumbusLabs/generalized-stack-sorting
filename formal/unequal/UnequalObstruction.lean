import UnequalStack

/-! Universal original-machine rejection of the unequal-width family.

For every `2 <= r < s` and `m >= 0`, no unrestricted history of the
slot-indexed `(r,s)` machine generates `family r s m` from increasing input.
The proof follows Section 4 of `docs/infinite-basis-unequal-draft.md`:
arbitrary histories are first made lazy (`generated_rangeLazy`, proved for
arbitrary widths), then the bottom token of the first batch is forced to be
the permanent token `r-1`, kept at depth `r-1` by every relay step, and buried
at depth exactly `s` by the terminal batch. -/
namespace StackSorting.Generalized
namespace Unequal

/-- The low phase `Q_0,0,Q_1,1,...,Q_k,k` (zero-based). After it the bottom
token is below `r`, differs from every low output so far, and has `s-1`
tokens above it. -/
theorem low_phase {r s limit : Nat} (hr : 2 ≤ r) (hrs : r < s) :
    ∀ k, k + 1 ≤ r - 1 → ∀ out,
      RangeLazyRun r s limit 0 []
        ((List.range (k+1)).flatMap (fun i => [s+1+2*i, i]) ++ out) →
      ∃ z st, z < r ∧ (∀ i, i ≤ k → z ≠ i) ∧ Shape z (s-1) (s+2*(k+1)) st ∧
        RangeLazyRun r s limit (s+2*(k+1)) st out := by
  intro k
  induction k with
  | zero =>
    intro _ out h
    have h₀ : RangeLazyRun r s limit 0 [] ((s+1) :: 0 :: out) := by
      simpa using h
    obtain ⟨z, st, hzr, hs, ht⟩ := first_record (by omega) hrs h₀
    have hz0 : z ≠ 0 := by
      intro he
      subst he
      have := hs.held_bottom ht
      omega
    obtain ⟨st₁, hs₁, h₁⟩ := hs.held_other (by omega) (Ne.symm hz0) ht
    refine ⟨z, st₁, hzr, ?_, ?_, h₁⟩
    · intro i hi; omega
    · simpa using hs₁
  | succ k ih =>
    intro hk out h
    have hsplit : (List.range (k+1+1)).flatMap (fun i => [s+1+2*i, i]) ++ out =
        (List.range (k+1)).flatMap (fun i => [s+1+2*i, i]) ++
          ((s+1+2*(k+1)) :: (k+1) :: out) := by
      rw [lowPairs_succ]
      simp [List.append_assoc]
    rw [hsplit] at h
    obtain ⟨z, st, hzr, hne, hs, ht⟩ := ih (by omega) _ h
    obtain ⟨st₁, hs₁, h₁⟩ := hs.record (by omega) (by omega) ht
    have hd : s - 1 + (s+1+2*(k+1) - (s+2*(k+1))) = s := by omega
    have hn : s+1+2*(k+1)+1 = s+2*(k+1+1) := by omega
    rw [hd, hn] at hs₁
    rw [hn] at h₁
    have hzk : z ≠ k+1 := by
      intro he
      subst he
      have := hs₁.held_bottom h₁
      omega
    obtain ⟨st₂, hs₂, h₂⟩ := hs₁.held_other (by omega) (Ne.symm hzk) h₁
    refine ⟨z, st₂, hzr, ?_, hs₂, h₂⟩
    intro i hi
    by_cases hik : i ≤ k
    · exact hne i hik
    · have : i = k+1 := by omega
      subst this
      exact hzk

/-- Each ordinary relay step `A_j,E_j` keeps the permanent token `r-1` at
the bottom with exactly `r-1` tokens above it. -/
theorem relay_phase {r s limit : Nat} (hr : 2 ≤ r) (hrs : r < s) :
    ∀ m {st : List Nat} (out : List Nat), Shape (r-1) (r-1) (s+2*r-2) st →
      RangeLazyRun r s limit (s+2*r-2) st (relayPairs r s m ++ out) →
      ∃ st', Shape (r-1) (r-1) (s+2*r-2+2*m) st' ∧
        RangeLazyRun r s limit (s+2*r-2+2*m) st' out := by
  intro m
  induction m with
  | zero => intro st out hs h; exact ⟨st, hs, by simpa [relayPairs] using h⟩
  | succ m ih =>
    intro st out hs h
    have hsplit : relayPairs r s (m+1) ++ out =
        relayPairs r s m ++ ((s+2*r-1+2*m) :: (s+2*m) :: out) := by
      rw [relayPairs_succ]
      simp [List.append_assoc]
    rw [hsplit] at h
    obtain ⟨st₁, hs₁, h₁⟩ := ih _ hs h
    obtain ⟨st₂, hs₂, h₂⟩ := hs₁.record (by omega) (by omega) h₁
    have hd : r - 1 + (s+2*r-1+2*m - (s+2*r-2+2*m)) = r := by omega
    have hn : s+2*r-1+2*m+1 = s+2*r-2+2*(m+1) := by omega
    rw [hd, hn] at hs₂
    rw [hn] at h₂
    obtain ⟨st₃, hs₃, h₃⟩ := hs₂.held_other (by omega) (by omega) h₂
    exact ⟨st₃, by simpa using hs₃, h₃⟩

/-- The family, split at its phase boundaries. -/
theorem family_split (r s m : Nat) (hr : 2 ≤ r) :
    family r s m =
      (List.range (r-2+1)).flatMap (fun i => [s+1+2*i, i]) ++
        (List.range' r (s-r) ++ (relayPairs r s m ++
          ((2*s+r+2*m-1) :: (r-1) ::
            (lateRelays r s m ++ List.range' (s+2*r-2+2*m) (s-r+1))))) := by
  have hk : r - 2 + 1 = r - 1 := by omega
  rw [hk]
  simp [family, lowPairs, List.append_assoc]

/-- No unrestricted original `(r,s)` history generates the family, for any
unequal widths `2 <= r < s` and any `m`. Capacity is unbounded. -/
theorem family_not_generated (r s m : Nat) (hr : 2 ≤ r) (hrs : r < s) :
    ¬ Run r s [] (List.range (2*s+r+2*m)) (family r s m) [] := by
  intro h
  have hl := generated_rangeLazy h
  rw [family_split r s m hr] at hl
  obtain ⟨z, st, hzr, hne, hs, ht⟩ := low_phase hr hrs (r-2) (by omega) _ hl
  have hz : z = r - 1 := by
    by_cases hz : z ≤ r - 2
    · exact absurd rfl (hne z hz)
    · omega
  subst hz
  have hn : s+2*(r-2+1) = s+2*r-2 := by omega
  rw [hn] at hs ht
  -- The extra outputs r,...,s-1 are held and lie above the permanent token.
  obtain ⟨st₁, hs₁, h₁⟩ := hs.drain (List.range' r (s-r))
    (by
      intro a ha
      rw [List.mem_range'] at ha
      omega) ht
  have hd : s - 1 - (List.range' r (s-r)).length = r - 1 := by
    simp only [List.length_range']
    omega
  rw [hd] at hs₁
  obtain ⟨st₂, hs₂, h₂⟩ := relay_phase hr hrs m _ hs₁ h₁
  -- The terminal batch buries the permanent token at depth exactly s.
  obtain ⟨st₃, hs₃, h₃⟩ := hs₂.record (by omega) (by omega) h₂
  have hd' : r - 1 + (2*s+r+2*m-1 - (s+2*r-2+2*m)) = s := by omega
  rw [hd'] at hs₃
  have := hs₃.held_bottom h₃
  omega

/-- The same impossibility for the executable no-bypass machine, quantifying
over every raw slot-indexed trace. -/
theorem family_no_executable_trace (r s m : Nat) (hr : 2 ≤ r) (hrs : r < s) :
    ¬ ∃ ops, run r s ops [] = some ([], family r s m) ∧
      inputs ops = List.range (2*s+r+2*m) := by
  rw [← run_relational_iff]
  exact family_not_generated r s m hr hrs

/-- Infinitely many distinct rejected permutations for every unequal pair:
each member is a permutation of its range, the members are distinct, and
their lengths are unbounded. -/
theorem infinitely_many_rejected (r s : Nat) (hr : 2 ≤ r) (hrs : r < s) (bound : Nat) :
    ∃ m, bound < (family r s m).length ∧
      (family r s m).Perm (List.range (family r s m).length) ∧
      ¬ Run r s [] (List.range (family r s m).length) (family r s m) [] := by
  refine ⟨bound, ?_, ?_, ?_⟩
  · rw [family_length r s bound (by omega) (by omega)]; omega
  · rw [family_length r s bound (by omega) (by omega)]; exact family_perm r s bound hr hrs
  · rw [family_length r s bound (by omega) (by omega)]
    exact family_not_generated r s bound hr hrs

#print axioms low_phase
#print axioms relay_phase
#print axioms family_not_generated
#print axioms family_no_executable_trace
#print axioms infinitely_many_rejected
end Unequal
end StackSorting.Generalized
