import UnequalPatterns

/-! The equal-width obstruction families `A_r(k)` and `B_r(k)`, zero-based.

Adding one to every entry of `famA r k` (resp. `famB r k`) gives the one-based
`A_r(k)` (resp. `B_r(k)`) of `docs/infinite-basis-equal-width-draft.md`,
Section 2. In zero-based labels, with `r >= 3`:
- the low pairs are `Q_i = r+1+2i, i` for `i < r-1` (`Unequal.lowSeg r 0 (r-1)`);
- the relays are `E_i = r+2i` for `i <= r-2`, and `P = r-1`;
- `C = 3r-2`, `U = 3r-1`, `M1 = 3r`, `V = 3r+1`, `M2 = 3r+2`;
- step `j` outputs `R_j = 3r+5+3j`, `a_j = 3r+3+3j` and the queue head `qv r j`,
  and `b_j = 3r+4+3j` joins the queue.
These definitions do not assume the families are forbidden. -/
namespace StackSorting.Generalized
namespace Equal
open Unequal (lowSeg mem_lowSeg length_lowSeg perm_range_of_mem)

/-- The queue stream: `qv r j` is the old token output third in step `j`.
Its values are `E_2,...,E_(r-2)`, then `V = 3r+1`, then `b_0, b_1, ...`
(note `3j+10 = b_(j-(r-2))`, and `3(r-3)+10 = V`). -/
def qv (r j : Nat) : Nat := if j + 3 < r then r+4+2*j else 3*j+10

/-- `E_0, M1, P, M2, U, E_1`. -/
def prefixTail (r : Nat) : List Nat := [r, 3*r, r-1, 3*r+2, 3*r-1, r+2]

/-- Steps `a,...,a+c-1`, each `R_j, a_j, qv r j`. -/
def stepSeg (r a c : Nat) : List Nat :=
  (List.range' a c).flatMap (fun j => [3*r+5+3*j, 3*r+3+3*j, qv r j])

/-- The queue after `k` steps, in increasing order. -/
def queue (r k : Nat) : List Nat := (List.range' k (r-2)).map (qv r)

/-- `A_r(k)`, zero-based: length `3r+7+3k`. -/
def famA (r k : Nat) : List Nat :=
  lowSeg r 0 (r-1) ++ (prefixTail r ++ (stepSeg r 0 k ++
    ((3*r+6+3*k) :: (3*r+3+3*k) :: (3*r-2) :: (queue r k ++ [3*r+4+3*k, 3*r+5+3*k]))))

/-- `B_r(k)`, zero-based: length `3r+8+3k`. -/
def famB (r k : Nat) : List Nat :=
  lowSeg r 0 (r-1) ++ (prefixTail r ++ (stepSeg r 0 k ++
    ((3*r+5+3*k) :: (3*r+3+3*k) :: (3*r+7+3*k) :: (3*r-2) ::
      (queue r k ++ [3*r+4+3*k, 3*r+6+3*k]))))

/-- At `r = 3` these are the `(3,3)` note's `A(0)` and `B(0)` (zero-based). -/
example : famA 3 0 = [4,0,6,1,3,9,2,11,8,5,15,12,7,10,13,14] := by decide
example : famB 3 0 = [4,0,6,1,3,9,2,11,8,5,14,12,16,7,10,13,15] := by decide

/-- Zero-based forms of the draft's displayed examples. -/
example : famA 4 0 = [5,0,7,1,9,2,4,12,3,14,11,6,18,15,10,8,13,16,17] := by decide
example : famB 4 0 = [5,0,7,1,9,2,4,12,3,14,11,6,17,15,19,10,8,13,16,18] := by decide
example : famB 4 2 =
    [5,0,7,1,9,2,4,12,3,14,11,6,17,15,8,20,18,13,23,21,25,10,16,19,22,24] := by decide
example : famA 5 1 =
    [6,0,8,1,10,2,12,3,5,15,4,17,14,7,20,18,9,24,21,13,11,16,19,22,23] := by decide

theorem stepSeg_succ (r a c : Nat) :
    stepSeg r a (c+1) = [3*r+5+3*a, 3*r+3+3*a, qv r a] ++ stepSeg r (a+1) c := by
  simp [stepSeg, List.range'_succ]

theorem stepSeg_zero (r a : Nat) : stepSeg r a 0 = [] := by simp [stepSeg]

theorem stepSeg_append (r a b c : Nat) :
    stepSeg r a b ++ stepSeg r (a+b) c = stepSeg r a (b+c) := by
  have h := List.range'_append (s := a) (m := b) (n := c) (step := 1)
  simp only [Nat.one_mul] at h
  simp only [stepSeg, ← List.flatMap_append, h]

theorem length_stepSeg (r a c : Nat) : (stepSeg r a c).length = 3*c := by
  induction c generalizing a with
  | zero => simp [stepSeg]
  | succ c ih => rw [stepSeg_succ, List.length_append, ih]; simp; omega

theorem mem_stepSeg {r a c x : Nat} :
    x ∈ stepSeg r a c ↔ ∃ j, a ≤ j ∧ j < a + c ∧
      (x = 3*r+5+3*j ∨ x = 3*r+3+3*j ∨ x = qv r j) := by
  simp only [stepSeg, List.mem_flatMap, List.mem_range', List.mem_cons, List.not_mem_nil]
  constructor
  · rintro ⟨j, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨a+i, by omega, by omega, by simpa using hx⟩
  · rintro ⟨j, h₁, h₂, hx⟩
    exact ⟨j, ⟨j-a, by omega, by omega⟩, by simpa using hx⟩

theorem length_queue (r k : Nat) : (queue r k).length = r - 2 := by simp [queue]

theorem mem_queue {r k x : Nat} :
    x ∈ queue r k ↔ ∃ i, k ≤ i ∧ i < k + (r-2) ∧ x = qv r i := by
  simp only [queue, List.mem_map, List.mem_range']
  constructor
  · rintro ⟨i, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨k+t, by omega, by omega, by simp⟩
  · rintro ⟨i, h₁, h₂, rfl⟩
    exact ⟨i, ⟨i-k, by omega, by omega⟩, rfl⟩

theorem qv_early {r j : Nat} (h : j + 3 < r) : qv r j = r+4+2*j := by simp [qv, h]
theorem qv_late {r j : Nat} (h : r ≤ j + 3) : qv r j = 3*j+10 := by
  simp [qv]; intro h'; omega

/-- Every queue value is an `E_i` with `2 <= i <= r-2`, or at least `V`. -/
theorem qv_cases (r j : Nat) :
    (j + 3 < r ∧ qv r j = r+4+2*j) ∨ (r ≤ j + 3 ∧ qv r j = 3*j+10) := by
  by_cases h : j + 3 < r
  · exact Or.inl ⟨h, qv_early h⟩
  · exact Or.inr ⟨by omega, qv_late (by omega)⟩

theorem qv_mono {r i j : Nat} (h : i < j) : qv r i < qv r j := by
  rcases qv_cases r i with ⟨hi, ei⟩ | ⟨hi, ei⟩ <;>
    rcases qv_cases r j with ⟨hj, ej⟩ | ⟨hj, ej⟩ <;> omega

theorem qv_mem (r k i : Nat) (hi : i < k + (r-2)) :
    qv r i ∈ stepSeg r 0 k ∨ qv r i ∈ queue r k := by
  by_cases h : i < k
  · exact Or.inl (mem_stepSeg.mpr ⟨i, by omega, by omega, Or.inr (Or.inr rfl)⟩)
  · exact Or.inr (mem_queue.mpr ⟨i, by omega, hi, rfl⟩)

/-- Every value below `a_k = 3r+3+3k` lies in the prefix, is `C`, or lies in
the steps or the final queue. -/
theorem value_cases (r k x : Nat) (hr : 3 ≤ r) (hx : x < 3*r+3+3*k) :
    x ∈ lowSeg r 0 (r-1) ∨ x ∈ prefixTail r ∨ x = 3*r-2 ∨
      x ∈ stepSeg r 0 k ∨ x ∈ queue r k := by
  have hlow : ∀ i, i < r - 1 → (x = r+1+2*i ∨ x = i) → x ∈ lowSeg r 0 (r-1) :=
    fun i hi hx => mem_lowSeg.mpr ⟨i, by omega, by omega, hx⟩
  have hq : ∀ i, i < k + (r-2) → x = qv r i →
      x ∈ lowSeg r 0 (r-1) ∨ x ∈ prefixTail r ∨ x = 3*r-2 ∨
        x ∈ stepSeg r 0 k ∨ x ∈ queue r k := by
    intro i hi hxi
    rw [hxi]
    rcases qv_mem r k i hi with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have htail : x = r ∨ x = 3*r ∨ x = r-1 ∨ x = 3*r+2 ∨ x = 3*r-1 ∨ x = r+2 →
      x ∈ prefixTail r := by
    intro h; simp only [prefixTail, List.mem_cons, List.not_mem_nil]; omega
  by_cases h₁ : x < r - 1
  · exact Or.inl (hlow x h₁ (Or.inr rfl))
  by_cases h₂ : x ≤ 3*r-3
  · by_cases h₃ : x = r-1 ∨ x = r ∨ x = r+2
    · exact Or.inr (Or.inl (htail (by omega)))
    rcases Nat.mod_two_eq_zero_or_one (x-r) with he | ho
    · -- a relay E_i = r+2i with 2 <= i <= r-2: the queue value qv r (i-2)
      exact hq ((x-r)/2-2) (by omega) (by rw [qv_early (by omega)]; omega)
    · exact Or.inl (hlow ((x-r-1)/2) (by omega) (Or.inl (by omega)))
  by_cases h₄ : x ≤ 3*r+2
  · by_cases h₅ : x = 3*r-2
    · exact Or.inr (Or.inr (Or.inl h₅))
    by_cases h₆ : x = 3*r+1
    · exact hq (r-3) (by omega) (by rw [qv_late (by omega)]; omega)
    · exact Or.inr (Or.inl (htail (by omega)))
  -- step values 3r+3+3j+e with j < k
  have hj : (x-(3*r+3))/3 < k := by omega
  rcases (by omega : (x-(3*r+3)) % 3 = 0 ∨ (x-(3*r+3)) % 3 = 1 ∨ (x-(3*r+3)) % 3 = 2)
    with he | he | he
  · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_stepSeg.mpr
      ⟨(x-(3*r+3))/3, by omega, by omega, Or.inr (Or.inl (by omega))⟩))))
  · exact hq ((x-(3*r+3))/3+(r-2)) (by omega) (by rw [qv_late (by omega)]; omega)
  · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_stepSeg.mpr
      ⟨(x-(3*r+3))/3, by omega, by omega, Or.inl (by omega)⟩))))

theorem length_famA (r k : Nat) (hr : 3 ≤ r) : (famA r k).length = 3*r+7+3*k := by
  simp only [famA, List.length_append, List.length_cons, length_lowSeg, length_stepSeg,
    length_queue, prefixTail, List.length_nil]
  omega

theorem length_famB (r k : Nat) (hr : 3 ≤ r) : (famB r k).length = 3*r+8+3*k := by
  simp only [famB, List.length_append, List.length_cons, length_lowSeg, length_stepSeg,
    length_queue, prefixTail, List.length_nil]
  omega

theorem famA_cover (r k : Nat) (hr : 3 ≤ r) (x : Nat) (hx : x < 3*r+7+3*k) :
    x ∈ famA r k := by
  simp only [famA, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  by_cases h : x < 3*r+3+3*k
  · rcases value_cases r k x hr h with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · omega

theorem famB_cover (r k : Nat) (hr : 3 ≤ r) (x : Nat) (hx : x < 3*r+8+3*k) :
    x ∈ famB r k := by
  simp only [famB, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  by_cases h : x < 3*r+3+3*k
  · rcases value_cases r k x hr h with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · omega

theorem famA_perm (r k : Nat) (hr : 3 ≤ r) : (famA r k).Perm (List.range (3*r+7+3*k)) :=
  perm_range_of_mem _ _ (length_famA r k hr) (famA_cover r k hr)

theorem famB_perm (r k : Nat) (hr : 3 ≤ r) : (famB r k).Perm (List.range (3*r+8+3*k)) :=
  perm_range_of_mem _ _ (length_famB r k hr) (famB_cover r k hr)

theorem famA_nodup (r k : Nat) (hr : 3 ≤ r) : (famA r k).Nodup :=
  (famA_perm r k hr).nodup_iff.mpr List.nodup_range

theorem famB_nodup (r k : Nat) (hr : 3 ≤ r) : (famB r k).Nodup :=
  (famB_perm r k hr).nodup_iff.mpr List.nodup_range

/-- The members are pairwise distinct: lengths `3r+7+3k` and `3r+8+3k`
never coincide across different `(family, k)`. -/
theorem fam_lengths_distinct (r k k' : Nat) (hr : 3 ≤ r) :
    (famA r k).length ≠ (famB r k').length ∧
      ((famA r k).length = (famA r k').length → k = k') ∧
      ((famB r k).length = (famB r k').length → k = k') := by
  rw [length_famA r k hr, length_famB r k' hr, length_famA r k' hr, length_famB r k hr]
  refine ⟨by omega, by omega, by omega⟩

#print axioms famA_perm
#print axioms famB_perm
#print axioms fam_lengths_distinct
end Equal
end StackSorting.Generalized
