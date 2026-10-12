import Std

/-! Literal permutation-pattern semantics for `Av(S_r ⊕ 1)`.
Labels are zero based, so `S_r ⊕ 1` consists of `q ++ [r]` with
`q.Perm (List.range r)`. Pattern occurrences use an order-preserving map
on all canonical ranks, followed by ordinary subsequence containment. -/
set_option linter.unusedSimpArgs false
namespace StackSorting.Generalized.Container

/-- Number of smaller entries before the first occurrence of `x`. -/
def smallerBefore (x : Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => if x = y then 0 else (if y < x then 1 else 0) + smallerBefore x ys

/-- The concrete smaller-predecessor condition. -/
def CountGood (r : Nat) (xs : List Nat) : Prop :=
  ∀ x ∈ xs, smallerBefore x xs < r

/-- Strict order-isomorphism from the canonical ranks `0,...,n-1`. -/
def OrderEmbeddingOn (n : Nat) (f : Nat → Nat) : Prop :=
  ∀ i j, i < n → j < n → (f i < f j ↔ i < j)

/-- Classical permutation-pattern containment, with an explicitly selected
subsequence and an order-isomorphism on the canonical ranks. -/
def Occurs (n : Nat) (p xs : List Nat) : Prop :=
  ∃ f, OrderEmbeddingOn n f ∧ (p.map f).Sublist xs

def Forbidden (r : Nat) (p : List Nat) : Prop :=
  ∃ q, q.Perm (List.range r) ∧ p = q ++ [r]

/-- The actual avoidance class, not a renamed counting condition. -/
def Avoids (r : Nat) (xs : List Nat) : Prop :=
  ∀ p, Forbidden r p → ¬ Occurs (r+1) p xs

/-- Labelled container membership includes distinct entries. -/
def Member (r : Nat) (xs : List Nat) : Prop := xs.Nodup ∧ Avoids r xs

/-- A selected subsequence ending with its maximum. -/
def BadShape (r : Nat) (xs : List Nat) : Prop :=
  ∃ q x, (q ++ [x]).Sublist xs ∧ q.length = r ∧ ∀ y ∈ q, y < x

theorem smallerBefore_append (x : Nat) (pre post : List Nat) (hx : x ∉ pre) :
    smallerBefore x (pre ++ post) =
      (pre.filter (fun y => y < x)).length + smallerBefore x post := by
  induction pre with
  | nil => simp [smallerBefore]
  | cons y pre ih =>
    have hy : x ≠ y := by simp only [List.mem_cons, not_or] at hx; exact hx.1
    have ht : x ∉ pre := by simp only [List.mem_cons, not_or] at hx; exact hx.2
    simp only [List.cons_append, smallerBefore, ite_eq_right hy, ih ht]
    by_cases h : y < x <;> simp [h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem smallerBefore_at (x : Nat) (pre post : List Nat) (hx : x ∉ pre) :
    smallerBefore x (pre ++ x :: post) = (pre.filter (fun y => y < x)).length := by
  rw [smallerBefore_append x pre (x :: post) hx]
  simp [smallerBefore]

/-- The statistic really counts all smaller predecessors of each occurrence. -/
theorem countGood_iff_splits {r : Nat} {xs : List Nat} (hn : xs.Nodup) :
    CountGood r xs ↔ ∀ pre x post, xs = pre ++ x :: post →
      (pre.filter (fun y => y < x)).length < r := by
  constructor
  · intro h pre x post he
    subst xs
    have hx : x ∉ pre := by
      intro hm
      have := (List.nodup_append.mp hn).2.2 x hm x (by simp)
      exact this rfl
    simpa [smallerBefore_at x pre post hx] using h x (by simp)
  · intro h x hx
    obtain ⟨pre, post, he⟩ := List.mem_iff_append.mp hx
    have hnot : x ∉ pre := by
      rw [he] at hn
      intro hm
      have := (List.nodup_append.mp hn).2.2 x hm x (by simp)
      exact this rfl
    rw [he, smallerBefore_at x pre post hnot]
    exact h pre x post he

/-- Split a subsequence at its final selected entry. -/
theorem sublist_last_split {q xs : List Nat} {x : Nat}
    (h : (q ++ [x]).Sublist xs) :
    ∃ pre post, xs = pre ++ x :: post ∧ q.Sublist pre := by
  induction xs generalizing q with
  | nil => have := h.length_le; simp at this
  | cons a xs ih =>
    rcases List.sublist_cons_iff.mp h with ht | ⟨u, he, hu⟩
    · obtain ⟨pre, post, hx, hp⟩ := ih ht
      exact ⟨a :: pre, post, by simp [hx], hp.cons a⟩
    · cases q with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        exact ⟨[], xs, rfl, List.Sublist.refl []⟩
      | cons b q =>
        simp only [List.cons_append, List.cons.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        obtain ⟨pre, post, hx, hp⟩ := ih hu
        exact ⟨b :: pre, post, by simp [hx], hp.cons_cons b⟩

theorem badShape_iff_count {r : Nat} {xs : List Nat} (hn : xs.Nodup) :
    BadShape r xs ↔ ¬ CountGood r xs := by
  rw [countGood_iff_splits hn]
  constructor
  · rintro ⟨q, x, hs, hl, hb⟩ h
    obtain ⟨pre, post, he, hq⟩ := sublist_last_split hs
    have hf : q.Sublist (pre.filter (fun y => y < x)) :=
      List.sublist_filter_iff.mpr ⟨q, hq, (List.filter_eq_self.mpr (by simpa using hb)).symm⟩
    have := hf.length_le
    have := h pre x post he
    omega
  · intro h
    simp only [Classical.not_forall, Classical.not_imp] at h
    obtain ⟨pre, x, post, he, h⟩ := h
    have hb : r ≤ (pre.filter (fun y => y < x)).length := by omega
    let q := (pre.filter (fun y => y < x)).take r
    have hq : q.Sublist pre := (List.take_sublist r _).trans List.filter_sublist
    refine ⟨q, x, ?_, by simp [q, Nat.min_eq_left hb], ?_⟩
    · rw [he]
      exact hq.append (by simp)
    · intro y hy
      exact of_decide_eq_true (List.mem_filter.mp ((List.take_sublist r _).subset hy)).2

/-- A nodup list has a canonical permutation and an increasing value map.
The proof constructs the ranks by sorting, rather than assuming that a
labelled forbidden shape is itself a canonical pattern. -/
theorem standardize_below {q : List Nat} {x : Nat} (hn : q.Nodup)
    (hb : ∀ y ∈ q, y < x) :
    ∃ (p : List Nat) (f : Nat → Nat), p.Perm (List.range q.length) ∧
      OrderEmbeddingOn (q.length+1) f ∧ p.map f = q ∧ f q.length = x := by
  let sorted := q.mergeSort (fun a b => a ≤ b)
  have hp : sorted.Perm q := List.mergeSort_perm q _
  have hl : sorted.length = q.length := hp.length_eq
  have hd : sorted.Nodup := hp.nodup_iff.mpr hn
  have hs : sorted.Pairwise (· ≤ ·) := by
    have hh := List.pairwise_mergeSort (le := fun a b : Nat => a ≤ b)
      (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) q
    simpa [sorted] using hh
  have hstrict : ∀ i j (hi : i < sorted.length) (hj : j < sorted.length),
      i < j → sorted[i] < sorted[j] := by
    intro i j hi hj hij
    have hle := hs.rel_getElem_of_lt hi hj hij
    have hne := (List.pairwise_iff_getElem.mp hd) i j hi hj hij
    omega
  let p := q.map sorted.idxOf
  let f := fun i => if i < q.length then sorted.getD i 0 else x
  have hidx : sorted.map sorted.idxOf = List.range q.length := by
    apply List.ext_getElem
    · simp [hl]
    · intro i h₁ h₂
      simp only [List.getElem_map, List.getElem_range]
      exact hd.idxOf_getElem i (by simpa using h₁)
  have hget : ∀ i (hi : i < q.length), f i = sorted[i]'(by omega) := by
    intro i hi
    simp [f, hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < sorted.length)]
  refine ⟨p, f, ?_, ?_, ?_, by simp [f]⟩
  · have := hp.symm.map sorted.idxOf
    simpa [p, hidx] using this
  · intro i j hi hj
    by_cases hi' : i < q.length <;> by_cases hj' : j < q.length
    · rw [hget i hi', hget j hj']
      constructor
      · intro h
        apply Classical.byContradiction
        intro hnij
        rcases Nat.eq_or_lt_of_le (by omega : j ≤ i) with he | hji
        · subst j; omega
        · have := hstrict j i (by omega) (by omega) hji; omega
      · exact hstrict i j (by omega) (by omega)
    · have hjq : j = q.length := by omega
      subst j
      rw [hget i hi']
      have hm : sorted[i]'(by omega) ∈ q := hp.subset (List.getElem_mem (by omega))
      have hv := hb _ hm
      simp [f, hv, hi']
    · have hiq : i = q.length := by omega
      subst i
      rw [hget j hj']
      have hm : sorted[j]'(by omega) ∈ q := hp.subset (List.getElem_mem (by omega))
      have hv := hb _ hm
      simp [f, show ¬ x < sorted[j]'(by omega) by omega, show ¬ q.length < j by omega]
    · have : i = q.length ∧ j = q.length := by omega
      rcases this with ⟨rfl, rfl⟩
      simp
  · simp only [p, List.map_map]
    calc
      _ = q.map id := by
        apply List.map_congr_left
        intro a ha
        have hm : a ∈ sorted := hp.mem_iff.mpr ha
        have hi : sorted.idxOf a < sorted.length := List.idxOf_lt_length_iff.mpr hm
        change f (sorted.idxOf a) = a
        rw [hget _ (by omega)]
        exact List.getElem_idxOf hi
      _ = q := List.map_id q

/-- Genuine bridge from the finite canonical forbidden patterns to the
labelled shape selected from the container. -/
theorem exists_forbidden_iff_badShape {r : Nat} {xs : List Nat} (hn : xs.Nodup) :
    (∃ p, Forbidden r p ∧ Occurs (r+1) p xs) ↔ BadShape r xs := by
  constructor
  · rintro ⟨_, ⟨q, hp, rfl⟩, f, hf, hsub⟩
    refine ⟨q.map f, f r, by simpa using hsub, by simpa using hp.length_eq, ?_⟩
    intro y hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
    have ha' : a < r := List.mem_range.mp (hp.mem_iff.mp ha)
    exact (hf a r (by omega) (by omega)).mpr ha'
  · rintro ⟨q, x, hsub, hl, hb⟩
    have hq : q.Nodup := hn.sublist ((List.sublist_append_left q [x]).trans hsub)
    obtain ⟨p, f, hp, hf, hm, hx⟩ := standardize_below hq hb
    refine ⟨p ++ [r], ⟨p, by simpa [hl] using hp, rfl⟩, f, by simpa [hl] using hf, ?_⟩
    simpa [List.map_append, hm, ← hl, hx] using hsub

/-- `Av(S_r ⊕ 1)` is exactly the smaller-predecessor condition. -/
theorem avoids_iff_countGood {r : Nat} {xs : List Nat} (hn : xs.Nodup) :
    Avoids r xs ↔ CountGood r xs := by
  have h := exists_forbidden_iff_badShape (r := r) hn
  have h' := badShape_iff_count (r := r) hn
  simp only [Avoids]
  classical
  constructor
  · intro ha
    apply Classical.byContradiction
    intro hc
    obtain ⟨p, hp, ho⟩ := h.mpr (h'.mpr hc)
    exact ha p hp ho
  · intro hc p hp ho
    exact h'.mp (h.mp ⟨p, hp, ho⟩) hc

#print axioms standardize_below
#print axioms exists_forbidden_iff_badShape
#print axioms avoids_iff_countGood
end StackSorting.Generalized.Container
