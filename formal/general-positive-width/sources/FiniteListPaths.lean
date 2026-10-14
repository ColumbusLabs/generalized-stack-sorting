import UCurveStemOrder

namespace StackSorting.GraphWidth.UCurve

inductive CountWalk {α : Type} (adj : α → α → Prop) : Nat → α → α → Prop
  | refl (a) : CountWalk adj 0 a a
  | step {n a b c} : adj a b → CountWalk adj n b c → CountWalk adj (n+1) a c

theorem CountWalk.toWalk {α} {adj : α → α → Prop} {n a b}
    (h : CountWalk adj n a b) : Walk adj (fun _ => True) a b := by
  induction h with
  | refl => exact .refl trivial
  | step hab _ ih => exact .step trivial hab ih

/-- Inclusive prefix, stopping at the first occurrence of the target. -/
def prefixThrough {α} [DecidableEq α] : List α → α → List α
  | [], _ => []
  | a :: xs, y => a :: if a = y then [] else prefixThrough xs y

theorem prefixThrough_subset {α} [DecidableEq α] (xs : List α) (y : α) :
    prefixThrough xs y ⊆ xs := by
  induction xs with
  | nil => simp [prefixThrough]
  | cons a xs ih =>
    intro x hx
    simp only [prefixThrough, List.mem_cons] at hx
    obtain rfl | hx := hx
    · simp
    · by_cases he : a = y
      · simp [he] at hx
      · simp only [ite_eq_right he] at hx
        exact List.mem_cons_of_mem _ (ih hx)

theorem prefixThrough_nodup {α} [DecidableEq α] {xs : List α} (hn : xs.Nodup) (y : α) :
    (prefixThrough xs y).Nodup := by
  induction xs with
  | nil => simp [prefixThrough]
  | cons a xs ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hn
    unfold prefixThrough
    by_cases he : a = y
    · simp [he]
    · simp only [ite_eq_right he, List.nodup_cons]
      exact ⟨fun h => ha (prefixThrough_subset xs y h), ih ht⟩

theorem prefixThrough_ne_nil {α} [DecidableEq α] {xs : List α} {y : α}
    (hy : y ∈ xs) : prefixThrough xs y ≠ [] := by
  cases xs with
  | nil => simp at hy
  | cons a xs => simp [prefixThrough]

theorem prefixThrough_ordered_bound {α} [DecidableEq α] (key : α → Nat)
    {xs : List α} {y : α} (hs : xs.Pairwise (fun a b => key a ≤ key b)) (hy : y ∈ xs) :
    ∀ x ∈ prefixThrough xs y, key x ≤ key y := by
  induction xs with
  | nil => simp at hy
  | cons a xs ih =>
    intro x hx
    simp only [prefixThrough, List.mem_cons] at hx
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hs
    by_cases he : a = y
    · simp only [ite_eq_left he, List.not_mem_nil, or_false] at hx
      subst x; exact Nat.le_of_eq (congrArg key he)
    · have hyt : y ∈ xs := (List.mem_cons.mp hy).resolve_left (Ne.symm he)
      obtain rfl | hx := hx
      · exact ha y hyt
      · simp only [ite_eq_right he] at hx
        exact ih ht hyt x hx

/-- Count the actual consecutive edges in the prefix, not just reachability. -/
theorem prefixThrough_countWalk {α} [DecidableEq α] {adj : α → α → Prop}
    (a : α) (xs : List α) {y : α} (hy : y ∈ a :: xs)
    (he : ∀ u v, Consecutive (a :: xs) u v → adj u v) :
    CountWalk adj ((prefixThrough (a :: xs) y).length - 1) a y := by
  induction xs generalizing a with
  | nil =>
    have hya : y = a := by simpa using hy
    subst y
    simpa [prefixThrough] using (CountWalk.refl (adj := adj) a)
  | cons b xs ih =>
    by_cases hay : a = y
    · subst y
      simpa [prefixThrough] using (CountWalk.refl (adj := adj) a)
    · have hyt : y ∈ b :: xs := (List.mem_cons.mp hy).resolve_left (Ne.symm hay)
      have ht := ih b hyt (fun u v h => he u v (h.cons a))
      have hn : 0 < (prefixThrough (b :: xs) y).length :=
        List.length_pos_iff.mpr (prefixThrough_ne_nil hyt)
      have hc := CountWalk.step (he a b ⟨[], xs, rfl⟩) ht
      have heq : (prefixThrough (a :: b :: xs) y).length - 1 =
          (prefixThrough (b :: xs) y).length - 1 + 1 := by
        simp only [prefixThrough, ite_eq_right hay, List.length_cons]
        simp only [prefixThrough, List.length_cons] at hn ⊢
        omega
      rw [heq]
      exact hc

end StackSorting.GraphWidth.UCurve
