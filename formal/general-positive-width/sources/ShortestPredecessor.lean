import RankedParentTree
import FiniteListPaths

/-! Shortest predecessors are selected from actual counted graph walks.
The finite numbered tree is derived, and its parent edges decrease shortest
walk distance by exactly one. -/
namespace StackSorting.GraphWidth
open FinitePort
open UCurve

/-- Core/Std least-witness principle, avoiding a Mathlib dependency. -/
theorem nat_exists_least (P : Nat → Prop) (hex : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, P m → n ≤ m := by
  classical
  obtain ⟨n, hn⟩ := hex
  have aux : ∀ t, P t → ∃ m, P m ∧ ∀ l, P l → m ≤ l := by
    intro t
    induction t using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      by_cases hs : ∃ m, m < n ∧ P m
      · obtain ⟨m, hmn, hm⟩ := hs
        exact ih m hmn hm
      · refine ⟨n, hn, ?_⟩
        intro m hm
        have hnot : ¬ m < n := fun hmn => hs ⟨m, hmn, hm⟩
        omega
  exact aux n hn

namespace UCurve.CountWalk

theorem snoc {α} {adj : α → α → Prop} {l a b c}
    (w : CountWalk adj l a b) (h : adj b c) : CountWalk adj (l+1) a c := by
  induction w with
  | refl => exact .step h (.refl _)
  | step hab _ ih => exact .step hab (ih h)

theorem map {α β} {adj : α → α → Prop} {adj' : β → β → Prop}
    (f : α → β) (hf : ∀ a b, adj a b → adj' (f a) (f b)) {l a b}
    (w : CountWalk adj l a b) : CountWalk adj' l (f a) (f b) := by
  induction w with
  | refl => exact .refl _
  | step hab _ ih => exact .step (hf _ _ hab) ih

theorem exists_last {α} {adj : α → α → Prop} {l a b}
    (w : CountWalk adj (l+1) a b) :
    ∃ u, CountWalk adj l a u ∧ adj u b := by
  induction l generalizing a b with
  | zero =>
    cases w with
    | step hab tail =>
      cases tail
      exact ⟨_, .refl _, hab⟩
  | succ l ih =>
    cases w with
    | step hac tail =>
      obtain ⟨u, hu, hub⟩ := ih tail
      exact ⟨u, .step hac hu, hub⟩

end UCurve.CountWalk

/-- Reachability is witnessed by actual finite counted walks. -/
structure RootReachable {α : Type} (adj : α → α → Prop) (root : α) where
  reachable : ∀ v, ∃ length, CountWalk adj length root v

namespace RootReachable

noncomputable def distance {α adj root} (R : @RootReachable α adj root) (v : α) : Nat :=
  Classical.choose (nat_exists_least (fun l => CountWalk adj l root v) (R.reachable v))

theorem distance_walk {α adj root} (R : @RootReachable α adj root) (v : α) :
    CountWalk adj (R.distance v) root v :=
  (Classical.choose_spec (nat_exists_least (fun l => CountWalk adj l root v)
    (R.reachable v))).1

theorem distance_le {α adj root} (R : @RootReachable α adj root) {v l}
    (w : CountWalk adj l root v) : R.distance v ≤ l :=
  (Classical.choose_spec (nat_exists_least (fun l => CountWalk adj l root v)
    (R.reachable v))).2 l w

@[simp] theorem distance_root {α adj root} (R : @RootReachable α adj root) :
    R.distance root = 0 := Nat.eq_zero_of_le_zero (R.distance_le (.refl root))

theorem distance_zero_iff {α adj root} (R : @RootReachable α adj root) (v : α) :
    R.distance v = 0 ↔ v = root := by
  constructor
  · intro h
    have w := R.distance_walk v
    rw [h] at w
    cases w
    rfl
  · intro h; subst v; exact R.distance_root

theorem predecessor_exists {α adj root} (R : @RootReachable α adj root)
    (v : α) (hv : v ≠ root) :
    ∃ u, adj u v ∧ R.distance u + 1 = R.distance v := by
  have hd : R.distance v ≠ 0 := fun h => hv ((R.distance_zero_iff v).mp h)
  have w := R.distance_walk v
  cases he : R.distance v with
  | zero => exact False.elim (hd he)
  | succ l =>
    rw [he] at w
    obtain ⟨u, hu, huv⟩ := w.exists_last
    have hle := R.distance_le hu
    have hge := R.distance_le ((R.distance_walk u).snoc huv)
    exact ⟨u, huv, by omega⟩

noncomputable def predecessor {α adj root} (R : @RootReachable α adj root) (v : α) : α := by
  classical
  exact if hv : v = root then root else Classical.choose (R.predecessor_exists v hv)

@[simp] theorem predecessor_root {α adj root} (R : @RootReachable α adj root) :
    R.predecessor root = root := by simp [predecessor]

theorem predecessor_edge {α adj root} (R : @RootReachable α adj root)
    (v : α) (hv : v ≠ root) : adj (R.predecessor v) v := by
  simp only [predecessor, dite_eq_right hv]
  exact (Classical.choose_spec (R.predecessor_exists v hv)).1

theorem predecessor_distance {α adj root} (R : @RootReachable α adj root)
    (v : α) (hv : v ≠ root) : R.distance (R.predecessor v) + 1 = R.distance v := by
  simp only [predecessor, dite_eq_right hv]
  exact (Classical.choose_spec (R.predecessor_exists v hv)).2

noncomputable def ranked {n adj root} (R : @RootReachable (Fin n) adj root) : RankedParent n where
  root := root
  parent := R.predecessor
  rank := R.distance
  parent_root := R.predecessor_root
  rank_lt := by intro v hv; have := R.predecessor_distance v hv; omega

noncomputable def numbered {n adj root} (R : @RootReachable (Fin n) adj root) :
    R.ranked.Numbered := R.ranked.numbered

theorem numbered_parent_edge {n adj root} (R : @RootReachable (Fin n) adj root)
    (i : Fin n) (hi : i.val ≠ 0) :
    adj (R.numbered.label (R.numbered.tree.parent i)) (R.numbered.label i) := by
  rw [R.numbered.parent_exact]
  exact R.predecessor_edge _ (fun h => hi ((R.numbered.label_eq_root_iff i).mp h))

theorem numbered_parent_distance {n adj root} (R : @RootReachable (Fin n) adj root)
    (i : Fin n) (hi : i.val ≠ 0) :
    R.distance (R.numbered.label (R.numbered.tree.parent i)) + 1 =
      R.distance (R.numbered.label i) := by
  rw [R.numbered.parent_exact]
  exact R.predecessor_distance _ (fun h => hi ((R.numbered.label_eq_root_iff i).mp h))

end RootReachable
end StackSorting.GraphWidth
