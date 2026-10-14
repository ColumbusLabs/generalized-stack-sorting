import BinaryPositionLists

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic
variable {α : Type} {n : Nat} (T : RootedTree n) (O : FixedOrder n)

/-- Generic inverse on a forest. The complete ordered child lists and enough
fuel determine the whole binary tree, including nil and disconnected forests.
No injectivity of the original labels is required. -/
theorem build_from_position_children (t : BinaryTree α) (f : Position t → Fin n)
    (hc : ∀ p, (positionChildren p).map f = children T O (f p))
    (fuel : Nat) (hf : ∀ p ∈ positionRoots t, n - (f p).val ≤ fuel) :
    build T O fuel ((positionRoots t).map f) = positionRelabel t f := by
  induction t generalizing fuel with
  | nil => simp only [positionRoots, List.map_nil, build_nil, positionRelabel]
  | node a l r ihl ihr =>
    have hroot := hf .root (by simp [positionRoots])
    cases fuel with
    | zero => have hi := (f .root).isLt; omega
    | succ fuel =>
      have hchildren : children T O (f .root) =
          (positionRoots l).map (fun p => f (.left p)) := by
        simpa only [positionChildren, List.map_map, Function.comp_def] using (hc .root).symm
      have hcl : ∀ p : Position l,
          (positionChildren p).map (fun q => f (.left q)) = children T O (f (.left p)) := by
        intro p
        simpa only [positionChildren, List.map_map, Function.comp_def] using hc (.left p)
      have hcr : ∀ p : Position r,
          (positionChildren p).map (fun q => f (.right q)) = children T O (f (.right p)) := by
        intro p
        simpa only [positionChildren, List.map_map, Function.comp_def] using hc (.right p)
      have hfl : ∀ p ∈ positionRoots l, n - (f (.left p)).val ≤ fuel := by
        intro p hp
        apply child_fuel T O hroot
        rw [hchildren]
        exact List.mem_map.mpr ⟨p,hp,rfl⟩
      have hfr : ∀ p ∈ positionRoots r, n - (f (.right p)).val ≤ fuel+1 := by
        intro p hp
        apply hf
        simp only [positionRoots, List.mem_cons, List.mem_map]
        exact Or.inr ⟨p,hp,rfl⟩
      simp only [positionRoots, List.map_cons, List.map_map, Function.comp_def,
        build, positionRelabel]
      rw [hchildren, ihl _ hcl _ hfl, ihr _ hcr _ hfr]

/-- A subsequence of a duplicate-free linear order is exactly the filtering
of that order by its membership predicate. -/
theorem ordered_filter_unique {δ : Type} (xs ys : List δ) (p : δ → Bool)
    (hs : xs.Sublist ys) (hy : ys.Nodup)
    (hm : ∀ x, p x = true ↔ x ∈ xs) : ys.filter p = xs := by
  have he : xs.filter p = xs := List.filter_eq_self.mpr (fun x hx => (hm x).mpr hx)
  have hsub : xs.Sublist (ys.filter p) := by
    have h := hs.filter p
    rwa [he] at h
  apply (hsub.eq_of_length_le ?_).symm
  exact (hy.filter p).length_le_of_subset (fun x hx =>
    (hm x).mp (List.mem_filter.mp hx).2)

/-- Semantic sibling-order condition: every literal child chain occurs in
increasing order within the independently supplied total vertex order. This
mentions positions, their sibling chain, and O only, never a build or code. -/
def SiblingOrderCompatible (t : BinaryTree α) (e : Position t → Fin n) : Prop :=
  ∀ p, ((positionChildren p).map e).Sublist O.vertices

/-- Exact ParentPosition plus the independent sibling order derives all
child lists; they are not assumed as a canonical-code witness. -/
theorem position_children_eq (t : BinaryTree α) (e : Position t ≃ Fin n)
    (hp : ∀ p q, ParentPosition p q ↔ (e q).val ≠ 0 ∧ T.parent (e q) = e p)
    (ho : SiblingOrderCompatible O t e) (p : Position t) :
    (positionChildren p).map e = children T O (e p) := by
  unfold children
  apply (ordered_filter_unique _ _ _ (ho p) O.nodup ?_).symm
  intro v
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    refine List.mem_map.mpr ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    apply (mem_positionChildren p (e.symm v)).mpr
    apply (hp p (e.symm v)).mpr
    simpa only [Equiv.apply_symm_apply] using h
  · intro h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
    exact (hp p q).mp ((mem_positionChildren p q).mp hq)

/-- Main forest inverse: the exact semantic parent relation and independently
ordered sibling chains force the binary representation. -/
theorem build_from_parent_and_order (t : BinaryTree α) (e : Position t ≃ Fin n)
    (hp : ∀ p q, ParentPosition p q ↔ (e q).val ≠ 0 ∧ T.parent (e q) = e p)
    (ho : SiblingOrderCompatible O t e) :
    build T O n ((positionRoots t).map e) = positionRelabel t e := by
  exact build_from_position_children T O t e (position_children_eq T O t e hp ho)
    n (fun _ _ => Nat.sub_le _ _)

#print axioms build_from_position_children
#print axioms ordered_filter_unique
#print axioms position_children_eq
#print axioms build_from_parent_and_order
end StackSorting.FinitePort.ChildSibling
