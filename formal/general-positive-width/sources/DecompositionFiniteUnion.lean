import DecompositionDisjointUnion

namespace StackSorting.GuidedPathwidth
universe u v
variable {V : Type u} {J : Type v} {G : SimpleGraph V} {c : Nat}

namespace GuidedDecomposition
/-- Empty allowed graphs admit an empty actual index forest and palette. -/
noncomputable def empty (G : SimpleGraph V) (c : Nat) : GuidedDecomposition G ∅ c where
  decomposition := {
    Node := PEmpty.{u+1}
    finiteNode := inferInstance
    forest := ⊥
    acyclic := SimpleGraph.isAcyclic_bot
    bag := PEmpty.elim
    inside := fun a => a.elim
    vertex := fun _ h => h.elim
    edge := fun _ h => h.elim
    running := fun _ a => a.elim }
  guides := fun _ => Color.empty G ∅
  captured := fun a => a.elim

/-- Arbitrarily many disjoint graph regions reuse one finite palette. The
finite index forest and all bags are constructed by literal disjoint unions. -/
theorem exists_finsetUnion (R : J → Set V) (S : Finset J)
    (D : ∀ j ∈ S, Nonempty (GuidedDecomposition G (R j) c))
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (R i) (R j))
    (hs : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ x ∈ R i, ∀ y ∈ R j, ¬ G.Adj x y) :
    Nonempty (GuidedDecomposition G {x | ∃ j ∈ S, x ∈ R j} c) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (show Nonempty (GuidedDecomposition G ∅ c) from ⟨empty G c⟩)
  | @insert j S hj ih =>
    obtain ⟨E⟩ := D j (by simp)
    obtain ⟨F⟩ := ih (fun i hi => D i (by simp [hi]))
      (fun i hi l hl hne => hd i (by simp [hi]) l (by simp [hl]) hne)
      (fun i hi l hl hne => hs i (by simp [hi]) l (by simp [hl]) hne)
    have hdisj : Disjoint (R j) {x | ∃ i ∈ S, x ∈ R i} := by
      apply Set.disjoint_left.mpr
      rintro x hx ⟨i,hi,hxi⟩
      exact Set.disjoint_left.mp (hd j (by simp) i (by simp [hi])
        (fun he => hj (he.symm ▸ hi))) hx hxi
    have hsep : ∀ x ∈ R j, ∀ y ∈ {x | ∃ i ∈ S, x ∈ R i}, ¬ G.Adj x y := by
      rintro x hx y ⟨i,hi,hyi⟩
      exact hs j (by simp) i (by simp [hi]) (fun he => hj (he.symm ▸ hi)) x hx y hyi
    have heq : R j ∪ {x | ∃ i ∈ S, x ∈ R i} = {x | ∃ i ∈ insert j S, x ∈ R i} := by
      ext x
      simp only [Set.mem_union,Set.mem_ofPred_eq,Finset.mem_insert]
      aesop
    exact ⟨heq ▸ E.disjointUnion F hdisj hsep⟩

end GuidedDecomposition
#print axioms GuidedDecomposition.exists_finsetUnion
end StackSorting.GuidedPathwidth
