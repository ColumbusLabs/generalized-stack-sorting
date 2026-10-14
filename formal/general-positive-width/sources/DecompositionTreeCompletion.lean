import ForestAttachment

namespace StackSorting.GuidedPathwidth
universe u
variable {V : Type u} {G : SimpleGraph V} {P : Set V} {c : Nat}

/-- Complete the finite index forest to a genuine tree by adjoining an empty
root bag and retaining every old edge, bag, capture witness and guide. -/
theorem GuidedDecomposition.exists_treeCompletion (D : GuidedDecomposition G P c) :
    ∃ E : GuidedDecomposition G P c, E.decomposition.forest.IsTree := by
  obtain ⟨F⟩ := exists_attached_forest D.decomposition.acyclic
    (M := Set.univ) (by intro a b hab ha; trivial)
  let E : Decomposition G P := {
    Node := Option D.decomposition.Node
    finiteNode := inferInstance
    forest := F.graph
    acyclic := F.acyclic
    bag := fun a => a.elim ∅ D.decomposition.bag
    inside := by
      intro a x hx
      cases a with
      | none => exact hx.elim
      | some a => exact D.decomposition.inside a hx
    vertex := by
      intro x hx
      obtain ⟨a,ha⟩ := D.decomposition.vertex x hx
      exact ⟨some a,ha⟩
    edge := by
      intro x y hxy hx hy
      obtain ⟨a,ha,hb⟩ := D.decomposition.edge hxy hx hy
      exact ⟨some a,ha,hb⟩
    running := by
      intro x a b ha hb
      cases a with
      | none => exact ha.elim
      | some a =>
        cases b with
        | none => exact hb.elim
        | some b =>
          have h := D.decomposition.running x a b ha hb
          refine ⟨ha,hb,?_⟩
          exact h.2.2.map some (fun _ _ hab => F.oldEdges hab) (fun _ ha => ha) }
  let E' : GuidedDecomposition G P c := ⟨E,D.guides,by
    intro a
    cases a with
    | none => exact captures_empty G D.guides
    | some a => exact D.captured a⟩
  refine ⟨E',{ connected := ?_, isAcyclic := F.acyclic }⟩
  let : Nonempty (Option D.decomposition.Node) := ⟨none⟩
  refine ⟨?_⟩
  have hr : ∀ a, F.graph.Reachable none a := by
    intro a
    cases a with
    | none => exact SimpleGraph.Reachable.refl _
    | some a =>
      obtain ⟨p⟩ := (F.markedConnected a trivial).induced
      exact ⟨p.map (SimpleGraph.Embedding.induce (G := F.graph) (attachmentSupport Set.univ)).toHom⟩
  intro a b
  exact (hr a).symm.trans (hr b)

#print axioms GuidedDecomposition.exists_treeCompletion
end StackSorting.GuidedPathwidth
