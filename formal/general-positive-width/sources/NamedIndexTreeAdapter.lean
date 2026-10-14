import FiniteIndexTreeAdapter
import Mathlib.Data.Fintype.EquivFin

namespace StackSorting.IndexTreeAdapter
open GraphWidth FinitePort
universe u
variable {Node : Type} {n : Nat}

/-- Exact orientation and numbering with the old node names retained. -/
structure NamedNumberedTree (H : SimpleGraph Node) where
  size : Nat
  tree : RootedTree size
  names : Fin size ≃ Node
  edge_iff : ∀ i j, TreeAdj tree i j ↔ H.Adj (names i) (names j)

noncomputable def numberNamedTree [Fintype Node] {H : SimpleGraph Node}
    (hH : H.IsTree) : NamedNumberedTree H := by
  let e := Fintype.equivFin Node
  let H' := H.comap e.symm
  let iso : H' ≃g H := { toEquiv := e.symm, map_rel_iff' := by intro a b; rfl }
  let S := numberTree (iso.isTree_iff.mpr hH)
  exact ⟨_,S.tree,S.names.trans e.symm,fun i j => S.edge_iff i j⟩

/-- Induced-graph walks preserve their actual occurrence set at every node. -/
theorem induced_to_guarded {α : Type} {H : SimpleGraph α} {P : Set α}
    {x y : P} (p : (H.induce P).Walk x y) : Walk H.Adj (fun z => z ∈ P) x.val y.val := by
  induction p with
  | @nil x => exact .refl x.property
  | @cons a b c hab tail ih => exact .step a.property hab ih

/-- A named actual tree decomposition, with no hidden parent or ancestry
assumption. Bags are finite lists on the original graph vertex names. -/
structure NamedDecomposition (G : Graph n) (H : SimpleGraph Node) where
  bag : Node → List (Fin n)
  nodup : ∀ i, (bag i).Nodup
  vertex : ∀ v, ∃ i, v ∈ bag i
  edge : ∀ {u v}, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i
  running : ∀ {v i j}, v ∈ bag i → v ∈ bag j →
    Walk H.Adj (fun k => v ∈ bag k) i j

noncomputable def reindexDecomposition {G : Graph n} {H : SimpleGraph Node}
    (N : NamedNumberedTree H) (D : NamedDecomposition G H) : Decomposition G N.tree where
  bag i := D.bag (N.names i)
  nodup i := D.nodup _
  vertex v := by
    obtain ⟨i,hi⟩ := D.vertex v
    exact ⟨N.names.symm i,by simpa only [Equiv.apply_symm_apply] using hi⟩
  edge := by
    intro u v huv
    obtain ⟨i,hu,hv⟩ := D.edge huv
    exact ⟨N.names.symm i,by simpa only [Equiv.apply_symm_apply] using hu,
      by simpa only [Equiv.apply_symm_apply] using hv⟩
  running := by
    intro v i j hi hj
    have h := map_guarded (B := TreeAdj N.tree)
      (P := fun a => v ∈ D.bag a) (Q := fun k => v ∈ D.bag (N.names k))
      N.names.symm (fun a b hab => by
      apply (N.edge_iff _ _).mpr
      simpa only [Equiv.apply_symm_apply] using hab)
      (fun a ha => by simpa only [Equiv.apply_symm_apply] using ha) (D.running hi hj)
    simpa only [Equiv.symm_apply_apply] using h

theorem reindexDecomposition_bound {G : Graph n} {H : SimpleGraph Node}
    (N : NamedNumberedTree H) (D : NamedDecomposition G H) {b}
    (hb : ∀ a, (D.bag a).length ≤ b) : (reindexDecomposition N D).BagBound b :=
  fun i => hb (N.names i)

/-- Arbitrary capture predicates on original bags survive orientation and
numbering verbatim. No property of a guidance presentation is assumed here. -/
theorem reindexDecomposition_capture {G : Graph n} {H : SimpleGraph Node}
    (N : NamedNumberedTree H) (D : NamedDecomposition G H)
    (Captured : List (Fin n) → Prop) (hc : ∀ a, Captured (D.bag a)) (i) :
    Captured ((reindexDecomposition N D).bag i) := hc (N.names i)

/-- Normalized bags retain an exact old index-tree origin after orientation. -/
theorem normalized_named_origin {G : Graph n} {H : SimpleGraph Node}
    (N : NamedNumberedTree H) (D : NamedDecomposition G H) {v u}
    (hu : u ∈ (ConnectedConeNormalization.normalizeSupplied (reindexDecomposition N D)).bag v) :
    u ∈ D.bag (N.names (introductionNode (reindexDecomposition N D) v)) :=
  ConnectedConeNormalization.normalizeSupplied_origin _ hu

theorem normalized_named_capture {G : Graph n} {H : SimpleGraph Node}
    (N : NamedNumberedTree H) (D : NamedDecomposition G H)
    (Captured : (Fin n → Prop) → Prop)
    (mono : ∀ A B, (∀ u, A u → B u) → Captured B → Captured A)
    (hc : ∀ a, Captured (fun u => u ∈ D.bag a)) (v) :
    Captured (fun u => u ∈ (ConnectedConeNormalization.normalizeSupplied
      (reindexDecomposition N D)).bag v) := by
  apply mono _ _ (fun u hu => normalized_named_origin N D hu)
  exact hc _

#print axioms normalized_named_capture
#print axioms numberNamedTree
#print axioms reindexDecomposition
#print axioms normalized_named_origin
end StackSorting.IndexTreeAdapter
