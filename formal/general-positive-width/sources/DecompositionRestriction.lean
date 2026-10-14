import DecompositionForests

namespace StackSorting.GuidedPathwidth
open BiInterface
universe u
variable {V : Type u} {G : SimpleGraph V} {P Q : Set V}

/-- Lift a walk of an actual induced graph back to the same original names. -/
theorem reachIn_of_induced {x y : Q} (h : (G.induce Q).Reachable x y) :
    ReachIn G Q x.val y.val := by
  refine ⟨x.property,y.property,?_⟩
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .refl _
  | @cons x y z hxy p ih => exact .join (.edge hxy) y.property ih

/-- The component label is an actual connected-component quotient of G[Q]. -/
def componentFiber (G : SimpleGraph V) (Q : Set V)
    (K : (G.induce Q).ConnectedComponent) : Set V :=
  {x | ∃ hx : x ∈ Q, (G.induce Q).connectedComponentMk ⟨x,hx⟩ = K}

theorem componentFiber_inside (K : (G.induce Q).ConnectedComponent) :
    componentFiber G Q K ⊆ Q := fun _ h => h.choose

theorem componentFiber_connected (K : (G.induce Q).ConnectedComponent)
    {x y : V} (hx : x ∈ componentFiber G Q K) (hy : y ∈ componentFiber G Q K) :
    ReachIn G Q x y := by
  obtain ⟨hx,hxK⟩ := hx
  obtain ⟨hy,hyK⟩ := hy
  exact reachIn_of_induced (SimpleGraph.ConnectedComponent.exact (hxK.trans hyK.symm))

namespace Decomposition
variable [Finite V]

/-- Restrict to an induced subgraph and split every old bag by actual surviving
components. All copied bag-index trees remain explicit and acyclic. -/
noncomputable def restrictComponents (D : Decomposition G P) (hQP : Q ⊆ P) :
    Decomposition G Q where
  Node := (G.induce Q).ConnectedComponent × D.Node
  finiteNode := inferInstance
  forest := forestCopies D.forest _
  acyclic := forestCopies_acyclic D.acyclic
  bag := fun a => D.bag a.2 ∩ componentFiber G Q a.1
  inside := fun a _ hx => componentFiber_inside a.1 hx.2
  vertex := by
    intro x hx
    obtain ⟨a,ha⟩ := D.vertex x (hQP hx)
    exact ⟨((G.induce Q).connectedComponentMk ⟨x,hx⟩,a),ha,hx,rfl⟩
  edge := by
    intro x y hxy hx hy
    obtain ⟨a,ha,hb⟩ := D.edge hxy (hQP hx) (hQP hy)
    refine ⟨((G.induce Q).connectedComponentMk ⟨x,hx⟩,a),⟨ha,hx,rfl⟩,hb,hy,?_⟩
    exact SimpleGraph.ConnectedComponent.sound
      (show (G.induce Q).Reachable ⟨y,hy⟩ ⟨x,hx⟩ from (show (G.induce Q).Adj ⟨y,hy⟩ ⟨x,hx⟩ from hxy.symm).reachable)
  running := by
    intro x a b ha hb
    obtain ⟨ka,a⟩ := a
    obtain ⟨kb,b⟩ := b
    have he : ka = kb := by
      obtain ⟨hx,hka⟩ := ha.2
      obtain ⟨_,hkb⟩ := hb.2
      exact hka.symm.trans hkb
    subst kb
    have h := D.running x a b ha.1 hb.1
    refine ⟨ha,hb,?_⟩
    exact h.2.2.map (fun n => (ka,n))
      (fun _ _ he => ⟨rfl,he⟩) (fun n hn => ⟨hn,ha.2⟩)
end Decomposition

namespace GuidedDecomposition
variable [Finite V] {c : Nat}

/-- Deleting one actual graph vertex constructs a finite captured decomposition
with twice the palette. It does not assume a decomposition of the remainder. -/
noncomputable def deleteVertex (D : GuidedDecomposition G P c) (u : V) :
    GuidedDecomposition G (P \ {u}) (c+c) where
  decomposition := D.decomposition.restrictComponents Set.sdiff_subset
  guides := D.guides.deleteVertex u
  captured := by
    intro a
    apply System.deleteVertex_captures
    · exact (D.decomposition.restrictComponents Set.sdiff_subset).inside a
    · intro r hr s hs
      exact componentFiber_connected a.1 hr.2 hs.2
    · exact captures_mono D.guides (D.captured a.2) Set.inter_subset_left
end GuidedDecomposition

#print axioms GuidedDecomposition.deleteVertex
end StackSorting.GuidedPathwidth
