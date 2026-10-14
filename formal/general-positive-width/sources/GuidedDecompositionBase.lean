import DecompositionRestriction

namespace StackSorting.GuidedPathwidth
universe u
variable {V : Type u} {G : SimpleGraph V} {P : Set V} {c d : Nat}

namespace System
noncomputable def pad (C : System G P c) (_hcd : c ≤ d) : System G P d :=
  fun i => if h : i.val < c then C ⟨i.val,h⟩ else Color.empty G P

theorem pad_captures (C : System G P c) (hcd : c ≤ d) {B : Set V}
    (h : Captures G C B) : Captures G (C.pad hcd) B := by
  intro hb
  obtain ⟨x,hx⟩ := h hb
  refine ⟨x,?_⟩
  intro r hr
  obtain ⟨i,hi⟩ := hx r hr
  refine ⟨⟨i.val,lt_of_lt_of_le i.isLt hcd⟩,?_⟩
  simpa only [pad,dite_eq_left i.isLt] using hi
end System

namespace GuidedDecomposition
noncomputable def pad (D : GuidedDecomposition G P c) (hcd : c ≤ d) :
    GuidedDecomposition G P d where
  decomposition := D.decomposition
  guides := D.guides.pad hcd
  captured := fun a => System.pad_captures D.guides hcd (D.captured a)

/-- Every finite graph gets an actual component-bag decomposition and concrete
rooted guides with one palette entry per vertex. The empty graph needs none. -/
theorem exists_card_bound [Finite V] (G : SimpleGraph V) :
    Nonempty (GuidedDecomposition G Set.univ (Nat.card V)) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let e : V ≃ Fin (Nat.card V) := Fintype.equivFinOfCardEq Nat.card_eq_fintype_card.symm
  let C : System G Set.univ (Nat.card V) := fun i => componentColor Set.univ (e.symm i)
  let D : Decomposition G Set.univ := {
    Node := (G.induce Set.univ).ConnectedComponent
    finiteNode := inferInstance
    forest := ⊥
    acyclic := SimpleGraph.isAcyclic_bot
    bag := componentFiber G Set.univ
    inside := fun _ => componentFiber_inside _
    vertex := fun x hx => ⟨(G.induce Set.univ).connectedComponentMk ⟨x,hx⟩,hx,rfl⟩
    edge := by
      intro x y hxy hx hy
      refine ⟨(G.induce Set.univ).connectedComponentMk ⟨x,hx⟩,⟨hx,rfl⟩,hy,?_⟩
      exact SimpleGraph.ConnectedComponent.sound
        (show (G.induce Set.univ).Reachable ⟨y,hy⟩ ⟨x,hx⟩ from
          (show (G.induce Set.univ).Adj ⟨y,hy⟩ ⟨x,hx⟩ from hxy.symm).reachable)
    running := by
      intro x a b ha hb
      obtain ⟨hx,he⟩ := ha
      obtain ⟨_,hf⟩ := hb
      have hab : a = b := he.symm.trans hf
      rw [← hab]
      exact ReachIn.refl (G := (⊥ : SimpleGraph (G.induce Set.univ).ConnectedComponent))
        (S := {a | x ∈ componentFiber G Set.univ a}) ⟨hx,he⟩ }
  refine ⟨⟨D,C,?_⟩⟩
  intro a hb
  obtain ⟨x,hx⟩ := hb
  refine ⟨x,?_⟩
  intro r hr
  refine ⟨e r,?_⟩
  simpa only [C,Equiv.symm_apply_apply,componentColor_self,component,Set.mem_ofPred_eq]
    using componentFiber_connected a hx hr

theorem exists_bounded [Finite V] (G : SimpleGraph V) (h : Nat.card V ≤ c) :
    Nonempty (GuidedDecomposition G Set.univ c) := by
  obtain ⟨D⟩ := exists_card_bound G
  exact ⟨D.pad h⟩
end GuidedDecomposition

#print axioms GuidedDecomposition.exists_card_bound
end StackSorting.GuidedPathwidth
