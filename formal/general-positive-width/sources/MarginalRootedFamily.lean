import MarginalLocalGuidance
import RootedLocalForest
import SaneParentConnector

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth
variable {n t k : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k)

/-- Fixed-copy-compatible local decomposition: one original-vertex node and
one empty root per outer owner. Arbitrary guidance index nodes are eliminated. -/
noncomputable def rootedNestedInput (ht : 0<t)
    (hm : ∀ x, ∃ v, introductionNode D v=x)
    (hc : ConnectedIntroductionComponents D) : NestedInput D where
  outerNonempty := ht
  vertices := F.vertices
  names := F.names
  marginNonempty := hm
  nodes x := Fintype.card (RootedLocal.Node (F.vertices x))
  localTree x := RootedLocal.tree (F.normalized x).order
  localDecomp x := RootedLocal.decomposition (F.normalized x)
  connector := sane_parent_margin_connector D hm hc

theorem rootedNestedInput_bound (ht : 0<t)
    (hm : ∀ x, ∃ v, introductionNode D v=x)
    (hc : ConnectedIntroductionComponents D) (x : Fin t) :
    ((F.rootedNestedInput ht hm hc).localDecomp x).BagBound
      (BiInterface.PathWord.pathwidthPalette (2*k+2)) :=
  RootedLocal.decomposition_bound (F.normalized x) (F.normalized_bound x)

theorem rooted_nodes_count (ht : 0<t)
    (hm : ∀ x, ∃ v, introductionNode D v=x)
    (hc : ConnectedIntroductionComponents D) (x : Fin t) :
    (F.rootedNestedInput ht hm hc).nodes x=F.vertices x+1 := RootedLocal.node_count _

/-- Exact logical node labels, used instead of the arbitrary mathematical
numbering in the finite-copy output. -/
noncomputable def rootedNames (x : Fin t) :
    Fin (Fintype.card (RootedLocal.Node (F.vertices x))) ≃ Option (Fin (F.vertices x)) where
  toFun := RootedLocal.label (F.normalized x).order
  invFun := RootedLocal.index (F.normalized x).order
  left_inv := RootedLocal.index_label _
  right_inv := RootedLocal.label_index _

#print axioms rootedNestedInput
#print axioms rootedNestedInput_bound
#print axioms rooted_nodes_count
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
