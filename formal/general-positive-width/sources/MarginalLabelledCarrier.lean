import MarginalNumberedCodes
import RootedLocalLabelLaws

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
variable {n t k : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k)

abbrev LabelledCarrier := Fin n ⊕ (Fin t ⊕ F.LocalLabels)

def labelledRelations : Nested.Syntax.Relations F.LabelledCarrier where
  original z := match z with | .inl _ => True | _ => False
  localNode z := match z with | .inr (.inr _) => True | _ => False
  localRoot z := match z with | .inr (.inr a) => a.2=none | _ => False
  owner z o := match z,o with | .inr (.inr a),.inr (.inl x) => a.1=x | _,_ => False
  margin o z := match o,z with | .inr (.inl x),.inl v => introductionNode D v=x | _,_ => False
  adhesion o z := match o,z with | .inr (.inl x),.inl v => outerAdhesion D x v | _,_ => False
  outerParent x y := match x,y with
    | .inr (.inl x),.inr (.inl y) => x.val≠0 ∧ T.parent x=y
    | _,_ => False
  localParent a b := match a,b with
    | .inr (.inr a),.inr (.inr b) => a.2≠none ∧ b=⟨a.1,RootedLocal.parent (F.normalized a.1).order a.2⟩
    | _,_ => False
  localBag a v := match a,v with
    | .inr (.inr a),.inl v => ∃ w u, a.2=some w ∧ u∈(F.normalized a.1).bag w ∧ (F.names a.1 u).val=v
    | _,_ => False
  originalEdge u v := match u,v with | .inl u,.inl v => G.Adj u v | _,_ => False

noncomputable def labelledFlatEquiv : F.LabelledCarrier ≃ NestedCodes.FlatCarrier n t :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) F.localLabelsEquiv)

variable (ht : 0<t) (hm : ∀ x, ∃ v, introductionNode D v=x) (hc : ConnectedIntroductionComponents D)
noncomputable def numberedLabelEquiv : CarrierSemantics.Carrier (F.rootedNestedInput ht hm hc) ≃ F.LabelledCarrier :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) (Equiv.sigmaCongrRight F.rootedNames))

noncomputable def numberedLocalLabelEquiv : (F.rootedNestedInput ht hm hc).substitution.Node ≃ F.LocalLabels :=
  Equiv.sigmaCongrRight F.rootedNames

theorem numbered_local_root (a : (F.rootedNestedInput ht hm hc).substitution.Node) :
    (F.numberedLocalLabelEquiv ht hm hc a).2=none ↔ a.2.val=0 :=
  RootedLocal.label_eq_none_iff (F.normalized a.1).order a.2

theorem numbered_local_parent (a b : (F.rootedNestedInput ht hm hc).substitution.Node) :
    (F.numberedLocalLabelEquiv ht hm hc a).2≠none ∧
      F.numberedLocalLabelEquiv ht hm hc b=⟨a.1,RootedLocal.parent (F.normalized a.1).order
        (F.numberedLocalLabelEquiv ht hm hc a).2⟩ ↔
      a.2.val≠0 ∧ b=⟨a.1,((F.rootedNestedInput ht hm hc).localTree a.1).parent a.2⟩ := by
  have hp : F.numberedLocalLabelEquiv ht hm hc
      ⟨a.1,((F.rootedNestedInput ht hm hc).localTree a.1).parent a.2⟩=
      ⟨a.1,RootedLocal.parent (F.normalized a.1).order (F.numberedLocalLabelEquiv ht hm hc a).2⟩ := by
    apply congrArg (fun z => (⟨a.1,z⟩ : F.LocalLabels))
    exact RootedLocal.exact_parent (F.normalized a.1).order a.2
  rw [←hp,(F.numberedLocalLabelEquiv ht hm hc).injective.eq_iff]
  exact and_congr (not_congr (F.numbered_local_root ht hm hc a)) Iff.rfl

theorem numbered_local_bag (a : (F.rootedNestedInput ht hm hc).substitution.Node) (v : Fin n) :
    (∃ w u, (F.numberedLocalLabelEquiv ht hm hc a).2=some w ∧
      u∈(F.normalized a.1).bag w ∧ (F.names a.1 u).val=v) ↔
      ∃ u, u∈((F.rootedNestedInput ht hm hc).localDecomp a.1).bag a.2 ∧ (F.names a.1 u).val=v := by
  constructor
  · rintro ⟨w,u,hw,hu,hv⟩
    exact ⟨u,(RootedLocal.mem_bag_iff (F.normalized a.1) a.2 u).mpr ⟨w,hw,hu⟩,hv⟩
  · rintro ⟨u,hu,hv⟩
    obtain ⟨w,hw,hu⟩ := (RootedLocal.mem_bag_iff (F.normalized a.1) a.2 u).mp hu
    exact ⟨w,u,hw,hu,hv⟩

#print axioms numbered_local_root
#print axioms numbered_local_parent
#print axioms numbered_local_bag
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
