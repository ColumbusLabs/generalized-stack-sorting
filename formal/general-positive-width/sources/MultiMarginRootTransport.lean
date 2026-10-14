import MultiMarginRealizedLinks

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.GraphWidth.MultiMargin
open FinitePort Nested
variable {n t : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}

/-- Graph equivalence transports every allowed-vertex walk, including deletion. -/
theorem equiv_walk_iff {α β : Type} (e : α ≃ β) (E : α → α → Prop) (F : β → β → Prop)
    (he : ∀ u v, E u v ↔ F (e u) (e v)) (P : β → Prop) (u v : α) :
    Walk E (fun z => P (e z)) u v ↔ Walk F P (e u) (e v) := by
  constructor
  · intro w
    induction w with
    | refl hp => exact .refl hp
    | step hp hh _ ih => exact .step hp ((he _ _).mp hh) ih
  · have back : ∀ {x y}, Walk F P x y → Walk E (fun z => P (e z)) (e.symm x) (e.symm y) := by
      intro x y w
      induction w with
      | refl hp => exact .refl (by simpa only [Equiv.apply_symm_apply] using hp)
      | step hp hh _ ih =>
        exact .step (by simpa only [Equiv.apply_symm_apply] using hp)
          ((he _ _).mpr (by simpa only [Equiv.apply_symm_apply] using hh)) ih
    intro w
    simpa only [Equiv.symm_apply_apply] using back w

namespace Encoding
variable (s : Sane D) (ht : 0<t)

noncomputable def numberedEquiv : Fin n ≃ Fin (Fintype.card (Node s ht)) :=
  (vertexEquiv s ht).symm.trans {
    toFun := (substitution s ht).index
    invFun := (substitution s ht).label
    left_inv := (substitution s ht).label_index
    right_inv := (substitution s ht).index_label }

@[simp] theorem numberedEquiv_apply (u : Fin n) : numberedEquiv s ht u=numberedVertex s ht u := rfl

theorem union_walk_numbered (P : Fin (Fintype.card (Node s ht)) → Prop) (u v : Fin n) :
    Walk (Union s ht) (fun z => P (numberedVertex s ht z)) u v ↔
      Walk (TreeAdj (substitution s ht).tree) P (numberedVertex s ht u) (numberedVertex s ht v) :=
  equiv_walk_iff (numberedEquiv s ht) _ _ (union_numbered s ht) P u v

theorem numbered_root_zero : (numberedVertex s ht (CompletedIncidence.rootVertex s ht)).val=0 := by
  unfold numberedVertex CompletedIncidence.rootVertex
  rw [index_vertex]
  exact ((substitution s ht).index_zero_iff _).mpr rfl

theorem root_avoid_exact (u v : Fin n) :
    (¬ Walk (Union s ht) (fun z => z≠u) v (CompletedIncidence.rootVertex s ht)) ↔
      UnionAncestor s ht u v := by
  let S := substitution s ht
  let r := numberedVertex s ht (CompletedIncidence.rootVertex s ht)
  have hp : (fun z => numberedVertex s ht z≠numberedVertex s ht u)=(fun z => z≠u) := by
    funext z
    apply propext
    exact not_congr ⟨fun h => (numberedEquiv s ht).injective h,congrArg (numberedVertex s ht)⟩
  rw [← hp,union_walk_numbered s ht (fun z => z≠numberedVertex s ht u)]
  change (¬ Walk (TreeAdj S.tree) (fun z => z≠numberedVertex s ht u) (numberedVertex s ht v) r) ↔
    FinitePort.Ancestor S.tree (numberedVertex s ht u) (numberedVertex s ht v)
  rw [← tree_rootSeparator_iff]
  constructor
  · intro h r' hr' _
    have he : r'=r := Fin.ext (hr'.trans (numbered_root_zero s ht).symm)
    simpa only [he] using h
  · intro h
    exact h r (numbered_root_zero s ht) (tree_connected S.tree _ _)

end Encoding

namespace CompletedIncidence
variable {α : Type} (H : CompletedIncidence D α) (s : Sane D) (ht : 0<t)

/-- Literal root-separator formula realizes genuine constructed union-tree
ancestry, including root existence and endpoint guards. -/
theorem ancestor_exact (u v : Fin n) :
    Syntax.Ancestor H.rel Syntax.fixed (H.parameters s ht) (H.vertex u) (H.vertex v) ↔
      Encoding.UnionAncestor s ht u v := by
  unfold Syntax.Ancestor
  have hu := (H.vertex_exact _).mpr ⟨u,rfl⟩
  have hr : (H.parameters s ht) Syntax.fixed.R=(fun z => z=H.vertex (rootVertex s ht)) := rfl
  simp only [hu,true_and,hr]
  have hc : Syntax.Connected H.rel Syntax.fixed (H.parameters s ht) .union none
      (H.vertex v) (H.vertex (rootVertex s ht)) :=
    (H.connected_exact s ht .union none v (rootVertex s ht)).mpr (Encoding.union_connected s ht v _)
  constructor
  · rintro ⟨_,h⟩
    apply (Encoding.root_avoid_exact s ht u v).mp
    intro w
    exact h (H.vertex (rootVertex s ht)) rfl hc
      ((H.connected_exact s ht .union (some u) v (rootVertex s ht)).mpr w)
  · intro h
    refine ⟨⟨H.vertex (rootVertex s ht),rfl,hc⟩,?_⟩
    intro r hr _ hw
    subst r
    exact (Encoding.root_avoid_exact s ht u v).mpr h
      ((H.connected_exact s ht .union (some u) v (rootVertex s ht)).mp hw)

theorem margin_exact (x : Fin t) (v : Fin n) :
    Syntax.Connected H.rel Syntax.fixed (H.parameters s ht) .marginal none
      (H.vertex (entry s x)) (H.vertex v) ↔ Margin D x v :=
  (H.connected_exact s ht .marginal none _ _).trans (Encoding.margin_exact s ht x v)

theorem component_exact (x : Fin t) (v : Fin n) :
    Syntax.Ancestor H.rel Syntax.fixed (H.parameters s ht) (H.vertex (entry s x)) (H.vertex v) ↔
      IntroductionComponent D x v :=
  (H.ancestor_exact s ht _ _).trans (Encoding.component_exact s ht x v)

/-- Existential intermediary vertices are forced into the original vertex
embedding by selected-link guards; no edge element can fake a parent. -/
theorem parent_exact (x y : Fin t) :
    Syntax.Parent H.rel Syntax.fixed (H.parameters s ht) (H.vertex (entry s x)) (H.vertex (entry s y)) ↔
      x.val≠0 ∧ T.parent x=y := by
  rw [← Encoding.parent_exact s ht x y]
  constructor
  · rintro ⟨w,hw,ha,hm⟩
    obtain ⟨u,v,he,hw,hk⟩ := (H.link_exact s ht .crossing _ _).mp hw
    have hu := H.injective he
    subst w
    refine ⟨v,?_,(H.ancestor_exact s ht _ _).mp ha,
      (H.connected_exact s ht .marginal none _ _).mp hm⟩
    simpa only [selected,← hu] using hk
  · rintro ⟨w,hk,ha,hm⟩
    exact ⟨H.vertex w,(H.link_exact s ht .crossing _ _).mpr ⟨_,_,rfl,rfl,hk⟩,
      (H.ancestor_exact s ht _ _).mpr ha,(H.connected_exact s ht .marginal none _ _).mpr hm⟩

/-- Original bag realization, with all quantified boundary witnesses forced
to be original vertices by the root-separator's explicit vertex guard. -/
theorem bag_exact (x : Fin t) (v : Fin n) :
    Syntax.Bag H.rel Syntax.fixed (H.parameters s ht) (H.vertex (entry s x)) (H.vertex v) ↔ v ∈ D.bag x := by
  rw [← Encoding.bag_exact s ht x v]
  unfold Syntax.Bag Encoding.RecoveredBag
  have hm := H.connected_exact s ht .marginal none (entry s x) v
  change Syntax.Connected H.rel Syntax.fixed (H.parameters s ht) .marginal none
    (H.vertex (entry s x)) (H.vertex v) ↔ Encoding.RecoveredMargin s ht (entry s x) v at hm
  rw [hm,H.ancestor_exact]
  apply or_congr Iff.rfl
  apply and_congr Iff.rfl
  constructor
  · rintro ⟨u,hu,he⟩
    obtain ⟨r,hr,hc⟩ := hu.2.1
    obtain ⟨w,rfl⟩ := (H.vertex_exact u).mp hc.1
    exact ⟨w,(H.ancestor_exact s ht _ _).mp hu,(H.original_pair v w).mp he⟩
  · rintro ⟨u,hu,he⟩
    exact ⟨H.vertex u,(H.ancestor_exact s ht _ _).mpr hu,(H.original_pair v u).mpr he⟩

#print axioms Encoding.root_avoid_exact
#print axioms ancestor_exact
#print axioms parent_exact
#print axioms bag_exact
end CompletedIncidence
end StackSorting.GraphWidth.MultiMargin
