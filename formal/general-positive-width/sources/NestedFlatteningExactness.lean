import NestedCarrierSemantics

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.GraphWidth.Nested.CarrierSemantics
open FinitePort
variable {n t : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}

@[simp] theorem outerParent_iff (N : NestedInput D) (x : Fin t) (q : Carrier N) :
    (relations N).outerParent (outer N x) q ↔
      x.val≠0 ∧ q=outer N (T.parent x) := by
  rcases q with v | (y | b) <;> simp [relations,outer,eq_comm]

/-- Literal cross-parent syntax selects the actual derived root-nearest
attachment; its endpoint is no longer merely specified by a coverage test. -/
theorem crossParent_exact (N : NestedInput D) (a b : N.substitution.Node) :
    Syntax.CrossParent (relations N) (localNode N a) (localNode N b) ↔
      a.2.val=0 ∧ a.1.val≠0 ∧ b=⟨T.parent a.1,N.attachment a.1⟩ := by
  constructor
  · rintro ⟨hr,c,p,hc,hp,hb,hn⟩
    have hc' := (owner_local_iff N a c).mp hc
    subst c
    obtain ⟨hx,hp'⟩ := (outerParent_iff N a.1 p).mp hp
    subst p
    have hb' := (owner_local_iff N b _).mp hb
    have hfirst : T.parent a.1=b.1 := by
      simpa only [outer,Sum.inr.injEq,Sum.inl.injEq] using hb'
    rcases a with ⟨x,i⟩
    rcases b with ⟨y,j⟩
    simp only at hfirst
    subst y
    have hn' := (nearest_local_iff N x hx j).mp hn
    have hj := rootNearest_unique (N.localDecomp (T.parent x)) (N.interface x)
      hn' (N.attachment_spec x hx)
    exact ⟨hr,hx,by rw [hj]⟩
  · rintro ⟨hr,hx,rfl⟩
    refine ⟨hr,outer N a.1,outer N (T.parent a.1),?_,?_,?_,?_⟩
    · exact (owner_local_iff N _ _).mpr rfl
    · exact (outerParent_iff N _ _).mpr ⟨hx,rfl⟩
    · exact (owner_local_iff N _ _).mpr rfl
    · exact (nearest_local_iff N a.1 hx (N.attachment a.1)).mpr (N.attachment_spec a.1 hx)

theorem node_eq_root_iff (N : NestedInput D) (a : N.substitution.Node) :
    a=N.substitution.root ↔ a.1.val=0 ∧ a.2.val=0 := by
  constructor
  · rintro rfl; exact ⟨rfl,rfl⟩
  · rintro ⟨hx,hi⟩
    obtain ⟨x,i⟩ := a
    have ex : x=N.substitution.root.1 := Fin.ext hx
    cases ex
    have ei : i=N.substitution.root.2 := Fin.ext hi
    cases ei
    rfl

/-- Exact actual strict parent relation of the constructed flattened tree,
expressed before its parent-preserving numbering. -/
theorem flattenedParent_exact (N : NestedInput D) (a b : N.substitution.Node) :
    ((relations N).localParent (localNode N a) (localNode N b) ∨
      Syntax.CrossParent (relations N) (localNode N a) (localNode N b)) ↔
      a≠N.substitution.root ∧ N.substitution.parent a=b := by
  rw [crossParent_exact]
  change ((a.2.val≠0 ∧ b=⟨a.1,(N.localTree a.1).parent a.2⟩) ∨
    (a.2.val=0 ∧ a.1.val≠0 ∧ b=⟨T.parent a.1,N.attachment a.1⟩)) ↔ _
  by_cases hi : a.2.val=0
  · by_cases hx : a.1.val=0
    · have hr := (node_eq_root_iff N a).mpr ⟨hx,hi⟩
      constructor
      · rintro (⟨hn,_⟩ | ⟨_,hn,_⟩)
        · exact (hn hi).elim
        · exact (hn hx).elim
      · rintro ⟨hn,_⟩
        exact (hn hr).elim
    · have hr : a≠N.substitution.root := fun h => hx ((node_eq_root_iff N a).mp h).1
      have hp : N.substitution.parent a=⟨T.parent a.1,N.attachment a.1⟩ := by
        unfold TreeSubstitution.parent
        split
        · contradiction
        · rfl
      constructor
      · rintro (⟨hn,_⟩ | ⟨_,_,h⟩)
        · exact (hn hi).elim
        · exact ⟨hr,hp.trans h.symm⟩
      · rintro ⟨_,h⟩
        exact Or.inr ⟨hi,hx,(hp.symm.trans h).symm⟩
  · have hr : a≠N.substitution.root := fun h => hi ((node_eq_root_iff N a).mp h).2
    have hp : N.substitution.parent a=⟨a.1,(N.localTree a.1).parent a.2⟩ := by
      unfold TreeSubstitution.parent
      split
      · rfl
      · contradiction
    constructor
    · rintro (⟨_,h⟩ | ⟨hn,_,_⟩)
      · exact ⟨hr,hp.trans h.symm⟩
      · exact (hi hn).elim
    · rintro ⟨_,h⟩
      exact Or.inl ⟨hi,(hp.symm.trans h).symm⟩

theorem flattenedBag_exact (N : NestedInput D) (a : N.substitution.Node) (v : Fin n) :
    ((relations N).localBag (localNode N a) (vertex N v) ∨
      ∃ x, (relations N).owner (localNode N a) x ∧ (relations N).adhesion x (vertex N v)) ↔
      v∈N.bagOn a := by
  have hx : (∃ x, (relations N).owner (localNode N a) x ∧
      (relations N).adhesion x (vertex N v)) ↔ outerAdhesion D a.1 v := by
    constructor
    · rintro ⟨x,hx,hv⟩
      obtain rfl := (owner_local_iff N a x).mp hx
      exact hv
    · intro hv
      exact ⟨outer N a.1,(owner_local_iff N a _).mpr rfl,hv⟩
  rw [hx,N.mem_bagOn]
  change ((∃ u, u∈(N.localDecomp a.1).bag a.2 ∧ (N.names a.1 u).val=v) ∨
    outerAdhesion D a.1 v) ↔ _
  exact or_comm

/-- The literal bag formula denotes the actual numbered flattened bag. -/
theorem literal_bag_exact (N : NestedInput D) (i : Fin (Fintype.card N.substitution.Node))
    (v : Fin n) :
    StackSorting.SparseEndpointMSO.FiniteCopy.ActualEval (Syntax.atoms (relations N))
      (Syntax.flattenedBagAt (b:=0) (0 : Fin 2) 1)
      (Fin.cases (localNode N (N.substitution.label i)) (fun _ => vertex N v)) Fin.elim0 ↔
      v∈N.flattened.bag i := by
  rw [Syntax.eval_flattenedBagAt]
  exact flattenedBag_exact N _ v

/-- Strict parent syntax preserves the actual numbered tree parent exactly,
including the exclusion of its root loop. -/
theorem literal_parent_exact (N : NestedInput D)
    (i j : Fin (Fintype.card N.substitution.Node)) :
    StackSorting.SparseEndpointMSO.FiniteCopy.ActualEval (Syntax.atoms (relations N))
      (Syntax.flattenedParentAt (b:=0) (0 : Fin 2) 1)
      (Fin.cases (localNode N (N.substitution.label i))
        (fun _ => localNode N (N.substitution.label j))) Fin.elim0 ↔
      i.val≠0 ∧ N.substitution.tree.parent i=j := by
  rw [Syntax.eval_flattenedParentAt]
  change ((relations N).localParent (localNode N (N.substitution.label i))
      (localNode N (N.substitution.label j)) ∨
    Syntax.CrossParent (relations N) (localNode N (N.substitution.label i))
      (localNode N (N.substitution.label j))) ↔ _
  rw [flattenedParent_exact]
  constructor
  · rintro ⟨hr,hp⟩
    refine ⟨fun h => hr (N.substitution.exact_root i h),?_⟩
    apply N.substitution.label_injective
    rw [N.substitution.exact_parent,hp]
  · rintro ⟨hi,hp⟩
    refine ⟨fun h => hi ((N.substitution.label_eq_root_iff i).mp h),?_⟩
    rw [← N.substitution.exact_parent,hp]

#print axioms literal_bag_exact
#print axioms literal_parent_exact
end StackSorting.GraphWidth.Nested.CarrierSemantics
