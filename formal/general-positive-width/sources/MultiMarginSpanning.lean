import MultiMarginGeometry
import SubstitutionWalks

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.GraphWidth.MultiMargin
open FinitePort Nested
attribute [local instance] Classical.propDecidable
variable {n t : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}

/-- Lift an actual allowed-vertex walk to its subtype without changing edges. -/
theorem walk_subtype {α : Type} {adj : α → α → Prop} {P : α → Prop}
    {u v : α} (w : Walk adj P u v) (hu : P u) (hv : P v) :
    Walk (fun a b : {x // P x} => adj a.val b.val) (fun _ => True) ⟨u,hu⟩ ⟨v,hv⟩ := by
  induction w with
  | refl _ => exact .refl trivial
  | @step u a v hu' he w ih => exact .step trivial he (ih w.start hv)

theorem walk_map {α β : Type} {adj : α → α → Prop} {adj' : β → β → Prop}
    (f : α → β) (he : ∀ {u v}, adj u v → adj' (f u) (f v)) {u v : α}
    (w : Walk adj (fun _ => True) u v) : Walk adj' (fun _ => True) (f u) (f v) := by
  induction w with
  | refl _ => exact .refl trivial
  | step _ h _ ih => exact .step trivial (he h) ih

noncomputable def marginSize (x : Fin t) : Nat := Fintype.card {v : Fin n // Margin D x v}
noncomputable def marginNames (x : Fin t) : Fin (marginSize (D := D) x) ≃ {v : Fin n // Margin D x v} :=
  (Fintype.equivFin _).symm

noncomputable def localGraph (x : Fin t) : Graph (marginSize (D := D) x) where
  Adj u v := (Completion D).Adj ((marginNames x) u).val ((marginNames x) v).val
  symm := (Completion D).symm
  loopless _u := (Completion D).loopless _

theorem local_connected (s : Sane D) (x : Fin t) (u v : Fin (marginSize (D := D) x)) :
    Walk (localGraph x).Adj (fun _ => True) u v := by
  have w := walk_subtype (marginal_connected s ((marginNames x) u).property
    ((marginNames x) v).property) ((marginNames x) u).property ((marginNames x) v).property
  have h := walk_map (marginNames x).symm (adj' := (localGraph x).Adj) (by
    intro a b he
    simpa only [localGraph,Equiv.apply_symm_apply] using he) w
  change Walk (localGraph x).Adj (fun _ => True)
    ((marginNames x).symm ((marginNames x) u)) ((marginNames x).symm ((marginNames x) v)) at h
  simpa only [Equiv.symm_apply_apply] using h

/-- A genuine completed edge from the parent margin into the child margin. -/
theorem exists_bridge (s : Sane D) (x : Fin t) (hx : x.val ≠ 0) :
    ∃ p : Fin n × Fin n, Margin D (T.parent x) p.1 ∧ Margin D x p.2 ∧
      (Completion D).Adj p.1 p.2 := by
  have hc := connector_spec s x hx
  obtain ⟨v,hv,he⟩ := adhesion_margin_neighbor s hc.2
  exact ⟨(connector s x hx,v),hc.1,hv,he⟩

noncomputable def bridge (s : Sane D) (x : Fin t) (hx : x.val ≠ 0) : Fin n × Fin n :=
  Classical.choose (exists_bridge s x hx)

theorem bridge_spec (s : Sane D) (x : Fin t) (hx : x.val ≠ 0) :
    Margin D (T.parent x) (bridge s x hx).1 ∧ Margin D x (bridge s x hx).2 ∧
      (Completion D).Adj (bridge s x hx).1 (bridge s x hx).2 :=
  Classical.choose_spec (exists_bridge s x hx)

noncomputable def entry (s : Sane D) (x : Fin t) : Fin n :=
  if hx : x.val ≠ 0 then (bridge s x hx).2 else Classical.choose (s.margin_nonempty x)

theorem entry_mem (s : Sane D) (x : Fin t) : Margin D x (entry s x) := by
  unfold entry
  split_ifs with hx
  · exact (bridge_spec s x hx).2.1
  · exact Classical.choose_spec (s.margin_nonempty x)

theorem marginSize_pos (s : Sane D) (x : Fin t) : 0<marginSize (D := D) x := by
  let e := (marginNames x).symm ⟨entry s x,entry_mem s x⟩
  exact Nat.zero_lt_of_lt e.isLt

noncomputable def localRoot (s : Sane D) (x : Fin t) : Fin (marginSize (D := D) x) :=
  (marginNames x).symm ⟨entry s x,entry_mem s x⟩

noncomputable def localSpanning (s : Sane D) (x : Fin t) :=
  relabeledSpanningTree (localGraph (D := D) x).Adj (local_connected s x) (localRoot s x)

/-- Root each child marginal tree at the endpoint of its selected incoming
bridge. This is what makes the union a literal substituted parent tree. -/
noncomputable def substitution (s : Sane D) (ht : 0<t) : TreeSubstitution T where
  outerNonempty := ht
  size := marginSize (D := D)
  positive := marginSize_pos s
  localTree x := (localSpanning s x).tree
  attachment x := if hx : x.val ≠ 0 then
    (localSpanning s (T.parent x)).index ((marginNames (T.parent x)).symm
      ⟨(bridge s x hx).1,(bridge_spec s x hx).1⟩) else ⟨0,marginSize_pos s _⟩

namespace Encoding
variable (s : Sane D) (ht : 0<t)
abbrev Node := (substitution s ht).Node
noncomputable def vertex (a : Node s ht) : Fin n :=
  ((marginNames a.1) ((localSpanning s a.1).label a.2)).val

@[simp] theorem vertex_margin (a : Node s ht) : Margin D a.1 (vertex s ht a) :=
  ((marginNames a.1) ((localSpanning s a.1).label a.2)).property

noncomputable def index (v : Fin n) : Node s ht :=
  ⟨introductionNode D v,(localSpanning s (introductionNode D v)).index
    ((marginNames (introductionNode D v)).symm ⟨v,rfl⟩)⟩

@[simp] theorem vertex_index (v : Fin n) : vertex s ht (index s ht v)=v := by
  simp only [vertex,index,RelabeledSpanningTree.label_index,Equiv.apply_symm_apply]

theorem index_of_margin (v : Fin n) (x : Fin t) (hv : Margin D x v) :
    index s ht v=⟨x,(localSpanning s x).index ((marginNames x).symm ⟨v,hv⟩)⟩ := by
  cases hv
  rfl

@[simp] theorem index_vertex (a : Node s ht) : index s ht (vertex s ht a)=a := by
  rcases a with ⟨x,u⟩
  rw [index_of_margin s ht _ x (vertex_margin s ht _)]
  have hsub : (⟨vertex s ht ⟨x,u⟩,vertex_margin s ht _⟩ : {v // Margin D x v})=
      (marginNames x) ((localSpanning s x).label u) := by rfl
  rw [hsub,Equiv.symm_apply_apply,RelabeledSpanningTree.index_label]

noncomputable def vertexEquiv : Node s ht ≃ Fin n where
  toFun := vertex s ht
  invFun := index s ht
  left_inv := index_vertex s ht
  right_inv := vertex_index s ht

/-- The root of a local tree is the actual chosen incoming endpoint. -/
theorem vertex_localRoot (x : Fin t) :
    vertex s ht ((substitution s ht).localRoot x)=entry s x := by
  unfold vertex TreeSubstitution.localRoot
  rw [(localSpanning s x).label_root _ rfl]
  simp only [localRoot,Equiv.apply_symm_apply]

/-- Internal marginal spanning-tree edges, with original vertices unchanged. -/
def M (u v : Fin n) : Prop :=
  ∃ (x : Fin t) (a b : Fin (marginSize (D := D) x)),
    u=vertex s ht ⟨x,a⟩ ∧ v=vertex s ht ⟨x,b⟩ ∧ TreeAdj (localSpanning s x).tree a b

/-- Exactly one unordered connector edge per nonroot outer node. -/
def K (u v : Fin n) : Prop :=
  ∃ (x : Fin t) (hx : x.val ≠ 0),
    (u=(bridge s x hx).1 ∧ v=(bridge s x hx).2) ∨
    (v=(bridge s x hx).1 ∧ u=(bridge s x hx).2)

theorem M_completed {u v} (h : M s ht u v) : (Completion D).Adj u v := by
  obtain ⟨x,a,b,rfl,rfl,he⟩ := h
  exact (localSpanning s x).edge (localGraph x).symm he

theorem K_completed {u v} (h : K s u v) : (Completion D).Adj u v := by
  obtain ⟨x,hx,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := h
  · exact (bridge_spec s x hx).2.2
  · exact (Completion D).symm (bridge_spec s x hx).2.2

theorem M_same_margin {u v} (h : M s ht u v) : introductionNode D u=introductionNode D v := by
  obtain ⟨x,a,b,rfl,rfl,_⟩ := h
  exact (vertex_margin s ht ⟨x,a⟩).trans (vertex_margin s ht ⟨x,b⟩).symm

theorem K_different_margin {u v} (h : K s u v) : introductionNode D u≠introductionNode D v := by
  obtain ⟨x,hx,h⟩ := h
  have hb := bridge_spec s x hx
  have hl := T.parent_lt x hx
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    rw [hb.1,hb.2.1] <;> intro he <;> have := congrArg Fin.val he <;> omega

theorem MK_disjoint {u v} (hm : M s ht u v) (hk : K s u v) : False :=
  K_different_margin s hk (M_same_margin s ht hm)

theorem M_walk_same_margin {u v} (w : Walk (M s ht) (fun _ => True) u v) :
    introductionNode D u=introductionNode D v := by
  induction w with
  | refl => rfl
  | step _ he _ ih => exact (M_same_margin s ht he).trans ih

/-- Every original margin is exactly one M-component. -/
theorem M_component_exact (u v : Fin n) :
    Walk (M s ht) (fun _ => True) u v ↔ introductionNode D u=introductionNode D v := by
  constructor
  · exact M_walk_same_margin s ht
  · intro he
    let a := index s ht u
    let b := index s ht v
    have hab : a.1=b.1 := he
    have hu : vertex s ht a=u := vertex_index s ht u
    have hv : vertex s ht b=v := vertex_index s ht v
    rcases a with ⟨x,i⟩
    rcases b with ⟨y,j⟩
    simp only at hab
    subst y
    rw [← hu,← hv]
    exact walk_map (fun z => vertex s ht ⟨x,z⟩)
      (fun {i j} hij => ⟨x,i,j,rfl,rfl,hij⟩) (tree_connected (localSpanning s x).tree i j)

theorem vertex_attachment (x : Fin t) (hx : x.val ≠ 0) :
    vertex s ht ⟨T.parent x,(substitution s ht).attachment x⟩=(bridge s x hx).1 := by
  simp only [vertex,substitution,dite_eq_left hx,RelabeledSpanningTree.label_index,
    Equiv.apply_symm_apply]

theorem M_union {u v} (h : M s ht u v) :
    (substitution s ht).Adj (index s ht u) (index s ht v) := by
  obtain ⟨x,a,b,rfl,rfl,he⟩ := h
  rw [index_vertex,index_vertex]
  exact (substitution s ht).local_adjacency x he

theorem K_union {u v} (h : K s u v) :
    (substitution s ht).Adj (index s ht u) (index s ht v) := by
  obtain ⟨x,hx,h⟩ := h
  have ha := (substitution s ht).attachment_adjacency x hx
  have he : vertex s ht ((substitution s ht).localRoot x)=(bridge s x hx).2 := by
    rw [vertex_localRoot]
    simp only [entry,dite_eq_left hx]
  have hf := vertex_attachment s ht x hx
  have hb : index s ht (bridge s x hx).2=(substitution s ht).localRoot x := by
    rw [← he,index_vertex]
  have hc : index s ht (bridge s x hx).1=⟨T.parent x,(substitution s ht).attachment x⟩ := by
    rw [← hf,index_vertex]
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rw [hc,hb]
    exact (substitution s ht).adj_symm ha
  · rw [hb,hc]
    exact ha

theorem parent_is_MK (a : Node s ht) (ha : a≠(substitution s ht).root) :
    M s ht (vertex s ht a) (vertex s ht ((substitution s ht).parent a)) ∨
    K s (vertex s ht a) (vertex s ht ((substitution s ht).parent a)) := by
  rcases a with ⟨x,i⟩
  by_cases hi : i.val ≠ 0
  · left
    simp [TreeSubstitution.parent,hi]
    exact ⟨x,i,(localSpanning s x).tree.parent i,rfl,rfl,Or.inl ⟨hi,rfl⟩⟩
  · have hiz : i.val=0 := Classical.not_not.mp hi
    have hx : x.val ≠ 0 := by
      intro hx
      apply ha
      have ex : x=(substitution s ht).root.1 := Fin.ext hx
      cases ex
      have ei : i=(substitution s ht).root.2 := Fin.ext hiz
      cases ei
      rfl
    right
    have eil : (⟨x,i⟩ : Node s ht)=(substitution s ht).localRoot x := by
      congr 1
      exact Fin.ext hiz
    rw [eil,(substitution s ht).parent_localRoot x hx,vertex_localRoot,vertex_attachment s ht x hx]
    simp only [entry,dite_eq_left hx]
    exact ⟨x,hx,Or.inr ⟨rfl,rfl⟩⟩

theorem M_symm {u v} (h : M s ht u v) : M s ht v u := by
  obtain ⟨x,a,b,hu,hv,he⟩ := h
  exact ⟨x,b,a,hv,hu,(treeAdj_symm _) he⟩

theorem K_symm {u v} (h : K s u v) : K s v u := by
  obtain ⟨x,hx,h⟩ := h
  exact ⟨x,hx,h.symm⟩

/-- The union is exactly the concrete substituted parent tree. Its rank,
parent and original-vertex bijection are all constructed above. -/
theorem union_exact (a b : Node s ht) :
    (substitution s ht).Adj a b ↔ M s ht (vertex s ht a) (vertex s ht b) ∨
      K s (vertex s ht a) (vertex s ht b) := by
  constructor
  · rintro (⟨ha,he⟩ | ⟨hb,he⟩)
    · rw [← he]
      exact parent_is_MK s ht a ha
    · rw [← he]
      rcases parent_is_MK s ht b hb with h | h
      · exact Or.inl (M_symm s ht h)
      · exact Or.inr (K_symm s h)
  · rintro (h | h)
    · have he := M_union s ht h
      simpa only [index_vertex] using he
    · have he := K_union s ht h
      simpa only [index_vertex] using he

def Union (u v : Fin n) : Prop := M s ht u v ∨ K s u v

theorem union_connected (u v : Fin n) : Walk (Union s ht) (fun _ => True) u v := by
  let S := substitution s ht
  have h := tree_connected S.tree (S.index (index s ht u)) (S.index (index s ht v))
  have w := walk_map (fun i => vertex s ht (S.label i)) (adj' := Union s ht)
    (by
      intro i j he
      apply (union_exact s ht _ _).mp
      apply (S.exact_adjacency _ _).mp
      simpa only [S.index_label] using he) h
  simpa only [S.label_index,vertex_index] using w

/-- Exact numbering of M∪K by a genuine parent-numbered tree. The theorem
retains the acyclicity certificate structurally, with no spanning-forest premise. -/
theorem union_numbered (u v : Fin n) :
    Union s ht u v ↔ TreeAdj (substitution s ht).tree
      ((substitution s ht).index (index s ht u)) ((substitution s ht).index (index s ht v)) := by
  rw [(substitution s ht).exact_adjacency,union_exact,vertex_index,vertex_index]
  rfl

#print axioms local_connected
#print axioms exists_bridge
#print axioms vertexEquiv
#print axioms MK_disjoint
#print axioms M_component_exact
#print axioms union_numbered
#print axioms union_connected
end Encoding
end StackSorting.GraphWidth.MultiMargin
