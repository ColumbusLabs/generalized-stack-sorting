import NestedFlattenedBags

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.GraphWidth.Nested.NestedInput
open FinitePort
variable {n t : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (N : NestedInput D)

/-- A child adhesion is present at the actual derived parent attachment. -/
theorem adhesion_at_attachment {x : Fin t} (hx : x.val≠0) {v : Fin n}
    (hv : outerAdhesion D x v) :
    v ∈ N.bagOn ⟨T.parent x,N.attachment x⟩ := by
  classical
  by_cases he : introductionNode D v=T.parent x
  · let u := (N.names (T.parent x)).symm ⟨v,he⟩
    have hu : u ∈ N.interface x := by
      apply (N.mem_interface x u).mpr
      simpa only [u,Equiv.apply_symm_apply] using hv
    have hb := (N.attachment_spec x hx).1 u hu
    apply (N.mem_bagOn _ _ _).mpr
    exact Or.inr ⟨u,hb,by simp only [u,Equiv.apply_symm_apply]⟩
  · exact (N.mem_bagOn _ _ _).mpr (Or.inl ⟨adhesion_parent_mem hv,he⟩)

/-- Within one local tree, occurrences stay connected after adding the outer
adhesion to every local bag. -/
theorem local_bag_walk (x : Fin t) {v : Fin n} {i j : Fin (N.nodes x)}
    (hi : v ∈ N.bagOn ⟨x,i⟩) (hj : v ∈ N.bagOn ⟨x,j⟩) :
    Walk N.substitution.Adj (fun a => v ∈ N.bagOn a) ⟨x,i⟩ ⟨x,j⟩ := by
  classical
  apply N.substitution.local_walk x
  by_cases ha : outerAdhesion D x v
  · exact (tree_connected (N.localTree x) i j).mono
      (fun y _ => (N.mem_bagOn x y v).mpr (Or.inl ha))
  · obtain ⟨u,hu,he⟩ := ((N.mem_bagOn x i v).mp hi).resolve_left ha
    obtain ⟨w,hw,hf⟩ := ((N.mem_bagOn x j v).mp hj).resolve_left ha
    have huw : u=w := (N.names x).injective (Subtype.ext (he.trans hf.symm))
    subst w
    exact ((N.localDecomp x).running hu hw).mono
      (fun y hy => (N.mem_bagOn x y v).mpr (Or.inr ⟨u,hy,he⟩))

/-- The real cross-tree edge has bags containing each overlap vertex at both ends. -/
theorem child_parent_bag_walk (x : Fin t) (hx : x.val≠0) {v : Fin n}
    {i : Fin (N.nodes x)} {j : Fin (N.nodes (T.parent x))}
    (hi : v ∈ N.bagOn ⟨x,i⟩) (hj : v ∈ N.bagOn ⟨T.parent x,j⟩) :
    Walk N.substitution.Adj (fun a => v ∈ N.bagOn a) ⟨x,i⟩ ⟨T.parent x,j⟩ := by
  have ha := overlap_adhesion hx (N.bagOn_subset ⟨x,i⟩ hi)
    (N.bagOn_subset ⟨T.parent x,j⟩ hj)
  have hr : v ∈ N.bagOn (N.substitution.localRoot x) :=
    (N.mem_bagOn x ⟨0,N.local_nonempty x⟩ v).mpr (Or.inl ha)
  have hp := N.adhesion_at_attachment hx ha
  have hcross : Walk N.substitution.Adj (fun a => v ∈ N.bagOn a)
      (N.substitution.localRoot x) ⟨T.parent x,N.attachment x⟩ :=
    .step hr (N.substitution.attachment_adjacency x hx) (.refl hp)
  exact (N.local_bag_walk x hi hr).trans
    (hcross.trans (N.local_bag_walk (T.parent x) hp hj))

theorem neighbour_bag_walk {x y : Fin t} (hxy : TreeAdj T x y) {v : Fin n}
    {i : Fin (N.nodes x)} {j : Fin (N.nodes y)}
    (hi : v ∈ N.bagOn ⟨x,i⟩) (hj : v ∈ N.bagOn ⟨y,j⟩) :
    Walk N.substitution.Adj (fun a => v ∈ N.bagOn a) ⟨x,i⟩ ⟨y,j⟩ := by
  rcases hxy with ⟨hx,rfl⟩ | ⟨hy,rfl⟩
  · exact N.child_parent_bag_walk x hx hi hj
  · exact (N.child_parent_bag_walk y hy hj hi).reverse N.substitution.adj_symm

/-- Lift the actual old occurrence walk by genuine local occurrence walks
and the concrete attachment edges; no global running witness is a premise. -/
theorem outer_bag_walk {v : Fin n} {x y : Fin t}
    (h : Walk (TreeAdj T) (fun z => v ∈ D.bag z) x y)
    {i : Fin (N.nodes x)} {j : Fin (N.nodes y)}
    (hi : v ∈ N.bagOn ⟨x,i⟩) (hj : v ∈ N.bagOn ⟨y,j⟩) :
    Walk N.substitution.Adj (fun a => v ∈ N.bagOn a) ⟨x,i⟩ ⟨y,j⟩ := by
  induction h with
  | refl => exact N.local_bag_walk _ hi hj
  | @step x z y hx hxz hzy ih =>
    obtain ⟨q,hq⟩ := N.occurs_at_outer hzy.start
    exact (N.neighbour_bag_walk hxz hi hq).trans (ih hq hj)

theorem bagOn_running {v : Fin n} {a b : N.substitution.Node}
    (ha : v ∈ N.bagOn a) (hb : v ∈ N.bagOn b) :
    Walk N.substitution.Adj (fun q => v ∈ N.bagOn q) a b :=
  N.outer_bag_walk (D.running (N.bagOn_subset a ha) (N.bagOn_subset b hb)) ha hb

/-- The actual flattened decomposition retains exactly the original graph.
Its new tree and all bag/running witnesses are constructed from the nested input. -/
noncomputable def flattened : Decomposition G N.substitution.tree where
  bag i := N.bagOn (N.substitution.label i)
  nodup i := N.bagOn_nodup _
  vertex v := by
    obtain ⟨a,ha⟩ := N.bagOn_vertex v
    exact ⟨N.substitution.index a,by simpa only [TreeSubstitution.label_index] using ha⟩
  edge h := by
    obtain ⟨a,hu,hv⟩ := N.bagOn_edge h
    exact ⟨N.substitution.index a,by simpa only [TreeSubstitution.label_index] using hu,
      by simpa only [TreeSubstitution.label_index] using hv⟩
  running := by
    intro v i j hi hj
    have h := N.substitution.walk_index (N.bagOn_running hi hj)
    simpa only [TreeSubstitution.index_label] using h

/-- The additive bound uses actual adhesion and local bag sizes. -/
theorem flattened_bound {a b : Nat}
    (ha : ∀ x, (N.adhesionList x).length ≤ a)
    (hb : ∀ x, (N.localDecomp x).BagBound b) : N.flattened.BagBound (a+b) := by
  intro i
  exact N.bagOn_bound ha hb (N.substitution.label i)

#print axioms bagOn_running
#print axioms flattened
#print axioms flattened_bound
end StackSorting.GraphWidth.Nested.NestedInput
