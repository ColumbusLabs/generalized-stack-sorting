import NestedCliqueAttachment
import SubstitutionWalks

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.GraphWidth.Nested
open FinitePort
variable {n t : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}

/-- The introduction-based adhesion really lies in the actual parent's bag. -/
theorem adhesion_parent_mem {x : Fin t} {v : Fin n} (h : outerAdhesion D x v) :
    v ∈ D.bag (T.parent x) := by
  have ha := introduction_ancestor D h.1
  have hz := ha.ne_zero_of_strict h.2
  exact TreeAncestry.walk_convex (T := T) (P := fun i => v ∈ D.bag i)
    (D.running (introduction_spec D v).1 h.1) (ha.parent_of_ne h.2) (.step hz (.refl _))

theorem overlap_adhesion {x : Fin t} {v : Fin n} (hx : x.val≠0)
    (hv : v ∈ D.bag x) (hp : v ∈ D.bag (T.parent x)) : outerAdhesion D x v := by
  refine ⟨hv,?_⟩
  intro he
  have ha := (introduction_ancestor D hp).val_le
  rw [he] at ha
  have ht := T.parent_lt x hx
  omega

namespace NestedInput
variable (N : NestedInput D)

noncomputable def adhesionList (_N : NestedInput D) (x : Fin t) : List (Fin n) := by
  classical
  exact (D.bag x).filter (fun v => introductionNode D v≠x)

@[simp] theorem mem_adhesionList (x : Fin t) (v : Fin n) :
    v ∈ N.adhesionList x ↔ outerAdhesion D x v := by
  classical
  simp [adhesionList,outerAdhesion]

noncomputable def bagOn (a : N.substitution.Node) : List (Fin n) :=
  uniqueList (N.adhesionList a.1 ++
    ((N.localDecomp a.1).bag a.2).map (fun u => (N.names a.1 u).val))

@[simp] theorem mem_bagOn (x : Fin t) (y : Fin (N.nodes x)) (v : Fin n) :
    v ∈ N.bagOn ⟨x,y⟩ ↔ outerAdhesion D x v ∨
      ∃ u, u ∈ (N.localDecomp x).bag y ∧ (N.names x u).val=v := by
  simp [bagOn,List.mem_map]

theorem bagOn_nodup (a : N.substitution.Node) : (N.bagOn a).Nodup :=
  uniqueList_nodup _

theorem bagOn_subset (a : N.substitution.Node) {v : Fin n} (hv : v ∈ N.bagOn a) :
    v ∈ D.bag a.1 := by
  rcases (N.mem_bagOn a.1 a.2 v).mp hv with h | ⟨u,_,hu⟩
  · exact h.1
  · have h := (N.names a.1 u).property
    rw [hu] at h
    simpa only [h] using (introduction_spec D v).1

theorem occurs_at_outer {x : Fin t} {v : Fin n} (hv : v ∈ D.bag x) :
    ∃ y, v ∈ N.bagOn ⟨x,y⟩ := by
  classical
  by_cases he : introductionNode D v=x
  · let u := (N.names x).symm ⟨v,he⟩
    obtain ⟨y,hy⟩ := (N.localDecomp x).vertex u
    refine ⟨y,(N.mem_bagOn x y v).mpr (Or.inr ⟨u,hy,?_⟩)⟩
    simp only [u,Equiv.apply_symm_apply]
  · exact ⟨⟨0,N.local_nonempty x⟩,(N.mem_bagOn _ _ _).mpr (Or.inl ⟨hv,he⟩)⟩

theorem bagOn_vertex (v : Fin n) : ∃ a : N.substitution.Node, v ∈ N.bagOn a := by
  obtain ⟨x,hx⟩ := D.vertex v
  obtain ⟨y,hy⟩ := N.occurs_at_outer hx
  exact ⟨⟨x,y⟩,hy⟩

private theorem edge_cover_forward {u v : Fin n} (he : G.Adj u v)
    (ha : Ancestor T (introductionNode D u) (introductionNode D v)) :
    ∃ a : N.substitution.Node, u ∈ N.bagOn a ∧ v ∈ N.bagOn a := by
  classical
  let x := introductionNode D v
  by_cases hi : introductionNode D u=x
  · let a := (N.names x).symm ⟨u,hi⟩
    let b := (N.names x).symm ⟨v,rfl⟩
    have hab : a≠b := by
      intro hab
      have h := congrArg (fun z => (N.names x z).val) hab
      have huv : u=v := by simpa only [a,b,Equiv.apply_symm_apply] using h
      exact G.loopless v (huv ▸ he)
    have hg : (marginalGraph D x (N.names x)).Adj a b := by
      refine ⟨hab,Or.inl ?_⟩
      simpa only [a,b,Equiv.apply_symm_apply] using he
    obtain ⟨y,hay,hby⟩ := (N.localDecomp x).edge hg
    refine ⟨⟨x,y⟩,(N.mem_bagOn x y u).mpr (Or.inr ⟨a,hay,?_⟩),
      (N.mem_bagOn x y v).mpr (Or.inr ⟨b,hby,?_⟩)⟩ <;>
      simp only [a,b,Equiv.apply_symm_apply]
  · obtain ⟨y,hy⟩ := N.occurs_at_outer (introduction_spec D v).1
    refine ⟨⟨x,y⟩,(N.mem_bagOn x y u).mpr (Or.inl ⟨?_,hi⟩),hy⟩
    exact frontier_mem_introduction_bag D ha (.refl _) he

theorem bagOn_edge {u v : Fin n} (he : G.Adj u v) :
    ∃ a : N.substitution.Node, u ∈ N.bagOn a ∧ v ∈ N.bagOn a := by
  rcases edge_introductions_comparable D he with h | h
  · exact N.edge_cover_forward he h
  · obtain ⟨a,hv,hu⟩ := N.edge_cover_forward (G.symm he) h
    exact ⟨a,hu,hv⟩

/-- Width accounting retains the actual adhesion plus actual local bag. -/
theorem bagOn_bound {a b : Nat}
    (ha : ∀ x, (N.adhesionList x).length ≤ a)
    (hb : ∀ x, (N.localDecomp x).BagBound b) (v : N.substitution.Node) :
    (N.bagOn v).length ≤ a+b := by
  have h := uniqueList_length_le (N.adhesionList v.1 ++
    ((N.localDecomp v.1).bag v.2).map (fun u => (N.names v.1 u).val))
  have h1 := ha v.1
  have h2 := hb v.1 v.2
  calc
    (N.bagOn v).length ≤ (N.adhesionList v.1).length + ((N.localDecomp v.1).bag v.2).length := by
      simpa only [bagOn,List.length_append,List.length_map] using h
    _ ≤ a+b := Nat.add_le_add h1 h2

#print axioms bagOn_vertex
#print axioms bagOn_edge
#print axioms bagOn_bound
end NestedInput
end StackSorting.GraphWidth.Nested
