import SelectedFrontierChildren

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FiniteFlow.Hypergraph
variable {n : Nat}

/-- An actual original edge with endpoints in the retained prefix remains a
covered hyperedge after deleting the other root-adhesion vertices. -/
theorem pruned_prefix_original_pair (G : Graph n) (O : RankedOrder n)
    (r s t : Fin n) (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    {x y : Fin n} (hx : x ∈ Z) (hy : y ∈ Z) (hxy : G.Adj x y) :
    ∃ e : ActiveEdge (CanonicalPrefixInc (inducedGraph G (rootAllowed G O r s t))
      (prunedOrder G O r s t) r Z),
      ActiveIncidence (CanonicalPrefixInc (inducedGraph G (rootAllowed G O r s t))
        (prunedOrder G O r s t) r Z) x e ∧
      ActiveIncidence (CanonicalPrefixInc (inducedGraph G (rootAllowed G O r s t))
        (prunedOrder G O r s t) r Z) y e := by
  classical
  let G' := inducedGraph G (rootAllowed G O r s t)
  let O' := prunedOrder G O r s t
  have keepx := cone_allowed G O r s t (hp.2.2 x hx)
  have keepy := cone_allowed G O r s t (hp.2.2 y hy)
  have hxvis : x ∈ prefixVertices G' O' r Z := Finset.mem_union_left _ hx
  have hyvis : y ∈ prefixVertices G' O' r Z := Finset.mem_union_left _ hy
  have hix : PrefixHypertorsoInc G' O' r Z x (.inl (x,y)) :=
    ⟨⟨hxy,keepx,keepy⟩,hxvis,hyvis,Or.inl rfl⟩
  have hiy : PrefixHypertorsoInc G' O' r Z y (.inl (x,y)) :=
    ⟨⟨hxy,keepx,keepy⟩,hxvis,hyvis,Or.inr rfl⟩
  let e : ActiveEdge (PrefixHypertorsoInc G' O' r Z) := ⟨.inl (x,y),⟨x,hix⟩⟩
  exact ⟨canonicalActiveEdge G' O' r Z e,
    (canonicalActive_incidence G' O' r Z x e).mpr hix,
    (canonicalActive_incidence G' O' r Z y e).mpr hiy⟩

/-- Both endpoints of every actual contracted-child completion edge lie in
one retained, indexed frontier hyperedge of the pruned prefix. -/
theorem pruned_prefix_child_pair (G : Graph n) (O : RankedOrder n)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r s t : Fin n) (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (A : RootedSelection O r)
    (honly : ∀ a ∈ A.nodes, a ∈ Z → a = r)
    (hfront : ∀ z, Frontier (clippedParent O r) Z z → z ∈ A.nodes)
    (a : {v : Fin n // v ∈ A.nodes}) (har : a.val ≠ r)
    (hparent : (A.contractedParent a).val = r)
    {x y : Fin n} (hx : x ∈ Z) (hy : y ∈ Z)
    (hxa : RegionAdhesion G O a.val x) (hya : RegionAdhesion G O a.val y) :
    ∃ e : ActiveEdge (CanonicalPrefixInc (inducedGraph G (rootAllowed G O r s t))
      (prunedOrder G O r s t) r Z),
      ActiveIncidence (CanonicalPrefixInc (inducedGraph G (rootAllowed G O r s t))
        (prunedOrder G O r s t) r Z) x e ∧
      ActiveIncidence (CanonicalPrefixInc (inducedGraph G (rootAllowed G O r s t))
        (prunedOrder G O r s t) r Z) y e := by
  classical
  let G' := inducedGraph G (rootAllowed G O r s t)
  let O' := prunedOrder G O r s t
  have ha := (A.root_child_iff_frontier Z hp honly hfront a har).mp hparent
  have ha' := (pruned_frontier_iff G O cones r s t Z hp a.val).mpr ha
  have hxa' : RegionAdhesion G' O' a.val x :=
    (pruned_adhesion_iff G O cones r s t (A.inside a.val a.property)).mpr
      ⟨hxa,cone_allowed G O r s t (hp.2.2 x hx)⟩
  have hya' : RegionAdhesion G' O' a.val y :=
    (pruned_adhesion_iff G O cones r s t (A.inside a.val a.property)).mpr
      ⟨hya,cone_allowed G O r s t (hp.2.2 y hy)⟩
  let e : ActiveEdge (CanonicalPrefixInc G' O' r Z) := ⟨.inr a.val,⟨x,⟨ha',hxa'⟩,rfl⟩⟩
  exact ⟨e,⟨⟨ha',hxa'⟩,rfl⟩,⟨⟨ha',hya'⟩,rfl⟩⟩

end StackSorting.LowPathwidthParts
