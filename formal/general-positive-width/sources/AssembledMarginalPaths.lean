import SelectedAssemblyTransport
import PrefixMarginalPath

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FiniteFlow.Hypergraph
variable {n : Nat}

/-- A child's literal margin is unchanged, including exclusion of its original
adhesion even when that child is the local recursive root. -/
theorem assembled_margin_child (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (children : ∀ z, Frontier (clippedParent O r) Z z → RootedSelection O z)
    (z : Fin n) (hz : Frontier (clippedParent O r) Z z)
    (a : {x : Fin n // x ∈ (children z hz).nodes}) :
    (assembleSelection O r Z hp children).marginSet G
      ⟨a.val,(assembled_mem O r Z hp children a.val).mpr (Or.inr ⟨z,hz,a.property⟩)⟩ =
      (children z hz).marginSet G a := by
  unfold RootedSelection.marginSet
  rw [assembled_bag_child]

/-- Every actual completion edge below a recursive child is an edge of that
child's literal marginal. The proof keeps the same selected child ID. -/
theorem assembled_marginal_edge_child (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (children : ∀ z, Frontier (clippedParent O r) Z z → RootedSelection O z)
    (z : Fin n) (hz : Frontier (clippedParent O r) Z z)
    (a : {x : Fin n // x ∈ (children z hz).nodes}) {u v : Fin n} :
    (assembleSelection O r Z hp children).MarginalEdge G
      ⟨a.val,(assembled_mem O r Z hp children a.val).mpr (Or.inr ⟨z,hz,a.property⟩)⟩ u v →
      (children z hz).MarginalEdge G a u v := by
  intro h
  rcases h with h | ⟨c,hcr,hparent,hu,hv⟩
  · exact Or.inl h
  · let A := assembleSelection O r Z hp children
    let C := children z hz
    have hac : O.rel a.val c.val := by
      have h := A.contractedParent_below c hcr
      rw [hparent] at h
      exact h
    have hzc : O.rel z c.val := by
      rcases C.inside a.val a.property with hza | hza
      · exact O.trans hza hac
      · exact hza ▸ hac
    have hcz : c.val ≠ z := fun he => O.irrefl z (by simpa only [he] using hzc)
    have hc : c.val ∈ C.nodes :=
      (assembled_mem_child_iff O r Z hp children z hz c.val (Or.inl hzc)).mp c.property
    let c' : {x : Fin n // x ∈ C.nodes} := ⟨c.val,hc⟩
    have hcparent := assembled_parent_child O r Z hp children z hz c' hcz
    have hcp : C.contractedParent c' = a := by
      apply Subtype.ext
      exact hcparent.symm.trans (congrArg Subtype.val hparent)
    exact Or.inr ⟨c',hcz,hcp,hu,hv⟩

/-- Assemble the actual finite bag paths simultaneously with the selected
regions. The only local root payload comes from the constructed prefix theorem;
no final path decomposition or scalar pathwidth bound is an input. -/
noncomputable def assemblePathwidthParts (G : Graph n) (O : RankedOrder n)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r : Fin n) (k : Nat) (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (small : Z = {r} ∨ ∃ s t, Nonempty (PrunedPrefixWitness G O r s t k Z))
    (children : ∀ z, Frontier (clippedParent O r) Z z → RootedSelection O z)
    (parts : ∀ z hz, (children z hz).PathwidthParts G (2*k+2)) :
    (assembleSelection O r Z hp children).PathwidthParts G (2*k+2) := by
  classical
  let A := assembleSelection O r Z hp children
  have cert : ∀ a : {x : Fin n // x ∈ A.nodes},
      ∃ D : BagPath (A.marginSet G a) (2*k+2), ∀ u v,
      u ∈ A.marginSet G a → v ∈ A.marginSet G a → A.MarginalEdge G a u v →
      ∃ i, i ≤ D.last ∧ u ∈ D.bag i ∧ v ∈ D.bag i := by
    intro a
    by_cases har : a.val = r
    · have he : a = ⟨r,A.root_mem⟩ := Subtype.ext har
      subst a
      have hm : A.marginSet G ⟨r,A.root_mem⟩ = Z := by
        ext v
        rw [A.mem_marginSet]
        exact A.contracted_root_margin_iff G Z hp
          (assembled_only_root O r Z hp children) (assembled_frontier O r Z hp children) v
      rw [hm]
      exact prefix_marginal_path G O cones r k Z hp small A
        (assembled_only_root O r Z hp children) (assembled_frontier O r Z hp children)
    · obtain ⟨z,hz,ha⟩ := ((assembled_mem O r Z hp children a.val).mp a.property).resolve_left har
      let a' : {x : Fin n // x ∈ (children z hz).nodes} := ⟨a.val,ha⟩
      have hm : A.marginSet G a = (children z hz).marginSet G a' :=
        assembled_margin_child G O r Z hp children z hz a'
      let Q := parts z hz
      rw [hm]
      refine ⟨Q.path a',?_⟩
      intro u v hu hv huv
      exact Q.edge a' u v hu hv (assembled_marginal_edge_child G O r Z hp children z hz a' huv)
  exact {
    path := fun a => Classical.choose (cert a)
    edge := fun a => Classical.choose_spec (cert a)
  }

end StackSorting.LowPathwidthParts
