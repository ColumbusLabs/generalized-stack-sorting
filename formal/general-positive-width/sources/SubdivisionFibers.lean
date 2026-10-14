import SubdivisionRealization

namespace StackSorting.GraphWidth.UCurve.SubdivisionTree
open FinitePort PlaneGrid

def ParentAdj {n} {G : Graph n} (S : RouteLengths G) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (x y : Vertex S) : Prop :=
  (x≠.original root ∧ parent S T he x=y) ∨ (y≠.original root ∧ parent S T he y=x)

theorem Realization.parent_nonroot_adj {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (x : Vertex S.toRouteLengths) (hx : x≠.original root) :
    H.Adj (S.embed x) (S.embed (parent S.toRouteLengths T he x)) := by
  cases x with
  | original v =>
    apply S.parent_original_adj T he v
    intro hz
    exact hx (congrArg Vertex.original (Fin.ext (hz.trans hr.symm)))
  | interior e a => exact S.parent_interior_adj T he e a

theorem Realization.parentAdj_realized {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    {x y : Vertex S.toRouteLengths} (h : ParentAdj S.toRouteLengths T he root x y) :
    H.Adj (S.embed x) (S.embed y) := by
  obtain ⟨hx,hy⟩ | ⟨hy,hx⟩ := h
  · rw [← hy]; exact S.parent_nonroot_adj T he root hr x hx
  · rw [← hx]; exact H.symm (S.parent_nonroot_adj T he root hr y hy)

/-- Every branch reaches its original source vertex through vertices carrying
that same branch. Non-tree route interiors attach to the high endpoint. -/
theorem Realization.branch_reaches_original {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (x : Vertex S.toRouteLengths) :
    Walk (ParentAdj S.toRouteLengths T he root)
      (fun y => branch S.toRouteLengths T y=branch S.toRouteLengths T x)
      x (.original (branch S.toRouteLengths T x)) := by
  cases x with
  | original v => exact .refl rfl
  | interior e a =>
    have hp := branch_parent_interior S.toRouteLengths T he e a
    have hwalk := S.branch_reaches_original T he root hr (parent S.toRouteLengths T he (.interior e a))
    rw [hp] at hwalk
    exact .step rfl (Or.inl ⟨(by intro h; cases h),rfl⟩) hwalk
termination_by rank S.toRouteLengths T m x
decreasing_by
  exact rank_parent_lt S.toRouteLengths T he m (fun e => Nat.le_of_lt (S.length_bound e))
    root hr (.interior e a) (by intro h; cases h)

/-- Every original edge still has an actual target edge between its two
endpoint branches. Tree edges use the last segment; non-tree edges use the
first omitted segment. Length-one routes are covered explicitly. -/
theorem Realization.ordered_edge_branches {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (e : OrderedEdge G) :
    ∃ x y : Vertex S.toRouteLengths, H.Adj (S.embed x) (S.embed y) ∧
      branch S.toRouteLengths T x=e.low ∧ branch S.toRouteLengths T y=e.high := by
  classical
  by_cases ht : IsTreeEdge T e
  · have hh : e.high.val≠0 := by have := e.ordered; omega
    refine ⟨parent S.toRouteLengths T he (.original e.high),.original e.high,
      H.symm (S.parent_original_adj T he e.high hh),?_,rfl⟩
    exact (branch_parent_original S.toRouteLengths T he e.high hh).trans ht
  · by_cases hl : 1<S.length e
    · refine ⟨.original e.low,.interior e ⟨0,by omega⟩,?_,rfl,?_⟩
      · have h := S.step e ⟨0,by omega⟩
        rw [S.first] at h
        exact h
      · simp only [branch,ite_eq_right ht]
    · have hp := S.positive e
      have hlen : S.length e=1 := by omega
      refine ⟨.original e.low,.original e.high,?_,rfl,rfl⟩
      have h := S.step e ⟨0,by omega⟩
      rw [S.first] at h
      have hi : (⟨0+1,by omega⟩ : Fin (S.length e+1))=⟨S.length e,by omega⟩ := by
        apply Fin.ext; dsimp; omega
      rw [hi,S.last] at h
      exact h

theorem Realization.source_edge_branches {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) {u v : Fin n} (huv : G.Adj u v) :
    ∃ x y : Vertex S.toRouteLengths, H.Adj (S.embed x) (S.embed y) ∧
      branch S.toRouteLengths T x=u ∧ branch S.toRouteLengths T y=v := by
  by_cases hlt : u.val<v.val
  · exact S.ordered_edge_branches T he ⟨u,v,hlt,huv⟩
  · have hne : u≠v := fun heq => G.loopless v (heq ▸ huv)
    have hlt' : v.val<u.val := by
      have hn : u.val≠v.val := fun h => hne (Fin.ext h)
      omega
    obtain ⟨x,y,hxy,hx,hy⟩ := S.ordered_edge_branches T he ⟨v,u,hlt',G.symm huv⟩
    exact ⟨y,x,H.symm hxy,hy,hx⟩

end StackSorting.GraphWidth.UCurve.SubdivisionTree
