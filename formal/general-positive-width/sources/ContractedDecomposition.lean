import SelectedParentNumbering

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FinitePort
variable {n : Nat}

namespace Walk
/-- Contracting an edge to a single vertex is allowed; surviving edges are
actual target edges. This constructs the target walk and its support proof. -/
theorem mapStutter {α β : Type} {adj : α → α → Prop} {adj' : β → β → Prop}
    {P : α → Prop} {Q : β → Prop} (f : α → β)
    (he : ∀ x y, adj x y → f x = f y ∨ adj' (f x) (f y))
    (hp : ∀ x, P x → Q (f x)) {x y : α} (h : GraphWidth.Walk adj P x y) :
    GraphWidth.Walk adj' Q (f x) (f y) := by
  induction h with
  | refl hx => exact .refl (hp _ hx)
  | @step x y z hx hxy htail ih =>
    rcases he x y hxy with e | e
    · exact e.symm ▸ ih
    · exact .step (hp _ hx) e ih
end Walk

namespace RootedSelection
variable {O : RankedOrder n} {r : Fin n} (A : RootedSelection O r)
noncomputable section
local instance contractedDecidable : DecidablePred (fun x => x ∈ A.nodes) := Classical.decPred _

theorem selectedIndex_nonzero (a : A.Selected) (ha : a.val ≠ r) :
    (A.selectedIndex a).val ≠ 0 := by
  intro hz
  have h := A.selectedLabel_root (A.selectedIndex a) hz
  rw [A.selectedLabel_index] at h
  exact ha (congrArg Subtype.val h)

/-- For a rooted component, every old bag has an actual contracted index. -/
def quotientIndex (hall : ∀ v, Cone O r v) (v : Fin n) : Fin (Fintype.card A.Selected) :=
  A.selectedIndex (A.owner v (hall v))

theorem quotient_parent_step (hall : ∀ v, Cone O r v) (v : Fin n)
    (hp : O.parent v ≠ v) :
    A.quotientIndex hall v = A.quotientIndex hall (O.parent v) ∨
    TreeAdj A.selectedTree (A.quotientIndex hall v) (A.quotientIndex hall (O.parent v)) := by
  by_cases hs : v ∈ A.nodes
  · have hv : v ≠ r := by
      intro e
      have hpr : O.rel (O.parent r) r := e ▸ O.parent_rel hp
      have hc := hall (O.parent r)
      exact O.irrefl r (by
        rcases hc with hc | hc
        · exact O.trans hc hpr
        · rw [← hc] at hpr
          exact hpr)
    have hrv : O.rel r v := (hall v).resolve_right (Ne.symm hv)
    let a : A.Selected := ⟨v,hs⟩
    have ho : A.owner v (hall v) = a := Subtype.ext (A.owner_selected v (hall v) hs)
    right
    change TreeAdj A.selectedTree (A.selectedIndex (A.owner v (hall v)))
      (A.selectedIndex (A.owner (O.parent v) (hall (O.parent v))))
    rw [ho]
    refine Or.inl ⟨A.selectedIndex_nonzero a hv,?_⟩
    rw [A.selectedIndex_parent,A.contractedParent_eq a hv hrv]
  · have hv : v ≠ r := fun e => hs (e.symm ▸ A.root_mem)
    have hrv : O.rel r v := (hall v).resolve_right (Ne.symm hv)
    left
    unfold quotientIndex
    rw [A.owner_parent v (hall v) hs hrv]

theorem quotient_adj (hall : ∀ v, Cone O r v) {v w : Fin n} (h : ParentAdj O v w) :
    A.quotientIndex hall v = A.quotientIndex hall w ∨
      TreeAdj A.selectedTree (A.quotientIndex hall v) (A.quotientIndex hall w) := by
  rcases h with ⟨hp,rfl⟩ | ⟨hp,rfl⟩
  · exact A.quotient_parent_step hall v hp
  · rcases A.quotient_parent_step hall w hp with he | he
    · exact Or.inl he.symm
    · exact Or.inr (treeAdj_symm A.selectedTree he)

/-- The actual union bags form a decomposition on the exactly parent-numbered
selected tree. The single-root hypothesis is explicit, not obtained by
silently joining disconnected components. -/
def contractedDecomposition (G : Graph n) (hall : ∀ v, Cone O r v)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u) :
    GraphWidth.Decomposition G A.selectedTree where
  bag i := (A.contractedBag G (A.selectedLabel i)).toList
  nodup i := Finset.nodup_toList _
  vertex v := by
    refine ⟨A.quotientIndex hall v,?_⟩
    simp only [Finset.mem_toList]
    unfold quotientIndex
    rw [A.selectedLabel_index]
    exact (A.mem_contractedBag G _ v).mpr ⟨v,hall v,rfl,Or.inl rfl⟩
  edge := by
    intro u v h
    obtain ⟨w,hwu,hwv⟩ := regionBag_edge G O helim h
    refine ⟨A.quotientIndex hall w,?_,?_⟩ <;>
      simp only [Finset.mem_toList,quotientIndex,A.selectedLabel_index]
    · exact (A.mem_contractedBag G _ u).mpr ⟨w,hall w,rfl,hwu⟩
    · exact (A.mem_contractedBag G _ v).mpr ⟨w,hall w,rfl,hwv⟩
  running := by
    intro u i j hi hj
    simp only [Finset.mem_toList] at hi hj ⊢
    obtain ⟨v,hv,hvi,hvu⟩ := (A.mem_contractedBag G _ u).mp hi
    obtain ⟨w,hw,hwj,hwu⟩ := (A.mem_contractedBag G _ u).mp hj
    have hqi : A.quotientIndex hall v = i := by
      unfold quotientIndex
      have he : A.owner v (hall v) = A.selectedLabel i := Subtype.ext hvi
      rw [he,A.selectedIndex_label]
    have hqj : A.quotientIndex hall w = j := by
      unfold quotientIndex
      have he : A.owner w (hall w) = A.selectedLabel j := Subtype.ext hwj
      rw [he,A.selectedIndex_label]
    rw [← hqi,← hqj]
    apply Walk.mapStutter (A.quotientIndex hall) (fun _ _ h => A.quotient_adj hall h)
      (fun z hz => ?_) (regionBag_running G O hvu hwu)
    unfold quotientIndex
    rw [A.selectedLabel_index]
    exact (A.mem_contractedBag G _ u).mpr ⟨z,hall z,rfl,hz⟩

end
end RootedSelection
end StackSorting.LowPathwidthParts
