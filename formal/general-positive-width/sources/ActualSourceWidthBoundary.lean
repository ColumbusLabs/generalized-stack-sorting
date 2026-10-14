import ActualSourceWidth

namespace StackSorting.GraphWidth.UCurve
open FinitePort Generalized

/-- The finite empty graph has a one-node empty-bag decomposition. -/
theorem empty_graph_treewidth (G : Graph 0) : HasTreewidthAtMost G 0 := by
  let T : RootedTree 1 := ⟨fun _ => 0,fun v hv => False.elim (hv (by have := v.isLt; omega))⟩
  let D : Decomposition G T := {
    bag := fun _ => []
    nodup := fun _ => List.nodup_nil
    vertex := fun v => Fin.elim0 v
    edge := fun {u} _ => Fin.elim0 u
    running := fun {v} _ _ => Fin.elim0 v }
  exact ⟨1,T,D,fun _ => Nat.zero_le 1⟩

theorem empty_canonical_sparse_treewidth :
    HasTreewidthAtMost (sparseGraph (SparseEndpointMSO.canonicalDiagram [])
      (canonicalEvents 0 []).length) 0 := empty_graph_treewidth _

/-- With both widths zero no first operation is legal. -/
theorem zero_width_run_empty {held input output final : List Nat}
    (h : Run 0 0 held input output final) : input=[] ∧ output=[] ∧ held=final := by
  cases h with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons head _ => cases head with
    | push pre post x allowed => omega
    | pop pre post x allowed => omega

/-- The zero-width boundary contains only the empty generated diagram, so the
natural-number width convention extends the geometric result to all widths. -/
theorem generated_sparse_treewidth_all {n r s : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hrun : Run r s [] (List.range n) output []) :
    HasTreewidthAtMost (sparseGraph (SparseEndpointMSO.canonicalDiagram output)
      (canonicalEvents 0 output).length) (12*max r s-1) := by
  by_cases hk : 0<max r s
  · exact generated_sparse_treewidth hp hrun hk
  · have hr : r=0 := by have := Nat.le_max_left r s; omega
    have hs : s=0 := by have := Nat.le_max_right r s; omega
    subst r; subst s
    have hout : output=[] := (zero_width_run_empty hrun).2.1
    subst output
    exact empty_canonical_sparse_treewidth

/-- The same bound from the original executable slot-indexed machine semantics. -/
theorem raw_generated_sparse_treewidth {n r s : Nat} {output : List Nat}
    (hp : output.Perm (List.range n))
    (hrun : CanTransform r s [] (List.range n) output) :
    HasTreewidthAtMost (sparseGraph (SparseEndpointMSO.canonicalDiagram output)
      (canonicalEvents 0 output).length) (12*max r s-1) :=
  generated_sparse_treewidth_all hp ((run_relational_iff r s [] (List.range n) output []).mpr hrun)

end StackSorting.GraphWidth.UCurve
