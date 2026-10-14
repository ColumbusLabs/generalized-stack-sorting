import UCurveSchedule

namespace StackSorting.GraphWidth.UCurve
open FinitePort Generalized IntervalCritical SparseEndpointMSO

def canonicalPairing {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) : EndpointPairing n (canonicalEvents 0 output).length :=
  eventPairing (permutation_canonical_validity hp).1
    (permutation_canonical_validity hp).2.1
    ((permutation_canonical_validity hp).2.2.1.symm ▸ hp)

def canonicalDrawing {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (order : List Nat) (ho : order.Perm (List.range n)) :
    Drawing (canonicalPairing hp) :=
  rankDrawing (permutation_canonical_validity hp).1
    (permutation_canonical_validity hp).2.1
    ((permutation_canonical_validity hp).2.2.1.symm ▸ hp)
    (permutation_canonical_validity hp).2.2.2.1 order ho

/-- A genuine original-machine run supplies the drawing's physical depth
order and both bounded stem-crossing counts. No geometric width is assumed. -/
theorem generated_drawing {n r s : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hrun : Run r s [] (List.range n) output []) :
    ∃ D : Drawing (canonicalPairing hp), ∀ v : Fin n,
      (stemCrossings D ((canonicalPairing hp).left v)).length < r ∧
      (stemCrossings D ((canonicalPairing hp).right v)).length < s := by
  have hpeel := (generated_iff_canonical_peelable hp).mp hrun
  obtain ⟨order, ho, hf⟩ := hpeel.feasible_order List.nodup_range
  refine ⟨canonicalDrawing hp order ho, ?_⟩
  intro v
  exact rank_stem_bounds (permutation_canonical_validity hp).1
    (permutation_canonical_validity hp).2.1
    ((permutation_canonical_validity hp).2.2.1.symm ▸ hp)
    (permutation_canonical_validity hp).2.2.2.1 order ho hf v

/-- The actual finite curve graph now supplies all of the previously explicit
curve-cover fields. Only a decomposition of this graph is still needed. -/
def canonicalCurveCover {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (D : Drawing (canonicalPairing hp)) :
    CurveCover (sourceGraph D)
      (sparseGraph (canonicalDiagram output) (canonicalEvents 0 output).length)
      (canonicalPairing hp) :=
  eventCurveCover (permutation_canonical_validity hp).1
    (permutation_canonical_validity hp).2.1
    ((permutation_canonical_validity hp).2.2.1.symm ▸ hp)
    (sourceGraph D) (labels D) (anchor D)
    (fun e => by change (canonicalPairing hp).owner e ∈ labels D (anchor D e); simp)
    (fun hi hj => curve_fiber_connected D hi hj) (baseline_edge D)

/-- Endpoint decomposition transfer with the source graph, labels, anchor
incidences, all curve fibers and their two-label bound explicitly constructed.
The remaining hypothesis is a bounded decomposition of the explicit source. -/
theorem explicit_source_decomposition_transfer {n t : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (D : Drawing (canonicalPairing hp))
    (T : RootedTree t) (dec : Decomposition (sourceGraph D) T)
    (k : Nat) (hb : dec.BagBound (3*k)) :
    ∃ target : Decomposition (sparseGraph (canonicalDiagram output)
      (canonicalEvents 0 output).length) T, target.BagBound (12*k) := by
  let C := canonicalCurveCover hp D
  exact ⟨dec.lift C.connectedLift, C.endpoint_bag_bound dec k hb (source_labels_bound D)⟩

/-- This is conditional only on the explicit source-graph decomposition,
not on an arbitrary curve-cover witness. Positivity handles subtraction. -/
theorem explicit_source_treewidth_transfer {n t : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (D : Drawing (canonicalPairing hp))
    (T : RootedTree t) (dec : Decomposition (sourceGraph D) T)
    (k : Nat) (hk : 0 < k) (hb : dec.BagBound (3*k)) :
    HasTreewidthAtMost (sparseGraph (canonicalDiagram output)
      (canonicalEvents 0 output).length) (12*k-1) := by
  obtain ⟨target, ht⟩ := explicit_source_decomposition_transfer hp D T dec k hb
  exact target.treewidthAtMost ht (by omega)

end StackSorting.GraphWidth.UCurve
