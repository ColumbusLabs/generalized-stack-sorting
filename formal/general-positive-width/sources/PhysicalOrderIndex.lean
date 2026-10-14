import PhysicalChronologicalOrder
import SparseEliminationSyntax

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.SparseEndpointMSO.CanonicalChoice
open FinitePort FinitePort.ChildSibling SparseTreeCompiler EliminationSyntax

theorem idxOf_map_finite_equiv {m n : Nat} (e : Fin m ≃ Fin n)
    (xs : List (Fin m)) (u : Fin m) : (xs.map e).idxOf (e u)=xs.idxOf u := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons,List.idxOf_cons,beq_iff_eq,e.apply_eq_iff_eq,ih]

/-- The physical successor chain gives an actual exhaustive order on any
finite naming of the domain. No equation of numeric and physical order is used. -/
theorem physical_has_fixed_chronology {D : Model} {r s n : Nat}
    (hD : Satisfies D (fullAcceptedSentence r s))
    (e : Fin n ≃ {x // x ∈ D.domain}) :
    ∃ O : FixedOrder n, ∀ u v,
      OrderEval D chronologicalBefore (e u).val (e v).val ↔ OrderBefore O u v := by
  obtain ⟨_,output,_,_,⟨iso⟩⟩ := (fullAcceptedSentence_iff_generated D r s).mp hD
  let m := (Generalized.canonicalEvents 0 output).length
  let J := orderedDomainOfTimeIsomorphism iso (eventDiagram_path (Generalized.canonicalEvents 0 output))
  let f : Fin m ≃ Fin n := J.vertex.trans e.symm
  let O : FixedOrder n := {
    vertices := (List.finRange m).map f
    nodup := (List.nodup_finRange m).map f.injective
    complete u := List.mem_map.mpr ⟨f.symm u,List.mem_finRange _,f.apply_symm_apply u⟩ }
  refine ⟨O,?_⟩
  intro u v
  have hv (x : Fin n) : J.vertex (f.symm x)=e x := by
    change J.vertex (J.vertex.symm (e x))=e x
    exact J.vertex.apply_symm_apply (e x)
  have hh := J.before_iff (f.symm u) (f.symm v)
  rw [hv,hv] at hh
  have hi (x : Fin n) : O.vertices.idxOf x=(f.symm x).val := by
    change ((List.finRange m).map f).idxOf x=(f.symm x).val
    calc
      _ = ((List.finRange m).map f).idxOf (f (f.symm x)) := congrArg (List.idxOf · ((List.finRange m).map f)) (f.apply_symm_apply x).symm
      _ = (List.finRange m).idxOf (f.symm x) := idxOf_map_finite_equiv f _ _
      _ = (f.symm x).val := List.idxOf_finRange _
  simpa only [OrderBefore,hi,Fin.lt_def] using hh

#print axioms physical_has_fixed_chronology
end StackSorting.SparseEndpointMSO.CanonicalChoice
