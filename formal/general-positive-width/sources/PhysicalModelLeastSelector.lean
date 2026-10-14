import OrderedDomainSelector
import SparseFullClass

namespace StackSorting.SparseEndpointMSO.CanonicalChoice

/-- The order formula uses only successor and monadic quantification already
in the original sparse vocabulary. Vertex names themselves are not ordered. -/
def chronologicalBefore : Formula 2 0 := strictBefore 0 1

noncomputable def orderedDomainOfTimeIsomorphism {D E : Model} {n : Nat}
    (iso : Isomorphism D E) (hp : TimePath E n) :
    OrderedDomain D chronologicalBefore (Fin n) where
  vertex := {
    toFun := fun p => ⟨iso.invFun p.val, iso.inv_mem p.val (by rw [hp.1]; exact List.mem_range.mpr p.isLt)⟩
    invFun := fun x => ⟨iso.toFun x.val, by
      have h := iso.to_mem x.val x.property
      rw [hp.1, List.mem_range] at h
      exact h⟩
    left_inv := by
      intro p
      apply Fin.ext
      exact iso.right_inv p.val (by rw [hp.1]; exact List.mem_range.mpr p.isLt)
    right_inv := by
      intro x
      apply Subtype.ext
      exact iso.left_inv x.val x.property }
  before_iff := by
    intro p q
    have hp' : p.val ∈ E.domain := by rw [hp.1]; exact List.mem_range.mpr p.isLt
    have hq' : q.val ∈ E.domain := by rw [hp.1]; exact List.mem_range.mpr q.isLt
    let d : Fin 2 → Nat := Fin.cases (iso.invFun p.val) (fun _ : Fin 1 => iso.invFun q.val)
    let e : Fin 2 → Nat := Fin.cases p.val (fun _ : Fin 1 => q.val)
    have hdom : ∀ i, d i ∈ D.domain := by
      intro i
      exact Fin.cases (iso.inv_mem _ hp') (fun _ => iso.inv_mem _ hq') i
    have henv : ∀ i, e i = iso.toFun (d i) := by
      intro i
      exact Fin.cases (iso.right_inv _ hp').symm (fun _ => (iso.right_inv _ hq').symm) i
    have hh := iso.eval chronologicalBefore d e Fin.elim0 Fin.elim0 hdom henv
      (fun X => Fin.elim0 X)
    change Eval D chronologicalBefore d Fin.elim0 ↔ p.val < q.val
    apply hh.trans
    exact eval_strictBefore E n hp 0 1 e Fin.elim0 hp' hq'

/-- Actual accepted physical sparse models, including the empty model and
arbitrary vertex names, admit a unique supported least witness for any
nonempty admissible monadic relation. No supplied ordering is required. -/
theorem physicalModel_exists_unique_leastSelector {D : Model} {r s k : Nat}
    (hD : Satisfies D (fullAcceptedSentence r s)) (f : Formula 0 k)
    (hex : ∃ X, SupportedTuple D X ∧ Eval D f Fin.elim0 X) :
    ∃! X, SupportedTuple D X ∧
      Eval D (leastSelector chronologicalBefore f) Fin.elim0 X := by
  obtain ⟨_, output, _, _, ⟨iso⟩⟩ := (fullAcceptedSentence_iff_generated D r s).mp hD
  let J := orderedDomainOfTimeIsomorphism iso (eventDiagram_path (Generalized.canonicalEvents 0 output))
  exact OrderedDomain.exists_unique_leastSelector J f hex

#print axioms orderedDomainOfTimeIsomorphism
#print axioms physicalModel_exists_unique_leastSelector
end StackSorting.SparseEndpointMSO.CanonicalChoice
