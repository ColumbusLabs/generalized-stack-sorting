import PhysicalPortDiagram

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.SparseTreeCompiler
open TreeAutomaton TreeAutomaton.Logic SparseEndpointMSO
open FinitePort FinitePort.ChildSibling GraphWidth

theorem physicalPortDecoder_successor_route {W : Nat}
    (t : BinaryTree (Alphabet 2 2 W)) (p q : Position t) :
    ((physicalPortDecoder W).relations t).successor p q ↔
      (relationRoute parentRoute (0 : Fin 2)).EvalAt t (binaryVal p q) := by
  classical
  rw [FinitePortDecoder.relations,FinitePortDecoder.successor_iff]
  change (∃ i : Fin 2, i ∈ ({0} : Finset _) ∧
    (relationRoute parentRoute i).EvalAt t (binaryVal p q)) ↔ _
  simp only [Finset.mem_singleton,exists_eq_left]

theorem physicalPortDecoder_matching_route {W : Nat}
    (t : BinaryTree (Alphabet 2 2 W)) (p q : Position t) :
    ((physicalPortDecoder W).relations t).matching p q ↔
      (relationRoute parentRoute (1 : Fin 2)).EvalAt t (binaryVal p q) := by
  classical
  rw [FinitePortDecoder.relations,FinitePortDecoder.matching_iff]
  change (∃ i : Fin 2, i ∈ ({1} : Finset _) ∧
    (relationRoute parentRoute i).EvalAt t (binaryVal p q)) ↔ _
  simp only [Finset.mem_singleton,exists_eq_left]

/-- All colors of the actual two-color vocabulary are determined by the
decoded model; there is no unused alphabet color to vary between codes. -/
theorem physical_sameNode_colors {D : Model} {n W : Nat}
    (e : Fin n ≃ {x // x ∈ D.domain})
    (t : BinaryTree (Alphabet 2 2 W)) (J : SameNodeDecoding (physicalPortDecoder W) D t)
    (f : Position t → Fin n) (he : ∀ p, e (f p)=J.vertex p) (p : Position t) :
    p.label.toLabel.color=(physicalPortDiagram D e).color (f p) := by
  classical
  funext c
  fin_cases c
  · have h := (J.insert_iff p).trans
      (constructedDecoder_insert parentRoute (0 : Fin 2) 1 (0 : Fin 2) 1 Position.label
        (fun d u v => Child d u v) p)
    apply Bool.eq_iff_iff.mpr
    simpa [physicalPortDiagram,he] using h.symm
  · have h := (J.remove_iff p).trans
      (constructedDecoder_remove parentRoute (0 : Fin 2) 1 (0 : Fin 2) 1 Position.label
        (fun d u v => Child d u v) p)
    apply Bool.eq_iff_iff.mpr
    simpa [physicalPortDiagram,he] using h.symm

/-- Both relation slots are likewise exact. In particular, direction and
zero-valued labels are not discarded by model transport. -/
theorem physical_sameNode_relations {D : Model} {n W : Nat}
    (e : Fin n ≃ {x // x ∈ D.domain})
    (t : BinaryTree (Alphabet 2 2 W)) (J : SameNodeDecoding (physicalPortDecoder W) D t)
    (f : Position t → Fin n) (he : ∀ p, e (f p)=J.vertex p)
    (q : Fin 2) (p p' : Position t) :
    (relationRoute parentRoute q).EvalAt t (binaryVal p p') ↔
      (physicalPortDiagram D e).rel q (f p) (f p')=true := by
  classical
  fin_cases q
  · have h := (physicalPortDecoder_successor_route t p p').symm.trans (J.successor_iff p p').symm
    simpa [physicalPortDiagram,he] using h
  · have h := (physicalPortDecoder_matching_route t p p').symm.trans (J.matching_iff p p').symm
    simpa [physicalPortDiagram,he] using h

#print axioms physical_sameNode_colors
#print axioms physical_sameNode_relations
end StackSorting.SparseTreeCompiler
