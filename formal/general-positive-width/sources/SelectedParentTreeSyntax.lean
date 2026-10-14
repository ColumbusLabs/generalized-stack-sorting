import PhysicalSelectedForest
import PhysicalChronologicalOrder

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.SparseTreeCompiler
open TreeAutomaton TreeAutomaton.Logic SparseEndpointMSO
open FinitePort FinitePort.ChildSibling FinitePort.ChildSibling.BinaryOrderMSO
open SparseEndpointMSO.CanonicalChoice SparseEndpointMSO.EliminationSyntax
variable {α : Type}

/-- Literal translation of a set-free binary sparse formula. Internal monadic
quantifiers, including the least-selector tuple, remain inside its syntax. -/
noncomputable def binarySparseFormula (D : FinitePortDecoder α)
    (f : SparseEndpointMSO.Formula 2 0) : TreeAutomaton.Logic.Formula α 2 :=
  compile D.codes f id Fin.elim0

theorem eval_binarySparseFormula (D : FinitePortDecoder α) (G : Model)
    (t : BinaryTree α) (J : SameNodeDecoding D G t)
    (f : SparseEndpointMSO.Formula 2 0) (p q : Position t) :
    (binarySparseFormula D f).EvalAt t (binaryVal p q) ↔
      RelationEval G f Fin.elim0 (J.vertex p).val (J.vertex q).val := by
  let envP : Fin 2 → Position t := Fin.cons p (fun _ => q)
  let envD : Fin 2 → Nat := Fin.cons (J.vertex p).val (fun _ => (J.vertex q).val)
  have rep : Represents id (Fin.elim0 : Fin 0 → Fin 2) (binaryVal p q) envP Fin.elim0 := by
    constructor
    · intro i; exact Fin.cases rfl (fun _ => rfl) i
    · intro i; exact Fin.elim0 i
  have hc := compile_correct Position.label (fun d u v => Child d u v) D.codes
    f id Fin.elim0 (binaryVal p q) envP Fin.elim0 rep
  have hj := J.eval f envD envP Fin.elim0 Fin.elim0
    (by intro i; exact Fin.cases rfl (fun _ => rfl) i) (fun i => Fin.elim0 i)
  exact hc.trans hj.symm

noncomputable def parentAgreementSentence (D : FinitePortDecoder α)
    (parent : SparseEndpointMSO.Formula 2 0) : TreeAutomaton.Logic.Formula α 0 :=
  allBlock 2 (.conj (implies parentRoute (binarySparseFormula D parent))
    (implies (binarySparseFormula D parent) parentRoute))

theorem eval_parentAgreementSentence (D : FinitePortDecoder α) (G : Model)
    (t : BinaryTree α) (J : SameNodeDecoding D G t)
    (parent : SparseEndpointMSO.Formula 2 0) :
    (parentAgreementSentence D parent).EvalAt t Fin.elim0 ↔
      ∀ p q : Position t, ParentPosition p q ↔
        RelationEval G parent Fin.elim0 (J.vertex p).val (J.vertex q).val := by
  have hblock (f : TreeAutomaton.Logic.Formula α 2) :
      (allBlock 2 f).EvalAt t Fin.elim0 ↔
        ∀ xs : Fin 2 → Position t,
          f.EvalAt t (fun i => point (xs i)) := by
    rw [Formula.EvalAt,eval_allBlock]
    simp [Formula.EvalAt]
  rw [parentAgreementSentence,hblock]
  have hval (xs : Fin 2 → Position t) :
      (fun i => point (xs i))=binaryVal (xs 0) (xs 1) := by
    funext i
    fin_cases i <;> rfl
  have hb (xs : Fin 2 → Position t) :
      (Formula.conj (implies parentRoute (binarySparseFormula D parent))
        (implies (binarySparseFormula D parent) parentRoute)).EvalAt t
          (fun i => point (xs i)) ↔
        (ParentPosition (xs 0) (xs 1) ↔
          RelationEval G parent Fin.elim0 (J.vertex (xs 0)).val (J.vertex (xs 1)).val) := by
    rw [hval]
    change ((implies parentRoute (binarySparseFormula D parent)).EvalOn Position.label
      (fun d p q => Child d p q) (binaryVal (xs 0) (xs 1)) ∧
      (implies (binarySparseFormula D parent) parentRoute).EvalOn Position.label
      (fun d p q => Child d p q) (binaryVal (xs 0) (xs 1))) ↔ _
    rw [eval_implies,eval_implies,parentRoute_correct]
    change ((ParentPosition (xs 0) (xs 1) →
      (binarySparseFormula D parent).EvalAt t (binaryVal (xs 0) (xs 1))) ∧
      ((binarySparseFormula D parent).EvalAt t (binaryVal (xs 0) (xs 1)) →
        ParentPosition (xs 0) (xs 1))) ↔ _
    rw [eval_binarySparseFormula D G t J]
    exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.mp,h.mpr⟩⟩
  constructor
  · intro h p q
    exact (hb (Fin.cons p (fun _ => q))).mp (h _)
  · intro h xs
    exact (hb xs).mpr (h (xs 0) (xs 1))

/-- This sentence fixes the parent with no free annotation sets and no
supplied parent relation. Admissible annotation existence is proved elsewhere. -/
noncomputable def selectedParentSentence {k : Nat} (D : FinitePortDecoder α)
    (earlier : SparseEndpointMSO.Formula 2 k) (b : Nat) :
    TreeAutomaton.Logic.Formula α 0 :=
  parentAgreementSentence D (selectedParent (admissibleSentence earlier b) earlier)

#print axioms eval_binarySparseFormula
#print axioms eval_parentAgreementSentence
end StackSorting.SparseTreeCompiler
