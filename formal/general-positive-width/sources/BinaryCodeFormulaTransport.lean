import BinaryParentMSO
import BinaryParentRelabeling
import RootEmptyNumberedCodec

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic SparseTreeCompiler GraphWidth
variable {α P Q : Type}

theorem binaryVal_equiv (e : P ≃ Q) (p q : P) :
    ∀ i x, binaryVal (e p) (e q) i (e x) = binaryVal p q i x := by
  classical
  intro i x
  refine Fin.cases ?_ (fun _ => ?_) i <;>
    simp [binaryVal,point]

noncomputable def codeChild {n colors relations W} {G : Diagram n colors relations}
    (E : ExactNumberedCodec G W) (O : FixedOrder n) (hn : 0 < n)
    (d : Bool) (u v : Fin n) : Prop :=
  Child d ((binaryCodeIndexEquiv E O hn).symm u) ((binaryCodeIndexEquiv E O hn).symm v)

/-- Every formula is transported through the actual position bijection;
quantification still ranges over exactly the original n vertices. -/
theorem eval_binaryCode_formula {n colors relations W} {G : Diagram n colors relations}
    (E : ExactNumberedCodec G W) (O : FixedOrder n) (hn : 0 < n)
    (f : Formula (Alphabet colors relations W) 2)
    (p q : Position (binaryCode E O hn)) :
    f.EvalOn Position.label (fun d u v => Child d u v) (binaryVal p q) ↔
      f.EvalOn (alphabetCode E.code E.bounded) (codeChild E O hn)
        (binaryVal (binaryCodeIndexEquiv E O hn p) (binaryCodeIndexEquiv E O hn q)) := by
  apply f.evalOn_equiv (binaryCodeIndexEquiv E O hn)
  · intro x
    apply Alphabet.toLabel_injective
    exact (Alphabet.toLabel_ofLabel ..).trans (binaryCode_label E O hn x).symm
  · intro d x y
    simp only [codeChild,Equiv.symm_apply_apply]
  · exact binaryVal_equiv (binaryCodeIndexEquiv E O hn) p q

/-- Exact proper-parent semantics on the numbered original carrier, obtained
from a literal tree-MSO formula rather than a definability assumption. -/
theorem binaryCode_exact_parent {n colors relations W} {G : Diagram n colors relations}
    (E : ExactNumberedCodec G W) (O : FixedOrder n) (hn : 0 < n) (p v : Fin n) :
    parentRoute.EvalOn (alphabetCode E.code E.bounded) (codeChild E O hn) (binaryVal p v) ↔
      v.val ≠ 0 ∧ p = E.tree.parent v := by
  let e := binaryCodeIndexEquiv E O hn
  have h := eval_binaryCode_formula E O hn parentRoute (e.symm p) (e.symm v)
  simp only [e,Equiv.apply_symm_apply] at h
  rw [← h,parentRoute_correct,binaryCode_parent]
  simp only [Equiv.apply_symm_apply,eq_comm]

#print axioms eval_binaryCode_formula
#print axioms binaryCode_exact_parent
end StackSorting.FinitePort.ChildSibling
