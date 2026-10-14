import PhysicalCanonicalCodeExistence
import PhysicalDecoderExactness

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.SparseTreeCompiler
open TreeAutomaton TreeAutomaton.Logic SparseEndpointMSO
open SparseEndpointMSO.CanonicalChoice SparseEndpointMSO.EliminationSyntax
open FinitePort FinitePort.ChildSibling FinitePort.ChildSibling.BinaryOrderMSO GraphWidth

/-- For two normalized nonempty codes of the same actual physical model,
the literal selected-parent sentence forces equal parent relations. Physical
chronology, both colors, and both sparse relations then force literal equality.
No common parent tree or matching labels are assumed. -/
theorem physical_same_model_canonical_unique {D : Model} {r s k b : Nat}
    (hD : Satisfies D (fullAcceptedSentence r s))
    (earlier : SparseEndpointMSO.Formula 2 k)
    (a a' : Alphabet 2 2 (b-1)) (l l' : BinaryTree (Alphabet 2 2 (b-1)))
    (J : SameNodeDecoding (physicalPortDecoder (b-1)) D (.node a l .nil))
    (J' : SameNodeDecoding (physicalPortDecoder (b-1)) D (.node a' l' .nil))
    (ha : (canonicalCodeSentence earlier b r s).EvalAt (.node a l .nil) Fin.elim0)
    (hb : (canonicalCodeSentence earlier b r s).EvalAt (.node a' l' .nil) Fin.elim0) :
    BinaryTree.node a l .nil=BinaryTree.node a' l' .nil := by
  let t := BinaryTree.node a l .nil
  let t' := BinaryTree.node a' l' .nil
  let e := positionIndexEquiv t
  let names := e.symm.trans J.vertex
  let f := J'.vertex.trans names.symm
  let T := normalPositionTree a l
  let G := physicalPortDiagram D names
  have he (p : Position t) : names (e p)=J.vertex p := congrArg J.vertex (e.symm_apply_apply p)
  have hf (p : Position t') : names (f p)=J'.vertex p := by simp [f]
  have hx (p : Position t') : J.vertex (e.symm (f p))=J'.vertex p := hf p
  obtain ⟨O,hO⟩ := physical_has_fixed_chronology hD names
  let order := treeChronologicalBefore (physicalPortDecoder (b-1))
  let parent := selectedParent (admissibleSentence earlier b) earlier
  have hpa : ∀ p q : Position t, ParentPosition p q ↔
      RelationEval D parent Fin.elim0 (J.vertex p).val (J.vertex q).val :=
    (eval_parentAgreementSentence _ D t J parent).mp ha.2.2
  have hpb : ∀ p q : Position t', ParentPosition p q ↔
      RelationEval D parent Fin.elim0 (J'.vertex p).val (J'.vertex q).val :=
    (eval_parentAgreementSentence _ D t' J' parent).mp hb.2.2
  have hp : ∀ p q : Position t, ParentPosition p q ↔
      (e q).val≠0 ∧ T.parent (e q)=e p :=
    fun p q => (normalPositionTree_exact_parent a l p q).symm
  have hp' : ∀ p q : Position t', ParentPosition p q ↔
      (f q).val≠0 ∧ T.parent (f q)=f p := by
    intro p q
    calc
      ParentPosition p q ↔ RelationEval D parent Fin.elim0
          (J'.vertex p).val (J'.vertex q).val := hpb p q
      _ ↔ ParentPosition (e.symm (f p)) (e.symm (f q)) := by rw [hpa,hx,hx]
      _ ↔ (f q).val≠0 ∧ T.parent (f q)=f p := by rw [hp]; simp only [Equiv.apply_symm_apply]
  have ho : ExactPositionOrder O t e order := by
    intro p q
    have h := hO (e p) (e q)
    rw [he,he] at h
    exact (eval_treeChronologicalBefore _ D t J p q).trans h
  have ho' : ExactPositionOrder O t' f order := by
    intro p q
    have h := hO (f p) (f q)
    rw [hf,hf] at h
    exact (eval_treeChronologicalBefore _ D t' J' p q).trans h
  exact exact_sentence_graph_code_unique T O G a a' l l' e f order _ hp hp' ho ho'
    (physical_sameNode_relations names t J e he)
    (physical_sameNode_relations names t' J' f hf)
    (physical_sameNode_colors names t J e he)
    (physical_sameNode_colors names t' J' f hf) ha.2.1 hb.2.1

#print axioms physical_same_model_canonical_unique
end StackSorting.SparseTreeCompiler
