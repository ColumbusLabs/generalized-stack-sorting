import PhysicalPortDiagram
import PhysicalOrderIndex

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.SparseTreeCompiler
open TreeAutomaton TreeAutomaton.Logic SparseEndpointMSO
open SparseEndpointMSO.CanonicalChoice SparseEndpointMSO.EliminationSyntax
open FinitePort FinitePort.ChildSibling FinitePort.ChildSibling.BinaryOrderMSO GraphWidth

/-- One fixed finite-tree sentence: physical sparse acceptance, normal ports
and chronological siblings, and agreement with the set-free selected parent. -/
noncomputable def canonicalCodeSentence {k : Nat}
    (earlier : SparseEndpointMSO.Formula 2 k) (b r s : Nat) :
    TreeAutomaton.Logic.Formula (Alphabet 2 2 (b-1)) 0 :=
  .conj (sentence (physicalPortDecoder (b-1)) (fullAcceptedSentence r s))
    (.conj (exactCodeSentence (treeChronologicalBefore (physicalPortDecoder (b-1)))
      (fun q => relationRoute parentRoute q))
      (selectedParentSentence (physicalPortDecoder (b-1)) earlier b))

/-- Actual forward existence, conditional on the one remaining definability
input: a supported tuple satisfying the literal admissibility formula.
Neither a parent, a normal codec, an order nor a decoder witness is supplied. -/
theorem physical_exists_canonical_tree {D : Model} {r s n k : Nat}
    (hD : Satisfies D (fullAcceptedSentence r s))
    (e : Fin n ≃ {x // x ∈ D.domain}) (hn : 0<n)
    (earlier : SparseEndpointMSO.Formula 2 k) (b : Nat)
    (hex : ∃ X, SupportedTuple D X ∧ Eval D (admissibleSentence earlier b) Fin.elim0 X) :
    ∃ t : BinaryTree (Alphabet 2 2 (b-1)),
      t.numNodes=n ∧ Nonempty (SameNodeDecoding (physicalPortDecoder (b-1)) D t) ∧
      (canonicalCodeSentence earlier b r s).EvalAt t Fin.elim0 := by
  obtain ⟨O,hO⟩ := physical_has_fixed_chronology hD e
  let H := physicalPortGraph hD e
  let G := physicalPortDiagram D e
  obtain ⟨P,E,hparent⟩ := physical_exists_normal_selected_codec hD e earlier b H
    (fun _ _ => Iff.rfl) G (fun u v => (physicalPortDiagram_adjacent D e u v).symm)
    (physicalPortDiagram_loopless hD e) hn O hex
  let C := E.toExactNumberedCodec
  let t := binaryCode C E.order hn
  let J := physicalCode_sameNode e E.toExactRootEmptyCodec E.order hn
  have hphys : (sentence (physicalPortDecoder (b-1)) (fullAcceptedSentence r s)).EvalAt t Fin.elim0 :=
    (sentence_evalAt _ _ _).mpr ((J.satisfies _).mp hD)
  have ho : ExactPositionOrder O t (binaryCodeVertexEquiv C E.order hn)
      (treeChronologicalBefore (physicalPortDecoder (b-1))) := by
    intro p q
    exact (eval_treeChronologicalBefore _ D t J p q).trans (hO _ _)
  have he := E.binaryCode_exact_sentence hn _ ho
  have hp : (selectedParentSentence (physicalPortDecoder (b-1)) earlier b).EvalAt t Fin.elim0 := by
    apply (eval_parentAgreementSentence _ D t J _).mpr
    intro p q
    rw [binaryCode_parent]
    have hh := hparent (binaryCodeVertexEquiv C E.order hn p)
      (binaryCodeVertexEquiv C E.order hn q)
    simpa only [C,J,physicalCode_sameNode,binaryCodeVertexEquiv,Equiv.trans_apply,Equiv.coe_fn_mk,E.index_label] using hh.symm
  exact ⟨t,binaryCode_numNodes C E.order hn,⟨J⟩,hphys,he,hp⟩

/-- Recognizability counts this explicit language of literal binary trees.
Graph-count identification additionally uses canonical uniqueness. -/
theorem canonicalCode_recognizable {k : Nat}
    (earlier : SparseEndpointMSO.Formula 2 k) (b r s : Nat) :
    Recognizable {t | (canonicalCodeSentence earlier b r s).EvalAt t Fin.elim0} := by
  classical
  exact (canonicalCodeSentence earlier b r s).evalAt_recognizable

#print axioms physical_exists_canonical_tree
#print axioms canonicalCode_recognizable
end StackSorting.SparseTreeCompiler
