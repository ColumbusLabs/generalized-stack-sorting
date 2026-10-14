import CanonicalCodeIsomorphism
import BinaryNormalRecognitionControls

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.SparseTreeCompiler
open TreeAutomaton TreeAutomaton.Logic SparseEndpointMSO
open SparseEndpointMSO.CanonicalChoice SparseEndpointMSO.EliminationSyntax
open FinitePort FinitePort.ChildSibling FinitePort.ChildSibling.BinaryOrderMSO

theorem canonicalCode_empty {k : Nat}
    (earlier : SparseEndpointMSO.Formula 2 k) (b r s : Nat) :
    (canonicalCodeSentence earlier b r s).EvalAt .nil Fin.elim0 := by
  let A := Alphabet 2 2 (b-1)
  let T : RootedTree 0 := ⟨Fin.elim0,fun v => Fin.elim0 v⟩
  let O := timeFixedOrder 0
  let G : Diagram 0 2 2 := ⟨Fin.elim0,fun _ => Fin.elim0⟩
  let e : Position (BinaryTree.nil : BinaryTree A) ≃ Fin 0 := positionIndexEquiv .nil
  let order := treeChronologicalBefore (physicalPortDecoder (b-1))
  have he : (exactCodeSentence order (fun q => relationRoute parentRoute q)).EvalAt
      (BinaryTree.nil : BinaryTree A) Fin.elim0 := by
    apply (exactCodeSentence_correct T O G .nil e order _
      (fun p => nomatch p) (fun p => nomatch p)
      (fun _ p => nomatch p) (fun p => nomatch p)).mpr
    refine ⟨Or.inl rfl,(fun p => nomatch p),?_⟩
    funext i
    exact Fin.elim0 i
  have hp : (selectedParentSentence (physicalPortDecoder (b-1)) earlier b).EvalAt .nil Fin.elim0 := by
    apply (eval_parentAgreementSentence _ _ .nil (decodedModel_sameNode _ .nil) _).mpr
    intro p
    exact nomatch p
  exact ⟨BinaryRecognitionControls.empty_physically_accepted _ r s,he,hp⟩

/-- Uniform forward existence includes the empty object with zero vertices
and no artificial root or annotation multiplicity. -/
theorem physical_exists_canonical_tree_all_sizes {D : Model} {r s n k : Nat}
    (hD : Satisfies D (fullAcceptedSentence r s))
    (e : Fin n ≃ {x // x ∈ D.domain})
    (earlier : SparseEndpointMSO.Formula 2 k) (b : Nat)
    (hex : ∃ X, SupportedTuple D X ∧ Eval D (admissibleSentence earlier b) Fin.elim0 X) :
    ∃ t : BinaryTree (Alphabet 2 2 (b-1)),
      t.numNodes=n ∧ Nonempty (SameNodeDecoding (physicalPortDecoder (b-1)) D t) ∧
      (canonicalCodeSentence earlier b r s).EvalAt t Fin.elim0 := by
  cases n with
  | zero =>
    let J : SameNodeDecoding (physicalPortDecoder (b-1)) D .nil := {
      vertex := {
        toFun := fun p => nomatch p
        invFun := fun x => Fin.elim0 (e.symm x)
        left_inv := fun p => nomatch p
        right_inv := fun x => Fin.elim0 (e.symm x) }
      insert_iff := fun p => nomatch p
      remove_iff := fun p => nomatch p
      successor_iff := fun p => nomatch p
      matching_iff := fun p => nomatch p }
    exact ⟨.nil,rfl,⟨J⟩,canonicalCode_empty earlier b r s⟩
  | succ n => exact physical_exists_canonical_tree hD e (by omega) earlier b hex

#print axioms canonicalCode_empty
#print axioms physical_exists_canonical_tree_all_sizes
end StackSorting.SparseTreeCompiler
