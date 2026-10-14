import BinaryDecodedPhysicalModel
import BinaryExactCodeSentence

namespace StackSorting.SparseTreeCompiler.BinaryRecognitionControls
open TreeAutomaton TreeAutomaton.Logic SparseEndpointMSO FinitePort.ChildSibling

variable {α : Type}

theorem decoded_empty_domain (D : FinitePortDecoder α) :
    (decodedModel D .nil).domain=[] := rfl

/-- The actual empty tree satisfies physical sparse acceptance at every width,
independently of unused alphabet labels and routes. -/
theorem empty_physically_accepted (D : FinitePortDecoder α) (r s : Nat) :
    (sentence D (fullAcceptedSentence r s)).EvalAt .nil Fin.elim0 := by
  apply (sentence_evalAt D _ .nil).mpr
  apply ((decodedModel_sameNode D .nil).satisfies _).mp
  change Eval (decodedModel D .nil) (disjunction emptySentence (acceptedSentence r s))
    Fin.elim0 Fin.elim0
  rw [eval_disjunction]
  exact Or.inl ((satisfies_emptySentence _).mpr rfl)

theorem no_single_event_model (D : FinitePortDecoder α) (a : α) (r s : Nat) :
    ¬ (sentence D (fullAcceptedSentence r s)).EvalAt (.node a .nil .nil) Fin.elim0 := by
  intro h
  obtain ⟨n,hn⟩ := decoded_physical_even_size D (.node a .nil .nil) r s h
  simp only [BinaryTree.numNodes] at hn
  omega

theorem physical_size_odd_rejected (D : FinitePortDecoder α) (t : BinaryTree α)
    (r s k : Nat) (hsize : t.numNodes=2*k+1) :
    ¬ (sentence D (fullAcceptedSentence r s)).EvalAt t Fin.elim0 := by
  intro h
  obtain ⟨n,hn⟩ := decoded_physical_even_size D t r s h
  omega

/-- Named predicates do not leak outside the actual finite domain. -/
theorem named_insert_off_domain {P : Type} {n : Nat} (R : Relations P)
    (e : P ≃ Fin n) (x : Nat) (hx : n≤x) : ¬ (finiteNamedModel R e).I x := by
  rintro ⟨p,hp,_⟩
  have hn := (e p).isLt
  omega

theorem named_edge_off_domain {P : Type} {n : Nat} (R : Relations P)
    (e : P ≃ Fin n) (x y : Nat) (hx : n≤x ∨ n≤y) :
    ¬ (finiteNamedModel R e).S x y := by
  rintro ⟨p,q,hp,hq,_⟩
  have hn := (e p).isLt
  have hm := (e q).isLt
  omega

#print axioms empty_physically_accepted
#print axioms no_single_event_model
#print axioms physical_size_odd_rejected
#print axioms named_insert_off_domain
#print axioms named_edge_off_domain
end StackSorting.SparseTreeCompiler.BinaryRecognitionControls
