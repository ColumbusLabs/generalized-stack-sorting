import BinaryNormalPortRecognition
import SparseFullClass

namespace StackSorting.SparseEndpointMSO

/-- A concrete duplicate-free natural-number presentation of any finite
relation carrier. Predicates outside the actual domain are false. -/
def finiteNamedModel {P : Type} {n : Nat} (R : Relations P) (e : P ≃ Fin n) : Model where
  domain := List.range n
  I x := ∃ p, (e p).val=x ∧ R.insert p
  R x := ∃ p, (e p).val=x ∧ R.remove p
  S x y := ∃ p q, (e p).val=x ∧ (e q).val=y ∧ R.successor p q
  M x y := ∃ p q, (e p).val=x ∧ (e q).val=y ∧ R.matching p q

def finiteNamedInterpretation {P : Type} {n : Nat} (R : Relations P) (e : P ≃ Fin n) :
    DomainInterpretation (finiteNamedModel R e) R where
  vertex := {
    toFun p := ⟨(e p).val,List.mem_range.mpr (e p).isLt⟩
    invFun p := e.symm ⟨p.val,List.mem_range.mp p.property⟩
    left_inv p := by simp
    right_inv p := by apply Subtype.ext; simp }
  insert_iff p := by
    constructor
    · rintro ⟨q,hq,h⟩
      have he : q=p := e.injective (Fin.ext hq)
      simpa only [he] using h
    · intro h; exact ⟨p,rfl,h⟩
  remove_iff p := by
    constructor
    · rintro ⟨q,hq,h⟩
      have he : q=p := e.injective (Fin.ext hq)
      simpa only [he] using h
    · intro h; exact ⟨p,rfl,h⟩
  successor_iff p q := by
    constructor
    · rintro ⟨u,v,hu,hv,h⟩
      have he : u=p := e.injective (Fin.ext hu)
      have hf : v=q := e.injective (Fin.ext hv)
      simpa only [he,hf] using h
    · intro h; exact ⟨p,q,rfl,rfl,h⟩
  matching_iff p q := by
    constructor
    · rintro ⟨u,v,hu,hv,h⟩
      have he : u=p := e.injective (Fin.ext hu)
      have hf : v=q := e.injective (Fin.ext hv)
      simpa only [he,hf] using h
    · intro h; exact ⟨p,q,rfl,rfl,h⟩

end StackSorting.SparseEndpointMSO

namespace StackSorting.SparseTreeCompiler
open TreeAutomaton TreeAutomaton.Logic SparseEndpointMSO FinitePort.ChildSibling
variable {α : Type}

/-- Every finite binary tree has an actual sparse model on exactly its internal
positions. This constructs the semantic witness instead of assuming one. -/
noncomputable def decodedModel (D : FinitePortDecoder α) (t : BinaryTree α) : Model :=
  finiteNamedModel (D.relations t) (positionIndexEquiv t)

noncomputable def decodedModel_sameNode (D : FinitePortDecoder α) (t : BinaryTree α) :
    SameNodeDecoding D (decodedModel D t) t :=
  finiteNamedInterpretation (D.relations t) (positionIndexEquiv t)

theorem decodedModel_domain (D : FinitePortDecoder α) (t : BinaryTree α) :
    (decodedModel D t).domain=List.range t.numNodes := rfl

/-- Literal sparse acceptance on the tree gives an actual generated output,
its exact event-size factor two, and uniqueness of that output. It does not
claim that different accepted trees cannot encode the same output. -/
theorem decoded_physical_unique_generated (D : FinitePortDecoder α) (t : BinaryTree α)
    (r s : Nat) (h : (sentence D (fullAcceptedSentence r s)).EvalAt t Fin.elim0) :
    ∃ n output, output.Perm (List.range n) ∧ Generalized.Run r s [] (List.range n) output [] ∧
      Nonempty (Isomorphism (decodedModel D t) (canonicalDiagram output)) ∧
      t.numNodes=2*n ∧
      ∀ m other, other.Perm (List.range m) →
        Nonempty (Isomorphism (decodedModel D t) (canonicalDiagram other)) → other=output := by
  have hd : Satisfies (decodedModel D t) (fullAcceptedSentence r s) :=
    ((decodedModel_sameNode D t).satisfies _).mpr ((sentence_evalAt D _ t).mp h)
  obtain ⟨n,output,hp,hg,hi,hu⟩ := fullAcceptedSentence_exists_unique_generated hd
  refine ⟨n,output,hp,hg,hi,?_,hu⟩
  obtain ⟨iso⟩ := hi
  have hs := canonical_isomorphism_domain_size
    (show (decodedModel D t).domain.Nodup from List.nodup_range) hp iso
  simpa only [decodedModel_domain,List.length_range] using hs

theorem decoded_physical_even_size (D : FinitePortDecoder α) (t : BinaryTree α)
    (r s : Nat) (h : (sentence D (fullAcceptedSentence r s)).EvalAt t Fin.elim0) :
    ∃ n, t.numNodes=2*n := by
  obtain ⟨n,_,_,_,_,hn,_⟩ := decoded_physical_unique_generated D t r s h
  exact ⟨n,hn⟩

#print axioms decodedModel_sameNode
#print axioms decoded_physical_unique_generated
#print axioms decoded_physical_even_size
end StackSorting.SparseTreeCompiler
