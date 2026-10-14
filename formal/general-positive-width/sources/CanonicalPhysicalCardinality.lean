import CanonicalEmptyCode
import DomainInterpretationIsomorphism
import GeneralizedActualCounting
import Mathlib.Data.Finset.Card

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.SparseTreeCompiler.CanonicalCounting
open TreeAutomaton TreeAutomaton.Logic SparseEndpointMSO
open SparseEndpointMSO.CanonicalChoice SparseEndpointMSO.EliminationSyntax
open Generalized Generalized.ActualCounting FinitePort
noncomputable section

/-- The still-required uniform original-vocabulary existence input. It is
explicit and is not a recognizability, decomposition or count assumption. -/
def UniformAdmissibility {k : Nat} (earlier : SparseEndpointMSO.Formula 2 k)
    (b r s : Nat) : Prop :=
  ∀ D : Model, Satisfies D (fullAcceptedSentence r s) →
    ∃ X, SupportedTuple D X ∧ Eval D (admissibleSentence earlier b) Fin.elim0 X

def acceptedTrees {k : Nat} (earlier : SparseEndpointMSO.Formula 2 k)
    (b r s m : Nat) : Finset (BinaryTree (Alphabet 2 2 (b-1))) := by
  classical
  exact (treesOfSize m).filter (fun t => (canonicalCodeSentence earlier b r s).EvalAt t Fin.elim0)

theorem mem_acceptedTrees {k : Nat} (earlier : SparseEndpointMSO.Formula 2 k)
    (b r s m : Nat) (t : BinaryTree (Alphabet 2 2 (b-1))) :
    t ∈ acceptedTrees earlier b r s m ↔ t.numNodes=m ∧
      (canonicalCodeSentence earlier b r s).EvalAt t Fin.elim0 := by
  classical
  simp [acceptedTrees]

def identityIso (D : Model) : Isomorphism D D where
  toFun := id
  invFun := id
  to_mem _ hx := hx
  inv_mem _ hx := hx
  left_inv _ _ := rfl
  right_inv _ _ := rfl
  insert_iff _ _ := Iff.rfl
  remove_iff _ _ := Iff.rfl
  successor_iff _ _ _ _ := Iff.rfl
  matching_iff _ _ _ _ := Iff.rfl

def timeNames (D : Model) (n : Nat) (hp : TimePath D n) :
    Fin n ≃ {x // x ∈ D.domain} where
  toFun i := ⟨i.val,by rw [hp.1,List.mem_range]; exact i.isLt⟩
  invFun x := ⟨x.val,by exact List.mem_range.mp (by simpa only [hp.1] using x.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem accepted_has_output {k b r s n : Nat}
    (earlier : SparseEndpointMSO.Formula 2 k) (hr : 0<r) (hs : 0<s)
    (t : BinaryTree (Alphabet 2 2 (b-1))) (ht : t ∈ acceptedTrees earlier b r s (2*n)) :
    ∃ output, output ∈ generatedOutputs r s n ∧
      Nonempty (Isomorphism (decodedModel (physicalPortDecoder (b-1)) t) (canonicalDiagram output)) := by
  have ht' := (mem_acceptedTrees earlier b r s (2*n) t).mp ht
  obtain ⟨m,output,_,hg,hi,hlen,_⟩ := decoded_physical_unique_generated _ t r s ht'.2.1
  have hm : m=n := by omega
  subst m
  exact ⟨output,(mem_generatedOutputs_iff hr hs output).mpr hg,hi⟩

theorem output_has_accepted {k b r s n : Nat}
    (earlier : SparseEndpointMSO.Formula 2 k) (hr : 0<r) (hs : 0<s)
    (hU : UniformAdmissibility earlier b r s)
    (output : List Nat) (ho : output ∈ generatedOutputs r s n) :
    ∃ t, t ∈ acceptedTrees earlier b r s (2*n) ∧
      Nonempty (Isomorphism (decodedModel (physicalPortDecoder (b-1)) t) (canonicalDiagram output)) := by
  have hg := (mem_generatedOutputs_iff hr hs output).mp ho
  have hp : output.Perm (List.range n) := by simpa using hg.supply.symm
  have hD : Satisfies (canonicalDiagram output) (fullAcceptedSentence r s) :=
    (fullAcceptedSentence_iff_generated _ _ _).mpr ⟨n,output,hp,hg,⟨identityIso _⟩⟩
  obtain ⟨t,ht,⟨J⟩,hc⟩ := physical_exists_canonical_tree_all_sizes hD
    (timeNames _ (2*n) (canonical_time_path hp)) earlier b (hU _ hD)
  exact ⟨t,(mem_acceptedTrees earlier b r s (2*n) t).mpr ⟨ht,hc⟩,
    ⟨(decodedModel_sameNode (physicalPortDecoder (b-1)) t).modelIsomorphism J⟩⟩

/-- Exact cardinality of literal canonical trees equals the actual distinct
physical output count, with event size 2n. No histories, decompositions or
monadic annotations are counted. -/
theorem accepted_card_generatedCount {k b r s : Nat}
    (earlier : SparseEndpointMSO.Formula 2 k) (hr : 0<r) (hs : 0<s)
    (hU : UniformAdmissibility earlier b r s) (n : Nat) :
    (acceptedTrees earlier b r s (2*n)).card = generatedCount r s n := by
  classical
  let A := acceptedTrees earlier b r s (2*n)
  let B := (generatedOutputs r s n).toFinset
  let f (t) (ht : t ∈ A) := Classical.choose (accepted_has_output earlier hr hs t ht)
  have hf (t) (ht : t ∈ A) : f t ht ∈ generatedOutputs r s n ∧
      Nonempty (Isomorphism (decodedModel (physicalPortDecoder (b-1)) t) (canonicalDiagram (f t ht))) :=
    Classical.choose_spec (accepted_has_output earlier hr hs t ht)
  have hc : A.card=B.card := by
    apply Finset.card_bij f
    · intro t ht; exact List.mem_toFinset.mpr (hf t ht).1
    · intro t ht u hu he
      obtain ⟨it⟩ := (hf t ht).2
      obtain ⟨iu⟩ := (hf u hu).2
      apply canonical_code_output_unique (b := b) (k := k) earlier t u
        ((mem_acceptedTrees earlier b r s (2*n) t).mp ht).2
        ((mem_acceptedTrees earlier b r s (2*n) u).mp hu).2 (f t ht) it
      simpa only [he] using iu
    · intro output ho
      have ho' := List.mem_toFinset.mp ho
      obtain ⟨t,ht,⟨it⟩⟩ := output_has_accepted earlier hr hs hU output ho'
      refine ⟨t,ht,?_⟩
      obtain ⟨iu⟩ := (hf t ht).2
      have hgp := (mem_generatedOutputs_iff hr hs _).mp (hf t ht).1
      have hgo := (mem_generatedOutputs_iff hr hs _).mp ho'
      have hp : (f t ht).Perm (List.range n) := by simpa using hgp.supply.symm
      have hq : output.Perm (List.range n) := by simpa using hgo.supply.symm
      exact canonicalDiagram_isomorphic_injective hp hq (iu.symm.trans it)
  exact hc.trans (List.toFinset_card_of_nodup (generatedOutputs_nodup r s n))

theorem accepted_card_odd {k b r s : Nat}
    (earlier : SparseEndpointMSO.Formula 2 k) (n : Nat) :
    (acceptedTrees earlier b r s (2*n+1)).card=0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have h := (mem_acceptedTrees earlier b r s (2*n+1) t).mp ht
  obtain ⟨m,hm⟩ := decoded_physical_even_size _ t r s h.2.1
  omega

#print axioms accepted_card_generatedCount
#print axioms accepted_card_odd
end
end StackSorting.SparseTreeCompiler.CanonicalCounting
