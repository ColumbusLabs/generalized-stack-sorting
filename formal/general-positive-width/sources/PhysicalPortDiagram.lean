import PhysicalNormalCodec
import NormalBinaryRecognition
import SelectedParentTreeSyntax

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.SparseTreeCompiler
open TreeAutomaton TreeAutomaton.Logic SparseEndpointMSO
open SparseEndpointMSO.CanonicalChoice SparseEndpointMSO.EliminationSyntax
open FinitePort FinitePort.ChildSibling GraphWidth

/-- Exactly the two original event colors and two sparse edge predicates. -/
noncomputable def physicalPortDiagram {n : Nat} (D : Model)
    (e : Fin n ≃ {x // x ∈ D.domain}) : Diagram n 2 2 := by
  classical
  exact {
    color v c := if c=0 then decide (D.I (e v).val) else decide (D.R (e v).val)
    rel q u v := if q=0 then decide (D.S (e u).val (e v).val)
      else decide (D.M (e u).val (e v).val) }

theorem physicalPortDiagram_adjacent {n : Nat} (D : Model)
    (e : Fin n ≃ {x // x ∈ D.domain}) (u v : Fin n) :
    Adjacent (physicalPortDiagram D e) u v ↔ ModelAdjacent D (e u).val (e v).val := by
  classical
  constructor
  · rintro ⟨q,h⟩
    fin_cases q <;> simp [physicalPortDiagram] at h
    · exact h.elim Or.inl (fun h => Or.inr (Or.inl h))
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h | h)
    · exact ⟨0,Or.inl (by simpa [physicalPortDiagram] using h)⟩
    · exact ⟨0,Or.inr (by simpa [physicalPortDiagram] using h)⟩
    · exact ⟨1,Or.inl (by simpa [physicalPortDiagram] using h)⟩
    · exact ⟨1,Or.inr (by simpa [physicalPortDiagram] using h)⟩

theorem physical_model_no_loops {D : Model} {r s : Nat}
    (hD : Satisfies D (fullAcceptedSentence r s)) (x : Nat) (hx : x ∈ D.domain) :
    ¬D.S x x ∧ ¬D.M x x := by
  obtain ⟨_,output,_,_,⟨iso⟩⟩ := (fullAcceptedSentence_iff_generated D r s).mp hD
  constructor
  · intro h
    have hs := (iso.successor_iff x hx x hx).mp h
    have hh : iso.toFun x+1=iso.toFun x := hs.2.2
    omega
  · intro h
    obtain ⟨v,h | h⟩ := (iso.matching_iff x hx x hx).mp h <;>
      have he := h.1.symm.trans h.2 <;> cases he

theorem physicalPortDiagram_loopless {D : Model} {r s n : Nat}
    (hD : Satisfies D (fullAcceptedSentence r s))
    (e : Fin n ≃ {x // x ∈ D.domain}) : Loopless (physicalPortDiagram D e) := by
  classical
  intro q v
  have hh := physical_model_no_loops hD (e v).val (e v).property
  fin_cases q <;> simp [physicalPortDiagram,hh.1,hh.2]

def physicalPortGraph {D : Model} {r s n : Nat}
    (hD : Satisfies D (fullAcceptedSentence r s))
    (e : Fin n ≃ {x // x ∈ D.domain}) : Graph n where
  Adj u v := ModelAdjacent D (e u).val (e v).val
  symm := by
    intro u v h
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  loopless v := by
    have hh := physical_model_no_loops hD (e v).val (e v).property
    rintro (h | h | h | h)
    · exact hh.1 h
    · exact hh.1 h
    · exact hh.2 h
    · exact hh.2 h

noncomputable def physicalPortDecoder (W : Nat) : FinitePortDecoder (Alphabet 2 2 W) :=
  constructedDecoder parentRoute 0 1 0 1

/-- The actual finite-alphabet code decodes the entire original model, with
no separately supplied interpretation or predicate agreement. -/
noncomputable def physicalCode_sameNode {D : Model} {n W : Nat}
    (e : Fin n ≃ {x // x ∈ D.domain})
    (E : ExactRootEmptyCodec (physicalPortDiagram D e) W)
    (O : FixedOrder n) (hn : 0<n) :
    SameNodeDecoding (physicalPortDecoder W) D (binaryCode E.toExactNumberedCodec O hn) where
  vertex := (binaryCodeVertexEquiv E.toExactNumberedCodec O hn).trans e
  insert_iff p := by
    change D.I _ ↔ ((constructedDecoder parentRoute (0 : Fin 2) 1 (0 : Fin 2) 1).relations _).insert p
    rw [binaryCode_decoder_insert]
    simp [physicalPortDiagram]
  remove_iff p := by
    change D.R _ ↔ ((constructedDecoder parentRoute (0 : Fin 2) 1 (0 : Fin 2) 1).relations _).remove p
    rw [binaryCode_decoder_remove]
    simp [physicalPortDiagram]
  successor_iff p q := by
    change D.S _ _ ↔ ((constructedDecoder parentRoute (0 : Fin 2) 1 (0 : Fin 2) 1).relations _).successor p q
    rw [binaryCode_decoder_successor]
    simp [physicalPortDiagram]
  matching_iff p q := by
    change D.M _ _ ↔ ((constructedDecoder parentRoute (0 : Fin 2) 1 (0 : Fin 2) 1).relations _).matching p q
    rw [binaryCode_decoder_matching]
    simp [physicalPortDiagram]

#print axioms physicalPortGraph
#print axioms physicalCode_sameNode
end StackSorting.SparseTreeCompiler
