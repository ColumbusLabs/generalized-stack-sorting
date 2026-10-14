import BinaryDecodedPhysicalModel
import BinaryExactCodeSentence
import PhysicalModelLeastSelector
import Mathlib.Data.List.FinRange

namespace StackSorting.SparseTreeCompiler
open TreeAutomaton TreeAutomaton.Logic SparseEndpointMSO
open SparseEndpointMSO.CanonicalChoice FinitePort FinitePort.ChildSibling
open FinitePort.ChildSibling.BinaryOrderMSO
variable {α : Type}

/-- A fixed literal translation of physical successor chronology. -/
noncomputable def treeChronologicalBefore (D : FinitePortDecoder α) : TreeAutomaton.Logic.Formula α 2 :=
  compile D.codes chronologicalBefore id Fin.elim0

theorem eval_treeChronologicalBefore (D : FinitePortDecoder α) (G : Model)
    (t : BinaryTree α) (J : SameNodeDecoding D G t) (p q : Position t) :
    (treeChronologicalBefore D).EvalAt t (binaryVal p q) ↔
      OrderEval G chronologicalBefore (J.vertex p).val (J.vertex q).val := by
  let envP : Fin 2 → Position t := Fin.cons p (fun _ => q)
  let envD : Fin 2 → Nat := Fin.cons (J.vertex p).val (fun _ => (J.vertex q).val)
  have rep : Represents id (Fin.elim0 : Fin 0 → Fin 2) (binaryVal p q) envP Fin.elim0 := by
    constructor
    · intro i; exact Fin.cases rfl (fun _ => rfl) i
    · intro i; exact Fin.elim0 i
  have hc := compile_correct Position.label (fun d u v => Child d u v) D.codes
    chronologicalBefore id Fin.elim0 (binaryVal p q) envP Fin.elim0 rep
  have hj := J.eval chronologicalBefore envD envP Fin.elim0 Fin.elim0
    (by intro i; exact Fin.cases rfl (fun _ => rfl) i) (fun i => Fin.elim0 i)
  exact hc.trans hj.symm

/-- The chronology on canonical time indices is fixed independently of the
binary representation and of its preorder enumeration. -/
def timeFixedOrder (n : Nat) : FixedOrder n where
  vertices := List.finRange n
  nodup := List.nodup_finRange n
  complete := List.mem_finRange

noncomputable def positionTimeEquiv {D : FinitePortDecoder α} {G : Model}
    {t : BinaryTree α} (J : SameNodeDecoding D G t) {n : Nat}
    (O : OrderedDomain G chronologicalBefore (Fin n)) : Position t ≃ Fin n :=
  J.vertex.trans O.vertex.symm

/-- The literal order formula has the exact chronology interpretation derived
from a genuine ordered physical model; no order-interpretation premise occurs. -/
theorem treeChronologicalBefore_exact {D : FinitePortDecoder α} {G : Model}
    {t : BinaryTree α} (J : SameNodeDecoding D G t) {n : Nat}
    (O : OrderedDomain G chronologicalBefore (Fin n)) :
    ExactPositionOrder (timeFixedOrder n) t (positionTimeEquiv J O) (treeChronologicalBefore D) := by
  intro p q
  have hv (x : Position t) : O.vertex (positionTimeEquiv J O x)=J.vertex x := by
    simp [positionTimeEquiv]
  have hb := O.before_iff (positionTimeEquiv J O p) (positionTimeEquiv J O q)
  rw [hv,hv] at hb
  simpa only [OrderBefore,timeFixedOrder,List.idxOf_finRange,TreeAutomaton.Logic.Formula.EvalAt,Fin.lt_def] using
    (eval_treeChronologicalBefore D G t J p q).trans hb

theorem canonical_time_path {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) : TimePath (canonicalDiagram output) (2*n) := by
  have hs : (Generalized.canonicalEvents 0 output).length=2*n := by
    simpa only [canonicalDiagram,eventDiagram,List.length_range] using canonical_domain_size hp
  simpa only [canonicalDiagram,hs] using eventDiagram_path (Generalized.canonicalEvents 0 output)

/-- Every physically accepted tree obtains an actual chronological bijection
and exact fixed syntax from its generated permutation. The supplied-order
premise of generic recognition is thereby discharged for physical models. -/
theorem physical_tree_has_chronology (D : FinitePortDecoder α) (t : BinaryTree α)
    (r s : Nat) (h : (sentence D (fullAcceptedSentence r s)).EvalAt t Fin.elim0) :
    ∃ n output, output.Perm (List.range n) ∧ Generalized.Run r s [] (List.range n) output [] ∧
      t.numNodes=2*n ∧ ∃ e : Position t ≃ Fin (2*n),
        ExactPositionOrder (timeFixedOrder (2*n)) t e (treeChronologicalBefore D) := by
  obtain ⟨n,output,hp,hg,⟨iso⟩,hs,_⟩ := decoded_physical_unique_generated D t r s h
  let J := decodedModel_sameNode D t
  let O := orderedDomainOfTimeIsomorphism iso (canonical_time_path hp)
  exact ⟨n,output,hp,hg,hs,positionTimeEquiv J O,treeChronologicalBefore_exact J O⟩

#print axioms treeChronologicalBefore_exact
#print axioms physical_tree_has_chronology
end StackSorting.SparseTreeCompiler
