import PortNormalFormSyntaxSemantics
import PortRelationalCompleteness

namespace StackSorting.FinitePort
open TreeAutomaton.Logic SparseTreeCompiler

variable {n colors relations W : Nat}
variable (T : RootedTree n) (G : Diagram n colors relations) (O : FixedOrder n)
variable (labels : Vertex n → Alphabet colors relations W)
variable (child : Bool → Vertex n → Vertex n → Prop)
variable (parent order : Formula (Alphabet colors relations W) 2)
variable (rel : Fin relations → Formula (Alphabet colors relations W) 2)

theorem orderedSlotsFormula_complete
    (hp : ExactParent T labels child parent) (hz : RootEmpty (labelCode labels))
    (ho : ∀ u v, order.EvalOn labels child (binaryVal u v) ↔
      O.vertices.idxOf u < O.vertices.idxOf v)
    (h : RelationalPortNormalForm T O G (labelCode labels)) :
    (orderedSlotsFormula parent order).EvalOn labels child Fin.elim0 := by
  classical
  rw [orderedSlotsFormula,eval_closeAll]
  intro xs
  rw [eval_allFinite]
  rintro ⟨i,j⟩
  split_ifs with hij
  · rw [FiniteState.eval_implies]
    rintro ⟨hP,hI,hJ⟩
    rw [slotPresent,eval_labelTest labels child _ 0 (xs 0) rfl] at hP
    rw [eval_atPair labels child _ 0 1 _ (xs 0) (xs 1) rfl rfl,
      eval_portRoute T labels child parent hp hz] at hI
    rw [eval_atPair labels child _ 0 2 _ (xs 0) (xs 2) rfl rfl,
      eval_portRoute T labels child parent hp hz] at hJ
    rw [eval_atPair labels child _ 1 2 _ (xs 1) (xs 2) rfl rfl,ho]
    exact h.ordered (xs 0) i.val j.val hij hP (xs 1) (xs 2) hI hJ
  · exact eval_truth labels child _

theorem bitsSlotsFormula_complete
    (hp : ExactParent T labels child parent) (hz : RootEmpty (labelCode labels))
    (hr : ∀ r u v, (rel r).EvalOn labels child (binaryVal u v) ↔ G.rel r u v=true)
    (h : RelationalPortNormalForm T O G (labelCode labels)) :
    (bitsSlotsFormula parent rel).EvalOn labels child Fin.elim0 := by
  classical
  rw [bitsSlotsFormula,eval_closeAll]
  intro xs
  have hv : (fun i => point (xs i))=binaryVal (xs 0) (xs 1) := by
    funext i
    fin_cases i <;> rfl
  rw [hv,eval_allFinite]
  rintro ⟨i,r,forward⟩
  rw [FiniteState.eval_implies]
  rintro ⟨hP,hR⟩
  rw [slotPresent,eval_labelTest labels child _ 0 (xs 0) rfl] at hP
  rw [eval_portRoute T labels child parent hp hz] at hR
  let e := (labelCode labels (xs 0)).ports[i.val]
  have he : (labelCode labels (xs 0)).ports[i.val]?=some e := List.getElem?_eq_getElem hP
  have hbit := h.bits (xs 0) i.val e he (xs 1) hR r forward
  rw [eval_iffFormula,slotBits,eval_labelTest labels child _ 0 (xs 0) rfl]
  have heval : (∃ e', (labels (xs 0)).toLabel.ports[i.val]?=some e' ∧
      e'.bit r forward=true) ↔ e.bit r forward=true := by
    change (∃ e', (labelCode labels (xs 0)).ports[i.val]?=some e' ∧ e'.bit r forward=true) ↔ _
    rw [he]
    simp
  rw [heval,hbit]
  cases forward with
  | false =>
    change (G.rel r (xs 1) (xs 0)=true) ↔
      (atPair (rel r) 1 0).EvalOn labels child (binaryVal (xs 0) (xs 1))
    rw [eval_atPair labels child _ 1 0 _ (xs 1) (xs 0) rfl rfl,hr]
  | true =>
    change (G.rel r (xs 0) (xs 1)=true) ↔
      (rel r).EvalOn labels child (binaryVal (xs 0) (xs 1))
    exact (hr r _ _).symm

/-- All actual encoder labels satisfy the literal finite normal-form sentence.
This is the converse of syntax soundness, with no assumed recognition theorem. -/
theorem normalSlotsFormula_complete
    (hp : ExactParent T labels child parent)
    (ho : ∀ u v, order.EvalOn labels child (binaryVal u v) ↔
      O.vertices.idxOf u < O.vertices.idxOf v)
    (hr : ∀ r u v, (rel r).EvalOn labels child (binaryVal u v) ↔ G.rel r u v=true)
    (he : labelCode labels = encode T O G) :
    (normalSlotsFormula parent order rel).EvalOn labels child Fin.elim0 := by
  have hn : PortNormalForm T O G (labelCode labels) := by
    rw [he]
    exact encode_normalForm T O G
  have h := hn.to_relational
  have hz : RootEmpty (labelCode labels) := hn.root_empty
  change (FiniteState.conjoin [rootEmptyFormula parent,validSlotsFormula parent,
    frontierSlotsFormula parent rel,orderedSlotsFormula parent order,
    bitsSlotsFormula parent rel]).EvalOn labels child Fin.elim0
  rw [FiniteState.eval_conjoin]
  intro f hf
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl
  · exact (eval_rootEmptyFormula T labels child parent hp).mpr hz
  · exact (eval_validSlotsFormula T labels child parent hp hz).mpr h.valid
  · exact (eval_frontierSlotsFormula T G labels child parent rel hp hz hr).mpr h.frontier
  · exact orderedSlotsFormula_complete T G O labels child parent order hp hz ho h
  · exact bitsSlotsFormula_complete T G O labels child parent rel hp hz hr h

/-- Exact two-way recognition of stored encoder labels by a uniform finite MSO
sentence. Primitive interpretations remain explicit for later binary decoding. -/
theorem normalSlotsFormula_correct
    (hp : ExactParent T labels child parent)
    (ho : ∀ u v, order.EvalOn labels child (binaryVal u v) ↔
      O.vertices.idxOf u < O.vertices.idxOf v)
    (hr : ∀ r u v, (rel r).EvalOn labels child (binaryVal u v) ↔ G.rel r u v=true)
    (hc : ∀ v, (labels v).toLabel.color=G.color v) :
    (normalSlotsFormula parent order rel).EvalOn labels child Fin.elim0 ↔
      labelCode labels = encode T O G :=
  ⟨normalSlotsFormula_sound T G labels child parent order rel O hp ho hr hc,
   normalSlotsFormula_complete T G O labels child parent order rel hp ho hr⟩

#print axioms normalSlotsFormula_complete
#print axioms normalSlotsFormula_correct
end StackSorting.FinitePort
