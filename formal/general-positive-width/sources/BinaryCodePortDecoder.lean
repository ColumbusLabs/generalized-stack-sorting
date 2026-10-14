import BinaryCodeFormulaTransport
import FinitePortDecoderConstruction

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic SparseTreeCompiler GraphWidth

/-- The actual finite-labelled binary code has exact original directed
relations under one fixed finite MSO formula. No parent or port semantics is
assumed: the proper-parent formula is constructed from left/right children. -/
theorem binaryCode_relationRoute {n colors relations W} {G : Diagram n colors relations}
    (E : ExactRootEmptyCodec G W) (O : FixedOrder n) (hn : 0 < n)
    (r : Fin relations) (p q : Position (binaryCode E.toExactNumberedCodec O hn)) :
    (relationRoute parentRoute r).EvalOn Position.label (fun d u v => Child d u v)
      (binaryVal p q) ↔
      G.rel r (binaryCodeVertexEquiv E.toExactNumberedCodec O hn p)
        (binaryCodeVertexEquiv E.toExactNumberedCodec O hn q) = true := by
  let C := E.toExactNumberedCodec
  rw [eval_binaryCode_formula C O hn]
  have hp : ExactParent C.tree (alphabetCode C.code C.bounded) (codeChild C O hn)
      parentRoute := binaryCode_exact_parent C O hn
  have hC : labelCode (alphabetCode C.code C.bounded) = C.code := alphabetCode_recovers ..
  have hr : RootEmpty (labelCode (alphabetCode C.code C.bounded)) := by
    rw [hC]
    exact E.root_ports
  have h := eval_relationRoute C.tree (alphabetCode C.code C.bounded) (codeChild C O hn)
    parentRoute hp hr r (binaryCodeIndexEquiv C O hn p) (binaryCodeIndexEquiv C O hn q)
  rw [hC] at h
  exact h.trans (binaryCode_original_relation C O hn r p q)

/-- The single finite-port decoder is independent of graph size and temporary
numbering. This result retains the supplied root-empty codec as its input. -/
theorem binaryCode_decoder_successor {n colors relations W} {G : Diagram n colors relations}
    (E : ExactRootEmptyCodec G W) (O : FixedOrder n) (hn : 0 < n)
    (i j : Fin colors) (s m : Fin relations)
    (p q : Position (binaryCode E.toExactNumberedCodec O hn)) :
    ((constructedDecoder parentRoute i j s m).relations
      (binaryCode E.toExactNumberedCodec O hn)).successor p q ↔
      G.rel s (binaryCodeVertexEquiv E.toExactNumberedCodec O hn p)
        (binaryCodeVertexEquiv E.toExactNumberedCodec O hn q) = true := by
  classical
  rw [FinitePortDecoder.relations,FinitePortDecoder.successor_iff]
  change (∃ port : Fin relations, port ∈ ({s} : Finset _) ∧
    (relationRoute parentRoute port).EvalOn Position.label (fun d u v => Child d u v)
      (binaryVal p q)) ↔ _
  simp only [Finset.mem_singleton,exists_eq_left]
  exact binaryCode_relationRoute E O hn s p q

theorem binaryCode_decoder_matching {n colors relations W} {G : Diagram n colors relations}
    (E : ExactRootEmptyCodec G W) (O : FixedOrder n) (hn : 0 < n)
    (i j : Fin colors) (s m : Fin relations)
    (p q : Position (binaryCode E.toExactNumberedCodec O hn)) :
    ((constructedDecoder parentRoute i j s m).relations
      (binaryCode E.toExactNumberedCodec O hn)).matching p q ↔
      G.rel m (binaryCodeVertexEquiv E.toExactNumberedCodec O hn p)
        (binaryCodeVertexEquiv E.toExactNumberedCodec O hn q) = true := by
  classical
  rw [FinitePortDecoder.relations,FinitePortDecoder.matching_iff]
  change (∃ port : Fin relations, port ∈ ({m} : Finset _) ∧
    (relationRoute parentRoute port).EvalOn Position.label (fun d u v => Child d u v)
      (binaryVal p q)) ↔ _
  simp only [Finset.mem_singleton,exists_eq_left]
  exact binaryCode_relationRoute E O hn m p q

theorem binaryCode_decoder_insert {n colors relations W} {G : Diagram n colors relations}
    (E : ExactRootEmptyCodec G W) (O : FixedOrder n) (hn : 0 < n)
    (i j : Fin colors) (s m : Fin relations)
    (p : Position (binaryCode E.toExactNumberedCodec O hn)) :
    ((constructedDecoder parentRoute i j s m).relations
      (binaryCode E.toExactNumberedCodec O hn)).insert p ↔
      G.color (binaryCodeVertexEquiv E.toExactNumberedCodec O hn p) i = true := by
  rw [FinitePortDecoder.relations,constructedDecoder_insert,binaryCode_original_color]

theorem binaryCode_decoder_remove {n colors relations W} {G : Diagram n colors relations}
    (E : ExactRootEmptyCodec G W) (O : FixedOrder n) (hn : 0 < n)
    (i j : Fin colors) (s m : Fin relations)
    (p : Position (binaryCode E.toExactNumberedCodec O hn)) :
    ((constructedDecoder parentRoute i j s m).relations
      (binaryCode E.toExactNumberedCodec O hn)).remove p ↔
      G.color (binaryCodeVertexEquiv E.toExactNumberedCodec O hn p) j = true := by
  rw [FinitePortDecoder.relations,constructedDecoder_remove,binaryCode_original_color]

#print axioms binaryCode_relationRoute
#print axioms binaryCode_decoder_successor
#print axioms binaryCode_decoder_matching
end StackSorting.FinitePort.ChildSibling
