import FinitePortRoutes

namespace StackSorting.FinitePort
open TreeAutomaton.Logic SparseTreeCompiler
variable {colors relations W : Nat}

/-- Instantiate the accepted graph compiler with constructed finite port
routes. Colors and relation indices are explicit choices in the vocabulary. -/
noncomputable def constructedDecoder
    (parent : Formula (Alphabet colors relations W) 2)
    (insertColor removeColor : Fin colors) (successorRelation matchingRelation : Fin relations) :
    FinitePortDecoder (Alphabet colors relations W) := by
  classical
  exact {
    portCount := relations
    insertLabels := Finset.univ.filter (fun a => a.toLabel.color insertColor = true)
    removeLabels := Finset.univ.filter (fun a => a.toLabel.color removeColor = true)
    route := relationRoute parent
    successorPorts := {successorRelation}
    matchingPorts := {matchingRelation}
  }

theorem constructedDecoder_insert {P : Type}
    (parent : Formula (Alphabet colors relations W) 2)
    (insertColor removeColor : Fin colors) (s m : Fin relations)
    (label : P → Alphabet colors relations W) (child : Bool → P → P → Prop) (v : P) :
    ((constructedDecoder parent insertColor removeColor s m).codes.relations label child).insert v ↔
      (label v).toLabel.color insertColor = true := by
  classical
  rw [FinitePortDecoder.insert_iff]
  simp [constructedDecoder]

theorem constructedDecoder_remove {P : Type}
    (parent : Formula (Alphabet colors relations W) 2)
    (insertColor removeColor : Fin colors) (s m : Fin relations)
    (label : P → Alphabet colors relations W) (child : Bool → P → P → Prop) (v : P) :
    ((constructedDecoder parent insertColor removeColor s m).codes.relations label child).remove v ↔
      (label v).toLabel.color removeColor = true := by
  classical
  rw [FinitePortDecoder.remove_iff]
  simp [constructedDecoder]

theorem constructedDecoder_successor {n} (T : RootedTree n)
    (labels : Vertex n → Alphabet colors relations W)
    (child : Bool → Vertex n → Vertex n → Prop)
    (parent : Formula (Alphabet colors relations W) 2)
    (hparent : ExactParent T labels child parent)
    (hroot : RootEmpty (labelCode labels))
    (insertColor removeColor : Fin colors) (s m : Fin relations) (v u : Vertex n) :
    ((constructedDecoder parent insertColor removeColor s m).codes.relations labels child).successor v u ↔
      DecodedRel T (labelCode labels) s v u := by
  classical
  rw [FinitePortDecoder.successor_iff]
  change (∃ port : Fin relations, port ∈ ({s} : Finset _) ∧
    (relationRoute parent port).EvalOn labels child (binaryVal v u)) ↔ _
  simp only [Finset.mem_singleton,exists_eq_left]
  exact eval_relationRoute T labels child parent hparent hroot s v u

theorem constructedDecoder_matching {n} (T : RootedTree n)
    (labels : Vertex n → Alphabet colors relations W)
    (child : Bool → Vertex n → Vertex n → Prop)
    (parent : Formula (Alphabet colors relations W) 2)
    (hparent : ExactParent T labels child parent)
    (hroot : RootEmpty (labelCode labels))
    (insertColor removeColor : Fin colors) (s m : Fin relations) (v u : Vertex n) :
    ((constructedDecoder parent insertColor removeColor s m).codes.relations labels child).matching v u ↔
      DecodedRel T (labelCode labels) m v u := by
  classical
  rw [FinitePortDecoder.matching_iff]
  change (∃ port : Fin relations, port ∈ ({m} : Finset _) ∧
    (relationRoute parent port).EvalOn labels child (binaryVal v u)) ↔ _
  simp only [Finset.mem_singleton,exists_eq_left]
  exact eval_relationRoute T labels child parent hparent hroot m v u

/-- Encoded bounded-width diagrams supply the root guard automatically. The
only outstanding external premise is the explicit, independently proved
parent formula; no port route or recognizability result is assumed. -/
theorem eval_encoded_relationRoute {n} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations)
    (hloop : Loopless G) (helim : Eliminates T G) (hW : WidthAtMost T O G W)
    (child : Bool → Vertex n → Vertex n → Prop)
    (parent : Formula (Alphabet colors relations W) 2)
    (hparent : ExactParent T (alphabetCode (encode T O G) (encode_bounded T O G W hW)) child parent)
    (r : Fin relations) (v u : Vertex n) :
    (relationRoute parent r).EvalOn
      (alphabetCode (encode T O G) (encode_bounded T O G W hW)) child (binaryVal v u) ↔
      G.rel r v u = true := by
  let labels := alphabetCode (encode T O G) (encode_bounded T O G W hW)
  have hcode : labelCode labels = encode T O G := alphabetCode_recovers ..
  have hroot : RootEmpty (labelCode labels) := hcode.symm ▸ encode_rootEmpty T O G
  have hh := eval_relationRoute T labels child parent hparent hroot r v u
  rw [hcode] at hh
  exact hh.trans (decode_encode_relation T O G hloop helim r v u)

#print axioms constructedDecoder_successor
#print axioms constructedDecoder_matching
#print axioms eval_encoded_relationRoute
end StackSorting.FinitePort
