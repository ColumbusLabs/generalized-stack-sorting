import FiniteStateMSO
import PortConfigurationWalk
import FinitePortAlphabet
import FinitePortGraphInterpretation

namespace StackSorting.FinitePort
open TreeAutomaton.Logic SparseTreeCompiler
variable {P : Type} {colors relations W : Nat}

/-- A literal disjunction of tests for the finitely many admissible labels. -/
noncomputable def labelTest {α : Type} [Fintype α] {n} (i : Fin n) (p : α → Prop) :
    Formula α n := by
  classical
  exact disjoin ((Finset.univ.filter p).toList.map (fun a => .atom (.label i a)))

theorem eval_disjoin_map {α : Type} {n} {I : Type} (label : P → α)
    (child : Bool → P → P → Prop) (v : Fin n → P → Bool)
    (is : List I) (f : I → Formula α n) :
    (disjoin (is.map f)).EvalOn label child v ↔
      ∃ i ∈ is, (f i).EvalOn label child v := by
  rw [eval_disjoin]
  simp

theorem eval_labelTest {α : Type} [Fintype α] {n} (label : P → α)
    (child : Bool → P → P → Prop) (v : Fin n → P → Bool) (i : Fin n)
    (x : P) (hx : v i = point x) (p : α → Prop) :
    (labelTest i p).EvalOn label child v ↔ p (label x) := by
  classical
  simp [labelTest,eval_disjoin,Formula.EvalOn,Atom.EvalOn,hx,point]

/-- This predicate sees stored indices, including entries whose every bit is
zero. It does not examine any relation bit. -/
def NextLabel (i j : Fin (W+1)) (a : Alphabet colors relations W) : Prop :=
  i.val ≠ 0 ∧ ∃ e, a.toLabel.ports[i.val-1]? = some e ∧ e.parentPort = j.val

/-- The supplied parent formula is applied in parent,child order. The route
itself moves child to parent. Only finite label tests choose the next state. -/
noncomputable def stepFormula (parent : Formula (Alphabet colors relations W) 2)
    (i j : Fin (W+1)) : Formula (Alphabet colors relations W) 2 :=
  .conj (parent.rename (Fin.cons 1 (fun _ => 0))) (labelTest 0 (NextLabel i j))

noncomputable def portRoute (parent : Formula (Alphabet colors relations W) 2)
    (i : Fin (W+1)) : Formula (Alphabet colors relations W) 2 :=
  FiniteState.route (stepFormula parent) i 0

def labelCode {n} (labels : Vertex n → Alphabet colors relations W) :
    Code n colors relations := fun v => (labels v).toLabel

theorem labelCode_bounded {n} (labels : Vertex n → Alphabet colors relations W) :
    BoundedCode (labelCode labels) W := fun v => (labels v).toLabel_bounded

/-- The only semantic input to the construction is the separately established
parent formula, with literal orientation and proper-root guard. -/
def ExactParent {n} (T : RootedTree n)
    (labels : Vertex n → Alphabet colors relations W)
    (child : Bool → Vertex n → Vertex n → Prop)
    (parent : Formula (Alphabet colors relations W) 2) : Prop :=
  ∀ p v, parent.EvalOn labels child (binaryVal p v) ↔
    v.val ≠ 0 ∧ p = T.parent v

theorem eval_stepFormula {n} (T : RootedTree n)
    (labels : Vertex n → Alphabet colors relations W)
    (child : Bool → Vertex n → Vertex n → Prop)
    (parent : Formula (Alphabet colors relations W) 2)
    (hparent : ExactParent T labels child parent)
    (i j : Fin (W+1)) (v u : Vertex n) :
    (stepFormula parent i j).EvalOn labels child (binaryVal v u) ↔
      PortStep T (labelCode labels) (v,i) (u,j) := by
  classical
  have hs : (fun x => binaryVal v u
      ((Fin.cons 1 (fun _ : Fin 1 => 0) : Fin 2 → Fin 2) x)) = binaryVal u v := by
    funext x
    fin_cases x <;> rfl
  rw [stepFormula,Formula.EvalOn,Formula.evalOn_rename,hs,hparent]
  rw [eval_labelTest labels child (binaryVal v u) 0 v rfl]
  simp only [NextLabel,PortStep,labelCode]
  tauto

theorem eval_portRoute {n} (T : RootedTree n)
    (labels : Vertex n → Alphabet colors relations W)
    (child : Bool → Vertex n → Vertex n → Prop)
    (parent : Formula (Alphabet colors relations W) 2)
    (hparent : ExactParent T labels child parent)
    (hroot : RootEmpty (labelCode labels)) (i : Fin (W+1)) (v u : Vertex n) :
    (portRoute parent i).EvalOn labels child (binaryVal v u) ↔
      readPort T (labelCode labels) n v i.val = some u := by
  rw [portRoute,FiniteState.eval_route]
  have hs : (fun a b : Configuration n W =>
      (stepFormula parent a.2 b.2).EvalOn labels child (binaryVal a.1 b.1)) =
      PortStep T (labelCode labels) := by
    funext a b
    exact propext (eval_stepFormula T labels child parent hparent a.2 b.2 a.1 b.1)
  rw [hs]
  exact portWalk_iff_readPort T (labelCode labels) (labelCode_bounded labels) hroot v u i

def BitLabel (r : Fin relations) (forward : Bool) (i : Fin (W+1))
    (a : Alphabet colors relations W) : Prop :=
  i.val ≠ 0 ∧ ∃ e, a.toLabel.ports[i.val-1]? = some e ∧ e.bit r forward = true

noncomputable def edgeRoute (parent : Formula (Alphabet colors relations W) 2)
    (r : Fin relations) (forward : Bool) : Formula (Alphabet colors relations W) 2 :=
  disjoin ((Finset.univ : Finset (Fin (W+1))).toList.map
    (fun i => .conj (labelTest 0 (BitLabel r forward i)) (portRoute parent i)))

theorem eval_edgeRoute {n} (T : RootedTree n)
    (labels : Vertex n → Alphabet colors relations W)
    (child : Bool → Vertex n → Vertex n → Prop)
    (parent : Formula (Alphabet colors relations W) 2)
    (hparent : ExactParent T labels child parent)
    (hroot : RootEmpty (labelCode labels))
    (r : Fin relations) (forward : Bool) (v u : Vertex n) :
    (edgeRoute parent r forward).EvalOn labels child (binaryVal v u) ↔
      EdgeAt T (labelCode labels) v u r forward := by
  classical
  simp only [edgeRoute,eval_disjoin_map,Finset.mem_toList,
    Finset.mem_univ,true_and,Formula.EvalOn]
  simp only [eval_labelTest labels child (binaryVal v u) 0 v rfl,
    eval_portRoute T labels child parent hparent hroot]
  constructor
  · rintro ⟨i,⟨hi,e,he,hb⟩,hr⟩
    refine ⟨i.val-1,e,he,?_,hb⟩
    have hh : i.val-1+1 = i.val := by omega
    rwa [hh]
  · rintro ⟨i,e,he,hr,hb⟩
    have hlen := (labelCode_bounded labels v).1
    obtain ⟨hi,_⟩ := List.getElem?_eq_some_iff.mp he
    let j : Fin (W+1) := ⟨i+1,by omega⟩
    refine ⟨j,⟨by simp [j],e,?_,hb⟩,hr⟩
    simpa [j,labelCode] using he

noncomputable def relationRoute (parent : Formula (Alphabet colors relations W) 2)
    (r : Fin relations) : Formula (Alphabet colors relations W) 2 :=
  disjoin [edgeRoute parent r true,
    (edgeRoute parent r false).rename (Fin.cons 1 (fun _ => 0))]

theorem eval_relationRoute {n} (T : RootedTree n)
    (labels : Vertex n → Alphabet colors relations W)
    (child : Bool → Vertex n → Vertex n → Prop)
    (parent : Formula (Alphabet colors relations W) 2)
    (hparent : ExactParent T labels child parent)
    (hroot : RootEmpty (labelCode labels))
    (r : Fin relations) (v u : Vertex n) :
    (relationRoute parent r).EvalOn labels child (binaryVal v u) ↔
      DecodedRel T (labelCode labels) r v u := by
  have hs : (fun x => binaryVal v u
      ((Fin.cons 1 (fun _ : Fin 1 => 0) : Fin 2 → Fin 2) x)) = binaryVal u v := by
    funext x
    fin_cases x <;> rfl
  simp only [relationRoute,eval_disjoin,List.mem_cons,
    exists_eq_or_imp,Formula.evalOn_rename,hs]
  rw [eval_edgeRoute T labels child parent hparent hroot,
    eval_edgeRoute T labels child parent hparent hroot]
  simp [DecodedRel]

#print axioms eval_portRoute
#print axioms eval_edgeRoute
#print axioms eval_relationRoute
end StackSorting.FinitePort
