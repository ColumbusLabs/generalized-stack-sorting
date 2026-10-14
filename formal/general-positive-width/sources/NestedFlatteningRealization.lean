import NestedFlatteningExactness
import ParameterizedRealizationTransport

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.GraphWidth.Nested.CarrierSemantics
open FinitePort
open StackSorting.SparseEndpointMSO StackSorting.SparseEndpointMSO.FiniteCopy
open StackSorting.SparseEndpointMSO.FiniteCopy.Parametric
variable {n t : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}

/-- The actual flattened structure retains original vertices and exactly the
constructed local bag nodes. Outer nodes are removed by the literal domain. -/
abbrev FlatCarrier (N : NestedInput D) := Fin n ⊕ N.substitution.Node

def flatEmbed (N : NestedInput D) : FlatCarrier N → Carrier N
  | .inl v => vertex N v
  | .inr a => localNode N a

abbrev FlatStep (N : NestedInput D) :=
  StepElement Syntax.interpretation (Syntax.atoms (relations N)) Fin.elim0

def flatStep (N : NestedInput D) (q : FlatCarrier N) : FlatStep N :=
  ⟨(0,flatEmbed N q),by
    cases q <;> simp [Syntax.interpretation,Syntax.disj,Syntax.unary,
      ActualEval,Syntax.atoms,relations,flatEmbed,vertex,localNode]⟩

def decodeFlatStep (N : NestedInput D) (q : FlatStep N) : FlatCarrier N :=
  match h : q.val.2 with
  | .inl v => .inl v
  | .inr (.inr a) => .inr a
  | .inr (.inl _) => False.elim (by
      have hd := q.property
      simp [Syntax.interpretation,Syntax.disj,Syntax.unary,ActualEval,
        Syntax.atoms,relations,h] at hd)

@[simp] theorem decode_flatStep (N : NestedInput D) (q : FlatCarrier N) :
    decodeFlatStep N (flatStep N q)=q := by
  cases q <;> rfl

@[simp] theorem flatStep_decode (N : NestedInput D) (q : FlatStep N) :
    flatStep N (decodeFlatStep N q)=q := by
  rcases q with ⟨⟨tag,v | (x | a)⟩,hd⟩
  · apply Subtype.ext
    exact Prod.ext (Subsingleton.elim _ _) rfl
  · simp [Syntax.interpretation,Syntax.disj,Syntax.unary,ActualEval,
      Syntax.atoms,relations] at hd
  · apply Subtype.ext
    exact Prod.ext (Subsingleton.elim _ _) rfl

/-- Actual domain equivalence. In particular, there are no extra outer-node
codes and no duplicated bag nodes hidden in the one-copy stage. -/
def flatStepEquiv (N : NestedInput D) : FlatStep N ≃ FlatCarrier N where
  toFun := decodeFlatStep N
  invFun := flatStep N
  left_inv := flatStep_decode N
  right_inv := decode_flatStep N

def outputAtoms (N : NestedInput D) : {r : Nat} → Syntax.OutputAtom r →
    (Fin r → FlatCarrier N) → Prop
  | _,.original,env => match env 0 with | .inl _ => True | .inr _ => False
  | _,.node,env => match env 0 with | .inr _ => True | .inl _ => False
  | _,.parent,env => match env 0,env 1 with
      | .inr a,.inr b => a≠N.substitution.root ∧ N.substitution.parent a=b
      | _,_ => False
  | _,.bag,env => match env 0,env 1 with
      | .inr a,.inl v => v∈N.bagOn a
      | _,_ => False
  | _,.originalEdge,env => match env 0,env 1 with
      | .inl u,.inl v => G.Adj u v
      | _,_ => False

/-- Every output atom is the concrete parent/bag/edge relation, not an atom
defined by evaluating its own defining formula. -/
theorem stepAtoms_flatStep (N : NestedInput D) {r : Nat} (A : Syntax.OutputAtom r)
    (env : Fin r → FlatCarrier N) :
    stepAtoms Syntax.interpretation (Syntax.atoms (relations N)) Fin.elim0 A
      (fun i => flatStep N (env i)) ↔ outputAtoms N A env := by
  cases A with
  | original =>
    cases h : env 0 <;>
      simp [stepAtoms,Syntax.interpretation,Syntax.unary,ActualEval,Syntax.atoms,
        flatStep,flatEmbed,vertex,localNode,relations,outputAtoms,h]
  | node =>
    cases h : env 0 <;>
      simp [stepAtoms,Syntax.interpretation,Syntax.unary,ActualEval,Syntax.atoms,
        flatStep,flatEmbed,vertex,localNode,relations,outputAtoms,h]
  | parent =>
    change ActualEval (Syntax.atoms (relations N)) (Syntax.flattenedParentAt 0 1)
      (fun i => flatEmbed N (env i)) Fin.elim0 ↔ _
    rw [Syntax.eval_flattenedParentAt]
    cases h0 : env 0 with
    | inl v =>
      cases h1 : env 1 <;>
        simp [outputAtoms,h0,h1,flatEmbed,vertex,localNode,relations,Syntax.CrossParent]
    | inr a =>
      cases h1 : env 1 with
      | inl v =>
        simp [outputAtoms,h0,h1,flatEmbed,vertex,localNode,relations,Syntax.CrossParent]
      | inr b =>
        simpa only [outputAtoms,h0,h1,flatEmbed] using flattenedParent_exact N a b
  | bag =>
    change ActualEval (Syntax.atoms (relations N)) (Syntax.flattenedBagAt 0 1)
      (fun i => flatEmbed N (env i)) Fin.elim0 ↔ _
    rw [Syntax.eval_flattenedBagAt]
    cases h0 : env 0 with
    | inl v =>
      cases h1 : env 1 <;>
        simp [outputAtoms,h0,h1,flatEmbed,vertex,localNode,relations]
    | inr a =>
      cases h1 : env 1 with
      | inl v =>
        simpa only [outputAtoms,h0,h1,flatEmbed] using flattenedBag_exact N a v
      | inr b =>
        simp [outputAtoms,h0,h1,flatEmbed,localNode,relations]
  | originalEdge =>
    cases h0 : env 0 <;> cases h1 : env 1 <;>
      simp [stepAtoms,Syntax.interpretation,Syntax.binary,Syntax.pair,ActualEval,Syntax.atoms,
        flatStep,flatEmbed,vertex,localNode,relations,outputAtoms,h0,h1]

theorem stepAtoms_exact (N : NestedInput D) {r : Nat} (A : Syntax.OutputAtom r)
    (env : Fin r → FlatStep N) :
    stepAtoms Syntax.interpretation (Syntax.atoms (relations N)) Fin.elim0 A env ↔
      outputAtoms N A (fun i => flatStepEquiv N (env i)) := by
  have he : (fun i => flatStep N (decodeFlatStep N (env i))) = env :=
    funext (fun i => flatStep_decode N (env i))
  have h := stepAtoms_flatStep N A (fun i => decodeFlatStep N (env i))
  rw [he] at h
  exact h

/-- Genuine finite-copy flattening of an actual nested representation.
The earlier pointwise representation is composed with the explicit one-copy,
zero-new-parameter stage and transported through its proved domain bijection. -/
def realizeFlattened (N : NestedInput D) {c d : Nat}
    {J : Interpretation Syntax.InputAtom c d} {M : Model} {params : Fin d → Nat → Prop}
    (R : Realization J M params (Carrier N) (Syntax.atoms (relations N))) :
    Realization (compose J Syntax.interpretation) M
      (flattenedSets params (fun i => R.liftSet (Fin.elim0 i)))
      (FlatCarrier N) (outputAtoms N) :=
  (R.compose Syntax.interpretation Fin.elim0).transport (flatStepEquiv N)
    (outputAtoms N) (stepAtoms_exact N)

#print axioms flatStepEquiv
#print axioms stepAtoms_exact
#print axioms realizeFlattened
end StackSorting.GraphWidth.Nested.CarrierSemantics
