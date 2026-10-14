import MarginalActualAtoms

set_option backward.isDefEq.respectTransparency false
namespace StackSorting.GraphWidth.MarginalA2.Actual
open SparseEndpointMSO SparseEndpointMSO.IncidenceOwnership SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.FiniteCopy.Parametric FinitePort Nested
variable {A : Model} {n t W : Nat} {G : Graph n} {T : RootedTree t}
variable (D : Decomposition G T) (names : Fin n ≃ Vertex A)

@[simp] theorem eval_binary {r : Nat} (a : Syntax.InputAtom 2) (u v : Fin r)
    (env : Fin r → Base (A := A) (t := t)) (sets : Fin b → Base (A := A) (t := t) → Prop) :
    ActualEval (outerAtoms D names) (Syntax.binary a u v) env sets ↔
      outerAtoms D names a (Fin.cases (env u) (fun _ => env v)) := by
  simp only [Syntax.binary,ActualEval]
  have h : (fun i => env (Syntax.pair u v i))=Fin.cases (env u) (fun _ => env v) := by
    funext i; fin_cases i <;> rfl
  rw [h]

@[simp] private theorem cases_one {α : Type} {m : Nat} (x : α) (env : Fin (m+1) → α) :
    Fin.cases x env (1 : Fin (m+2))=env 0 := rfl

def OriginalIncidence (u e : Base (A := A) (t := t)) : Prop :=
  outerAtoms D names .incidence (Fin.cases u (fun _ => e))
def OriginalEdge (e : Base (A := A) (t := t)) : Prop :=
  outerAtoms D names .originalEdge (fun _ => e)

def OldEdgeOwner (e x : Base (A := A) (t := t)) : Prop :=
  OriginalEdge D names e ∧ ∃ u v, u≠v ∧ OriginalIncidence D names u e ∧
    OriginalIncidence D names v e ∧ Margin D names x u ∧ Margin D names x v

def OldOwner (z x : Base (A := A) (t := t)) : Prop :=
  Margin D names x z ∨ OldEdgeOwner D names z x

def OldLocalEdge (e : Base (A := A) (t := t)) : Prop := ∃ x, OldEdgeOwner D names e x

def OriginalAdj (u v : Base (A := A) (t := t)) : Prop :=
  u≠v ∧ ∃ e, OriginalEdge D names e ∧ OriginalIncidence D names u e ∧ OriginalIncidence D names v e

/-- Formula helper evaluation is over literal original incidence relations. -/
theorem eval_oldEdgeOwner (e x : Fin a) (env : Fin a → Base (A := A) (t := t))
    (sets : Fin b → Base (A := A) (t := t) → Prop) :
    ActualEval (outerAtoms D names) (Syntax.originalOwner e x) env sets ↔
      OldEdgeOwner D names (env e) (env x) := by
  simp only [Syntax.originalOwner,Syntax.unary,eval_binary,ActualEval,
    OldEdgeOwner,OriginalEdge,OriginalIncidence,Margin,Fin.cases_zero,Fin.cases_succ,cases_one]

theorem eval_oldOwner (z x : Fin a) (env : Fin a → Base (A := A) (t := t))
    (sets : Fin b → Base (A := A) (t := t) → Prop) :
    ActualEval (outerAtoms D names) (Syntax.oldOwner z x) env sets ↔
      OldOwner D names (env z) (env x) := by
  classical
  simp [Syntax.oldOwner,Syntax.disj,ActualEval,eval_oldEdgeOwner,OldOwner,
    eval_binary,Margin]
  tauto

theorem eval_oldLocalEdge (e : Fin a) (env : Fin a → Base (A := A) (t := t))
    (sets : Fin b → Base (A := A) (t := t) → Prop) :
    ActualEval (outerAtoms D names) (Syntax.oldLocalEdge e) env sets ↔
      OldLocalEdge D names (env e) := by
  simp [Syntax.oldLocalEdge,ActualEval,eval_oldEdgeOwner,OldLocalEdge]

theorem eval_originalAdj (u v : Fin a) (env : Fin a → Base (A := A) (t := t))
    (sets : Fin b → Base (A := A) (t := t) → Prop) :
    ActualEval (outerAtoms D names) (Syntax.originalAdj u v) env sets ↔
      OriginalAdj D names (env u) (env v) := by
  simp only [Syntax.originalAdj,ActualEval,Syntax.unary,eval_binary,
    OriginalAdj,OriginalEdge,OriginalIncidence,Fin.cases_zero,Fin.cases_succ]

/-- Direct semantics on the actual ambient carrier. Synthetic edge equality
is equality of actual unordered vertex pairs. Owner is an actual outer node.
Old crossing edges remain auxiliary; localEdge/owner restrict local carriers. -/
def outputAtoms : {r : Nat} → Syntax.OutputAtom r → (Fin r → Carrier.Actual (A := A) D) → Prop
  | _, .vertex, env => match env 0 with
    | .inl z => outerAtoms D names .vertex (fun _ => z) | .inr _ => False
  | _, .localEdge, env => match env 0 with
    | .inl z => OldLocalEdge D names z | .inr _ => True
  | _, .outerNode, env => match env 0 with
    | .inl z => outerAtoms D names .node (fun _ => z) | .inr _ => False
  | _, .incidence, env => match env 0,env 1 with
    | .inl u,.inl e => OldLocalEdge D names e ∧ OriginalIncidence D names u e
    | .inl u,.inr e => u=vertex names e.val.1 ∨ u=vertex names e.val.2
    | _,_ => False
  | _, .owner, env => match env 0,env 1 with
    | .inl z,.inl x => OldOwner D names z x
    | .inr e,.inl x => x=node (introductionNode D e.val.1)
    | _,_ => False
  | _, .margin, env => match env 0,env 1 with
    | .inl x,.inl u => Margin D names x u | _,_ => False
  | _, .adhesion, env => match env 0,env 1 with
    | .inl x,.inl u => Bag D names x u ∧ ¬Margin D names x u | _,_ => False
  | _, .outerParent, env => match env 0,env 1 with
    | .inl x,.inl y => Parent D names x y | _,_ => False
  | _, .originalAdj, env => match env 0,env 1 with
    | .inl u,.inl v => OriginalAdj D names u v | _,_ => False

variable (C : AdhesionColoring D W)

theorem chosen_parent (e : ExtraEdge D) (x : Base (A := A) (t := t)) :
    let q := chosenCandidate D C e
    Parent D names (node q.2.2) x ↔ x=node (introductionNode D e.val.1) := by
  dsimp only
  have h := chosenCandidate_spec D C e
  cases x with
  | inl x => simp [Parent,outerAtoms,node]
  | inr x =>
    change Parent D names (node (chosenCandidate D C e).2.2) (node x) ↔ _
    rw [parent_named]
    constructor
    · intro hx
      exact congrArg node (hx.2.symm.trans h.2.1)
    · intro hx
      exact ⟨h.1,h.2.1.trans (Sum.inr.inj hx).symm⟩

theorem chosen_left_sum (e : ExtraEdge D) (z : Base (A := A) (t := t)) :
    ColoredEndpoint D names C (chosenCandidate D C e).1 (Sum.inr (chosenCandidate D C e).2.2) z ↔
      z=vertex names e.val.1 := chosen_left D names C e z

theorem chosen_right_sum (e : ExtraEdge D) (z : Base (A := A) (t := t)) :
    ColoredEndpoint D names C (chosenCandidate D C e).2.1 (Sum.inr (chosenCandidate D C e).2.2) z ↔
      z=vertex names e.val.2 := chosen_right D names C e z

/-- Every output atom is proved pointwise from the concrete original input
and explicit edge selection. No whole-output recognition premise occurs. -/
theorem encoded_atoms {r : Nat} (a : Syntax.OutputAtom r)
    (env : Fin r → Carrier.Actual (A := A) D) :
    stepAtoms (Syntax.interpretation W) (outerAtoms D names) (Carrier.sets D names C) a
      (fun i => Carrier.encode D names C (outerAtoms D names) (env i)) ↔ outputAtoms D names a env := by
  classical
  cases a with
  | vertex => cases h : env 0 <;>
      simp [stepAtoms,Syntax.interpretation,Syntax.atom,Carrier.encode,outputAtoms,h,Syntax.unary,ActualEval]
  | localEdge => cases h : env 0 <;>
      simp [stepAtoms,Syntax.interpretation,Syntax.atom,Carrier.encode,outputAtoms,h,ActualEval,eval_oldLocalEdge]
  | outerNode => cases h : env 0 <;>
      simp [stepAtoms,Syntax.interpretation,Syntax.atom,Carrier.encode,outputAtoms,h,Syntax.unary,ActualEval]
  | incidence =>
      cases h : env 0 <;> cases j : env 1 <;>
        simp [stepAtoms,Syntax.interpretation,Syntax.atom,Carrier.encode,outputAtoms,h,j,
          Syntax.disj,ActualEval,eval_oldLocalEdge,eval_coloredEndpoint,chosen_left_sum,chosen_right_sum,
          eval_binary,OriginalIncidence] ; tauto
  | owner =>
      cases h : env 0 with
      | inl z => cases j : env 1 <;>
          simp [stepAtoms,Syntax.interpretation,Syntax.atom,Carrier.encode,outputAtoms,h,j,
            ActualEval,eval_oldOwner]
      | inr e => cases j : env 1 with
        | inl x =>
          simpa [stepAtoms,Syntax.interpretation,Syntax.atom,Carrier.encode,outputAtoms,h,j,
            ActualEval,eval_binary,Parent,node] using chosen_parent D names C e x
        | inr f => simp [stepAtoms,Syntax.interpretation,Syntax.atom,Carrier.encode,outputAtoms,h,j,ActualEval]
  | margin => cases h : env 0 <;> cases j : env 1 <;>
      simp [stepAtoms,Syntax.interpretation,Syntax.atom,Carrier.encode,outputAtoms,h,j,
        ActualEval,eval_binary,Margin]
  | adhesion => cases h : env 0 <;> cases j : env 1 <;>
      simp [stepAtoms,Syntax.interpretation,Syntax.atom,Carrier.encode,outputAtoms,h,j,
        ActualEval,Syntax.adhesion,eval_binary,Bag,Margin]
  | outerParent => cases h : env 0 <;> cases j : env 1 <;>
      simp [stepAtoms,Syntax.interpretation,Syntax.atom,Carrier.encode,outputAtoms,h,j,
        ActualEval,eval_binary,Parent]
  | originalAdj => cases h : env 0 <;> cases j : env 1 <;>
      simp [stepAtoms,Syntax.interpretation,Syntax.atom,Carrier.encode,outputAtoms,h,j,
        ActualEval,eval_originalAdj]

/-- Conditional only on the already proved actual outer input realization;
all marginal-domain, equality, and atomic obligations have been discharged. -/
noncomputable def realization {c d : Nat} {J : Parametric.Interpretation Syntax.InputAtom c d}
    {params : Fin d → Nat → Prop}
    (R : Parametric.Realization J A params (Base (A := A) (t := t)) (outerAtoms D names)) :
    Parametric.Realization (Parametric.compose J (Syntax.interpretation W)) A
      (Parametric.flattenedSets params (fun i => R.liftSet (Carrier.sets D names C i)))
      (Carrier.Actual (A := A) D) (outputAtoms D names) := by
  apply MultiMargin.Retained.transportRealization (R.compose (Syntax.interpretation W) (Carrier.sets D names C))
    (Carrier.codeEquiv D names C (outerAtoms D names)).symm (outputAtoms D names)
  intro r a env
  have h := encoded_atoms D names C a
    (fun i => (Carrier.codeEquiv D names C (outerAtoms D names)).symm (env i))
  have he : (fun i => Carrier.encode D names C (outerAtoms D names)
      ((Carrier.codeEquiv D names C (outerAtoms D names)).symm (env i)))=env := by
    funext i
    exact (Carrier.codeEquiv D names C (outerAtoms D names)).apply_symm_apply (env i)
  rw [he] at h
  exact h

#print axioms encoded_atoms
#print axioms realization
end StackSorting.GraphWidth.MarginalA2.Actual
