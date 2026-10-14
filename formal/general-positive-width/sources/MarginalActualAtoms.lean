import MarginalCarrierRealization
import MultiMarginCompletionAdapter

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.GraphWidth.MarginalA2
open SparseEndpointMSO SparseEndpointMSO.IncidenceOwnership SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.FiniteCopy.Parametric FinitePort Nested CapturedLinkExtraction
namespace Actual
variable {A : Model} {n t W : Nat} {G : Graph n} {T : RootedTree t}
variable (D : Decomposition G T) (names : Fin n ≃ Vertex A)

abbrev Base := Carrier.Base A t

def vertex (u : Fin n) : Base (A := A) (t := t) := .inl (.inl (names u))
def node (x : Fin t) : Base (A := A) (t := t) := .inr x

@[simp] theorem vertex_inj {u v : Fin n} :
    vertex (t := t) names u=vertex names v ↔ u=v := by
  exact ⟨fun h => names.injective (Sum.inl.inj (Sum.inl.inj h)),congrArg (vertex names)⟩

@[simp] theorem node_inj {x y : Fin t} :
    node (A := A) x=node y ↔ x=y := ⟨Sum.inr.inj,congrArg node⟩

/-- Explicit original incidence plus actual original outer decomposition.
There is no marginal adjacency, local parent, or local bag input atom. -/
def outerAtoms : {r : Nat} → Syntax.InputAtom r → (Fin r → Base (A := A) (t := t)) → Prop
  | _, .vertex, env => match env 0 with
    | .inl a => IsVertex a | .inr _ => False
  | _, .originalEdge, env => match env 0 with
    | .inl a => IsEdge a | .inr _ => False
  | _, .node, env => match env 0 with
    | .inr _ => True | .inl _ => False
  | _, .incidence, env => match env 0,env 1 with
    | .inl a,.inl e => IsEdge e ∧ ElementIncident a e | _,_ => False
  | _, .margin, env => match env 0,env 1 with
    | .inr x,.inl a => ∃ v, a=namedVertex names v ∧ introductionNode D v=x
    | _,_ => False
  | _, .component, env => match env 0,env 1 with
    | .inr x,.inl a => ∃ v, a=namedVertex names v ∧ IntroductionComponent D x v
    | _,_ => False
  | _, .parent, env => match env 0,env 1 with
    | .inr x,.inr y => x.val≠0 ∧ T.parent x=y | _,_ => False
  | _, .bag, env => match env 0,env 1 with
    | .inr x,.inl a => ∃ v, a=namedVertex names v ∧ v∈D.bag x
    | _,_ => False

/-- The concrete input semantics agrees pointwise with the actual C.2 output.
This is an eight-atom equality, not a recognizer for an unspecified structure. -/
theorem outerAtoms_c2 (hA : Laws A)
    (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
    {r : Nat} (a : Syntax.InputAtom r) (env : Fin r → Base (A := A) (t := t)) :
    outerAtoms D names a env ↔ (MultiMargin.ActualC2.retained D names hA hG).outputAtoms a env := by
  cases a with
  | vertex => cases h : env 0 <;> simp [outerAtoms,MultiMargin.Retained.outputAtoms,MultiMargin.ActualC2.retained,MultiMargin.ActualC2.completed,MultiMargin.ActualC2.relations,CapturedLinkExtraction.MultiMargin.CompletionIncidence.vertex,h]
  | originalEdge => cases h : env 0 <;> simp [outerAtoms,MultiMargin.Retained.outputAtoms,MultiMargin.ActualC2.retained,MultiMargin.ActualC2.completed,MultiMargin.ActualC2.relations,CapturedLinkExtraction.MultiMargin.CompletionIncidence.originalEdge,h]
  | node => cases h : env 0 <;> simp [outerAtoms,MultiMargin.Retained.outputAtoms,h]
  | incidence => cases h : env 0 <;> cases j : env 1 <;> simp [outerAtoms,MultiMargin.Retained.outputAtoms,MultiMargin.ActualC2.retained,MultiMargin.ActualC2.completed,MultiMargin.ActualC2.relations,CapturedLinkExtraction.MultiMargin.CompletionIncidence.originalEdge,CapturedLinkExtraction.MultiMargin.CompletionIncidence.incident,h,j]
  | margin => cases h : env 0 <;> cases j : env 1 <;>
      simp [outerAtoms,MultiMargin.Retained.outputAtoms,MultiMargin.ActualC2.retained,
        MultiMargin.ActualC2.completed,MultiMargin.Margin,
        CapturedLinkExtraction.MultiMargin.CompletionIncidence.named,h,j]
  | component => cases h : env 0 <;> cases j : env 1 <;>
      simp [outerAtoms,MultiMargin.Retained.outputAtoms,MultiMargin.ActualC2.retained,
        MultiMargin.ActualC2.completed,CapturedLinkExtraction.MultiMargin.CompletionIncidence.named,h,j]
  | parent => cases h : env 0 <;> cases j : env 1 <;> simp [outerAtoms,MultiMargin.Retained.outputAtoms,h,j]
  | bag => cases h : env 0 <;> cases j : env 1 <;>
      simp [outerAtoms,MultiMargin.Retained.outputAtoms,MultiMargin.ActualC2.retained,
        MultiMargin.ActualC2.completed,CapturedLinkExtraction.MultiMargin.CompletionIncidence.named,h,j]

def Margin (x u : Base (A := A) (t := t)) : Prop := outerAtoms D names .margin (Fin.cases x (fun _ => u))
def Bag (x u : Base (A := A) (t := t)) : Prop := outerAtoms D names .bag (Fin.cases x (fun _ => u))
def Parent (x y : Base (A := A) (t := t)) : Prop := outerAtoms D names .parent (Fin.cases x (fun _ => y))

def Interface (y u : Base (A := A) (t := t)) : Prop :=
  Bag D names y u ∧ ¬Margin D names y u ∧ ∃ x, Parent D names y x ∧ Margin D names x u

def ColoredEndpoint (C : AdhesionColoring D W) (i : Fin W) (y u : Base (A := A) (t := t)) : Prop :=
  Interface D names y u ∧ Carrier.parameter D names C (.inl i) u

theorem eval_interface (y u : Fin a) (env : Fin a → Base (A := A) (t := t))
    (sets : Fin b → Base (A := A) (t := t) → Prop) :
    ActualEval (outerAtoms D names) (Syntax.interfaceAt y u) env sets ↔
      Interface D names (env y) (env u) := by
  simp only [Syntax.interfaceAt,Syntax.adhesion,Syntax.binary,ActualEval,Interface,Margin,Bag,Parent]
  simp only [Syntax.pair]
  tauto

theorem eval_coloredEndpoint (C : AdhesionColoring D W) (i : Fin W)
    (y u : Fin a) (env : Fin a → Base (A := A) (t := t)) :
    ActualEval (outerAtoms D names) (Syntax.coloredEndpoint (Syntax.fixed W) i y u)
      env (Carrier.sets D names C) ↔ ColoredEndpoint D names C i (env y) (env u) := by
  simp only [Syntax.coloredEndpoint,ActualEval,eval_interface,Carrier.sets_color,ColoredEndpoint]

@[simp] theorem margin_named (x : Fin t) (u : Fin n) :
    Margin D names (node x) (vertex names u) ↔ introductionNode D u=x := by
  change (∃ v, namedVertex names u=namedVertex names v ∧ introductionNode D v=x) ↔ _
  constructor
  · rintro ⟨v,h,hi⟩
    have hv := namedVertex_injective names h
    subst v
    exact hi
  · intro h; exact ⟨u,rfl,h⟩

@[simp] theorem bag_named (x : Fin t) (u : Fin n) :
    Bag D names (node x) (vertex names u) ↔ u∈D.bag x := by
  change (∃ v, namedVertex names u=namedVertex names v ∧ v∈D.bag x) ↔ _
  constructor
  · rintro ⟨v,h,hi⟩
    have hv := namedVertex_injective names h
    subst v
    exact hi
  · intro h; exact ⟨u,rfl,h⟩

@[simp] theorem parent_named (x y : Fin t) :
    Parent D names (node x) (node y) ↔ x.val≠0 ∧ T.parent x=y := by
  rfl

/-- The unique local owner is the actual parent of the chosen child node. -/
theorem interface_named (y : Fin t) (u : Fin n) :
    Interface D names (node y) (vertex names u) ↔
      outerAdhesion D y u ∧ y.val≠0 ∧ introductionNode D u=T.parent y := by
  rw [Interface,bag_named,margin_named]
  constructor
  · rintro ⟨hb,hn,x,hp,hm⟩
    cases x with
    | inl a => exact hp.elim
    | inr x =>
      have hp' := (parent_named D names y x).mp hp
      have hm' := (margin_named D names x u).mp hm
      exact ⟨⟨hb,hn⟩,hp'.1,hm'.trans hp'.2.symm⟩
  · rintro ⟨⟨hb,hn⟩,hy,hi⟩
    exact ⟨hb,hn,node (T.parent y),(parent_named D names y _).mpr ⟨hy,rfl⟩,
      (margin_named D names _ u).mpr hi⟩

/-- Every colored interface endpoint is an original vertex. -/
theorem colored_vertex (C : AdhesionColoring D W) (i : Fin W)
    (y z : Base (A := A) (t := t)) (h : ColoredEndpoint D names C i y z) :
    ∃ u, z=vertex names u := by
  cases z with
  | inr x => exact h.2.elim
  | inl a => cases a with
    | inr e => exact h.2.elim
    | inl v => exact ⟨names.symm v,by simp [vertex]⟩

theorem colored_named (C : AdhesionColoring D W) (i : Fin W) (y : Fin t) (u : Fin n) :
    ColoredEndpoint D names C i (node y) (vertex names u) ↔
      outerAdhesion D y u ∧ y.val≠0 ∧ introductionNode D u=T.parent y ∧ C.color u=i := by
  change (Interface D names (node y) (vertex names u) ∧ C.color (names.symm (names u))=i) ↔ _
  rw [interface_named,Equiv.symm_apply_apply]
  tauto

/-- Exact chosen synthetic endpoint, on every ambient base object. -/
theorem chosen_left (C : AdhesionColoring D W) (e : ExtraEdge D)
    (z : Base (A := A) (t := t)) :
    let q := chosenCandidate D C e
    ColoredEndpoint D names C q.1 (node q.2.2) z ↔ z=vertex names e.val.1 := by
  dsimp only
  have hq := chosenCandidate_spec D C e
  constructor
  · intro h
    obtain ⟨u,rfl⟩ := colored_vertex D names C _ _ _ h
    have hu := (colored_named D names C _ _ _).mp h
    have he := C.separates _ _ _ hu.1 hq.2.2.1 (hu.2.2.2.trans hq.2.2.2.2.1.symm)
    exact congrArg (vertex (t := t) names) he
  · rintro rfl
    exact (colored_named D names C _ _ _).mpr
      ⟨hq.2.2.1,hq.1,hq.2.1.symm,hq.2.2.2.2.1⟩

theorem chosen_right (C : AdhesionColoring D W) (e : ExtraEdge D)
    (z : Base (A := A) (t := t)) :
    let q := chosenCandidate D C e
    ColoredEndpoint D names C q.2.1 (node q.2.2) z ↔ z=vertex names e.val.2 := by
  dsimp only
  have hq := chosenCandidate_spec D C e
  constructor
  · intro h
    obtain ⟨u,rfl⟩ := colored_vertex D names C _ _ _ h
    have hu := (colored_named D names C _ _ _).mp h
    have he := C.separates _ _ _ hu.1 hq.2.2.2.1 (hu.2.2.2.trans hq.2.2.2.2.2.symm)
    exact congrArg (vertex (t := t) names) he
  · rintro rfl
    exact (colored_named D names C _ _ _).mpr
      ⟨hq.2.2.2.1,hq.1,(extra_same_owner D e).trans hq.2.1.symm,hq.2.2.2.2.2⟩

#print axioms outerAtoms_c2
#print axioms eval_interface
#print axioms chosen_left
#print axioms chosen_right
end Actual
end StackSorting.GraphWidth.MarginalA2
