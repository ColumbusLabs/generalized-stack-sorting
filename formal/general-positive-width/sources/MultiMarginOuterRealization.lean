import MultiMarginRootTransport

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.GraphWidth.MultiMargin
open FinitePort Nested
open SparseEndpointMSO SparseEndpointMSO.FiniteCopy SparseEndpointMSO.FiniteCopy.Parametric
variable {n t : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}

/-- Exact retention of original incidence elements in the completed carrier.
The concrete completion adapter uses the literal left injection. -/
structure Retained (H : CompletedIncidence D α) (β : Type) where
  embed : β → α
  injective : Function.Injective embed
  retained_exact : ∀ z, (H.rel.vertex z ∨ H.rel.originalEdge z) ↔ ∃ a, z=embed a

namespace CompletedIncidence
variable {α : Type} (H : CompletedIncidence D α) (s : Sane D) (ht : 0<t)

theorem ancestor_right_vertex {u v : α}
    (h : Syntax.Ancestor H.rel Syntax.fixed (H.parameters s ht) u v) : H.rel.vertex v := by
  obtain ⟨r,hr,hc⟩ := h.2.1
  exact hc.1

theorem margin_any (x : Fin t) (z : α) :
    Syntax.Connected H.rel Syntax.fixed (H.parameters s ht) .marginal none
      (H.vertex (entry s x)) z ↔ ∃ v, z=H.vertex v ∧ Margin D x v := by
  constructor
  · intro h
    obtain ⟨v,rfl⟩ := (H.vertex_exact z).mp h.2.1
    exact ⟨v,rfl,(H.margin_exact s ht x v).mp h⟩
  · rintro ⟨v,rfl,hv⟩
    exact (H.margin_exact s ht x v).mpr hv

theorem component_any (x : Fin t) (z : α) :
    Syntax.Ancestor H.rel Syntax.fixed (H.parameters s ht) (H.vertex (entry s x)) z ↔
      ∃ v, z=H.vertex v ∧ IntroductionComponent D x v := by
  constructor
  · intro h
    obtain ⟨v,rfl⟩ := (H.vertex_exact z).mp (H.ancestor_right_vertex s ht h)
    exact ⟨v,rfl,(H.component_exact s ht x v).mp h⟩
  · rintro ⟨v,rfl,hv⟩
    exact (H.component_exact s ht x v).mpr hv

theorem bag_any (x : Fin t) (z : α) :
    Syntax.Bag H.rel Syntax.fixed (H.parameters s ht) (H.vertex (entry s x)) z ↔
      ∃ v, z=H.vertex v ∧ v ∈ D.bag x := by
  constructor
  · intro h
    have hv : H.rel.vertex z := by
      rcases h with h | ⟨_,u,_,_,e,_,he,_⟩
      · exact h.2.1
      · exact H.incidence_vertex z e he
    obtain ⟨v,rfl⟩ := (H.vertex_exact z).mp hv
    exact ⟨v,rfl,(H.bag_exact s ht x v).mp h⟩
  · rintro ⟨v,rfl,hv⟩
    exact (H.bag_exact s ht x v).mpr hv

end CompletedIncidence

namespace Retained
variable {α β : Type} {H : CompletedIncidence D α} (B : Retained H β)
variable (s : Sane D) (ht : 0<t)

abbrev Output (_B : Retained H β) := β ⊕ Fin t
abbrev Stage (_B : Retained H β) := StepElement Syntax.interpretation (Syntax.atoms H.rel) (H.parameters s ht)

/-- Pointwise original graph and decomposition semantics on the actual
carrier of original elements plus the original outer nodes. -/
def outputAtoms : {r : Nat} → Syntax.OutputAtom r → (Fin r → B.Output) → Prop
  | _, .vertex, env => match env 0 with
    | .inl a => H.rel.vertex (B.embed a) | .inr _ => False
  | _, .originalEdge, env => match env 0 with
    | .inl a => H.rel.originalEdge (B.embed a) | .inr _ => False
  | _, .node, env => match env 0 with
    | .inl _ => False | .inr _ => True
  | _, .incidence, env => match env 0,env 1 with
    | .inl a,.inl b => H.rel.originalEdge (B.embed b) ∧ H.rel.incidence (B.embed a) (B.embed b)
    | _,_ => False
  | _, .margin, env => match env 0,env 1 with
    | .inr x,.inl a => ∃ v, B.embed a=H.vertex v ∧ Margin D x v
    | _,_ => False
  | _, .component, env => match env 0,env 1 with
    | .inr x,.inl a => ∃ v, B.embed a=H.vertex v ∧ IntroductionComponent D x v
    | _,_ => False
  | _, .parent, env => match env 0,env 1 with
    | .inr x,.inr y => x.val≠0 ∧ T.parent x=y
    | _,_ => False
  | _, .bag, env => match env 0,env 1 with
    | .inr x,.inl a => ∃ v, B.embed a=H.vertex v ∧ v ∈ D.bag x
    | _,_ => False

noncomputable def toStage : B.Output → B.Stage s ht
  | .inl a => ⟨(0,B.embed a),by
      change ¬ (¬ H.rel.vertex (B.embed a) ∧ ¬ H.rel.originalEdge (B.embed a))
      intro hn
      exact ((B.retained_exact _).mpr ⟨a,rfl⟩).elim hn.1 hn.2⟩
  | .inr x => ⟨(1,H.vertex (entry s x)),by
      change H.rel.vertex (H.vertex (entry s x)) ∧ ∃ y, H.vertex (entry s x)=H.vertex (entry s y)
      exact ⟨(H.vertex_exact _).mpr ⟨entry s x,rfl⟩,x,rfl⟩⟩

theorem toStage_injective : Function.Injective (B.toStage s ht) := by
  intro a b h
  have hp := congrArg Subtype.val h
  cases a with
  | inl a => cases b with
    | inl b => exact congrArg Sum.inl (B.injective (congrArg Prod.snd hp))
    | inr b => have ht := congrArg Prod.fst hp; exact (Fin.zero_ne_one ht).elim
  | inr a => cases b with
    | inl b => have hval := congrArg (fun p : Fin 2 × α => p.1.val) hp; change (1 : Nat)=0 at hval; omega
    | inr b =>
      exact congrArg Sum.inr (Encoding.entry_injective s
        (H.injective (congrArg Prod.snd hp)))

theorem toStage_surjective : Function.Surjective (B.toStage s ht) := by
  rintro ⟨⟨tag,z⟩,hz⟩
  have hh : tag=0 ∨ tag=1 := by omega
  rcases hh with rfl | rfl
  · have hr : H.rel.vertex z ∨ H.rel.originalEdge z := by
      change ¬ (¬ H.rel.vertex z ∧ ¬ H.rel.originalEdge z) at hz
      classical
      simpa only [not_and_or,not_not] using hz
    obtain ⟨a,rfl⟩ := (B.retained_exact z).mp hr
    exact ⟨.inl a,rfl⟩
  · change H.rel.vertex z ∧ ∃ x, z=H.vertex (entry s x) at hz
    obtain ⟨x,rfl⟩ := hz.2
    exact ⟨.inr x,rfl⟩

noncomputable def stageEquiv : B.Output ≃ B.Stage s ht :=
  Equiv.ofBijective (B.toStage s ht) ⟨B.toStage_injective s ht,B.toStage_surjective s ht⟩

/-- Atomic stage realization is checked on actual original elements and
actual decomposition nodes, never on an unspecified interpretation witness. -/
theorem stage_atoms {r : Nat} (A : Syntax.OutputAtom r) (env : Fin r → B.Output) :
    stepAtoms Syntax.interpretation (Syntax.atoms H.rel) (H.parameters s ht) A
      (fun i => B.toStage s ht (env i)) ↔ B.outputAtoms A env := by
  cases A with
  | vertex => cases h : env 0 <;> simp [stepAtoms,Syntax.interpretation,toStage,outputAtoms,h,Syntax.unary,ActualEval,Syntax.atoms]
  | originalEdge => cases h : env 0 <;> simp [stepAtoms,Syntax.interpretation,toStage,outputAtoms,h,Syntax.unary,ActualEval,Syntax.atoms]
  | node => cases h : env 0 <;> simp [stepAtoms,Syntax.interpretation,toStage,outputAtoms,h,ActualEval]
  | incidence => cases h : env 0 <;> cases j : env 1 <;>
      simp [stepAtoms,Syntax.interpretation,toStage,outputAtoms,h,j,Syntax.unary,Syntax.incident,ActualEval,Syntax.atoms]
  | margin => cases h : env 0 <;> cases j : env 1 <;>
      simp [stepAtoms,Syntax.interpretation,toStage,outputAtoms,h,j,ActualEval,Syntax.eval_connected,
        H.margin_any s ht,ConnectedConeNormalization.vertexCutValue]
  | component => cases h : env 0 <;> cases j : env 1 <;>
      simp [stepAtoms,Syntax.interpretation,toStage,outputAtoms,h,j,ActualEval,Syntax.eval_ancestor,H.component_any s ht]
  | parent => cases h : env 0 <;> cases j : env 1 <;>
      simp [stepAtoms,Syntax.interpretation,toStage,outputAtoms,h,j,ActualEval,Syntax.eval_parent,H.parent_exact s ht]
  | bag => cases h : env 0 <;> cases j : env 1 <;>
      simp [stepAtoms,Syntax.interpretation,toStage,outputAtoms,h,j,ActualEval,Syntax.eval_bag,H.bag_any s ht]

/-- Relabel a pointwise realization along a proved carrier equivalence. -/
def transportRealization {Atom : Nat → Type} {c d : Nat} {A : Model}
    {J : Parametric.Interpretation Atom c d} {params : Fin d → Nat → Prop}
    {γ δ : Type} {ats : {r : Nat} → Atom r → (Fin r → γ) → Prop}
    (R : Parametric.Realization J A params γ ats) (e : γ ≃ δ)
    (ats' : {r : Nat} → Atom r → (Fin r → δ) → Prop)
    (ha : ∀ {r} (a : Atom r) (env : Fin r → γ), ats a env ↔ ats' a (fun i => e (env i))) :
    Parametric.Realization J A params δ ats' where
  rep v x := R.rep v (e.symm x)
  valid v x hx := R.valid v _ hx
  cover x := R.cover (e.symm x)
  complete v hv := by
    obtain ⟨x,hx⟩ := R.complete v hv
    exact ⟨e x,by simpa only [Equiv.symm_apply_apply] using hx⟩
  equal v w x y hx hy := (R.equal v w _ _ hx hy).trans ⟨fun h => e.symm.injective h,congrArg e.symm⟩
  atom a env actual hr := by
    rw [R.atom a env (fun i => e.symm (actual i)) hr,ha]
    simp only [Equiv.apply_symm_apply]

/-- Genuine application-specific outer realization from the pointwise H
realization. Composition is the accepted parameter-dependent compiler. -/
noncomputable def realization {A : Model} {c d : Nat}
    {J : Parametric.Interpretation Syntax.InputAtom c d} {params : Fin d → Nat → Prop}
    (R : Parametric.Realization J A params α (Syntax.atoms H.rel)) :
    Parametric.Realization (Parametric.compose J Syntax.interpretation) A
      (Parametric.flattenedSets params (fun i => R.liftSet ((H.parameters s ht) i)))
      (B.Output) B.outputAtoms := by
  apply transportRealization (R.compose Syntax.interpretation (H.parameters s ht))
    (B.stageEquiv s ht).symm B.outputAtoms
  intro r atom env
  have he : (fun i => B.toStage s ht ((B.stageEquiv s ht).symm (env i)))=env := by
    funext i
    exact (B.stageEquiv s ht).apply_symm_apply (env i)
  have h := B.stage_atoms s ht atom (fun i => (B.stageEquiv s ht).symm (env i))
  rw [he] at h
  exact h

/-- Final source-vocabulary formula transport, for every actual output
formula, with the exact fixed-parameter and copied-free-set flattening. -/
theorem pullback_actual {A : Model} {c d a b : Nat}
    {J : Parametric.Interpretation Syntax.InputAtom c d} {params : Fin d → Nat → Prop}
    (R : Parametric.Realization J A params α (Syntax.atoms H.rel))
    (p : CopyFormula Syntax.OutputAtom a b) (tags : Fin a → Fin (2*c)) (env : Fin a → Nat)
    (actual : Fin a → B.Output) (sets : Fin b → B.Output → Prop)
    (hr : ∀ i, (B.realization s ht R).rep (tags i,env i) (actual i)) :
    Eval A (Parametric.pullback (Parametric.compose J Syntax.interpretation) p tags) env
      (Parametric.flattenedSets
        (Parametric.flattenedSets params (fun i => R.liftSet ((H.parameters s ht) i)))
        (fun i => (B.realization s ht R).liftSet (sets i))) ↔
      ActualEval B.outputAtoms p actual sets :=
  (B.realization s ht R).pullback_actual p tags env actual sets hr

#print axioms toStage_injective
#print axioms toStage_surjective
#print axioms stage_atoms
#print axioms realization
#print axioms pullback_actual
end Retained
end StackSorting.GraphWidth.MultiMargin
