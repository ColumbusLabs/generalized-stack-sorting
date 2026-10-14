import SparseParametricRealization

namespace StackSorting.SparseEndpointMSO.FiniteCopy.Parametric

/-- A later stage is syntax over the earlier intermediate signature, not
an oracle assigning meanings to newly introduced atoms. -/
structure CopyInterpretation (InputAtom OutputAtom : Nat → Type) (e f : Nat) where
  domain : Fin e → CopyFormula InputAtom 1 f
  atom : {r : Nat} → OutputAtom r → (Fin r → Fin e) → CopyFormula InputAtom r f

def outerTag (t : Fin (e*c)) : Fin e := (finProdFinEquiv.symm t).1
def innerTag (t : Fin (e*c)) : Fin c := (finProdFinEquiv.symm t).2

/-- Both copy counts and parameter counts are fixed before the graph is
provided. The first-stage domain is retained explicitly in the composition. -/
def compose (J : Interpretation InputAtom c d)
    (K : CopyInterpretation InputAtom OutputAtom e f) :
    Interpretation OutputAtom (e*c) (d+f*c) where
  domain t := .conj ((J.domain (innerTag t)).reindex id (Fin.castAdd (f*c)))
    (pullback J (K.domain (outerTag t)) (fun _ => innerTag t))
  atom A tags := pullback J (K.atom A (fun i => outerTag (tags i)))
    (fun i => innerTag (tags i))

/-- Actual carrier for the later stage, cut out by its actual domain formula. -/
def StepElement (K : CopyInterpretation InputAtom OutputAtom e f)
    {α : Type} (atoms : {r : Nat} → InputAtom r → (Fin r → α) → Prop)
    (sets : Fin f → α → Prop) :=
  {w : Fin e × α // ActualEval atoms (K.domain w.1) (fun _ => w.2) sets}

def stepAtoms (K : CopyInterpretation InputAtom OutputAtom e f)
    {α : Type} (atoms : {r : Nat} → InputAtom r → (Fin r → α) → Prop)
    (sets : Fin f → α → Prop) {r : Nat} (A : OutputAtom r)
    (env : Fin r → StepElement K atoms sets) : Prop :=
  ActualEval atoms (K.atom A (fun i => (env i).val.1))
    (fun i => (env i).val.2) sets

theorem eval_compose_domain (J : Interpretation InputAtom c d)
    (K : CopyInterpretation InputAtom OutputAtom e f) (D : Model)
    (params : Fin d → Nat → Prop) (sets : Fin f → Element c → Prop)
    (t : Fin (e*c)) (x : Nat) :
    Eval D ((compose J K).domain t) (fun _ => x) (flattenedSets params sets) ↔
      Eval D (J.domain (innerTag t)) (fun _ => x) params ∧
        CopyEval J D params (K.domain (outerTag t)) (fun _ => (innerTag t,x)) sets := by
  change (_ ∧ _) ↔ _
  rw [Formula.eval_reindex,eval_pullback]
  have hp : (fun i => flattenedSets params sets (Fin.castAdd (f*c) i)) = params := by
    funext i
    exact flattenedSets_parameter params sets i
  rw [hp]

/-- Two stages introduce d+f*c fixed original sets. A later b-set output
formula therefore uses exactly (d+f*c)+b*(e*c), independent of graph size. -/
theorem composed_parameter_count (d f c e b : Nat) :
    (d+f*c)+b*(e*c) = d+(f+b*e)*c := by
  simp only [Nat.add_mul,Nat.mul_assoc,Nat.add_assoc]

variable {J : Interpretation InputAtom c d} {D : Model}
  {params : Fin d → Nat → Prop} {α : Type}
  {atoms : {r : Nat} → InputAtom r → (Fin r → α) → Prop}

def composedRep (R : Realization J D params α atoms)
    (K : CopyInterpretation InputAtom OutputAtom e f) (sets : Fin f → α → Prop)
    (v : Element (e*c)) (w : StepElement K atoms sets) : Prop :=
  outerTag v.1 = w.val.1 ∧ R.rep (innerTag v.1,v.2) w.val.2

/-- Pointwise realization of syntactic composition. Every obligation reduces
to a first-stage pointwise fact or an explicit later-stage domain/atom formula.
No whole-output recognition predicate is assumed. -/
def Realization.compose (R : Realization J D params α atoms)
    (K : CopyInterpretation InputAtom OutputAtom e f) (sets : Fin f → α → Prop) :
    Realization (compose J K) D (flattenedSets params (fun i => R.liftSet (sets i)))
      (StepElement K atoms sets) (stepAtoms K atoms sets) where
  rep := composedRep R K sets
  valid v w hw := by
    have hv := R.valid _ _ hw.2
    refine ⟨hv.1,(eval_compose_domain J K D params _ v.1 v.2).mpr ⟨hv.2,?_⟩⟩
    apply (R.eval (K.domain (outerTag v.1)) (fun _ => (innerTag v.1,v.2))
      (fun _ => w.val.2) _ sets (fun _ => hw.2)
      (fun i q x hx => R.liftSet_iff (sets i) hx)).mpr
    simpa only [hw.1] using w.property
  cover w := by
    obtain ⟨v,hv⟩ := R.cover w.val.2
    refine ⟨(finProdFinEquiv (w.val.1,v.1),v.2),?_⟩
    change outerTag (finProdFinEquiv (w.val.1,v.1)) = w.val.1 ∧
      R.rep (innerTag (finProdFinEquiv (w.val.1,v.1)),v.2) w.val.2
    constructor
    · simp only [outerTag,Equiv.symm_apply_apply]
    · simpa only [innerTag,Equiv.symm_apply_apply] using hv
  complete v hv := by
    obtain ⟨hd,hk⟩ := (eval_compose_domain J K D params _ v.1 v.2).mp hv.2
    obtain ⟨x,hx⟩ := R.complete (innerTag v.1,v.2) ⟨hv.1,hd⟩
    have hh : ActualEval atoms (K.domain (outerTag v.1)) (fun _ => x) sets :=
      (R.eval _ _ _ _ _ (fun _ => hx) (fun i q z hz => R.liftSet_iff (sets i) hz)).mp hk
    exact ⟨⟨(outerTag v.1,x),hh⟩,rfl,hx⟩
  equal v z w y hv hz := by
    constructor
    · intro he
      subst z
      apply Subtype.ext
      exact Prod.ext (hv.1.symm.trans hz.1) ((R.equal _ _ _ _ hv.2 hz.2).mp rfl)
    · intro he
      subst y
      have hi := (R.equal _ _ _ _ hv.2 hz.2).mpr rfl
      have ht : v.1 = z.1 := by
        apply finProdFinEquiv.symm.injective
        exact Prod.ext (hv.1.trans hz.1.symm) (congrArg Prod.fst hi)
      exact Prod.ext ht (congrArg (fun q : Element c => q.2) hi)
  atom A env actual hr := by
    change Eval D (pullback J (K.atom A (fun i => outerTag (env i).1))
      (fun i => innerTag (env i).1)) (fun i => (env i).2)
      (flattenedSets params (fun i => R.liftSet (sets i))) ↔ _
    rw [R.pullback_actual _ _ _ (fun i => (actual i).val.2) sets (fun i => (hr i).2)]
    have ht : (fun i => outerTag (env i).1) = (fun i => (actual i).val.1) :=
      funext (fun i => (hr i).1)
    rw [ht]
    rfl

#print axioms eval_compose_domain
#print axioms composed_parameter_count
#print axioms Realization.compose
end StackSorting.SparseEndpointMSO.FiniteCopy.Parametric
