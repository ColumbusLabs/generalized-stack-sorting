import DecompositionIntroductionSyntax
import SparseEliminationIdentification

namespace StackSorting.GraphWidth.Nested.IntroductionSyntax
open FinitePort
open StackSorting.SparseEndpointMSO StackSorting.SparseEndpointMSO.FiniteCopy
open StackSorting.SparseEndpointMSO.FiniteCopy.Parametric
open StackSorting.SparseEndpointMSO.EliminationSyntax
variable {n t c d : Nat} {G : Graph n} {T : RootedTree t}

/-- The source formula is fixed by the literal representation and its retained
original-vertex copy tag, independently of graph size or a decomposition witness. -/
def sourcePreorder (J : Interpretation Syntax.OutputAtom c d) (tag : Fin c) :
    Formula 2 (d+0*c) :=
  pullback J (preorderAt (b:=0) (0 : Fin 2) 1) (fun _ => tag)

theorem sourcePreorder_exact (D : Decomposition G T) {M : Model}
    {J : Interpretation Syntax.OutputAtom c d} {params : Fin d → Nat → Prop}
    (R : Realization J M params (Carrier n t) (atoms D))
    (tag : Fin c) (name : Fin n → Nat)
    (hcode : ∀ v, R.rep (tag,name v) (.inl v)) (u v : Fin n) :
    RelationEval M (sourcePreorder J tag)
      (flattenedSets params (fun i : Fin 0 => R.liftSet (Fin.elim0 i))) (name u) (name v) ↔
      Ancestor T (introductionNode D u) (introductionNode D v) := by
  unfold RelationEval sourcePreorder
  have hr : ∀ i : Fin 2, R.rep (tag,pairEnv (name u) (name v) i)
      (Fin.cases (.inl u) (fun _ => .inl v) i) := by
    intro i
    refine Fin.cases (hcode u) (fun j => ?_) i
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    exact hcode v
  rw [R.pullback_actual _ _ _ (Fin.cases (.inl u) (fun _ => .inl v)) Fin.elim0 hr]
  exact preorder_original_exact D 0 1 _ Fin.elim0 u v rfl rfl

/-- On canonical physical-time names this supplies exactly the previously
external RepresentsIntroduction API, without assuming that preorder relation. -/
theorem source_represents_introduction (D : Decomposition G T) {M : Model}
    {J : Interpretation Syntax.OutputAtom c d} {params : Fin d → Nat → Prop}
    (R : Realization J M params (Carrier n t) (atoms D))
    (tag : Fin c) (hcode : ∀ v, R.rep (tag,v.val) (.inl v)) :
    RepresentsIntroduction D M (sourcePreorder J tag)
      (flattenedSets params (fun i : Fin 0 => R.liftSet (Fin.elim0 i))) :=
  fun u v => sourcePreorder_exact D R tag Fin.val hcode u v

theorem source_split_identifies (D : Decomposition G T) {M : Model}
    (hp : TimePath M n) {J : Interpretation Syntax.OutputAtom c d}
    {params : Fin d → Nat → Prop}
    (R : Realization J M params (Carrier n t) (atoms D))
    (tag : Fin c) (hcode : ∀ v, R.rep (tag,v.val) (.inl v)) (u v : Fin n) :
    RelationEval M (splitPreorder (sourcePreorder J tag))
      (flattenedSets params (fun i : Fin 0 => R.liftSet (Fin.elim0 i))) u.val v.val ↔
      IntroductionEarlier D u v :=
  splitPreorder_identifies D M hp _ _ (source_represents_introduction D R tag hcode) u v

#print axioms sourcePreorder_exact
#print axioms source_represents_introduction
#print axioms source_split_identifies
end StackSorting.GraphWidth.Nested.IntroductionSyntax
