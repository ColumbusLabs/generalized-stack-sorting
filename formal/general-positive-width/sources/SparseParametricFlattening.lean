import SparseParametricFiniteCopy

namespace StackSorting.SparseEndpointMSO.FiniteCopy.Parametric
open CanonicalChoice

/-- The first d sets are fixed interpretation parameters. Each of the b free
copied-universe sets contributes c further original-vertex sets. -/
def flattenedSets (params : Fin d → Nat → Prop) (sets : Fin b → Element c → Prop) :
    Fin (d+b*c) → Nat → Prop :=
  Fin.addCases params (fun j x =>
    let q := finProdFinEquiv.symm j
    sets q.1 (q.2,x))

@[simp] theorem flattenedSets_parameter (params : Fin d → Nat → Prop)
    (sets : Fin b → Element c → Prop) (i : Fin d) :
    flattenedSets params sets (Fin.castAdd (b*c) i) = params i := by
  simp only [flattenedSets,Fin.addCases_left]

@[simp] theorem flattenedSets_copy (params : Fin d → Nat → Prop)
    (sets : Fin b → Element c → Prop) (i : Fin b) (t : Fin c) (x : Nat) :
    flattenedSets params sets (Fin.natAdd d (finProdFinEquiv (i,t))) x = sets i (t,x) := by
  simp only [flattenedSets,Fin.addCases_right,Equiv.symm_apply_apply]

/-- Support of fixed parameters is requested exactly here, where the whole
output tuple is asserted to be supported on original input vertices. -/
theorem flattenedSets_supported (J : Interpretation Atom c d) (D : Model)
    (params : Fin d → Nat → Prop) (sets : Fin b → Element c → Prop)
    (hp : SupportedTuple D params) (hs : ∀ i, Supported J D params (sets i)) :
    SupportedTuple D (flattenedSets params sets) := by
  intro j x
  refine Fin.addCases ?_ ?_ j
  · intro i hi
    rw [flattenedSets_parameter] at hi
    exact hp i x hi
  · intro q hq
    simp only [flattenedSets,Fin.addCases_right] at hq
    exact (hs (finProdFinEquiv.symm q).1 ((finProdFinEquiv.symm q).2,x) hq).1

/-- Fixed-arity original-vocabulary formula. The finite arithmetic in this
type depends on d,b,c only and never on the input graph or its cardinality. -/
def pullback (J : Interpretation Atom c d) (p : CopyFormula Atom a b)
    (tags : Fin a → Fin c) : Formula a (d+b*c) :=
  compile J p tags id (fun i t => Fin.natAdd d (finProdFinEquiv (i,t)))
    (Fin.castAdd (b*c))

theorem eval_pullback (J : Interpretation Atom c d) (D : Model)
    (p : CopyFormula Atom a b) (tags : Fin a → Fin c) (env : Fin a → Nat)
    (params : Fin d → Nat → Prop) (sets : Fin b → Element c → Prop) :
    Eval D (pullback J p tags) env (flattenedSets params sets) ↔
      CopyEval J D params p (fun i => (tags i,env i)) sets := by
  have hp : (fun i => flattenedSets params sets (Fin.castAdd (b*c) i)) = params := by
    funext i
    exact flattenedSets_parameter params sets i
  have hs : (fun i v => flattenedSets params sets
      (Fin.natAdd d (finProdFinEquiv (i,v.1))) v.2) = sets := by
    funext i v
    exact flattenedSets_copy params sets i v.1 v.2
  unfold pullback
  rw [eval_compile,hp,hs]
  rfl

/-- Existence of a supported copied tuple is transported constructively to
one fixed original tuple. This does not assume a recognition conclusion. -/
theorem exists_supported_pullback (J : Interpretation Atom c d) (D : Model)
    (p : CopyFormula Atom a b) (tags : Fin a → Fin c) (env : Fin a → Nat)
    (params : Fin d → Nat → Prop) (hp : SupportedTuple D params)
    (sets : Fin b → Element c → Prop) (hs : ∀ i, Supported J D params (sets i))
    (he : CopyEval J D params p (fun i => (tags i,env i)) sets) :
    ∃ X : Fin (d+b*c) → Nat → Prop,
      SupportedTuple D X ∧ Eval D (pullback J p tags) env X :=
  ⟨flattenedSets params sets,flattenedSets_supported J D params sets hp hs,
    (eval_pullback J D p tags env params sets).mpr he⟩

/-- An empty copy universe has no supported selected elements. This covers
c=0 without imposing nonemptiness on the original physical domain. -/
theorem zero_copy_supported (J : Interpretation Atom 0 d) (D : Model)
    (params : Fin d → Nat → Prop) (X : Element 0 → Prop) : Supported J D params X := by
  intro v
  exact Fin.elim0 v.1

/-- Empty original domains force every supported copied set to be empty,
regardless of the interpretation's free parameters. -/
theorem supported_empty_domain (J : Interpretation Atom c d) (D : Model)
    (params : Fin d → Nat → Prop) (hD : D.domain = [])
    (X : Element c → Prop) (hX : Supported J D params X) : X = fun _ => False := by
  funext v
  apply propext
  constructor
  · intro hx
    have hv := (hX v hx).1
    simp only [hD,List.mem_nil_iff] at hv
  · exact False.elim

#print axioms flattenedSets_supported
#print axioms eval_pullback
#print axioms exists_supported_pullback
#print axioms supported_empty_domain
end StackSorting.SparseEndpointMSO.FiniteCopy.Parametric
