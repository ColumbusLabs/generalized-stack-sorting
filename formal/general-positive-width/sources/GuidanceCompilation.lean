import GuidanceMSO

namespace StackSorting.SparseEndpointMSO.Guidance
open IncidenceOwnership FiniteCopy

/-- A fixed conjunction is syntax, including the zero-color empty conjunction. -/
def allColorFormulas : {k : Nat} → (Fin k → IFormula a b) → IFormula a b
  | 0, _ => .truth
  | k + 1, fs => .conj (fs 0) (@allColorFormulas a b k (fun i => fs i.succ))

@[simp] theorem eval_allColorFormulas {D : Model} {k : Nat} (fs : Fin k → IFormula a b)
    (env : Fin a → IncidenceOwnership.Element D) (sets : Fin b → IncSet D) :
    ActualEval AtomEval (allColorFormulas fs) env sets ↔
      ∀ i, ActualEval AtomEval (fs i) env sets := by
  induction k with
  | zero => simp [allColorFormulas, ActualEval]
  | succ k ih => simp [allColorFormulas, ActualEval, ih, Fin.forall_fin_succ]

def colorsFormula (k : Nat) : IFormula 0 (k * 3) :=
  allColorFormulas (fun i : Fin k => forestFormula
    (finProdFinEquiv (i, 0)) (finProdFinEquiv (i, 1)) (finProdFinEquiv (i, 2)))

def colorSets {D : Model} (C : Colors D k) : Fin (k * 3) → IncSet D :=
  fun j => let p := finProdFinEquiv.symm j
    Fin.cases (C p.1).vertices (Fin.cases (C p.1).edges (fun _ => (C p.1).roots)) p.2

@[simp] theorem eval_colorsFormula {D : Model} (C : Colors D k) :
    ActualEval AtomEval (colorsFormula k) Fin.elim0 (colorSets C) ↔ C.Valid := by
  simp [colorsFormula, colorSets, Colors.Valid, ColorData.Valid]

/-- Exact three original-vertex sets per actual incidence-set parameter. -/
def originalSets {D : Model} (h : Laws D) (sets : Fin b → IncSet D) :
    Fin (b * 3) → Nat → Prop := fun j x =>
  let p := finProdFinEquiv.symm j
  (realization h).liftSet (sets p.1) (p.2, x)

def compileActual (p : IFormula a b) (tags : Fin a → Fin 3) : Formula a (b * 3) :=
  compile interpretation p tags id (fun X t => finProdFinEquiv (X, t))

/-- Pointwise transport for these explicit formulas, including their free set
parameters, through the previously checked physical incidence interpretation. -/
theorem eval_compileActual {D : Model} (h : Laws D) (p : IFormula a b)
    (tags : Fin a → Fin 3) (env : Fin a → Nat)
    (actual : Fin a → IncidenceOwnership.Element D) (sets : Fin b → IncSet D)
    (hr : ∀ i, Represents D (tags i) (env i) (actual i)) :
    Eval D (compileActual p tags) env (originalSets h sets) ↔
      ActualEval AtomEval p actual sets := by
  rw [compileActual, eval_compile]
  apply (realization h).eval p (fun i => (tags i, env i)) actual
    (fun X v => originalSets h sets (finProdFinEquiv (X, v.1)) v.2) sets hr
  intro i v x hx
  simp only [originalSets, Equiv.symm_apply_apply]
  exact (realization h).liftSet_iff (sets i) hx

/-- No additional graph ownership premise is needed on accepted physical models. -/
theorem accepted_root_formula {D : Model} {r s : Nat}
    (hD : Satisfies D (fullAcceptedSentence r s))
    (X F R : Fin b) (u v : Fin a) (tags : Fin a → Fin 3)
    (env : Fin a → Nat) (actual : Fin a → IncidenceOwnership.Element D)
    (sets : Fin b → IncSet D)
    (hr : ∀ i, Represents D (tags i) (env i) (actual i)) :
    Eval D (compileActual (rootFormula X F R u v) tags) env
      (originalSets (laws_of_fullAcceptedSentence hD) sets) ↔
        RootRelation (sets X) (sets F) (sets R) (actual u) (actual v) :=
  (eval_compileActual (laws_of_fullAcceptedSentence hD) _ tags env actual sets hr).trans
    (eval_rootFormula X F R u v actual sets)

/-- Fixed k colors use exactly 3k incidence-set parameters, hence 9k original
vertex-set parameters, without claiming any bounded-width witness exists. -/
theorem accepted_colors_formula {D : Model} {r s k : Nat}
    (hD : Satisfies D (fullAcceptedSentence r s)) (C : Colors D k) :
    Eval D (compileActual (colorsFormula k) Fin.elim0) Fin.elim0
      (originalSets (laws_of_fullAcceptedSentence hD) (colorSets C)) ↔ C.Valid :=
  (eval_compileActual (laws_of_fullAcceptedSentence hD) _ Fin.elim0 Fin.elim0
    Fin.elim0 (colorSets C) (fun i => Fin.elim0 i)).trans (eval_colorsFormula C)

end StackSorting.SparseEndpointMSO.Guidance
