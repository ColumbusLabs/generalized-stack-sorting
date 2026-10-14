import GuidanceGraphSemantics

namespace StackSorting.SparseEndpointMSO.Guidance
open IncidenceOwnership FiniteCopy

abbrev IFormula := CopyFormula IncidenceAtom

@[simp] theorem cases_one (x : α) (env : Fin (a + 1) → α) :
    Fin.cases x env (1 : Fin (a + 2)) = env 0 := rfl
@[simp] theorem cases_two (x : α) (env : Fin (a + 2) → α) :
    Fin.cases x env (2 : Fin (a + 3)) = env 1 := rfl

def vertexFormula (u : Fin a) : IFormula a b := .atom .vertex (fun _ => u)
def edgeFormula (e : Fin a) : IFormula a b := .atom .edge (fun _ => e)
def incidentFormula (u e : Fin a) : IFormula a b :=
  .atom .incidence (Fin.cases u (fun _ => e))
def orFormula (p q : IFormula a b) : IFormula a b := .neg (.conj (.neg p) (.neg q))
def iffFormula (p q : IFormula a b) : IFormula a b := .conj (.implies p q) (.implies q p)

def stepFormula (X F : Fin b) (u v : Fin a) : IFormula a b :=
  .conj (vertexFormula u) (.conj (.member u X)
    (.conj (vertexFormula v) (.conj (.member v X)
      (.conj (.neg (.equal u v)) (.existsFO
        (.conj (edgeFormula 0) (.conj (.member 0 F)
          (.conj (incidentFormula u.succ 0) (incidentFormula v.succ 0)))))))))

def pairFormula (cut : Option (Fin a × Fin a)) (u v : Fin a) : IFormula a b :=
  match cut with
  | none => .truth
  | some (p, q) => .neg (orFormula
      (.conj (.equal u p) (.equal v q)) (.conj (.equal u q) (.equal v p)))

def cutValue (env : Fin a → α) (cut : Option (Fin a × Fin a)) : Option (α × α) :=
  cut.map (fun p => (env p.1, env p.2))

def liftCut (cut : Option (Fin a × Fin a)) : Option (Fin (a + 1) × Fin (a + 1)) :=
  cut.map (fun p => (p.1.succ, p.2.succ))

@[simp] theorem cutValue_lift (env : Fin a → α) (x : α) (cut : Option (Fin a × Fin a)) :
    cutValue (Fin.cases x env) (liftCut cut) = cutValue env cut := by
  cases cut <;> rfl

def filteredStepFormula (X F : Fin b) (cut : Option (Fin a × Fin a))
    (u v : Fin a) : IFormula a b := .conj (stepFormula X F u v) (pairFormula cut u v)

/-- Connectivity by an explicitly bound closed incidence set. Bound variables
are introduced with Fin.succ, so no free variable can be captured. -/
def connectedFormula (X F : Fin b) (cut : Option (Fin a × Fin a))
    (u v : Fin a) : IFormula a b :=
  .conj (.member u X) (.conj (.member v X) (.allSet
    (.implies (.conj (.member u 0) (.allFO (.allFO
      (.implies (filteredStepFormula X.succ F.succ (liftCut (liftCut cut)) 1 0)
        (.implies (.member 1 0) (.member 0 0)))))) (.member v 0))))

def rootFormula (X F R : Fin b) (u r : Fin a) : IFormula a b :=
  .conj (.member r R) (connectedFormula X F none u r)

def typedFormula (X F R : Fin b) : IFormula a b :=
  .conj (.allFO (.implies (.member 0 X) (vertexFormula 0)))
    (.conj (.allFO (.implies (.member 0 F) (edgeFormula 0)))
      (.conj (.allFO (.implies (.member 0 R) (.member 0 X)))
        (.allFO (.allFO (.implies (.conj (.member 1 F) (incidentFormula 0 1))
          (.member 0 X))))))

def rootedFormula (X F R : Fin b) : IFormula a b :=
  .conj (typedFormula X F R) (.allFO (.implies (.member 0 X) (.existsFO
    (.conj (rootFormula X F R 1 0) (.allFO
      (.implies (rootFormula X F R 2 0) (.equal 0 1)))))))

/-- Every selected edge is a bridge. The semantic theorem identifies this with
Mathlib's standard absence-of-finite-cycles predicate. -/
def acyclicFormula (X F : Fin b) : IFormula a b :=
  .allFO (.allFO (.implies (stepFormula X F 1 0)
    (.neg (connectedFormula X F (some (1, 0)) 1 0))))

def forestFormula (X F R : Fin b) : IFormula a b :=
  .conj (rootedFormula X F R) (acyclicFormula X F)

variable {D : Model}

@[simp] theorem eval_stepFormula (X F : Fin b) (u v : Fin a)
    (env : Fin a → IncidenceOwnership.Element D) (sets : Fin b → IncSet D) :
    ActualEval AtomEval (stepFormula X F u v) env sets ↔ Step (sets X) (sets F) (env u) (env v) := by
  simp [stepFormula, vertexFormula, edgeFormula, incidentFormula, ActualEval, AtomEval, Step]

@[simp] theorem eval_pairFormula (cut : Option (Fin a × Fin a)) (u v : Fin a)
    (env : Fin a → IncidenceOwnership.Element D) (sets : Fin b → IncSet D) :
    ActualEval AtomEval (pairFormula cut u v) env sets ↔
      PairAllowed (cutValue env cut) (env u) (env v) := by
  classical
  cases cut with
  | none => rfl
  | some p =>
    rcases p with ⟨p, q⟩
    simp [pairFormula, PairAllowed, cutValue, orFormula, ActualEval]

@[simp] theorem eval_filteredStepFormula (X F : Fin b) (cut : Option (Fin a × Fin a))
    (u v : Fin a) (env : Fin a → IncidenceOwnership.Element D) (sets : Fin b → IncSet D) :
    ActualEval AtomEval (filteredStepFormula X F cut u v) env sets ↔
      (filteredGraph (sets X) (sets F) (cutValue env cut)).Adj (env u) (env v) := by
  simp [filteredStepFormula, ActualEval, filteredGraph]

@[simp] theorem eval_connectedFormula (X F : Fin b) (cut : Option (Fin a × Fin a))
    (u v : Fin a) (env : Fin a → IncidenceOwnership.Element D) (sets : Fin b → IncSet D) :
    ActualEval AtomEval (connectedFormula X F cut u v) env sets ↔
      Connected (sets X) (sets F) (cutValue env cut) (env u) (env v) := by
  simp only [connectedFormula, ActualEval, eval_filteredStepFormula,
    Fin.cases_zero, Fin.cases_succ, cases_one, cutValue_lift]
  unfold Connected
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  simpa only [ClosedReach, and_imp] using closedReach_iff_walk
    (filteredGraph (sets X) (sets F) (cutValue env cut)) (env u) (env v)

@[simp] theorem eval_rootFormula (X F R : Fin b) (u r : Fin a)
    (env : Fin a → IncidenceOwnership.Element D) (sets : Fin b → IncSet D) :
    ActualEval AtomEval (rootFormula X F R u r) env sets ↔
      RootRelation (sets X) (sets F) (sets R) (env u) (env r) := by
  simp [rootFormula, ActualEval, RootRelation, cutValue]

@[simp] theorem eval_typedFormula (X F R : Fin b)
    (env : Fin a → IncidenceOwnership.Element D) (sets : Fin b → IncSet D) :
    ActualEval AtomEval (typedFormula X F R) env sets ↔ Typed (sets X) (sets F) (sets R) := by
  simp only [typedFormula, ActualEval, vertexFormula, edgeFormula, incidentFormula,
    AtomEval, Fin.cases_zero]
  constructor
  · rintro ⟨hv, he, hr, hi⟩
    exact ⟨hv, he, hr, fun e u hF hI => hi e u ⟨hF, hI⟩⟩
  · intro h
    exact ⟨h.vertices, h.edges, h.roots, fun e u he => h.endpoints e u he.1 he.2⟩

@[simp] theorem eval_rootedFormula (X F R : Fin b)
    (env : Fin a → IncidenceOwnership.Element D) (sets : Fin b → IncSet D) :
    ActualEval AtomEval (rootedFormula X F R) env sets ↔ Rooted (sets X) (sets F) (sets R) := by
  simp [rootedFormula, ActualEval, Rooted, ExistsUnique]

@[simp] theorem eval_acyclicFormula (X F : Fin b)
    (env : Fin a → IncidenceOwnership.Element D) (sets : Fin b → IncSet D) :
    ActualEval AtomEval (acyclicFormula X F) env sets ↔ (selectedGraph (sets X) (sets F)).IsAcyclic := by
  simp only [acyclicFormula, ActualEval, eval_stepFormula, eval_connectedFormula,
    Fin.cases_zero]
  change (∀ u v, Step (sets X) (sets F) u v →
    ¬ Connected (sets X) (sets F) (some (u, v)) u v) ↔ _
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  constructor
  · intro h u v huv
    rw [SimpleGraph.isBridge_iff]
    intro hw
    exact h u v huv ⟨huv.2.1, huv.2.2.2.1, by
      rw [filteredGraph_pair]
      exact hw⟩
  · intro h u v huv hc
    have hb := h huv
    rw [SimpleGraph.isBridge_iff] at hb
    apply hb
    rw [← filteredGraph_pair]
    exact hc.2.2

@[simp] theorem eval_forestFormula (X F R : Fin b)
    (env : Fin a → IncidenceOwnership.Element D) (sets : Fin b → IncSet D) :
    ActualEval AtomEval (forestFormula X F R) env sets ↔ Forest (sets X) (sets F) (sets R) := by
  simp [forestFormula, ActualEval, Forest]

end StackSorting.SparseEndpointMSO.Guidance
