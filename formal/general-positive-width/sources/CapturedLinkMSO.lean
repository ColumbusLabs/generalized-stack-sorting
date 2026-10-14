import ForestPreorderMSO
import GuidanceCompilation

/-! Literal fixed-color-pair elimination of potential copied edges. Candidate
edge copies are represented by one unary set of bases per ordered color pair;
no binary selected-link atom is added to the original incidence vocabulary. -/
namespace StackSorting.CapturedLinkExtraction
open SparseEndpointMSO SparseEndpointMSO.Guidance SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.IncidenceOwnership GraphWidth

structure LinkIndices (k b : Nat) where
  color : Fin k → Fin 3 → Fin b
  candidate : Fin k → Fin k → Fin b
  original : Fin b
  roots : Fin b

def LinkIndices.lift (I : LinkIndices k b) : LinkIndices k (b+1) where
  color i j := (I.color i j).succ
  candidate i j := (I.candidate i j).succ
  original := I.original.succ
  roots := I.roots.succ

def anyColorFormulas (fs : Fin k → IFormula a b) : IFormula a b :=
  .neg (allColorFormulas (fun i => .neg (fs i)))

@[simp] theorem eval_anyColorFormulas {D : Model} (fs : Fin k → IFormula a b)
    (env : Fin a → IncidenceOwnership.Element D) (sets : Fin b → IncSet D) :
    ActualEval AtomEval (anyColorFormulas fs) env sets ↔
      ∃ i, ActualEval AtomEval (fs i) env sets := by
  classical
  simp only [anyColorFormulas,ActualEval,eval_allColorFormulas,not_forall,not_not]

def originalLinkFormula (K : Fin b) (u v : Fin a) : IFormula a b :=
  .existsFO (.conj (edgeFormula 0) (.conj (.member 0 K)
    (.conj (incidentFormula u.succ 0) (incidentFormula v.succ 0))))

def pairLinkFormula (I : LinkIndices k b) (i j : Fin k) (u v : Fin a) : IFormula a b :=
  .existsFO (.conj (.member 0 (I.candidate i j))
    (.conj (rootFormula (I.color i 0) (I.color i 1) (I.color i 2) 0 u.succ)
      (rootFormula (I.color j 0) (I.color j 1) (I.color j 2) 0 v.succ)))

def capturedLinkFormula (I : LinkIndices k b) (u v : Fin a) : IFormula a b :=
  .conj (.neg (.equal u v)) (orFormula (originalLinkFormula I.original u v)
    (anyColorFormulas (fun i => anyColorFormulas (fun j => pairLinkFormula I i j u v))))

def RawLink {D : Model} (I : LinkIndices k b) (sets : Fin b → IncSet D)
    (u v : IncidenceOwnership.Element D) : Prop :=
  u ≠ v ∧ ((∃ e, IsEdge e ∧ sets I.original e ∧ ElementIncident u e ∧ ElementIncident v e) ∨
    ∃ i j x, sets (I.candidate i j) x ∧
      RootRelation (sets (I.color i 0)) (sets (I.color i 1)) (sets (I.color i 2)) x u ∧
      RootRelation (sets (I.color j 0)) (sets (I.color j 1)) (sets (I.color j 2)) x v)

@[simp] theorem eval_capturedLinkFormula {D : Model} (I : LinkIndices k b)
    (u v : Fin a) (env : Fin a → IncidenceOwnership.Element D) (sets : Fin b → IncSet D) :
    ActualEval AtomEval (capturedLinkFormula I u v) env sets ↔ RawLink I sets (env u) (env v) := by
  classical
  simp only [capturedLinkFormula,ActualEval,orFormula,not_and_or,not_not,
    originalLinkFormula,edgeFormula,incidentFormula,AtomEval,Fin.cases_zero,
    Fin.cases_succ,eval_anyColorFormulas,pairLinkFormula,eval_rootFormula]
  rfl

@[simp] theorem rawLink_lift {D : Model} (I : LinkIndices k b)
    (sets : Fin b → IncSet D) (X : IncSet D) (u v : IncidenceOwnership.Element D) :
    RawLink I.lift (Fin.cases X sets) u v ↔ RawLink I sets u v := Iff.rfl

open ConnectedConeNormalization

def rawAvoidFormula (cut : Option (Fin a)) (u : Fin a) : IFormula a b :=
  match cut with | none => .truth | some x => .neg (.equal u x)

@[simp] theorem eval_rawAvoidFormula {D : Model} (cut : Option (Fin a)) (u : Fin a)
    (env : Fin a → IncidenceOwnership.Element D) (sets : Fin b → IncSet D) :
    ActualEval AtomEval (rawAvoidFormula cut u) env sets ↔
      Avoid (vertexCutValue env cut) (env u) := by
  cases cut <;> rfl

/-- Closed-set vertex-deletion connectivity over the explicit selected-link
formula. Both endpoint guards are retained, including zero-edge walks. -/
def capturedConnectedFormula (I : LinkIndices k b) (cut : Option (Fin a))
    (u v : Fin a) : IFormula a b :=
  .conj (rawAvoidFormula cut u) (.conj (rawAvoidFormula cut v) (.allSet
    (.implies (.conj (.member u 0) (.allFO (.allFO
      (.implies (.conj (rawAvoidFormula (liftVertexCut (liftVertexCut cut)) 1)
        (.conj (rawAvoidFormula (liftVertexCut (liftVertexCut cut)) 0)
          (capturedLinkFormula I.lift 1 0)))
        (.implies (.member 1 0) (.member 0 0)))))) (.member v 0))))

@[simp] theorem eval_capturedConnectedFormula {D : Model} (I : LinkIndices k b)
    (cut : Option (Fin a)) (u v : Fin a) (env : Fin a → IncidenceOwnership.Element D)
    (sets : Fin b → IncSet D) :
    ActualEval AtomEval (capturedConnectedFormula I cut u v) env sets ↔
      Walk (RawLink I sets) (Avoid (vertexCutValue env cut)) (env u) (env v) := by
  simp only [capturedConnectedFormula,ActualEval,eval_rawAvoidFormula,
    eval_capturedLinkFormula,rawLink_lift,vertexCutValue_lift,Fin.cases_zero,and_imp]
  exact closedWithin_iff_walk (RawLink I sets) (Avoid (vertexCutValue env cut)) (env u) (env v)

/-- Ancestry syntax now uses only original incidence atoms and unary sets. -/
def capturedPreorderFormula (I : LinkIndices k b) (x y : Fin a) : IFormula a b :=
  .allFO (.implies (.member 0 I.roots)
    (.implies (capturedConnectedFormula I none y.succ 0)
      (.neg (capturedConnectedFormula I (some x.succ) y.succ 0))))

def capturedEarlierFormula (I : LinkIndices k b) (x y : Fin a) : IFormula a b :=
  .conj (capturedPreorderFormula I x y) (.neg (.equal x y))

def RawRootSeparator {D : Model} (I : LinkIndices k b) (sets : Fin b → IncSet D)
    (x y : IncidenceOwnership.Element D) : Prop :=
  ∀ r, sets I.roots r → Walk (RawLink I sets) (fun _ => True) y r →
    ¬ Walk (RawLink I sets) (fun z => z ≠ x) y r

@[simp] theorem eval_capturedPreorderFormula {D : Model} (I : LinkIndices k b)
    (x y : Fin a) (env : Fin a → IncidenceOwnership.Element D) (sets : Fin b → IncSet D) :
    ActualEval AtomEval (capturedPreorderFormula I x y) env sets ↔
      RawRootSeparator I sets (env x) (env y) := by
  simp only [capturedPreorderFormula,ActualEval,eval_capturedConnectedFormula,
    Fin.cases_zero,Fin.cases_succ,vertexCutValue,Option.map]
  rfl

#print axioms eval_capturedConnectedFormula
#print axioms eval_capturedPreorderFormula
#print axioms eval_capturedLinkFormula
end StackSorting.CapturedLinkExtraction
