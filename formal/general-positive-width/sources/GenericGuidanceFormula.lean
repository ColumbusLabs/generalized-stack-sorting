import GenericGuidanceIncidence

/-! The existing literal X/F/R formulas are carrier-generic. Their semantics
is proved here on genuine incidence systems, rather than falsely constructing
a sparse chronological model for each marginal. -/
namespace StackSorting.GuidedPathwidth.GenericIncidence.System
open SparseEndpointMSO SparseEndpointMSO.FiniteCopy SparseEndpointMSO.Guidance
variable {V : Type} {G : SimpleGraph V} (S : System G)

def filteredGraph (X F : S.IncSet) (cut : Option (S.Element × S.Element)) :
    SimpleGraph S.Element where
  Adj u v := S.step X F u v ∧ PairAllowed cut u v
  symm := ⟨by
    intro u v h
    refine ⟨S.step_symm h.1,?_⟩
    cases cut with
    | none => trivial
    | some p =>
      rcases p with ⟨a,b⟩
      rintro (⟨ha,hb⟩ | ⟨ha,hb⟩)
      · exact h.2 (Or.inr ⟨hb,ha⟩)
      · exact h.2 (Or.inl ⟨hb,ha⟩)⟩
  loopless := ⟨fun _ h => h.1.2.2.2.2.1 rfl⟩

@[simp] theorem filteredGraph_none (X F : S.IncSet) :
    S.filteredGraph X F none = S.selectedGraph X F := by
  ext u v
  simp [filteredGraph,selectedGraph,PairAllowed]

theorem filteredGraph_pair (X F : S.IncSet) (a b : S.Element) :
    S.filteredGraph X F (some (a,b)) = (S.selectedGraph X F).deleteEdges {s(a,b)} := by
  ext u v
  simp [filteredGraph,selectedGraph,PairAllowed]

def connected (X F : S.IncSet) (cut : Option (S.Element × S.Element)) (u v : S.Element) : Prop :=
  X u ∧ X v ∧ (S.filteredGraph X F cut).Reachable u v

@[simp] theorem eval_stepFormula (X F : Fin b) (u v : Fin a)
    (env : Fin a → S.Element) (sets : Fin b → S.IncSet) :
    ActualEval S.atoms (stepFormula X F u v) env sets ↔
      S.step (sets X) (sets F) (env u) (env v) := by
  simp [stepFormula,vertexFormula,edgeFormula,incidentFormula,ActualEval,atoms,step]

@[simp] theorem eval_pairFormula (cut : Option (Fin a × Fin a)) (u v : Fin a)
    (env : Fin a → S.Element) (sets : Fin b → S.IncSet) :
    ActualEval S.atoms (pairFormula cut u v) env sets ↔
      PairAllowed (cutValue env cut) (env u) (env v) := by
  classical
  cases cut with
  | none => rfl
  | some p =>
    rcases p with ⟨p,q⟩
    simp [pairFormula,PairAllowed,cutValue,orFormula,ActualEval]

@[simp] theorem eval_filteredStepFormula (X F : Fin b)
    (cut : Option (Fin a × Fin a)) (u v : Fin a)
    (env : Fin a → S.Element) (sets : Fin b → S.IncSet) :
    ActualEval S.atoms (filteredStepFormula X F cut u v) env sets ↔
      (S.filteredGraph (sets X) (sets F) (cutValue env cut)).Adj (env u) (env v) := by
  simp [filteredStepFormula,ActualEval,filteredGraph]

@[simp] theorem eval_connectedFormula (X F : Fin b)
    (cut : Option (Fin a × Fin a)) (u v : Fin a)
    (env : Fin a → S.Element) (sets : Fin b → S.IncSet) :
    ActualEval S.atoms (connectedFormula X F cut u v) env sets ↔
      S.connected (sets X) (sets F) (cutValue env cut) (env u) (env v) := by
  simp only [connectedFormula,ActualEval,eval_filteredStepFormula,
    Fin.cases_zero,Fin.cases_succ,cases_one,cutValue_lift]
  unfold connected
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  simpa only [Guidance.ClosedReach,and_imp,SimpleGraph.Reachable] using closedReach_iff_walk
    (S.filteredGraph (sets X) (sets F) (cutValue env cut)) (env u) (env v)

@[simp] theorem eval_rootFormula (X F R : Fin b) (u r : Fin a)
    (env : Fin a → S.Element) (sets : Fin b → S.IncSet) :
    ActualEval S.atoms (rootFormula X F R u r) env sets ↔
      S.rootRelation (sets X) (sets F) (sets R) (env u) (env r) := by
  simp [rootFormula,ActualEval,rootRelation,connected,cutValue]

@[simp] theorem eval_typedFormula (X F R : Fin b)
    (env : Fin a → S.Element) (sets : Fin b → S.IncSet) :
    ActualEval S.atoms (typedFormula X F R) env sets ↔ S.Typed (sets X) (sets F) (sets R) := by
  simp only [typedFormula,ActualEval,vertexFormula,edgeFormula,incidentFormula,
    atoms,Fin.cases_zero]
  constructor
  · rintro ⟨hv,he,hr,hi⟩
    exact ⟨hv,he,hr,fun e u hF hI => hi e u ⟨hF,hI⟩⟩
  · intro h
    exact ⟨h.vertices,h.edges,h.roots,fun e u he => h.endpoints e u he.1 he.2⟩

@[simp] theorem eval_rootedFormula (X F R : Fin b)
    (env : Fin a → S.Element) (sets : Fin b → S.IncSet) :
    ActualEval S.atoms (rootedFormula X F R) env sets ↔
      S.Typed (sets X) (sets F) (sets R) ∧
        ∀ u, sets X u → ∃! r, S.rootRelation (sets X) (sets F) (sets R) u r := by
  simp [rootedFormula,ActualEval,ExistsUnique]

@[simp] theorem eval_acyclicFormula (X F : Fin b)
    (env : Fin a → S.Element) (sets : Fin b → S.IncSet) :
    ActualEval S.atoms (acyclicFormula X F) env sets ↔
      (S.selectedGraph (sets X) (sets F)).IsAcyclic := by
  simp only [acyclicFormula,ActualEval,eval_stepFormula,eval_connectedFormula,Fin.cases_zero]
  change (∀ u v, S.step (sets X) (sets F) u v →
    ¬ S.connected (sets X) (sets F) (some (u,v)) u v) ↔ _
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  constructor
  · intro h u v huv
    rw [SimpleGraph.isBridge_iff]
    intro hw
    exact h u v huv ⟨huv.2.1,huv.2.2.2.1,by rw [filteredGraph_pair]; exact hw⟩
  · intro h u v huv hc
    have hb := h huv
    rw [SimpleGraph.isBridge_iff] at hb
    apply hb
    rw [← filteredGraph_pair]
    exact hc.2.2

/-- Exact same fixed forest-validation formula on every genuine marginal
incidence carrier; the sparse model's laws are not assumptions. -/
theorem eval_forestFormula (X F R : Fin b)
    (env : Fin a → S.Element) (sets : Fin b → S.IncSet) :
    ActualEval S.atoms (forestFormula X F R) env sets ↔
      (⟨sets X,sets F,sets R⟩ : S.ColorData).Valid := by
  simp only [forestFormula,ActualEval,eval_rootedFormula,eval_acyclicFormula,ColorData.Valid]
  tauto

#print axioms eval_rootFormula
#print axioms eval_forestFormula
end StackSorting.GuidedPathwidth.GenericIncidence.System
