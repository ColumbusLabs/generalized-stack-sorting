import RootedForestPathExtraction
import SparseFiniteCopyRealization

/-!
Literal MSO extraction over a selected undirected forest vocabulary. Link and
root atoms are interpreted below by actual parent edges and fixed points.
This is the output-side extraction formula; realizing its link predicate from
captured decorations remains a separate obligation.
-/
namespace StackSorting.ConnectedConeNormalization
open GraphWidth SameVertexForest SparseEndpointMSO.FiniteCopy
variable {n : Nat}

inductive ForestAtom : Nat → Type
  | link : ForestAtom 2
  | root : ForestAtom 1
  | originalEdge : ForestAtom 2

abbrev ForestFormula := CopyFormula ForestAtom

def parentAtomEval (G : Graph n) (O : RankedOrder n) : {r : Nat} → ForestAtom r → (Fin r → Fin n) → Prop
  | _, .link, env => ParentAdj O (env 0) (env 1)
  | _, .root, env => O.parent (env 0) = env 0
  | _, .originalEdge, env => G.Adj (env 0) (env 1)

def linkFormula (u v : Fin a) : ForestFormula a b := .atom .link (Fin.cases u (fun _ => v))
def fixedRootFormula (u : Fin a) : ForestFormula a b := .atom .root (fun _ => u)

def avoidFormula (cut : Option (Fin a)) (u : Fin a) : ForestFormula a b :=
  match cut with
  | none => .truth
  | some x => .neg (.equal u x)

def Avoid {α : Type} (cut : Option α) (u : α) : Prop :=
  match cut with
  | none => True
  | some x => u ≠ x

def liftVertexCut (cut : Option (Fin a)) : Option (Fin (a+1)) := cut.map Fin.succ

def vertexCutValue (env : Fin a → α) (cut : Option (Fin a)) : Option α := cut.map env

@[simp] theorem vertexCutValue_lift (env : Fin a → α) (x : α) (cut : Option (Fin a)) :
    vertexCutValue (Fin.cases x env) (liftVertexCut cut) = vertexCutValue env cut := by
  cases cut <;> rfl

/-- Closed-set MSO connectivity, including both endpoint membership guards
when one displayed vertex is removed. -/
def vertexCutConnectedFormula (cut : Option (Fin a)) (u v : Fin a) : ForestFormula a b :=
  .conj (avoidFormula cut u) (.conj (avoidFormula cut v) (.allSet
    (.implies (.conj (.member u 0) (.allFO (.allFO
      (.implies (.conj (avoidFormula (liftVertexCut (liftVertexCut cut)) 1)
        (.conj (avoidFormula (liftVertexCut (liftVertexCut cut)) 0) (linkFormula 1 0)))
        (.implies (.member 1 0) (.member 0 0)))))) (.member v 0))))

/-- The two displayed original vertices remain free throughout extraction. -/
def preorderFormula (x y : Fin a) : ForestFormula a b :=
  .allFO (.implies (fixedRootFormula 0)
    (.implies (vertexCutConnectedFormula none y.succ 0)
      (.neg (vertexCutConnectedFormula (some x.succ) y.succ 0))))

/-- Uniform closed-set connectivity is exactly an actual finite guarded walk.
No connectivity or ancestor predicate is added as a primitive atom. -/
theorem closedWithin_iff_walk {α : Type} (A : α → α → Prop) (P : α → Prop) (x y : α) :
    (P x ∧ P y ∧ ∀ Z : α → Prop, Z x →
      (∀ u v, P u → P v → A u v → Z u → Z v) → Z y) ↔ Walk A P x y := by
  constructor
  · rintro ⟨hx,_,h⟩
    exact h (fun z => Walk A P x z) (.refl hx)
      (fun u v hu hv ha hp => hp.trans (.step hu ha (.refl hv)))
  · intro h
    refine ⟨h.start,h.finish,?_⟩
    intro Z hx hc
    induction h with
    | refl => exact hx
    | @step u v w hu huv tail ih => exact ih (hc u v hu tail.start huv hx)

@[simp] theorem eval_avoidFormula (G : Graph n) (O : RankedOrder n) (cut : Option (Fin a)) (u : Fin a)
    (env : Fin a → Fin n) (sets : Fin b → Fin n → Prop) :
    ActualEval (parentAtomEval G O) (avoidFormula cut u) env sets ↔
      Avoid (vertexCutValue env cut) (env u) := by
  cases cut <;> rfl

@[simp] theorem eval_linkFormula (G : Graph n) (O : RankedOrder n) (u v : Fin a)
    (env : Fin a → Fin n) (sets : Fin b → Fin n → Prop) :
    ActualEval (parentAtomEval G O) (linkFormula u v) env sets ↔ ParentAdj O (env u) (env v) := Iff.rfl

@[simp] theorem eval_vertexCutConnectedFormula (G : Graph n) (O : RankedOrder n)
    (cut : Option (Fin a)) (u v : Fin a)
    (env : Fin a → Fin n) (sets : Fin b → Fin n → Prop) :
    ActualEval (parentAtomEval G O) (vertexCutConnectedFormula cut u v) env sets ↔
      Walk (ParentAdj O) (Avoid (vertexCutValue env cut)) (env u) (env v) := by
  simp only [vertexCutConnectedFormula,ActualEval,eval_avoidFormula,eval_linkFormula,
    vertexCutValue_lift,Fin.cases_zero,and_imp]
  exact closedWithin_iff_walk (ParentAdj O) (Avoid (vertexCutValue env cut)) (env u) (env v)

@[simp] theorem eval_preorderFormula (G : Graph n) (O : RankedOrder n) (x y : Fin a)
    (env : Fin a → Fin n) (sets : Fin b → Fin n → Prop) :
    ActualEval (parentAtomEval G O) (preorderFormula x y) env sets ↔ Cone O (env x) (env y) := by
  simp only [preorderFormula,ActualEval,fixedRootFormula,parentAtomEval,
    eval_vertexCutConnectedFormula,Fin.cases_zero,Fin.cases_succ,vertexCutValue,Option.map]
  exact rootSeparator_iff O (env x) (env y)

/-- A single closed-set MSO formula with two free vertex variables extracts
exact ancestry of the actual normalized decomposition. This statement is
still over the explicitly named output forest vocabulary. -/
theorem normalized_preorderFormula (G : Graph n) (O : RankedOrder n) (x y : Fin n) :
    ActualEval (parentAtomEval G (normalizedOrder G O))
      (preorderFormula (b := 0) (0 : Fin 2) 1)
      (Fin.cases x (fun _ => y)) Fin.elim0 ↔ ReachCone G O x y := by
  exact (eval_preorderFormula _ _ _ _ _ _).trans (normalized_cone G O x y)

#print axioms eval_vertexCutConnectedFormula
#print axioms eval_preorderFormula
#print axioms normalized_preorderFormula
end StackSorting.ConnectedConeNormalization
