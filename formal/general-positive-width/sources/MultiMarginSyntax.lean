import SparseParametricComposition
import ForestPreorderMSO

namespace StackSorting.GraphWidth.MultiMargin.Syntax
open StackSorting.SparseEndpointMSO.FiniteCopy
open StackSorting.SparseEndpointMSO.FiniteCopy.Parametric
open StackSorting.ConnectedConeNormalization

/-- Completed incidence retains the distinction between original and extra
edges. There is deliberately no parent, margin, component or bag input atom. -/
inductive InputAtom : Nat → Type where
  | vertex : InputAtom 1
  | originalEdge : InputAtom 1
  | edge : InputAtom 1
  | incidence : InputAtom 2

structure Relations (α : Type) where
  vertex : α → Prop
  originalEdge : α → Prop
  edge : α → Prop
  incidence : α → α → Prop

def atoms (R : Relations α) : {r : Nat} → InputAtom r → (Fin r → α) → Prop
  | _, .vertex, env => R.vertex (env 0)
  | _, .originalEdge, env => R.originalEdge (env 0)
  | _, .edge, env => R.edge (env 0)
  | _, .incidence, env => R.incidence (env 0) (env 1)

abbrev Form := CopyFormula InputAtom

def unary (A : InputAtom 1) (u : Fin a) : Form a b := .atom A (fun _ => u)
def incident (u e : Fin a) : Form a b := .atom .incidence (fun q => if q=0 then u else e)
def disj (p q : Form a b) : Form a b := .neg (.conj (.neg p) (.neg q))

structure Indices (b : Nat) where
  M : Fin b
  K : Fin b
  R : Fin b
  N : Fin b

def Indices.lift (I : Indices b) : Indices (b+1) :=
  ⟨I.M.succ,I.K.succ,I.R.succ,I.N.succ⟩

def fixed : Indices 4 := ⟨0,1,2,3⟩

inductive Channel where | marginal | crossing | union

def selectedEdge (I : Indices b) : Channel → Fin a → Form a b
  | .marginal, e => .member e I.M
  | .crossing, e => .member e I.K
  | .union, e => disj (.member e I.M) (.member e I.K)

def link (I : Indices b) (channel : Channel) (u v : Fin a) : Form a b :=
  .conj (unary .vertex u) (.conj (unary .vertex v) (.conj (.neg (.equal u v))
    (.existsFO (.conj (unary .edge 0) (.conj (selectedEdge I channel 0)
      (.conj (incident u.succ 0) (incident v.succ 0)))))))

def Selected (I : Indices b) (sets : Fin b → α → Prop) : Channel → α → Prop
  | .marginal, e => sets I.M e
  | .crossing, e => sets I.K e
  | .union, e => sets I.M e ∨ sets I.K e

def Link (R : Relations α) (I : Indices b) (sets : Fin b → α → Prop)
    (channel : Channel) (u v : α) : Prop :=
  R.vertex u ∧ R.vertex v ∧ u≠v ∧ ∃ e, R.edge e ∧ Selected I sets channel e ∧
    R.incidence u e ∧ R.incidence v e

theorem eval_selectedEdge (R : Relations α) (I : Indices b) (channel : Channel)
    (e : Fin a) (env : Fin a → α) (sets : Fin b → α → Prop) :
    ActualEval (atoms R) (selectedEdge I channel e) env sets ↔ Selected I sets channel (env e) := by
  classical
  cases channel <;> simp only [selectedEdge,Selected,disj,ActualEval,not_and_or,not_not]

theorem eval_link (R : Relations α) (I : Indices b) (channel : Channel)
    (u v : Fin a) (env : Fin a → α) (sets : Fin b → α → Prop) :
    ActualEval (atoms R) (link I channel u v) env sets ↔ Link R I sets channel (env u) (env v) := by
  simp [link,Link,unary,incident,ActualEval,atoms,eval_selectedEdge]

def avoid (cut : Option (Fin a)) (u : Fin a) : Form a b :=
  match cut with | none => .truth | some x => .neg (.equal u x)

def connected (I : Indices b) (channel : Channel) (cut : Option (Fin a))
    (u v : Fin a) : Form a b :=
  .conj (unary .vertex u) (.conj (unary .vertex v)
    (.conj (avoid cut u) (.conj (avoid cut v) (.allSet
      (.implies (.conj (.member u 0) (.allFO (.allFO
        (.implies (.conj (avoid (liftVertexCut (liftVertexCut cut)) 1)
          (.conj (avoid (liftVertexCut (liftVertexCut cut)) 0) (link I.lift channel 1 0)))
          (.implies (.member 1 0) (.member 0 0)))))) (.member v 0))))))

def Connected (R : Relations α) (I : Indices b) (sets : Fin b → α → Prop)
    (channel : Channel) (cut : Option α) (u v : α) : Prop :=
  R.vertex u ∧ R.vertex v ∧ Walk (Link R I sets channel) (Avoid cut) u v

@[simp] theorem selected_lift (I : Indices b) (sets : Fin b → α → Prop) (X : α → Prop)
    (c : Channel) (e : α) : Selected I.lift (Fin.cases X sets) c e ↔ Selected I sets c e := by
  cases c <;> rfl

@[simp] theorem link_lift (R : Relations α) (I : Indices b) (sets : Fin b → α → Prop)
    (X : α → Prop) (c : Channel) (u v : α) :
    Link R I.lift (Fin.cases X sets) c u v ↔ Link R I sets c u v := by
  simp only [Link,selected_lift]

@[simp] theorem eval_avoid (R : Relations α) (cut : Option (Fin a)) (u : Fin a)
    (env : Fin a → α) (sets : Fin b → α → Prop) :
    ActualEval (atoms R) (avoid cut u) env sets ↔ Avoid (vertexCutValue env cut) (env u) := by
  cases cut <;> rfl

theorem eval_connected (R : Relations α) (I : Indices b) (channel : Channel)
    (cut : Option (Fin a)) (u v : Fin a) (env : Fin a → α) (sets : Fin b → α → Prop) :
    ActualEval (atoms R) (connected I channel cut u v) env sets ↔
      Connected R I sets channel (vertexCutValue env cut) (env u) (env v) := by
  simp only [connected,Connected,ActualEval,unary,atoms,eval_avoid,eval_link,link_lift,
    vertexCutValue_lift,Fin.cases_zero,and_imp]
  exact and_congr Iff.rfl (and_congr Iff.rfl
    (closedWithin_iff_walk (Link R I sets channel) (Avoid (vertexCutValue env cut)) (env u) (env v)))

/-- Reachable-root existence is explicit, preventing vacuous ancestry when
R is empty. Deletion connectivity retains both endpoint guards. -/
def ancestor (I : Indices b) (x y : Fin a) : Form a b :=
  .conj (unary .vertex x) (.conj
    (.existsFO (.conj (.member 0 I.R) (connected I .union none y.succ 0)))
    (.allFO (.implies (.member 0 I.R)
      (.implies (connected I .union none y.succ 0)
        (.neg (connected I .union (some x.succ) y.succ 0))))))

def Ancestor (R : Relations α) (I : Indices b) (sets : Fin b → α → Prop) (x y : α) : Prop :=
  R.vertex x ∧ (∃ r, sets I.R r ∧ Connected R I sets .union none y r) ∧
    ∀ r, sets I.R r → Connected R I sets .union none y r →
      ¬ Connected R I sets .union (some x) y r

theorem eval_ancestor (R : Relations α) (I : Indices b)
    (x y : Fin a) (env : Fin a → α) (sets : Fin b → α → Prop) :
    ActualEval (atoms R) (ancestor I x y) env sets ↔ Ancestor R I sets (env x) (env y) := by
  simp only [ancestor,Ancestor,ActualEval,unary,atoms,eval_connected,
    Fin.cases_zero,Fin.cases_succ,vertexCutValue,Option.map]

def parent (I : Indices b) (child par : Fin a) : Form a b :=
  .existsFO (.conj (link I .crossing child.succ 0)
    (.conj (ancestor I 0 child.succ) (connected I .marginal none par.succ 0)))

def Parent (R : Relations α) (I : Indices b) (sets : Fin b → α → Prop) (child par : α) : Prop :=
  ∃ w, Link R I sets .crossing child w ∧ Ancestor R I sets w child ∧
    Connected R I sets .marginal none par w

def originalAdjacent (u v : Fin a) : Form a b :=
  .conj (.neg (.equal u v)) (.existsFO (.conj (unary .originalEdge 0)
    (.conj (incident u.succ 0) (incident v.succ 0))))

def OriginalAdjacent (R : Relations α) (u v : α) : Prop :=
  u≠v ∧ ∃ e, R.originalEdge e ∧ R.incidence u e ∧ R.incidence v e

def bag (I : Indices b) (node v : Fin a) : Form a b :=
  disj (connected I .marginal none node v)
    (.conj (.neg (ancestor I node v)) (.existsFO
      (.conj (ancestor I node.succ 0) (originalAdjacent v.succ 0))))

def Bag (R : Relations α) (I : Indices b) (sets : Fin b → α → Prop) (node v : α) : Prop :=
  Connected R I sets .marginal none node v ∨ (¬ Ancestor R I sets node v ∧
    ∃ u, Ancestor R I sets node u ∧ OriginalAdjacent R v u)

theorem eval_parent (R : Relations α) (I : Indices b)
    (child par : Fin a) (env : Fin a → α) (sets : Fin b → α → Prop) :
    ActualEval (atoms R) (parent I child par) env sets ↔ Parent R I sets (env child) (env par) := by
  simp only [parent,Parent,ActualEval,eval_link,eval_ancestor,eval_connected,
    Fin.cases_zero,Fin.cases_succ,vertexCutValue,Option.map]

theorem eval_originalAdjacent (R : Relations α)
    (u v : Fin a) (env : Fin a → α) (sets : Fin b → α → Prop) :
    ActualEval (atoms R) (originalAdjacent u v) env sets ↔ OriginalAdjacent R (env u) (env v) := by
  simp [originalAdjacent,OriginalAdjacent,unary,incident,ActualEval,atoms]

theorem eval_bag (R : Relations α) (I : Indices b)
    (node v : Fin a) (env : Fin a → α) (sets : Fin b → α → Prop) :
    ActualEval (atoms R) (bag I node v) env sets ↔ Bag R I sets (env node) (env v) := by
  classical
  simp only [bag,Bag,disj,ActualEval,not_and_or,not_or,not_not,eval_connected,eval_ancestor,
    eval_originalAdjacent,Fin.cases_zero,Fin.cases_succ,vertexCutValue,Option.map]

inductive OutputAtom : Nat → Type where
  | vertex : OutputAtom 1
  | originalEdge : OutputAtom 1
  | node : OutputAtom 1
  | incidence : OutputAtom 2
  | margin : OutputAtom 2
  | component : OutputAtom 2
  | parent : OutputAtom 2
  | bag : OutputAtom 2

/-- Two-copy outer stage: original graph elements in copy zero and exactly
the selected representative nodes in copy one. Four genuine unary parameters
encode M, K, R and the representatives. All other relations are literal MSO. -/
def interpretation : CopyInterpretation InputAtom OutputAtom 2 4 where
  domain tag := if tag=0 then disj (unary .vertex 0) (unary .originalEdge 0)
    else .conj (unary .vertex 0) (.member 0 fixed.N)
  atom A tags := match A with
    | .vertex => if tags 0=0 then unary .vertex 0 else .neg .truth
    | .originalEdge => if tags 0=0 then unary .originalEdge 0 else .neg .truth
    | .node => if tags 0=1 then .truth else .neg .truth
    | .incidence => if tags 0=0 ∧ tags 1=0 then
        .conj (unary .originalEdge 1) (incident 0 1) else .neg .truth
    | .margin => if tags 0=1 ∧ tags 1=0 then connected fixed .marginal none 0 1 else .neg .truth
    | .component => if tags 0=1 ∧ tags 1=0 then ancestor fixed 0 1 else .neg .truth
    | .parent => if tags 0=1 ∧ tags 1=1 then parent fixed 0 1 else .neg .truth
    | .bag => if tags 0=1 ∧ tags 1=0 then bag fixed 0 1 else .neg .truth

#print axioms eval_connected
#print axioms eval_ancestor
#print axioms eval_parent
#print axioms eval_bag
end StackSorting.GraphWidth.MultiMargin.Syntax
