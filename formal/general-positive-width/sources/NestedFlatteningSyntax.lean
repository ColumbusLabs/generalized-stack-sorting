import SparseParametricComposition

namespace StackSorting.GraphWidth.Nested.Syntax

private theorem cases_one {α : Type} {n : Nat} (x : α) (env : Fin (n+1) → α) :
    Fin.cases x env (1 : Fin (n+2)) = env 0 := rfl
open StackSorting.SparseEndpointMSO.FiniteCopy
open StackSorting.SparseEndpointMSO.FiniteCopy.Parametric

/-- Literal vocabulary of a nested decomposition. `localParent` is the strict
(nonroot) local parent edge; local roots are marked separately. -/
inductive InputAtom : Nat → Type where
  | original : InputAtom 1
  | localNode : InputAtom 1
  | localRoot : InputAtom 1
  | owner : InputAtom 2
  | margin : InputAtom 2
  | adhesion : InputAtom 2
  | outerParent : InputAtom 2
  | localParent : InputAtom 2
  | localBag : InputAtom 2
  | originalEdge : InputAtom 2

structure Relations (α : Type) where
  original : α → Prop
  localNode : α → Prop
  localRoot : α → Prop
  owner : α → α → Prop
  margin : α → α → Prop
  adhesion : α → α → Prop
  outerParent : α → α → Prop
  localParent : α → α → Prop
  localBag : α → α → Prop
  originalEdge : α → α → Prop

def atoms (R : Relations α) : {r : Nat} → InputAtom r → (Fin r → α) → Prop
  | _, .original, v => R.original (v 0)
  | _, .localNode, v => R.localNode (v 0)
  | _, .localRoot, v => R.localRoot (v 0)
  | _, .owner, v => R.owner (v 0) (v 1)
  | _, .margin, v => R.margin (v 0) (v 1)
  | _, .adhesion, v => R.adhesion (v 0) (v 1)
  | _, .outerParent, v => R.outerParent (v 0) (v 1)
  | _, .localParent, v => R.localParent (v 0) (v 1)
  | _, .localBag, v => R.localBag (v 0) (v 1)
  | _, .originalEdge, v => R.originalEdge (v 0) (v 1)

def pair (i j : Fin a) : Fin 2 → Fin a := fun q => if q=0 then i else j
def unary (A : InputAtom 1) (i : Fin a) : CopyFormula InputAtom a b := .atom A (fun _ => i)
def binary (A : InputAtom 2) (i j : Fin a) : CopyFormula InputAtom a b := .atom A (pair i j)
def disj (p q : CopyFormula InputAtom a b) : CopyFormula InputAtom a b :=
  .neg (.conj (.neg p) (.neg q))

/-- The shared clique is defined from the actual child adhesion and the
actual parent's margin. It is not a new primitive interpreted relation. -/
def interfaceAt (child vertex : Fin a) : CopyFormula InputAtom a b :=
  .conj (binary .adhesion child vertex)
    (.existsFO (.conj (binary .outerParent child.succ 0) (binary .margin 0 vertex.succ)))

def coversAt (child bag : Fin a) : CopyFormula InputAtom a b :=
  .allFO (.implies (interfaceAt child.succ 0) (binary .localBag bag.succ 0))

/-- The root-nearest covering member is characterized by coverage and
noncoverage at the strict local parent. This never asserts uniqueness of all
covering bags. The combinatorial clique theorem supplies exactness. -/
def nearestAt (child bag : Fin a) : CopyFormula InputAtom a b :=
  .conj (coversAt child bag)
    (disj (unary .localRoot bag)
      (.allFO (.implies (binary .localParent bag.succ 0)
        (.neg (coversAt child.succ 0)))))

def crossParentAt (childBag parentBag : Fin a) : CopyFormula InputAtom a b :=
  .conj (unary .localRoot childBag)
    (.existsFO (.existsFO
      (.conj (binary .owner childBag.succ.succ 1)
        (.conj (binary .outerParent 1 0)
          (.conj (binary .owner parentBag.succ.succ 0)
            (nearestAt 1 parentBag.succ.succ))))))

def flattenedParentAt (childBag parentBag : Fin a) : CopyFormula InputAtom a b :=
  disj (binary .localParent childBag parentBag) (crossParentAt childBag parentBag)

def flattenedBagAt (bag vertex : Fin a) : CopyFormula InputAtom a b :=
  disj (binary .localBag bag vertex)
    (.existsFO (.conj (binary .owner bag.succ 0) (binary .adhesion 0 vertex.succ)))

def Interface (R : Relations α) (child vertex : α) : Prop :=
  R.adhesion child vertex ∧ ∃ p, R.outerParent child p ∧ R.margin p vertex

def Covers (R : Relations α) (child bag : α) : Prop :=
  ∀ v, Interface R child v → R.localBag bag v

def Nearest (R : Relations α) (child bag : α) : Prop :=
  Covers R child bag ∧ (R.localRoot bag ∨
    ∀ p, R.localParent bag p → ¬ Covers R child p)

def CrossParent (R : Relations α) (childBag parentBag : α) : Prop :=
  R.localRoot childBag ∧ ∃ c p, R.owner childBag c ∧ R.outerParent c p ∧
    R.owner parentBag p ∧ Nearest R c parentBag

theorem eval_interfaceAt (R : Relations α) (child vertex : Fin a)
    (env : Fin a → α) (sets : Fin b → α → Prop) :
    ActualEval (atoms R) (interfaceAt child vertex) env sets ↔
      Interface R (env child) (env vertex) := by
  simp [interfaceAt,Interface,binary,pair,ActualEval,atoms]

theorem eval_coversAt (R : Relations α) (child bag : Fin a)
    (env : Fin a → α) (sets : Fin b → α → Prop) :
    ActualEval (atoms R) (coversAt child bag) env sets ↔
      Covers R (env child) (env bag) := by
  simp [coversAt,Covers,ActualEval,eval_interfaceAt,binary,pair,atoms]

theorem eval_nearestAt (R : Relations α) (child bag : Fin a)
    (env : Fin a → α) (sets : Fin b → α → Prop) :
    ActualEval (atoms R) (nearestAt child bag) env sets ↔
      Nearest R (env child) (env bag) := by
  classical
  simp [nearestAt,Nearest,ActualEval,eval_coversAt,disj,unary,binary,pair,atoms]
  tauto

theorem eval_crossParentAt (R : Relations α) (childBag parentBag : Fin a)
    (env : Fin a → α) (sets : Fin b → α → Prop) :
    ActualEval (atoms R) (crossParentAt childBag parentBag) env sets ↔
      CrossParent R (env childBag) (env parentBag) := by
  simp [crossParentAt,CrossParent,ActualEval,eval_nearestAt,unary,binary,pair,atoms,cases_one]

theorem eval_flattenedParentAt (R : Relations α) (childBag parentBag : Fin a)
    (env : Fin a → α) (sets : Fin b → α → Prop) :
    ActualEval (atoms R) (flattenedParentAt childBag parentBag) env sets ↔
      R.localParent (env childBag) (env parentBag) ∨
        CrossParent R (env childBag) (env parentBag) := by
  classical
  simp [flattenedParentAt,disj,ActualEval,eval_crossParentAt,binary,pair,atoms]
  tauto

theorem eval_flattenedBagAt (R : Relations α) (bag vertex : Fin a)
    (env : Fin a → α) (sets : Fin b → α → Prop) :
    ActualEval (atoms R) (flattenedBagAt bag vertex) env sets ↔
      R.localBag (env bag) (env vertex) ∨
        ∃ x, R.owner (env bag) x ∧ R.adhesion x (env vertex) := by
  classical
  simp [flattenedBagAt,disj,ActualEval,binary,pair,atoms]
  tauto

inductive OutputAtom : Nat → Type where
  | original : OutputAtom 1
  | node : OutputAtom 1
  | parent : OutputAtom 2
  | bag : OutputAtom 2
  | originalEdge : OutputAtom 2

/-- One-copy, zero-new-parameter flattening stage. Every output atom is an
explicit formula over the earlier nested structure. -/
def interpretation : CopyInterpretation InputAtom OutputAtom 1 0 where
  domain _ := disj (unary .original 0) (unary .localNode 0)
  atom A _ := match A with
    | .original => unary .original 0
    | .node => unary .localNode 0
    | .parent => flattenedParentAt 0 1
    | .bag => flattenedBagAt 0 1
    | .originalEdge => binary .originalEdge 0 1

#print axioms eval_nearestAt
#print axioms eval_flattenedParentAt
#print axioms eval_flattenedBagAt
end StackSorting.GraphWidth.Nested.Syntax
