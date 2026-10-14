import MarginalIncidenceSyntax
import OwnerParameterMerge
import CapturedLinkParameters
import NestedFlatteningSyntax

namespace StackSorting.GraphWidth.MarginalA2.NestedSyntax
open SparseEndpointMSO SparseEndpointMSO.FiniteCopy SparseEndpointMSO.FiniteCopy.Parametric
open CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership
abbrev InputAtom := Syntax.OutputAtom
abbrev Form := CopyFormula InputAtom

/-- Carrier-generic incidence formulas are projected to actual marginal
vertex/edge/incidence atoms. Ownership is reversed from anchor-to-member to
the literal member-to-owner convention. No new relation oracle is introduced. -/
def project : CopyFormula (OwnerMerge.Atom IncidenceAtom) a b → Form a b
  | .truth => .truth
  | .equal i j => .equal i j
  | .member i X => .member i X
  | .atom (.belongs) args => .atom .owner (fun i => args (if i=0 then 1 else 0))
  | .atom (.loc .vertex) args => .atom .vertex args
  | .atom (.loc .edge) args => .atom .localEdge args
  | .atom (.loc .incidence) args => .atom .incidence args
  | .atom (.loc .insert) _ => .neg .truth
  | .atom (.loc .remove) _ => .neg .truth
  | .neg p => .neg (project p)
  | .conj p q => .conj (project p) (project q)
  | .implies p q => .implies (project p) (project q)
  | .existsFO p => .existsFO (project p)
  | .allFO p => .allFO (project p)
  | .allSet p => .allSet (project p)

def pair (u v : Fin a) : Fin 2 → Fin a := Fin.cases u (fun _ => v)
def unary (a : InputAtom 1) (u : Fin r) : Form r b := .atom a (fun _ => u)
def binary (a : InputAtom 2) (u v : Fin r) : Form r b := .atom a (pair u v)
def disj (p q : Form a b) : Form a b := .neg (.conj (.neg p) (.neg q))

/-- A local relation is evaluated only in the unique owner's incidence fiber.
All quantified vertices and edges are owner-guarded, including nested binders. -/
noncomputable def earlier (colors : Nat) (u v : Fin a) : Form a (CapturedLinkExtraction.parameterCount colors) :=
  .conj (unary .vertex u) (.conj (unary .vertex v)
  (.existsFO (.conj (binary .owner u.succ 0) (.conj (binary .owner v.succ 0)
    (project (OwnerMerge.relativize (capturedEarlierFormula (fixedIndices colors) (0 : Fin 2) 1)
      (pair u.succ v.succ) 0))))))

noncomputable def cone (colors : Nat) (u v : Fin a) : Form a (CapturedLinkExtraction.parameterCount colors) :=
  disj (.equal u v) (earlier colors u v)

noncomputable def forestParent (colors : Nat) (child parent : Fin a) : Form a (CapturedLinkExtraction.parameterCount colors) :=
  .conj (earlier colors parent child) (.neg (.existsFO
    (.conj (earlier colors parent.succ 0) (earlier colors 0 child.succ))))

noncomputable def forestRoot (colors : Nat) (v : Fin a) : Form a (CapturedLinkExtraction.parameterCount colors) :=
  .conj (unary .vertex v) (.neg (.existsFO (earlier colors 0 v.succ)))

def marginalAdj (u v : Fin a) : Form a b :=
  .conj (.neg (.equal u v)) (.existsFO (.conj (unary .localEdge 0)
    (.conj (binary .incidence u.succ 0) (binary .incidence v.succ 0))))

/-- Actual normalized region bags: the margin vertex and its external
original-marginal-graph neighborhood. The added local root has an empty bag. -/
noncomputable def localBag (colors : Nat) (v u : Fin a) : Form a (CapturedLinkExtraction.parameterCount colors) :=
  disj (.equal u v) (.conj (earlier colors u v) (.existsFO
    (.conj (cone colors v.succ 0) (marginalAdj u.succ 0))))

/-- Three graph-size-independent channels: retained original vertex/outer
node; normalized local vertex-node; artificial empty local root. -/
def domain : Fin 3 → Form 1 b := Fin.cases
  (disj (unary .vertex 0) (unary .outerNode 0))
  (Fin.cases (unary .vertex 0) (fun _ => unary .outerNode 0))

noncomputable def atom (colors : Nat) : {r : Nat} → Nested.Syntax.InputAtom r →
    (Fin r → Fin 3) → Form r (CapturedLinkExtraction.parameterCount colors)
  | _, .original, tags => if tags 0=0 then unary .vertex 0 else .neg .truth
  | _, .localNode, tags => if tags 0=1 ∨ tags 0=2 then .truth else .neg .truth
  | _, .localRoot, tags => if tags 0=2 then .truth else .neg .truth
  | _, .owner, tags =>
      if tags 0=1 ∧ tags 1=0 then binary .owner 0 1
      else if tags 0=2 ∧ tags 1=0 then .equal 0 1 else .neg .truth
  | _, .margin, tags => if tags 0=0 ∧ tags 1=0 then binary .margin 0 1 else .neg .truth
  | _, .adhesion, tags => if tags 0=0 ∧ tags 1=0 then binary .adhesion 0 1 else .neg .truth
  | _, .outerParent, tags => if tags 0=0 ∧ tags 1=0 then binary .outerParent 0 1 else .neg .truth
  | _, .localParent, tags =>
      if tags 0=1 ∧ tags 1=1 then forestParent colors 0 1
      else if tags 0=1 ∧ tags 1=2 then .conj (forestRoot colors 0) (binary .owner 0 1)
      else .neg .truth
  | _, .localBag, tags => if tags 0=1 ∧ tags 1=0 then .conj (unary .vertex 1) (localBag colors 0 1) else .neg .truth
  | _, .originalEdge, tags => if tags 0=0 ∧ tags 1=0 then binary .originalAdj 0 1 else .neg .truth

noncomputable def interpretation (colors : Nat) :
    CopyInterpretation InputAtom Nested.Syntax.InputAtom 3 (CapturedLinkExtraction.parameterCount colors) where
  domain := domain
  atom := atom colors

/-- The full fixed parameter arithmetic after the marginal and local stages.
There is no factor depending on the number of outer owners. -/
theorem arity (c d W colors b : Nat) :
    (d+(W+W*W)*c)+CapturedLinkExtraction.parameterCount colors*((1+W*W)*c)+b*(3*((1+W*W)*c)) =
      d+((W+W*W)+(CapturedLinkExtraction.parameterCount colors+b*3)*(1+W*W))*c := by
  simp only [Nat.add_mul,Nat.mul_assoc,Nat.add_assoc]

#print axioms interpretation
#print axioms arity
end StackSorting.GraphWidth.MarginalA2.NestedSyntax
