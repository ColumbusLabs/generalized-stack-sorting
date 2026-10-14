import MultiMarginSyntax
import MarginalEdgeCodes

namespace StackSorting.GraphWidth.MarginalA2.Syntax
open SparseEndpointMSO.FiniteCopy SparseEndpointMSO.FiniteCopy.Parametric
abbrev InputAtom := MultiMargin.Syntax.OutputAtom
abbrev Form := CopyFormula InputAtom

abbrev Tag (W : Nat) := Unit ⊕ (Fin W × Fin W)
abbrev Parameter (W : Nat) := Fin W ⊕ (Fin W × Fin W)
abbrev copies (W : Nat) := Fintype.card (Tag W)
abbrev parameters (W : Nat) := Fintype.card (Parameter W)
noncomputable def tagEquiv (W : Nat) : Tag W ≃ Fin (copies W) := Fintype.equivFin _
noncomputable def parameterEquiv (W : Nat) : Parameter W ≃ Fin (parameters W) := Fintype.equivFin _

structure Indices (W b : Nat) where
  color : Fin W → Fin b
  selected : Fin W → Fin W → Fin b

noncomputable def fixed (W : Nat) : Indices W (parameters W) :=
  ⟨fun i => parameterEquiv W (.inl i),fun i j => parameterEquiv W (.inr (i,j))⟩

def pair (u v : Fin a) : Fin 2 → Fin a := fun i => if i=0 then u else v
def unary (A : InputAtom 1) (u : Fin a) : Form a b := .atom A (fun _ => u)
def binary (A : InputAtom 2) (u v : Fin a) : Form a b := .atom A (pair u v)
def disj (p q : Form a b) : Form a b := .neg (.conj (.neg p) (.neg q))

/-- An adhesion is bag minus margin, expressed in the literal outer vocabulary. -/
def adhesion (y u : Fin a) : Form a b :=
  .conj (binary .bag y u) (.neg (binary .margin y u))

/-- Both original adjacency and its complement retain endpoint inequality. -/
def originalAdj (u v : Fin a) : Form a b :=
  .conj (.neg (.equal u v)) (.existsFO (.conj (unary .originalEdge 0)
    (.conj (binary .incidence u.succ 0) (binary .incidence v.succ 0))))

/-- Child adhesion endpoints are required to lie in that child's actual
parent margin. This rules out unrelated ancestor adhesion vertices. -/
def interfaceAt (y u : Fin a) : Form a b :=
  .conj (adhesion y u) (.existsFO (.conj (binary .parent y.succ 0)
    (binary .margin 0 u.succ)))

def coloredEndpoint (I : Indices W b) (i : Fin W) (y u : Fin a) : Form a b :=
  .conj (interfaceAt y u) (.member u (I.color i))

def candidatePair (I : Indices W b) (i j : Fin W) (y u v : Fin a) : Form a b :=
  .conj (.neg (.equal u v)) (.conj (.neg (originalAdj u v))
    (.conj (coloredEndpoint I i y u) (coloredEndpoint I j y v)))

def candidateValid (I : Indices W b) (i j : Fin W) (y : Fin a) : Form a b :=
  .existsFO (.existsFO (candidatePair I i j y.succ.succ 1 0))

/-- Raw old incidence elements and old nodes are retained once. Selected
synthetic codes are the only added elements. The realization below uses the
explicitly constructed selector tuple. The optional validity formula is not
asserted here to classify arbitrary parameter tuples; no quotient is used. -/
def domain (I : Indices W b) : Tag W → Form 1 b
  | .inl _ => .truth
  | .inr (i,j) => .member 0 (I.selected i j)

/-- Internal original edges have a unique owner because actual margins
partition vertices. Crossing original edges remain available as auxiliary
objects for original-graph adjacency, but are not in any local carrier. -/
def originalOwner (e x : Fin a) : Form a b :=
  .conj (unary .originalEdge e) (.existsFO (.existsFO
    (.conj (.neg (.equal 1 0))
      (.conj (binary .incidence 1 e.succ.succ)
        (.conj (binary .incidence 0 e.succ.succ)
          (.conj (binary .margin x.succ.succ 1) (binary .margin x.succ.succ 0)))))))

def oldOwner (z x : Fin a) : Form a b := disj (binary .margin x z) (originalOwner z x)

def oldLocalEdge (e : Fin a) : Form a b := .existsFO (originalOwner e.succ 0)

inductive OutputAtom : Nat → Type where
  | vertex : OutputAtom 1
  | localEdge : OutputAtom 1
  | outerNode : OutputAtom 1
  | incidence : OutputAtom 2
  | owner : OutputAtom 2
  | margin : OutputAtom 2
  | adhesion : OutputAtom 2
  | outerParent : OutputAtom 2
  | originalAdj : OutputAtom 2

def atom (I : Indices W b) : {r : Nat} → OutputAtom r → (Fin r → Tag W) → Form r b
  | _, .vertex, tags => match tags 0 with
    | .inl _ => unary .vertex 0 | .inr _ => .neg .truth
  | _, .localEdge, tags => match tags 0 with
    | .inl _ => oldLocalEdge 0 | .inr _ => .truth
  | _, .outerNode, tags => match tags 0 with
    | .inl _ => unary .node 0 | .inr _ => .neg .truth
  | _, .incidence, tags => match tags 0,tags 1 with
    | .inl _,.inl _ => .conj (oldLocalEdge 1) (binary .incidence 0 1)
    | .inl _,.inr (i,j) => disj (coloredEndpoint I i 1 0) (coloredEndpoint I j 1 0)
    | _,_ => .neg .truth
  | _, .owner, tags => match tags 0,tags 1 with
    | .inl _,.inl _ => oldOwner 0 1
    | .inr _,.inl _ => binary .parent 0 1
    | _,_ => .neg .truth
  | _, .margin, tags => match tags 0,tags 1 with
    | .inl _,.inl _ => binary .margin 0 1 | _,_ => .neg .truth
  | _, .adhesion, tags => match tags 0,tags 1 with
    | .inl _,.inl _ => adhesion 0 1 | _,_ => .neg .truth
  | _, .outerParent, tags => match tags 0,tags 1 with
    | .inl _,.inl _ => binary .parent 0 1 | _,_ => .neg .truth
  | _, .originalAdj, tags => match tags 0,tags 1 with
    | .inl _,.inl _ => originalAdj 0 1 | _,_ => .neg .truth

noncomputable def interpretation (W : Nat) :
    CopyInterpretation InputAtom OutputAtom (copies W) (parameters W) where
  domain t := domain (fixed W) ((tagEquiv W).symm t)
  atom A tags := atom (fixed W) A (fun i => (tagEquiv W).symm (tags i))

theorem copy_count (W : Nat) : copies W=1+W*W := by simp [copies,Tag]
theorem parameter_count (W : Nat) : parameters W=W+W*W := by simp [parameters,Parameter]

/-- Fixed finite conjunctions, used to quantify copy tags without graph-size
unrolling. -/
def allFin : {m : Nat} → (Fin m → Form a b) → Form a b
  | 0, _ => .truth
  | m+1, f => .conj (f 0) (allFin (fun i : Fin m => f i.succ))
def anyFin {m : Nat} (f : Fin m → Form a b) : Form a b := .neg (allFin (fun i => .neg (f i)))

/-- A candidate is sound only when its selected child and ordered colors
have real distinct nonoriginal endpoints in the parent's margin. -/
def selectedSound (I : Indices W b) : Form 0 b :=
  allFin (fun i : Fin W => allFin (fun j : Fin W => .allFO
    (.implies (.member 0 (I.selected i j)) (candidateValid I i j 0))))

/-- A synthetic clique pair must be represented once. This formula uses only
W² tag comparisons; child-node equality is ordinary FO equality. -/
def uniqueSelectedFor (I : Indices W b) (i j : Fin W) (y u v : Fin a) : Form a b :=
  .conj (.member y (I.selected i j))
    (allFin (fun h : Fin W => allFin (fun l : Fin W => .allFO
      (.implies (.conj (.member 0 (I.selected h l))
        (disj (candidatePair I h l 0 u.succ v.succ) (candidatePair I h l 0 v.succ u.succ)))
        (if i=h ∧ j=l then .equal 0 y.succ else .neg .truth)))))

/-- Coverage and uniqueness are tested on every available nonoriginal
candidate pair, including candidates from repeated child adhesions. -/
def selectedCoverageUnique (I : Indices W b) : Form 0 b :=
  allFin (fun i : Fin W => allFin (fun j : Fin W => .allFO (.allFO (.allFO
    (.implies (candidatePair I i j 2 1 0)
      (anyFin (fun h : Fin W => anyFin (fun l : Fin W => .existsFO
        (.conj (disj (candidatePair I h l 0 2 1) (candidatePair I h l 0 1 2))
          (uniqueSelectedFor I h l 0 2 1))))))))))

def validSelection (I : Indices W b) : Form 0 b :=
  .conj (selectedSound I) (selectedCoverageUnique I)

#print axioms interpretation
#print axioms copy_count
#print axioms parameter_count
end StackSorting.GraphWidth.MarginalA2.Syntax
