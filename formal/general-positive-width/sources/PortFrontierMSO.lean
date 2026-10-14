import FinitePortRoutes

namespace StackSorting.FinitePort
open TreeAutomaton.Logic SparseTreeCompiler

theorem singleton_eq_point {P : Type} [DecidableEq P] (x : P) :
    (fun y => decide (y=x))=point x := by
  funext y
  simp only [point]
  congr 1

/-- Apply a two-endpoint formula to two designated singleton variables. -/
def atPair {α : Type} {k : Nat} (f : Formula α 2) (i j : Fin k) : Formula α k :=
  f.rename (Fin.cons i (fun _ => j))

theorem eval_atPair {α P : Type} {k : Nat} (label : P → α)
    (child : Bool → P → P → Prop) (f : Formula α 2) (i j : Fin k)
    (v : Fin k → P → Bool) (x y : P) (hi : v i=point x) (hj : v j=point y) :
    (atPair f i j).EvalOn label child v ↔ f.EvalOn label child (binaryVal x y) := by
  rw [atPair,Formula.evalOn_rename]
  have he : (fun z => v ((Fin.cons i (fun _ => j) : Fin 2 → Fin k) z)) =
      binaryVal x y := by
    funext z
    fin_cases z <;> simp [binaryVal,hi,hj]
  rw [he]

/-- One-state reachability of the proper parent relation, in ancestor-to-child
orientation. The formula quantifies sets of actual vertices only. -/
noncomputable def ancestorFormula {α : Type} (parent : Formula α 2) : Formula α 2 :=
  FiniteState.route (fun (_ _ : Fin 1) => parent) 0 0

theorem eval_ancestorFormula {n colors relations W} (T : RootedTree n)
    (labels : Vertex n → Alphabet colors relations W)
    (child : Bool → Vertex n → Vertex n → Prop)
    (parent : Formula (Alphabet colors relations W) 2)
    (hp : ExactParent T labels child parent) (u v : Vertex n) :
    (ancestorFormula parent).EvalOn labels child (binaryVal u v) ↔ Ancestor T u v := by
  rw [ancestorFormula,FiniteState.eval_route]
  constructor
  · intro h
    have all : ∀ x y : Vertex n × Fin 1,
        FiniteState.Walk (fun a b => parent.EvalOn labels child (binaryVal a.1 b.1)) x y →
          Ancestor T x.1 y.1 := by
      intro x y hh
      induction hh with
      | refl => exact .refl _
      | @step x y z hxy _ ih =>
        have hs := (hp x.1 y.1).mp hxy
        have he : Ancestor T x.1 y.1 := hs.2 ▸ Ancestor.step hs.1 (.refl _)
        exact he.trans ih
    exact all (u,0) (v,0) h
  · intro h
    induction h with
    | refl => exact .refl _
    | @step v hv _ ih =>
      exact ih.trans (.step ((hp (T.parent v) v).mpr ⟨hv,rfl⟩) (.refl _))

/-- Free endpoints are v then u; the bound endpoint is a descendant z. -/
noncomputable def inheritedFormula {α : Type} (parent adjacent : Formula α 2) : Formula α 2 :=
  .conj (atPair (ancestorFormula parent) 1 0)
    (.conj (.neg (.atom (.subset 1 0)))
      (.existsFirst (.conj (atPair (ancestorFormula parent) 1 0) (atPair adjacent 2 0))))

theorem eval_inheritedFormula {n colors relations W} (T : RootedTree n)
    (G : Diagram n colors relations) (labels : Vertex n → Alphabet colors relations W)
    (child : Bool → Vertex n → Vertex n → Prop)
    (parent adjacent : Formula (Alphabet colors relations W) 2)
    (hp : ExactParent T labels child parent)
    (ha : ∀ u v, adjacent.EvalOn labels child (binaryVal u v) ↔ Adjacent G u v)
    (v u : Vertex n) :
    (inheritedFormula parent adjacent).EvalOn labels child (binaryVal v u) ↔
      Inherited T G v u := by
  classical
  change ((atPair (ancestorFormula parent) 1 0).EvalOn labels child (binaryVal v u) ∧
    ¬ (Atom.subset 1 0).EvalOn labels child (binaryVal v u) ∧
    (Formula.existsFirst (.conj (atPair (ancestorFormula parent) 1 0)
      (atPair adjacent 2 0))).EvalOn labels child (binaryVal v u)) ↔ _
  rw [Formula.evalOn_existsFirst]
  simp_rw [singleton_eq_point]
  change ((atPair (ancestorFormula parent) 1 0).EvalOn labels child (binaryVal v u) ∧
    ¬ (∀ p, binaryVal v u 1 p = true → binaryVal v u 0 p = true) ∧
    ∃ z, (atPair (ancestorFormula parent) 1 0).EvalOn labels child
      (Fin.cons (point z) (binaryVal v u)) ∧
      (atPair adjacent 2 0).EvalOn labels child (Fin.cons (point z) (binaryVal v u))) ↔ _
  rw [eval_atPair labels child _ 1 0 _ u v rfl rfl,eval_ancestorFormula T labels child parent hp]
  have hneq : (∀ p, binaryVal v u 1 p = true → binaryVal v u 0 p = true) ↔ u=v := by
    simp [binaryVal,point]
  rw [hneq]
  have hex : (∃ z, (atPair (ancestorFormula parent) 1 0).EvalOn labels child
        (Fin.cons (point z) (binaryVal v u)) ∧
      (atPair adjacent 2 0).EvalOn labels child (Fin.cons (point z) (binaryVal v u))) ↔
      ∃ z, Ancestor T v z ∧ Adjacent G u z := by
    apply exists_congr
    intro z
    rw [eval_atPair labels child _ 1 0 _ v z rfl rfl,
      eval_atPair labels child _ 2 0 _ u z rfl rfl,
      eval_ancestorFormula T labels child parent hp,ha]
  rw [hex]
  rfl

#print axioms eval_ancestorFormula
#print axioms eval_inheritedFormula
end StackSorting.FinitePort
