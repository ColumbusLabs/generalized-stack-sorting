import BinaryParentReachability
import SparseTreeCompiler

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic SparseTreeCompiler
variable {α P : Type}

/-- Closed-set reachability in the exact accepted sparse syntax, interpreted
on an arbitrary carrier. This does not assume a path or finite cardinality. -/
theorem evalOn_reach (R : SparseEndpointMSO.Relations P) {a b}
    (i j : Fin a) (env : Fin a → P) (sets : Fin b → P → Bool) :
    (SparseEndpointMSO.reach i j).EvalOn R env sets ↔
      Relation.ReflTransGen R.successor (env i) (env j) := by
  classical
  simp only [SparseEndpointMSO.reach, SparseEndpointMSO.Formula.EvalOn,
    Fin.cons_zero, Fin.addCases_left]
  constructor
  · intro h
    let X : P → Bool := fun u => decide (Relation.ReflTransGen R.successor (env i) u)
    have hx : X (env i) = true := by simp [X,Relation.ReflTransGen.refl]
    have hy := h X ⟨hx, fun v hv => by
      simp only [X,decide_eq_true_eq] at hv ⊢
      exact hv.1.tail hv.2⟩
    exact of_decide_eq_true hy
  · intro h X hx
    have hc : ∀ u v, X u = true → R.successor u v → X v = true := by
      intro u v hu huv
      exact hx.2 (Fin.cons u (fun _ => v)) ⟨hu,huv⟩
    have preserved : ∀ {x y}, Relation.ReflTransGen R.successor x y →
        X x = true → X y = true := by
      intro x y walk
      induction walk with
      | refl => exact id
      | tail h e ih => exact fun hh => hc _ _ (ih hh) e
    exact preserved h hx.1

/-- Two endpoints: original parent at index zero, child at index one. The
newly bound vertex is the first child; matching means binary left-child and
successor means binary right-child. -/
def parentSparseFormula : SparseEndpointMSO.Formula 2 0 :=
  .existsFO 1 (.conj (.matching 1 0) (SparseEndpointMSO.reach 0 2))

theorem eval_parentSparseFormula (R : SparseEndpointMSO.Relations P) (p q : P) :
    parentSparseFormula.EvalOn R (Fin.cons p (fun _ => q)) Fin.elim0 ↔
      ∃ z, R.matching p z ∧ Relation.ReflTransGen R.successor z q := by
  simp only [parentSparseFormula, SparseEndpointMSO.Formula.EvalOn, evalOn_reach]
  constructor
  · rintro ⟨v,h⟩
    exact ⟨v 0,h⟩
  · rintro ⟨z,h⟩
    exact ⟨(fun _ => z),h⟩

/-- Literal binary child atoms supply the sparse vocabulary used solely for
this parent route. No graph interpretation oracle appears. -/
def binaryChildCodes : Codes α where
  insert := truth
  remove := truth
  successor := .atom (.child true 0 1)
  matching := .atom (.child false 0 1)

@[simp] theorem binaryChildCodes_successor (label : P → α)
    (child : Bool → P → P → Prop) (p q : P) :
    (binaryChildCodes.relations label child).successor p q ↔ child true p q := by
  classical
  simp [binaryChildCodes,Codes.relations,Formula.EvalOn,Atom.EvalOn,binaryVal,point]

@[simp] theorem binaryChildCodes_matching (label : P → α)
    (child : Bool → P → P → Prop) (p q : P) :
    (binaryChildCodes.relations label child).matching p q ↔ child false p q := by
  classical
  simp [binaryChildCodes,Codes.relations,Formula.EvalOn,Atom.EvalOn,binaryVal,point]

def parentRoute : Formula α 2 := compile binaryChildCodes parentSparseFormula id Fin.elim0

/-- The explicit finite tree-MSO route recognizes exactly the FCNS parent on
actual positions, preserving one position per original graph vertex. -/
theorem parentRoute_correct (t : BinaryTree α) (p q : Position t) :
    parentRoute.EvalOn Position.label (fun d u v => Child d u v) (binaryVal p q) ↔
      ParentPosition p q := by
  have hrep : Represents id (Fin.elim0 : Fin 0 → Fin 2)
      (binaryVal p q) (Fin.cons p (fun _ => q)) Fin.elim0 := by
    constructor
    · intro i; exact Fin.cases rfl (fun _ => rfl) i
    · intro i; exact Fin.elim0 i
  have hc := compile_correct Position.label (fun d u v => Child d u v)
    binaryChildCodes parentSparseFormula id Fin.elim0 (binaryVal p q)
    (Fin.cons p (fun _ => q)) Fin.elim0 hrep
  change (compile binaryChildCodes parentSparseFormula id Fin.elim0).EvalOn _ _ _ ↔ _
  rw [hc, eval_parentSparseFormula, parentPosition_iff_reach]
  have hs : (binaryChildCodes.relations Position.label (fun d u v => Child d u v)).successor =
      (fun u v : Position t => Child true u v) := by
    funext u v
    exact propext (binaryChildCodes_successor ..)
  simp only [binaryChildCodes_matching,hs]

#print axioms evalOn_reach
#print axioms parentRoute_correct
end StackSorting.FinitePort.ChildSibling
