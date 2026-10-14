import FiniteConfigurationWalk
import SparseTreeCompiler
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases

/-! Explicit finite-state tree-MSO reachability. States index unary sets on
actual vertices; they do not enlarge the first-order carrier. -/
namespace StackSorting.FiniteState
open TreeAutomaton.Logic SparseTreeCompiler
variable {α P : Type}

def implies {n} (f g : Formula α n) : Formula α n := .neg (.conj f (.neg g))

theorem eval_implies {n} (label : P → α) (child : Bool → P → P → Prop)
    (v : Fin n → P → Bool) (f g : Formula α n) :
    (implies f g).EvalOn label child v ↔
      (f.EvalOn label child v → g.EvalOn label child v) := by
  classical
  simp only [implies, Formula.EvalOn]
  tauto

def conjoin {n} : List (Formula α n) → Formula α n
  | [] => truth
  | p::ps => .conj p (conjoin ps)

theorem eval_conjoin {n} (label : P → α) (child : Bool → P → P → Prop)
    (v : Fin n → P → Bool) (ps : List (Formula α n)) :
    (conjoin ps).EvalOn label child v ↔ ∀ p ∈ ps, p.EvalOn label child v := by
  induction ps with
  | nil => simp [conjoin,eval_truth]
  | cons p ps ih => simp [conjoin,Formula.EvalOn,ih]

/-- Exactly k ordinary monadic binders, with no state-valued quantifier. -/
def existsSets : (k : Nat) → {n : Nat} → Formula α (k+n) → Formula α n
  | 0, n, f => f.rename (Fin.cast (Nat.zero_add n))
  | k+1, n, f => .existsSet (existsSets k
      (f.rename (Fin.cast (Nat.succ_add_eq_add_succ k n))))

def allSets (k : Nat) {n} (f : Formula α (k+n)) : Formula α n :=
  .neg (existsSets k (.neg f))

theorem eval_existsSets (label : P → α) (child : Bool → P → P → Prop)
    (k : Nat) {n} (f : Formula α (k+n)) (v : Fin n → P → Bool) :
    (existsSets k f).EvalOn label child v ↔
      ∃ S : Fin k → P → Bool, f.EvalOn label child (Fin.append S v) := by
  induction k generalizing n with
  | zero =>
    rw [existsSets,Formula.evalOn_rename]
    have hv (S : Fin 0 → P → Bool) : Fin.append S v =
        (fun i => v (Fin.cast (Nat.zero_add n) i)) :=
      Fin.append_left_nil S v rfl
    constructor
    · intro h; exact ⟨Fin.elim0,(hv Fin.elim0).symm ▸ h⟩
    · rintro ⟨S,h⟩; rwa [hv S] at h
  | succ k ih =>
    simp only [existsSets,Formula.EvalOn]
    have he (S : Fin k → P → Bool) (X : P → Bool) :
        (fun i => Fin.append S (Fin.cons X v)
          (Fin.cast (Nat.succ_add_eq_add_succ k n) i)) =
          Fin.append (Fin.snoc S X) v :=
      (Fin.append_left_snoc S X v).symm
    constructor
    · rintro ⟨X,hX⟩
      obtain ⟨S,hS⟩ := (ih _ _).mp hX
      refine ⟨Fin.snoc S X,?_⟩
      rw [Formula.evalOn_rename] at hS
      change f.EvalOn label child (fun i => Fin.append S (Fin.cons X v)
        (Fin.cast (Nat.succ_add_eq_add_succ k n) i)) at hS
      rwa [he] at hS
    · rintro ⟨S,hS⟩
      refine ⟨S (Fin.last k),(ih _ _).mpr ⟨Fin.init S,?_⟩⟩
      rw [Formula.evalOn_rename]
      change f.EvalOn label child (fun i => Fin.append (Fin.init S)
        (Fin.cons (S (Fin.last k)) v) (Fin.cast (Nat.succ_add_eq_add_succ k n) i))
      rw [he,Fin.snoc_init_self]
      exact hS

theorem eval_allSets (label : P → α) (child : Bool → P → P → Prop)
    (k : Nat) {n} (f : Formula α (k+n)) (v : Fin n → P → Bool) :
    (allSets k f).EvalOn label child v ↔
      ∀ S : Fin k → P → Bool, f.EvalOn label child (Fin.append S v) := by
  classical
  simp only [allSets,Formula.EvalOn,eval_existsSets,not_exists,not_not]

/-- One transition-closure clause. The two newly bound vertices are ordinary
first-order variables. The set indices are shifted past both of them. -/
def closedClause {k} (step : Fin k → Fin k → Formula α 2) (i j : Fin k) :
    Formula α (k+2) :=
  allBlock 2 (implies
    (.conj (.atom (.subset (Fin.castAdd (k+2) (0 : Fin 2)) (Fin.natAdd 2 (Fin.castAdd 2 i))))
      ((step i j).rename (Fin.castAdd (k+2))))
    (.atom (.subset (Fin.castAdd (k+2) (1 : Fin 2)) (Fin.natAdd 2 (Fin.castAdd 2 j)))))

noncomputable def closedFormula {k} (step : Fin k → Fin k → Formula α 2) :
    Formula α (k+2) :=
  conjoin ((Finset.univ : Finset (Fin k × Fin k)).toList.map
    (fun ij => closedClause step ij.1 ij.2))

/-- Literal closed-set formula for reachability between two given states.
It adds exactly k outer universally quantified sets and has two free endpoints. -/
noncomputable def route {k} (step : Fin k → Fin k → Formula α 2) (i j : Fin k) :
    Formula α 2 :=
  allSets k (implies
    (.conj (.atom (.subset (Fin.natAdd k 0) (Fin.castAdd 2 i)))
      (closedFormula step))
    (.atom (.subset (Fin.natAdd k 1) (Fin.castAdd 2 j))))

theorem eval_closedClause {k} (label : P → α) (child : Bool → P → P → Prop)
    (step : Fin k → Fin k → Formula α 2) (i j : Fin k)
    (S : Fin k → P → Bool) (v : Fin 2 → P → Bool) :
    (closedClause step i j).EvalOn label child (Fin.append S v) ↔
      ∀ x y, S i x = true → (step i j).EvalOn label child (binaryVal x y) →
        S j y = true := by
  classical
  rw [closedClause,eval_allBlock]
  have he (xs : Fin 2 → P) :
      (fun z => point (xs z)) = binaryVal (xs 0) (xs 1) := by
    funext z
    fin_cases z <;> rfl
  simp only [eval_implies,Formula.EvalOn,Formula.evalOn_rename,
    Atom.EvalOn,Fin.append_left,Fin.append_right,he]
  simp only [binaryVal,Fin.cons_zero,Fin.cons_one,point,decide_eq_true_eq,forall_eq]
  constructor
  · intro h x y hx hs
    exact h (Fin.cons x (fun _ => y)) ⟨hx,hs⟩
  · intro h xs hh
    exact h (xs 0) (xs 1) hh.1 hh.2

theorem eval_closedFormula {k} (label : P → α) (child : Bool → P → P → Prop)
    (step : Fin k → Fin k → Formula α 2)
    (S : Fin k → P → Bool) (v : Fin 2 → P → Bool) :
    (closedFormula step).EvalOn label child (Fin.append S v) ↔
      ∀ i j x y, S i x = true → (step i j).EvalOn label child (binaryVal x y) →
        S j y = true := by
  classical
  simp only [closedFormula,eval_conjoin,List.forall_mem_map,Finset.mem_toList,
    Finset.mem_univ,forall_const,eval_closedClause]
  exact ⟨fun h i j => h (i,j), fun h ij => h ij.1 ij.2⟩

theorem eval_route {k} (label : P → α) (child : Bool → P → P → Prop)
    (step : Fin k → Fin k → Formula α 2) (i j : Fin k) (x y : P) :
    (route step i j).EvalOn label child (binaryVal x y) ↔
      Walk (fun a b : P × Fin k =>
        (step a.2 b.2).EvalOn label child (binaryVal a.1 b.1)) (x,i) (y,j) := by
  classical
  rw [route,eval_allSets,walk_iff_all_closed]
  simp only [eval_implies,Formula.EvalOn,eval_closedFormula,Atom.EvalOn,
    Fin.append_left,Fin.append_right,binaryVal,Fin.cons_zero,Fin.cons_one,
    point,decide_eq_true_eq,forall_eq]
  constructor
  · intro h S hx hc
    exact h S ⟨hx,fun i j a b ha hab => hc (a,i) (b,j) ha hab⟩
  · intro h S hh
    exact h S hh.1 (fun a b ha hab => hh.2 a.2 b.2 a.1 b.1 ha hab)

#print axioms eval_allSets
#print axioms eval_route
end StackSorting.FiniteState
