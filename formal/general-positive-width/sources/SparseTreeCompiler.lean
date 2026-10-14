import SparsePositionSemantics
import FiniteTreeFixedSemantics
import Mathlib.Data.Fin.Tuple.Basic

/-! Constructive syntax translation from sparse graph MSO to tree MSO.
Graph vertices are the same carrier as tree nodes. The finite atomic codes are
actual tree formulas; there is no recognizability premise. -/
namespace StackSorting.SparseTreeCompiler
open TreeAutomaton.Logic

variable {α : Type} {P : Type}

/-- Four finite pieces of tree-MSO syntax specify the graph vocabulary.
Two-variable codes receive endpoint singletons at indices zero and one. -/
structure Codes (α : Type) where
  insert : TreeAutomaton.Logic.Formula α 1
  remove : TreeAutomaton.Logic.Formula α 1
  successor : TreeAutomaton.Logic.Formula α 2
  matching : TreeAutomaton.Logic.Formula α 2

noncomputable def point (x : P) : P → Bool := by
  classical
  exact fun p => decide (p = x)

noncomputable def unaryVal (x : P) : Fin 1 → P → Bool := fun _ => point x

noncomputable def binaryVal (x y : P) : Fin 2 → P → Bool := Fin.cons (point x) (fun _ => point y)

noncomputable def Codes.relations (C : Codes α) (label : P → α)
    (child : Bool → P → P → Prop) : SparseEndpointMSO.Relations P where
  insert x := C.insert.EvalOn label child (unaryVal x)
  remove x := C.remove.EvalOn label child (unaryVal x)
  successor x y := C.successor.EvalOn label child (binaryVal x y)
  matching x y := C.matching.EvalOn label child (binaryVal x y)

/-- A block is compiled to ordinary singleton first-order binders. The cast
only reassociates finite indices; it neither adds nodes nor changes size. -/
def existsBlock : (k : Nat) → {n : Nat} → TreeAutomaton.Logic.Formula α (k+n) → TreeAutomaton.Logic.Formula α n
  | 0, n, f => f.rename (Fin.cast (Nat.zero_add n))
  | k+1, n, f => .existsFirst (existsBlock k
      (f.rename (Fin.cast (Nat.succ_add_eq_add_succ k n))))

def allBlock (k : Nat) {n : Nat} (f : TreeAutomaton.Logic.Formula α (k+n)) : TreeAutomaton.Logic.Formula α n :=
  .neg (existsBlock k (.neg f))

def truth {n : Nat} : TreeAutomaton.Logic.Formula α n :=
  .neg (.existsFirst (.neg (.atom (.subset 0 0))))

/-- Compilation is parameterized by index embeddings, allowing arbitrary
interleaving of first- and second-order binders in the target's single scope. -/
def compile (C : Codes α) : {a b n : Nat} → SparseEndpointMSO.Formula a b →
    (Fin a → Fin n) → (Fin b → Fin n) → TreeAutomaton.Logic.Formula α n
  | _, _, _, .truth, _, _ => truth
  | _, _, _, .equal i j, first, _ => .atom (.subset (first i) (first j))
  | _, _, _, .member i X, first, sets => .atom (.subset (first i) (sets X))
  | _, _, _, .insert i, first, _ => C.insert.rename (fun _ => first i)
  | _, _, _, .remove i, first, _ => C.remove.rename (fun _ => first i)
  | _, _, _, .successor i j, first, _ =>
      C.successor.rename (Fin.cons (first i) (fun _ => first j))
  | _, _, _, .matching i j, first, _ =>
      C.matching.rename (Fin.cons (first i) (fun _ => first j))
  | _, _, _, .neg f, first, sets => .neg (compile C f first sets)
  | _, _, _, .conj f g, first, sets =>
      .conj (compile C f first sets) (compile C g first sets)
  | _, _, _, .implies f g, first, sets =>
      .neg (.conj (compile C f first sets) (.neg (compile C g first sets)))
  | _, _, n, .existsFO k f, first, sets => existsBlock k
      (compile C f (Fin.addCases (Fin.castAdd n) (fun i => Fin.natAdd k (first i)))
        (fun X => Fin.natAdd k (sets X)))
  | _, _, n, .allFO k f, first, sets => allBlock k
      (compile C f (Fin.addCases (Fin.castAdd n) (fun i => Fin.natAdd k (first i)))
        (fun X => Fin.natAdd k (sets X)))
  | _, _, _, .allSet f, first, sets => .neg (.existsSet (.neg
      (compile C f (fun i => (first i).succ) (Fin.cons 0 (fun X => (sets X).succ)))))

/-- The environment invariant requires singleton FO values, but no restriction
on any monadic variable or on unused target indices. -/
structure Represents {a b n : Nat} (first : Fin a → Fin n) (sets : Fin b → Fin n)
    (v : Fin n → P → Bool) (env : Fin a → P) (subsets : Fin b → P → Bool) : Prop where
  first_eq : ∀ i, v (first i) = point (env i)
  sets_eq : ∀ X, v (sets X) = subsets X

variable (label : P → α) (child : Bool → P → P → Prop)

private theorem point_snoc {k : Nat} (xs : Fin k → P) (x : P) :
    (fun i : Fin (k+1) => point ((Fin.snoc xs x : Fin (k+1) → P) i)) = (Fin.snoc (fun i => point (xs i)) (point x) : Fin (k+1) → P → Bool) := by
  exact Fin.comp_snoc point xs x

theorem eval_existsBlock (k : Nat) {n : Nat} (f : TreeAutomaton.Logic.Formula α (k+n))
    (v : Fin n → P → Bool) :
    (existsBlock k f).EvalOn label child v ↔ ∃ xs : Fin k → P,
      f.EvalOn label child (Fin.append (fun i => point (xs i)) v) := by
  classical
  induction k generalizing n with
  | zero =>
    rw [existsBlock, TreeAutomaton.Logic.Formula.evalOn_rename]
    have hv (xs : Fin 0 → P) : Fin.append (fun i => point (xs i)) v =
        (fun i => v (Fin.cast (Nat.zero_add n) i)) :=
      Fin.append_left_nil (fun i => point (xs i)) v rfl
    constructor
    · intro h; exact ⟨Fin.elim0, (hv Fin.elim0).symm ▸ h⟩
    · rintro ⟨xs, h⟩; rwa [hv xs] at h
  | succ k ih =>
    simp only [existsBlock, TreeAutomaton.Logic.Formula.evalOn_existsFirst]
    have he (xs : Fin k → P) (x : P) :
        (fun i => Fin.append (fun j => point (xs j))
          (Fin.cons (point x) v) (Fin.cast (Nat.succ_add_eq_add_succ k n) i)) =
          Fin.append (fun i => point (Fin.snoc xs x i)) v := by
      rw [point_snoc]
      exact (Fin.append_left_snoc (fun j => point (xs j)) (point x) v).symm
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨xs, hxs⟩ := (ih _ _).mp hx
      refine ⟨Fin.snoc xs x, ?_⟩
      rw [TreeAutomaton.Logic.Formula.evalOn_rename] at hxs
      change f.EvalOn label child (fun i => Fin.append (fun j => point (xs j))
        (Fin.cons (point x) v) (Fin.cast (Nat.succ_add_eq_add_succ k n) i)) at hxs
      rwa [he xs x] at hxs
    · rintro ⟨ys, hys⟩
      refine ⟨ys (Fin.last k), (ih _ _).mpr ⟨Fin.init ys, ?_⟩⟩
      rw [TreeAutomaton.Logic.Formula.evalOn_rename]
      change f.EvalOn label child (fun i => Fin.append (fun j => point (Fin.init ys j))
        (Fin.cons (point (ys (Fin.last k))) v) (Fin.cast (Nat.succ_add_eq_add_succ k n) i))
      rw [he, Fin.snoc_init_self]
      exact hys

theorem eval_allBlock (k : Nat) {n : Nat} (f : TreeAutomaton.Logic.Formula α (k+n))
    (v : Fin n → P → Bool) :
    (allBlock k f).EvalOn label child v ↔ ∀ xs : Fin k → P,
      f.EvalOn label child (Fin.append (fun i => point (xs i)) v) := by
  classical
  simp only [allBlock, TreeAutomaton.Logic.Formula.EvalOn, eval_existsBlock]
  simp only [not_exists, not_not]

@[simp] theorem eval_truth {n : Nat} (v : Fin n → P → Bool) :
    (truth : TreeAutomaton.Logic.Formula α n).EvalOn label child v := by
  simp [truth, TreeAutomaton.Logic.Formula.EvalOn, TreeAutomaton.Logic.Atom.EvalOn]

private theorem Represents.append {a b n k : Nat} {first : Fin a → Fin n}
    {sets : Fin b → Fin n} {v : Fin n → P → Bool} {env : Fin a → P}
    {subsets : Fin b → P → Bool} (h : Represents first sets v env subsets)
    (xs : Fin k → P) :
    Represents (Fin.addCases (Fin.castAdd n) (fun i => Fin.natAdd k (first i)))
      (fun X => Fin.natAdd k (sets X))
      (Fin.append (fun i => point (xs i)) v) (Fin.addCases xs env) subsets := by
  constructor
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · simpa using h.first_eq j
  · intro X
    simpa using h.sets_eq X

private theorem Represents.cons {a b n : Nat} {first : Fin a → Fin n}
    {sets : Fin b → Fin n} {v : Fin n → P → Bool} {env : Fin a → P}
    {subsets : Fin b → P → Bool} (h : Represents first sets v env subsets)
    (X : P → Bool) :
    Represents (fun i => (first i).succ) (Fin.cons 0 (fun i => (sets i).succ))
      (Fin.cons X v) env (Fin.cons X subsets) := by
  constructor
  · intro i; simpa using h.first_eq i
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simpa using h.sets_eq j

/-- Semantic preservation for every sparse formula, under arbitrary free
valuations, including zero-length FO blocks and unrestricted set quantifiers. -/
theorem compile_correct (C : Codes α) (f : SparseEndpointMSO.Formula a b)
    (first : Fin a → Fin n) (sets : Fin b → Fin n) (v : Fin n → P → Bool)
    (env : Fin a → P) (subsets : Fin b → P → Bool)
    (h : Represents first sets v env subsets) :
    (compile C f first sets).EvalOn label child v ↔
      f.EvalOn (C.relations label child) env subsets := by
  classical
  induction f generalizing n with
  | truth => exact iff_true_intro (eval_truth label child v)
  | equal i j =>
    simp only [compile, TreeAutomaton.Logic.Formula.EvalOn,
      TreeAutomaton.Logic.Atom.EvalOn, SparseEndpointMSO.Formula.EvalOn, h.first_eq, point]
    simp
  | member i X =>
    simp only [compile, TreeAutomaton.Logic.Formula.EvalOn,
      TreeAutomaton.Logic.Atom.EvalOn, SparseEndpointMSO.Formula.EvalOn,
      h.first_eq, h.sets_eq, point]
    simp
  | insert i =>
    simp only [compile, TreeAutomaton.Logic.Formula.evalOn_rename,
      SparseEndpointMSO.Formula.EvalOn, Codes.relations, h.first_eq]
    rfl
  | remove i =>
    simp only [compile, TreeAutomaton.Logic.Formula.evalOn_rename,
      SparseEndpointMSO.Formula.EvalOn, Codes.relations, h.first_eq]
    rfl
  | successor i j =>
    simp only [compile, TreeAutomaton.Logic.Formula.evalOn_rename,
      SparseEndpointMSO.Formula.EvalOn, Codes.relations]
    have hv : (fun x => v ((Fin.cons (first i) (fun _ : Fin 1 => first j) : Fin 2 → Fin n) x)) =
        binaryVal (env i) (env j) := by
      funext x
      refine Fin.cases ?_ (fun y => ?_) x <;> simp [binaryVal, h.first_eq]
    rw [hv]
  | matching i j =>
    simp only [compile, TreeAutomaton.Logic.Formula.evalOn_rename,
      SparseEndpointMSO.Formula.EvalOn, Codes.relations]
    have hv : (fun x => v ((Fin.cons (first i) (fun _ : Fin 1 => first j) : Fin 2 → Fin n) x)) =
        binaryVal (env i) (env j) := by
      funext x
      refine Fin.cases ?_ (fun y => ?_) x <;> simp [binaryVal, h.first_eq]
    rw [hv]
  | neg f ih => exact not_congr (ih _ _ _ _ _ h)
  | conj f g ihf ihg => exact and_congr (ihf _ _ _ _ _ h) (ihg _ _ _ _ _ h)
  | implies f g ihf ihg =>
    simp only [compile, TreeAutomaton.Logic.Formula.EvalOn, SparseEndpointMSO.Formula.EvalOn]
    rw [ihf _ _ _ _ _ h, ihg _ _ _ _ _ h]
    tauto
  | existsFO k f ih =>
    rw [compile, eval_existsBlock]
    exact exists_congr (fun xs => ih _ _ _ _ _ (h.append xs))
  | allFO k f ih =>
    rw [compile, eval_allBlock]
    exact forall_congr' (fun xs => ih _ _ _ _ _ (h.append xs))
  | allSet f ih =>
    simp only [compile, TreeAutomaton.Logic.Formula.EvalOn,
      SparseEndpointMSO.Formula.EvalOn, not_exists, not_not]
    exact forall_congr' (fun X => ih _ _ _ _ _ (h.cons X))

#print axioms eval_existsBlock
#print axioms compile_correct
end StackSorting.SparseTreeCompiler
