import SparseMonadicBlock
import Mathlib.Logic.Equiv.Fin.Basic

/-! Finite-copy MSO interpretations with explicit sparse-graph atom formulas.
No interpreted atom is granted semantic recognition: every atom is an actual
formula in the original I/R/S/M/equality/membership language. -/
namespace StackSorting.SparseEndpointMSO.FiniteCopy

open CanonicalChoice

structure Interpretation (Atom : Nat → Type) (c : Nat) where
  domain : Fin c → Formula 1 0
  atom : {r : Nat} → Atom r → (Fin r → Fin c) → Formula r 0

abbrev Element (c : Nat) := Fin c × Nat

def InDomain (J : Interpretation Atom c) (D : Model) (v : Element c) : Prop :=
  v.2 ∈ D.domain ∧ Eval D (J.domain v.1) (fun _ => v.2) Fin.elim0

def Supported (J : Interpretation Atom c) (D : Model) (X : Element c → Prop) : Prop :=
  ∀ v, X v → InDomain J D v

/-- A set of incidence/copy elements is exactly one original-node set per tag. -/
def splitSet (X : Element c → Prop) : Fin c → Nat → Prop := fun t x => X (t, x)
def joinSet (X : Fin c → Nat → Prop) : Element c → Prop := fun v => X v.1 v.2

@[simp] theorem join_split (X : Element c → Prop) : joinSet (splitSet X) = X := rfl
@[simp] theorem split_join (X : Fin c → Nat → Prop) : splitSet (joinSet X) = X := rfl

/-- Exact support, including the copy-specific domain restriction. -/
theorem supported_iff_split (J : Interpretation Atom c) (D : Model)
    (X : Element c → Prop) :
    Supported J D X ↔ SupportedTuple D (splitSet X) ∧
      ∀ t x, splitSet X t x → Eval D (J.domain t) (fun _ => x) Fin.elim0 := by
  constructor
  · intro h
    exact ⟨fun t x hx => (h (t,x) hx).1, fun t x hx => (h (t,x) hx).2⟩
  · rintro ⟨h, hd⟩ ⟨t,x⟩ hx
    exact ⟨h t x hx, hd t x hx⟩

/-- A genuine equivalence, not merely equinumerosity: arbitrary supported sets
of copied elements and domain-restricted tuples have mutually inverse maps. -/
def supportedSetEquiv (J : Interpretation Atom c) (D : Model) :
    {X : Element c → Prop // Supported J D X} ≃
    {X : Fin c → Nat → Prop // SupportedTuple D X ∧
      ∀ t x, X t x → Eval D (J.domain t) (fun _ => x) Fin.elim0} where
  toFun X := ⟨splitSet X.val, (supported_iff_split J D X.val).mp X.property⟩
  invFun X := ⟨joinSet X.val, (supported_iff_split J D (joinSet X.val)).mpr X.property⟩
  left_inv X := by apply Subtype.ext; rfl
  right_inv X := by apply Subtype.ext; rfl

/-- Syntax over a finitely copied universe. Individual binders bind one element;
set binders range over supported sets of copied elements. -/
inductive CopyFormula (Atom : Nat → Type) : Nat → Nat → Type where
  | truth : CopyFormula Atom a b
  | equal : Fin a → Fin a → CopyFormula Atom a b
  | member : Fin a → Fin b → CopyFormula Atom a b
  | atom {r : Nat} : Atom r → (Fin r → Fin a) → CopyFormula Atom a b
  | neg : CopyFormula Atom a b → CopyFormula Atom a b
  | conj : CopyFormula Atom a b → CopyFormula Atom a b → CopyFormula Atom a b
  | implies : CopyFormula Atom a b → CopyFormula Atom a b → CopyFormula Atom a b
  | existsFO : CopyFormula Atom (a+1) b → CopyFormula Atom a b
  | allFO : CopyFormula Atom (a+1) b → CopyFormula Atom a b
  | allSet : CopyFormula Atom a (b+1) → CopyFormula Atom a b

def CopyEval (J : Interpretation Atom c) (D : Model) :
    CopyFormula Atom a b → (Fin a → Element c) → (Fin b → Element c → Prop) → Prop
  | .truth, _, _ => True
  | .equal i j, env, _ => env i = env j
  | .member i X, env, sets => sets X (env i)
  | .atom A args, env, _ =>
      Eval D (J.atom A (fun i => (env (args i)).1))
        (fun i => (env (args i)).2) Fin.elim0
  | .neg p, env, sets => ¬ CopyEval J D p env sets
  | .conj p q, env, sets => CopyEval J D p env sets ∧ CopyEval J D q env sets
  | .implies p q, env, sets => CopyEval J D p env sets → CopyEval J D q env sets
  | .existsFO p, env, sets => ∃ x, InDomain J D x ∧ CopyEval J D p (Fin.cases x env) sets
  | .allFO p, env, sets => ∀ x, InDomain J D x → CopyEval J D p (Fin.cases x env) sets
  | .allSet p, env, sets => ∀ X, Supported J D X → CopyEval J D p env (Fin.cases X sets)

/-- Finite disjunction expressed using only the original connectives. -/
def anyFin (fs : Fin c → Formula n m) : Formula n m :=
  .neg (allFin (fun t => .neg (fs t)))

@[simp] theorem eval_anyFin (D : Model) (fs : Fin c → Formula n m)
    (env : Fin n → Nat) (sets : Fin m → Nat → Prop) :
    Eval D (anyFin fs) env sets ↔ ∃ t, Eval D (fs t) env sets := by
  classical
  simp [anyFin, Eval]

private theorem empty_comp {α β : Sort _} (f : α → β) :
    (fun i : Fin 0 => f (Fin.elim0 i)) = Fin.elim0 := by
  funext i
  exact Fin.elim0 i

private theorem addCases_zero (x : Fin 1 → Nat) (env : Fin n → Nat) :
    Fin.addCases x env (0 : Fin (1+n)) = x 0 := rfl

/-- All new set copies stay inside their declared copy domains. The original
allSet support condition already keeps them inside the original graph domain. -/
def setGuard (J : Interpretation Atom c) : Formula n (c+m) :=
  allFin (fun t => .allFO 1 (.implies
    (.member 0 (Fin.castAdd m t))
    ((J.domain t).reindex (fun _ => 0) Fin.elim0)))

theorem eval_setGuard (J : Interpretation Atom c) (D : Model)
    (env : Fin n → Nat) (sets : Fin m → Nat → Prop)
    (X : Fin c → Nat → Prop) :
    Eval D (setGuard J) env (Fin.addCases X sets) ↔
      ∀ t x, x ∈ D.domain → X t x →
        Eval D (J.domain t) (fun _ => x) Fin.elim0 := by
  simp only [setGuard, eval_allFin, Eval, Formula.eval_reindex, Fin.addCases_left, empty_comp, addCases_zero]
  constructor
  · intro h t x hx hX
    exact h t (fun _ => x) (fun _ => hx) hX
  · intro h t values hv hX
    exact h t (values 0) (hv 0) hX

/-- Constructive finite-copy pullback. Arbitrary free-variable maps make capture
avoidance explicit and permit immediate composition with the graph/tree compiler.
One source set binder expands to exactly c original monadic binders. -/
def compile (J : Interpretation Atom c) : CopyFormula Atom a b →
    (Fin a → Fin c) → (Fin a → Fin n) →
    (Fin b → Fin c → Fin m) → Formula n m
  | .truth, _, _, _ => .truth
  | .equal i j, tags, vars, _ =>
      if tags i = tags j then .equal (vars i) (vars j) else .neg .truth
  | .member i X, tags, vars, sets => .member (vars i) (sets X (tags i))
  | .atom A args, tags, vars, _ =>
      (J.atom A (fun i => tags (args i))).reindex (fun i => vars (args i)) Fin.elim0
  | .neg p, tags, vars, sets => .neg (compile J p tags vars sets)
  | .conj p q, tags, vars, sets =>
      .conj (compile J p tags vars sets) (compile J q tags vars sets)
  | .implies p q, tags, vars, sets =>
      .implies (compile J p tags vars sets) (compile J q tags vars sets)
  | .existsFO p, tags, vars, sets => anyFin (fun t => .existsFO 1
      (.conj ((J.domain t).reindex (fun _ => 0) Fin.elim0)
        (compile J p (Fin.cases t tags)
          (Fin.cases 0 (fun i => Fin.natAdd 1 (vars i))) sets)))
  | .allFO p, tags, vars, sets => allFin (fun t => .allFO 1
      (.implies ((J.domain t).reindex (fun _ => 0) Fin.elim0)
        (compile J p (Fin.cases t tags)
          (Fin.cases 0 (fun i => Fin.natAdd 1 (vars i))) sets)))
  | .allSet p, tags, vars, sets => allSets c (.implies (setGuard J)
      (compile J p tags vars
        (Fin.cases (Fin.castAdd m) (fun X t => Fin.natAdd c (sets X t)))))

private theorem fo_cons_env (t : Fin c) (tags : Fin a → Fin c)
    (vars : Fin a → Fin n) (env : Fin n → Nat) (x : Fin 1 → Nat) :
    (fun i => (Fin.cases t tags i,
      Fin.addCases x env (Fin.cases 0 (fun i => Fin.natAdd 1 (vars i)) i))) =
      Fin.cases (t, x 0) (fun i => (tags i, env (vars i))) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp

private theorem set_cons_env (X : Fin c → Nat → Prop)
    (sets : Fin m → Nat → Prop) (map : Fin b → Fin c → Fin m) :
    (fun i v => Fin.addCases X sets
      (Fin.cases (Fin.castAdd m) (fun i t => Fin.natAdd c (map i t)) i v.1) v.2) =
      Fin.cases (joinSet X) (fun i v => sets (map i v.1) v.2) := by
  funext i v
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [joinSet]
  · simp

/-- Semantics-preserving translation for every formula, every free assignment,
and every explicit finite-copy interpretation. No sentence-level assumption. -/
theorem eval_compile (J : Interpretation Atom c) (D : Model)
    (p : CopyFormula Atom a b) (tags : Fin a → Fin c) (vars : Fin a → Fin n)
    (map : Fin b → Fin c → Fin m) (env : Fin n → Nat) (sets : Fin m → Nat → Prop) :
    Eval D (compile J p tags vars map) env sets ↔
      CopyEval J D p (fun i => (tags i, env (vars i)))
        (fun X v => sets (map X v.1) v.2) := by
  induction p generalizing n m with
  | truth => rfl
  | equal i j =>
    simp only [compile, CopyEval]
    split <;> simp_all [Eval, Prod.mk.injEq]
  | member => rfl
  | atom A args =>
    simp only [compile, Formula.eval_reindex, CopyEval, empty_comp]
  | neg p ih => exact not_congr (ih tags vars map env sets)
  | conj p q ihp ihq => exact and_congr (ihp tags vars map env sets) (ihq tags vars map env sets)
  | implies p q ihp ihq => exact imp_congr (ihp tags vars map env sets) (ihq tags vars map env sets)
  | existsFO p ih =>
    simp only [compile, eval_anyFin, Eval, Formula.eval_reindex, ih, fo_cons_env, CopyEval, empty_comp, addCases_zero]
    constructor
    · rintro ⟨t, x, hx, hd, hp⟩
      exact ⟨(t, x 0), ⟨hx 0, hd⟩, hp⟩
    · rintro ⟨⟨t,x⟩, ⟨hx,hd⟩, hp⟩
      exact ⟨t, (fun _ => x), (fun _ => hx), hd, hp⟩
  | allFO p ih =>
    simp only [compile, eval_allFin, Eval, Formula.eval_reindex, ih, fo_cons_env, CopyEval, empty_comp, addCases_zero]
    constructor
    · intro h ⟨t,x⟩ ⟨hx,hd⟩
      exact h t (fun _ => x) (fun _ => hx) hd
    · intro h t x hx hd
      exact h (t, x 0) ⟨hx 0, hd⟩
  | allSet p ih =>
    simp only [compile, eval_allSets, Eval, eval_setGuard, ih, set_cons_env, CopyEval]
    constructor
    · intro h X hX
      have hs := (supported_iff_split J D X).mp hX
      exact h (splitSet X) hs.1 (fun t x _ hx => hs.2 t x hx)
    · intro h X hX hd
      apply h (joinSet X)
      rintro ⟨t,x⟩ hx
      exact ⟨hX t x hx, hd t x (hX t x hx) hx⟩

#print axioms supported_iff_split
#print axioms eval_compile
end StackSorting.SparseEndpointMSO.FiniteCopy
