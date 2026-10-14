import GeneralizedEndpointMSO

/-! Genuine sparse event MSO: no reachability, order, endpoint comparison,
eligibility or machine property is an atom. -/
namespace StackSorting.SparseEndpointMSO

structure Model where
  domain : List Nat
  I : Nat → Prop
  R : Nat → Prop
  S : Nat → Nat → Prop
  M : Nat → Nat → Prop

inductive Formula : Nat → Nat → Type where
  | truth : Formula a b
  | equal : Fin a → Fin a → Formula a b
  | member : Fin a → Fin b → Formula a b
  | insert : Fin a → Formula a b
  | remove : Fin a → Formula a b
  | successor : Fin a → Fin a → Formula a b
  | matching : Fin a → Fin a → Formula a b
  | neg : Formula a b → Formula a b
  | conj : Formula a b → Formula a b → Formula a b
  | implies : Formula a b → Formula a b → Formula a b
  | existsFO (k : Nat) : Formula (k + a) b → Formula a b
  | allFO (k : Nat) : Formula (k + a) b → Formula a b
  | allSet : Formula a (b + 1) → Formula a b

def Eval (D : Model) : Formula a b → (Fin a → Nat) →
    (Fin b → Nat → Prop) → Prop
  | .truth, _, _ => True
  | .equal i j, env, _ => env i = env j
  | .member i X, env, sets => sets X (env i)
  | .insert i, env, _ => D.I (env i)
  | .remove i, env, _ => D.R (env i)
  | .successor i j, env, _ => D.S (env i) (env j)
  | .matching i j, env, _ => D.M (env i) (env j)
  | .neg f, env, sets => ¬ Eval D f env sets
  | .conj f g, env, sets => Eval D f env sets ∧ Eval D g env sets
  | .implies f g, env, sets => Eval D f env sets → Eval D g env sets
  | .existsFO k f, env, sets => ∃ values : Fin k → Nat,
      (∀ i, values i ∈ D.domain) ∧ Eval D f (Fin.addCases values env) sets
  | .allFO k f, env, sets => ∀ values : Fin k → Nat,
      (∀ i, values i ∈ D.domain) → Eval D f (Fin.addCases values env) sets
  | .allSet f, env, sets => ∀ X : Nat → Prop,
      (∀ v, X v → v ∈ D.domain) → Eval D f env (Fin.cases X sets)

def Satisfies (D : Model) (f : Formula 0 0) : Prop := Eval D f Fin.elim0 Fin.elim0

def conjoin : List (Formula a b) → Formula a b
  | [] => .truth
  | f :: fs => .conj f (conjoin fs)

def allFin (fs : Fin k → Formula a b) : Formula a b := conjoin (List.ofFn fs)

@[simp] theorem eval_conjoin (D : Model) (fs : List (Formula a b))
    (env : Fin a → Nat) (sets : Fin b → Nat → Prop) :
    Eval D (conjoin fs) env sets ↔ ∀ f ∈ fs, Eval D f env sets := by
  induction fs with
  | nil => simp [conjoin, Eval]
  | cons f fs ih => simp [conjoin, Eval, ih]

@[simp] theorem eval_allFin (D : Model) (fs : Fin k → Formula a b)
    (env : Fin a → Nat) (sets : Fin b → Nat → Prop) :
    Eval D (allFin fs) env sets ↔ ∀ i, Eval D (fs i) env sets := by
  simp [allFin, List.mem_ofFn]

/-- The usual closed-set MSO formula for reflexive reachability. The fresh set
is index zero. Fresh individual variables p,q are zero and one. -/
def reach (i j : Fin a) : Formula a b :=
  .allSet (.implies
    (.conj (.member i 0)
      (.allFO 2 (.implies
        (.conj (.member ((0 : Fin 2).castAdd a) 0)
          (.successor ((0 : Fin 2).castAdd a) ((1 : Fin 2).castAdd a)))
        (.member ((1 : Fin 2).castAdd a) 0))))
    (.member j 0))

def strictBefore (i j : Fin a) : Formula a b :=
  .conj (.neg (.equal i j)) (reach i j)

/-- Semantic closed-set reachability, with sets and vertices bounded by domain. -/
def ClosedReach (D : Model) (x y : Nat) : Prop :=
  ∀ X : Nat → Prop, (∀ v, X v → v ∈ D.domain) →
    X x → (∀ p ∈ D.domain, ∀ q ∈ D.domain, X p → D.S p q → X q) → X y

theorem eval_reach (D : Model) (i j : Fin a)
    (env : Fin a → Nat) (sets : Fin b → Nat → Prop) :
    Eval D (reach i j) env sets ↔ ClosedReach D (env i) (env j) := by
  simp only [reach, Eval, Fin.cases_zero, Fin.addCases_left]
  constructor
  · intro h X hX hx hclosed
    apply h X hX ⟨hx, ?_⟩
    intro values hv h
    exact hclosed (values 0) (hv 0) (values 1) (hv 1) h.1 h.2
  · intro h X hX hx
    apply h X hX hx.1
    intro p hp q hq hxp hpq
    let values : Fin 2 → Nat := Fin.cases p (fun _ => q)
    have hv : ∀ i, values i ∈ D.domain := by
      intro i; exact Fin.cases hp (fun _ => hq) i
    exact hx.2 values hv ⟨hxp, hpq⟩

/-- Finite successor walks are defined independently of the MSO formula. -/
inductive Walk (D : Model) (x : Nat) : Nat → Prop where
  | refl (hx : x ∈ D.domain) : Walk D x x
  | step {p q : Nat} : Walk D x p → q ∈ D.domain → D.S p q → Walk D x q

theorem Walk.mem {D : Model} {x y : Nat} (h : Walk D x y) : y ∈ D.domain := by
  cases h with
  | refl hx => exact hx
  | step _ hq _ => exact hq

theorem closedReach_iff_walk (D : Model) {x y : Nat} (hx : x ∈ D.domain) :
    ClosedReach D x y ↔ Walk D x y := by
  constructor
  · intro h
    exact h (Walk D x) (fun _ h => h.mem) (.refl hx)
      (fun _ _ _ hq hp hs => .step hp hq hs)
  · intro h X hX hstart hclosed
    induction h with
    | refl => exact hstart
    | @step p q hp hq hs ih => exact hclosed p hp.mem q hq ih hs

/-- A diagram whose only successor edges are consecutive finite time indices. -/
def TimePath (D : Model) (length : Nat) : Prop :=
  D.domain = List.range length ∧
    ∀ x ∈ D.domain, ∀ y ∈ D.domain, D.S x y ↔ x + 1 = y

theorem walk_iff_le (D : Model) (length : Nat) (hpath : TimePath D length)
    {x y : Nat} (hx : x ∈ D.domain) (hy : y ∈ D.domain) :
    Walk D x y ↔ x ≤ y := by
  constructor
  · intro h
    induction h with
    | refl => exact Nat.le_refl _
    | @step p q hp hq hs ih =>
      have he := (hpath.2 p hp.mem q hq).mp hs
      have hxp := ih hp.mem
      omega
  · intro hle
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    clear hle
    induction d with
    | zero => simpa using Walk.refl (D := D) hx
    | succ d ih =>
      have hm : x + d ∈ D.domain := by
        rw [hpath.1, List.mem_range] at hy ⊢
        omega
      exact .step (ih hm) hy ((hpath.2 _ hm _ hy).mpr (by omega))

theorem eval_strictBefore (D : Model) (length : Nat) (hpath : TimePath D length)
    (i j : Fin a) (env : Fin a → Nat) (sets : Fin b → Nat → Prop)
    (hi : env i ∈ D.domain) (hj : env j ∈ D.domain) :
    Eval D (strictBefore i j) env sets ↔ env i < env j := by
  simp only [strictBefore, Eval]
  rw [eval_reach, closedReach_iff_walk D hi, walk_iff_le D length hpath hi hj]
  omega

end StackSorting.SparseEndpointMSO
