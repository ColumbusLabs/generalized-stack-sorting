import SparseFiniteCopy

/-! Parameter-dependent finite-copy pullback. Parameters used by domain and
atom formulas are genuine original-vocabulary unary sets. They remain free
under every binder; one copied set binder introduces exactly c fresh sets. -/
namespace StackSorting.SparseEndpointMSO.FiniteCopy.Parametric
open CanonicalChoice

structure Interpretation (Atom : Nat → Type) (c d : Nat) where
  domain : Fin c → Formula 1 d
  atom : {r : Nat} → Atom r → (Fin r → Fin c) → Formula r d

def InDomain (J : Interpretation Atom c d) (D : Model)
    (params : Fin d → Nat → Prop) (v : Element c) : Prop :=
  v.2 ∈ D.domain ∧ Eval D (J.domain v.1) (fun _ => v.2) params

def Supported (J : Interpretation Atom c d) (D : Model)
    (params : Fin d → Nat → Prop) (X : Element c → Prop) : Prop :=
  ∀ v, X v → InDomain J D params v

theorem supported_iff_split (J : Interpretation Atom c d) (D : Model)
    (params : Fin d → Nat → Prop) (X : Element c → Prop) :
    Supported J D params X ↔ SupportedTuple D (splitSet X) ∧
      ∀ t x, splitSet X t x → Eval D (J.domain t) (fun _ => x) params := by
  constructor
  · intro h
    exact ⟨fun t x hx => (h (t,x) hx).1,fun t x hx => (h (t,x) hx).2⟩
  · rintro ⟨h,hd⟩ ⟨t,x⟩ hx
    exact ⟨h t x hx,hd t x hx⟩

/-- A parameterized bijection, with the fixed parameter tuple held constant.
No injectivity or support assumption on the parameter indexing map is needed. -/
def supportedSetEquiv (J : Interpretation Atom c d) (D : Model)
    (params : Fin d → Nat → Prop) :
    {X : Element c → Prop // Supported J D params X} ≃
    {X : Fin c → Nat → Prop // SupportedTuple D X ∧
      ∀ t x, X t x → Eval D (J.domain t) (fun _ => x) params} where
  toFun X := ⟨splitSet X.val,(supported_iff_split J D params X.val).mp X.property⟩
  invFun X := ⟨joinSet X.val,(supported_iff_split J D params (joinSet X.val)).mpr X.property⟩
  left_inv X := by apply Subtype.ext; rfl
  right_inv X := by apply Subtype.ext; rfl

def CopyEval (J : Interpretation Atom c d) (D : Model) (params : Fin d → Nat → Prop) :
    CopyFormula Atom a b → (Fin a → Element c) → (Fin b → Element c → Prop) → Prop
  | .truth, _, _ => True
  | .equal i j, env, _ => env i = env j
  | .member i X, env, sets => sets X (env i)
  | .atom A args, env, _ =>
      Eval D (J.atom A (fun i => (env (args i)).1))
        (fun i => (env (args i)).2) params
  | .neg p, env, sets => ¬ CopyEval J D params p env sets
  | .conj p q, env, sets => CopyEval J D params p env sets ∧ CopyEval J D params q env sets
  | .implies p q, env, sets => CopyEval J D params p env sets → CopyEval J D params q env sets
  | .existsFO p, env, sets => ∃ x, InDomain J D params x ∧
      CopyEval J D params p (Fin.cases x env) sets
  | .allFO p, env, sets => ∀ x, InDomain J D params x →
      CopyEval J D params p (Fin.cases x env) sets
  | .allSet p, env, sets => ∀ X, Supported J D params X →
      CopyEval J D params p env (Fin.cases X sets)

/-- The new bound sets occupy indices below c. Every fixed parameter is
explicitly shifted past all of them, preventing capture by a set binder. -/
def setGuard (J : Interpretation Atom c d) (params : Fin d → Fin m) : Formula n (c+m) :=
  allFin (fun t => .allFO 1 (.implies (.member 0 (Fin.castAdd m t))
    ((J.domain t).reindex (fun _ => 0) (fun i => Fin.natAdd c (params i)))))

private theorem addCases_zero (x : Fin 1 → Nat) (env : Fin n → Nat) :
    Fin.addCases x env (0 : Fin (1+n)) = x 0 := rfl

private theorem params_cons_env (X : Fin c → Nat → Prop)
    (sets : Fin m → Nat → Prop) (params : Fin d → Fin m) :
    (fun i => Fin.addCases X sets (Fin.natAdd c (params i))) =
      (fun i => sets (params i)) := by
  funext i
  simp only [Fin.addCases_right]

theorem eval_setGuard (J : Interpretation Atom c d) (D : Model)
    (params : Fin d → Fin m) (env : Fin n → Nat) (sets : Fin m → Nat → Prop)
    (X : Fin c → Nat → Prop) :
    Eval D (setGuard J params) env (Fin.addCases X sets) ↔
      ∀ t x, x ∈ D.domain → X t x →
        Eval D (J.domain t) (fun _ => x) (fun i => sets (params i)) := by
  simp only [setGuard,eval_allFin,Eval,Formula.eval_reindex,
    Fin.addCases_left,Fin.addCases_right,addCases_zero]
  constructor
  · intro h t x hx hX
    exact h t (fun _ => x) (fun _ => hx) hX
  · intro h t values hv hX
    exact h t (values 0) (hv 0) hX

/-- All output atoms are actual I/R/S/M formulas. Both the fixed-parameter
map and copied-free-set map are explicit; neither is an oracle predicate. -/
def compile (J : Interpretation Atom c d) : CopyFormula Atom a b →
    (Fin a → Fin c) → (Fin a → Fin n) →
    (Fin b → Fin c → Fin m) → (Fin d → Fin m) → Formula n m
  | .truth, _, _, _, _ => .truth
  | .equal i j, tags, vars, _, _ =>
      if tags i = tags j then .equal (vars i) (vars j) else .neg .truth
  | .member i X, tags, vars, sets, _ => .member (vars i) (sets X (tags i))
  | .atom A args, tags, vars, _, params =>
      (J.atom A (fun i => tags (args i))).reindex (fun i => vars (args i)) params
  | .neg p, tags, vars, sets, params => .neg (compile J p tags vars sets params)
  | .conj p q, tags, vars, sets, params =>
      .conj (compile J p tags vars sets params) (compile J q tags vars sets params)
  | .implies p q, tags, vars, sets, params =>
      .implies (compile J p tags vars sets params) (compile J q tags vars sets params)
  | .existsFO p, tags, vars, sets, params => anyFin (fun t => .existsFO 1
      (.conj ((J.domain t).reindex (fun _ => 0) params)
        (compile J p (Fin.cases t tags)
          (Fin.cases 0 (fun i => Fin.natAdd 1 (vars i))) sets params)))
  | .allFO p, tags, vars, sets, params => allFin (fun t => .allFO 1
      (.implies ((J.domain t).reindex (fun _ => 0) params)
        (compile J p (Fin.cases t tags)
          (Fin.cases 0 (fun i => Fin.natAdd 1 (vars i))) sets params)))
  | .allSet p, tags, vars, sets, params => allSets c (.implies (setGuard J params)
      (compile J p tags vars
        (Fin.cases (Fin.castAdd m) (fun X t => Fin.natAdd c (sets X t)))
        (fun i => Fin.natAdd c (params i))))

private theorem fo_cons_env (t : Fin c) (tags : Fin a → Fin c)
    (vars : Fin a → Fin n) (env : Fin n → Nat) (x : Fin 1 → Nat) :
    (fun i => (Fin.cases t tags i,
      Fin.addCases x env (Fin.cases 0 (fun i => Fin.natAdd 1 (vars i)) i))) =
      Fin.cases (t,x 0) (fun i => (tags i,env (vars i))) := by
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

/-- Pointwise correctness for arbitrary syntax and assignments. Fixed
parameters are preserved through arbitrary nesting of both binder sorts. -/
theorem eval_compile (J : Interpretation Atom c d) (D : Model)
    (p : CopyFormula Atom a b) (tags : Fin a → Fin c) (vars : Fin a → Fin n)
    (map : Fin b → Fin c → Fin m) (params : Fin d → Fin m)
    (env : Fin n → Nat) (sets : Fin m → Nat → Prop) :
    Eval D (compile J p tags vars map params) env sets ↔
      CopyEval J D (fun i => sets (params i)) p
        (fun i => (tags i,env (vars i))) (fun X v => sets (map X v.1) v.2) := by
  induction p generalizing n m with
  | truth => rfl
  | equal i j =>
    simp only [compile,CopyEval]
    split <;> simp_all [Eval,Prod.mk.injEq]
  | member => rfl
  | atom A args => simp only [compile,Formula.eval_reindex,CopyEval]
  | neg p ih => exact not_congr (ih tags vars map params env sets)
  | conj p q ihp ihq =>
    exact and_congr (ihp tags vars map params env sets) (ihq tags vars map params env sets)
  | implies p q ihp ihq =>
    exact imp_congr (ihp tags vars map params env sets) (ihq tags vars map params env sets)
  | existsFO p ih =>
    simp only [compile,eval_anyFin,Eval,Formula.eval_reindex,ih,fo_cons_env,
      CopyEval,addCases_zero]
    constructor
    · rintro ⟨t,x,hx,hd,hp⟩
      exact ⟨(t,x 0),⟨hx 0,hd⟩,hp⟩
    · rintro ⟨⟨t,x⟩,⟨hx,hd⟩,hp⟩
      exact ⟨t,(fun _ => x),(fun _ => hx),hd,hp⟩
  | allFO p ih =>
    simp only [compile,eval_allFin,Eval,Formula.eval_reindex,ih,fo_cons_env,
      CopyEval,addCases_zero]
    constructor
    · intro h ⟨t,x⟩ ⟨hx,hd⟩
      exact h t (fun _ => x) (fun _ => hx) hd
    · intro h t x hx hd
      exact h (t,x 0) ⟨hx 0,hd⟩
  | allSet p ih =>
    simp only [compile,eval_allSets,Eval,eval_setGuard,ih,params_cons_env,
      set_cons_env,CopyEval]
    constructor
    · intro h X hX
      have hs := (supported_iff_split J D _ X).mp hX
      exact h (splitSet X) hs.1 (fun t x _ hx => hs.2 t x hx)
    · intro h X hX hd
      apply h (joinSet X)
      rintro ⟨t,x⟩ hx
      exact ⟨hX t x hx,hd t x (hX t x hx) hx⟩

#print axioms supported_iff_split
#print axioms eval_compile
end StackSorting.SparseEndpointMSO.FiniteCopy.Parametric
