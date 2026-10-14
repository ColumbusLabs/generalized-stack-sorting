import SparseEndpointMSO

namespace StackSorting.SparseEndpointMSO
open IntervalCritical
open EndpointMSO (Side endpoint endpointModel)

/-- Explicit geometric encoding data. This contract contains only domain,
labels, successor and unique endpoint matching facts; no logical preservation
or feasibility proposition is assumed. It is instantiated for canonical events
in CanonicalSparseEndpoint.lean. -/
structure Encoding (D : Model) (e : Endpoints) (U : List Nat) where
  length : Nat
  path : TimePath D length
  left_mem : ∀ v ∈ U, e.left v ∈ D.domain
  right_mem : ∀ v ∈ U, e.right v ∈ D.domain
  left_inj : ∀ u ∈ U, ∀ v ∈ U, e.left u = e.left v → u = v
  insert_iff : ∀ x, D.I x ↔ ∃ v ∈ U, e.left v = x
  remove_right : ∀ v ∈ U, D.R (e.right v)
  matching_iff : ∀ v ∈ U, ∀ y ∈ D.domain, D.M (e.left v) y ↔ y = e.right v

/-- Select the requested endpoint of an insertion vertex. Right endpoints are
found by an existential matching edge, rather than stored in an atom. -/
def atEndpoint (side : Side) (token point : Fin a) : Formula a b :=
  match side with
  | .left => .equal token point
  | .right => .conj (.remove point) (.matching token point)

def compareEndpoints (p q : Side) (i j : Fin a) : Formula a b :=
  .existsFO 2 (.conj (atEndpoint p (Fin.natAdd 2 i) ((0 : Fin 2).castAdd a))
    (.conj (atEndpoint q (Fin.natAdd 2 j) ((1 : Fin 2).castAdd a))
      (strictBefore ((0 : Fin 2).castAdd a) ((1 : Fin 2).castAdd a))))

def insertionBlock (k a b : Nat) : Formula (k+a) b :=
  allFin fun i : Fin k => .insert (i.castAdd a)

def onlyInsertions (X : Fin b) : Formula a b :=
  .allFO 1 (.implies (.member ((0 : Fin 1).castAdd a) X)
    (.insert ((0 : Fin 1).castAdd a)))

/-- Structural translation, including relativization of BOTH quantifier sorts.
All dense comparisons expand into matching plus closed-set time reachability. -/
def translate : EndpointMSO.Formula a b → Formula a b
  | .truth => .truth
  | .equal i j => .equal i j
  | .member i X => .member i X
  | .before p q i j => compareEndpoints p q i j
  | .neg f => .neg (translate f)
  | .conj f g => .conj (translate f) (translate g)
  | .implies f g => .implies (translate f) (translate g)
  | .existsFO k f => .existsFO k (.conj (insertionBlock k _ _) (translate f))
  | .allSet f => .allSet (.implies (onlyInsertions 0) (translate f))

theorem eval_onlyInsertions (D : Model) (X : Fin b)
    (env : Fin a → Nat) (sets : Fin b → Nat → Prop) :
    Eval D (onlyInsertions X) env sets ↔ ∀ x ∈ D.domain, sets X x → D.I x := by
  simp only [onlyInsertions, Eval, Fin.addCases_left]
  constructor
  · intro h x hx
    exact h (fun _ => x) (fun _ => hx)
  · intro h values hv
    exact h (values 0) (hv 0)

theorem eval_atEndpoint {D : Model} {e : Endpoints} {U : List Nat}
    (enc : Encoding D e U) (side : Side) (i j : Fin a)
    (env : Fin a → Nat) (sets : Fin b → Nat → Prop)
    {v : Nat} (hv : v ∈ U) (hi : env i = e.left v) (hj : env j ∈ D.domain) :
    Eval D (atEndpoint side i j) env sets ↔ env j = endpoint e side v := by
  cases side with
  | left => simp [atEndpoint, Eval, hi, endpoint, eq_comm]
  | right =>
    simp only [atEndpoint, Eval, hi, enc.matching_iff v hv _ hj, endpoint]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ enc.remove_right v hv, h⟩⟩

theorem eval_compareEndpoints {D : Model} {e : Endpoints} {U : List Nat}
    (enc : Encoding D e U) (p q : Side) (i j : Fin a)
    (env : Fin a → Nat) (sets : Fin b → Nat → Prop)
    {u v : Nat} (hu : u ∈ U) (hv : v ∈ U)
    (hi : env i = e.left u) (hj : env j = e.left v) :
    Eval D (compareEndpoints p q i j) env sets ↔ endpoint e p u < endpoint e q v := by
  have hmem : ∀ side t, t ∈ U → endpoint e side t ∈ D.domain := by
    intro side t ht; cases side
    · exact enc.left_mem t ht
    · exact enc.right_mem t ht
  simp only [compareEndpoints, Eval]
  constructor
  · rintro ⟨w, hw, hleft, hright, hlt⟩
    have hl := (eval_atEndpoint enc p _ _ _ sets hu (by simpa using hi) (by simpa using hw 0)).mp hleft
    have hr := (eval_atEndpoint enc q _ _ _ sets hv (by simpa using hj) (by simpa using hw 1)).mp hright
    have ht := (eval_strictBefore D enc.length enc.path _ _ _ sets
      (by simpa using hw 0) (by simpa using hw 1)).mp hlt
    simpa only [hl, hr] using ht
  · intro hlt
    let w : Fin 2 → Nat := Fin.cases (endpoint e p u) (fun _ => endpoint e q v)
    have hw : ∀ i, w i ∈ D.domain :=
      fun i => Fin.cases (hmem p u hu) (fun _ => hmem q v hv) i
    refine ⟨w, hw, ?_, ?_, ?_⟩
    · apply (eval_atEndpoint enc p _ _ _ sets hu (by simpa using hi) (by simpa using hw 0)).mpr
      rfl
    · apply (eval_atEndpoint enc q _ _ _ sets hv (by simpa using hj) (by simpa using hw 1)).mpr
      rfl
    · apply (eval_strictBefore D enc.length enc.path _ _ _ sets
        (by simpa using hw 0) (by simpa using hw 1)).mpr
      exact hlt

/-- Push forward a token subset to its insertion events. -/
def liftSet (e : Endpoints) (U : List Nat) (X : Nat → Prop) (x : Nat) : Prop :=
  ∃ v ∈ U, X v ∧ e.left v = x

theorem liftSet_at_left {D : Model} {e : Endpoints} {U : List Nat}
    (enc : Encoding D e U) (X : Nat → Prop) {v : Nat} (hv : v ∈ U) :
    liftSet e U X (e.left v) ↔ X v := by
  constructor
  · rintro ⟨u, hu, hX, he⟩
    exact enc.left_inj u hu v hv he ▸ hX
  · intro h; exact ⟨v, hv, h, rfl⟩

/-- Truth preservation for every formula in the entire dense fragment, for
arbitrary related assignments, proved by structural induction. -/
theorem eval_translate {D : Model} {e : Endpoints} {U : List Nat}
    (enc : Encoding D e U) (f : EndpointMSO.Formula a b)
    (tenv : Fin a → Nat) (eenv : Fin a → Nat)
    (tsets : Fin b → Nat → Prop) (esets : Fin b → Nat → Prop)
    (hdom : ∀ i, tenv i ∈ U) (henv : ∀ i, eenv i = e.left (tenv i))
    (hsets : ∀ X v, v ∈ U → (esets X (e.left v) ↔ tsets X v)) :
    Eval D (translate f) eenv esets ↔ EndpointMSO.Eval (endpointModel e U) f tenv tsets := by
  classical
  induction f with
  | truth => rfl
  | equal i j =>
    simp only [translate, Eval, EndpointMSO.Eval, henv]
    exact ⟨enc.left_inj _ (hdom i) _ (hdom j), congrArg e.left⟩
  | member i X =>
    simp only [translate, Eval, EndpointMSO.Eval, henv]
    exact hsets X _ (hdom i)
  | before p q i j =>
    exact eval_compareEndpoints enc p q i j eenv esets (hdom i) (hdom j) (henv i) (henv j)
  | neg f ih =>
    simp only [translate, Eval, EndpointMSO.Eval]
    exact not_congr (ih tenv eenv tsets esets hdom henv hsets)
  | conj f g ihf ihg =>
    simp only [translate, Eval, EndpointMSO.Eval]
    exact and_congr (ihf tenv eenv tsets esets hdom henv hsets)
      (ihg tenv eenv tsets esets hdom henv hsets)
  | implies f g ihf ihg =>
    simp only [translate, Eval, EndpointMSO.Eval]
    exact imp_congr (ihf tenv eenv tsets esets hdom henv hsets)
      (ihg tenv eenv tsets esets hdom henv hsets)
  | @existsFO a b k f ih =>
    simp only [translate, Eval, insertionBlock, eval_allFin, Fin.addCases_left]
    constructor
    · rintro ⟨ev, hev, hins, hf⟩
      have hex : ∀ i, ∃ v ∈ U, e.left v = ev i := fun i => (enc.insert_iff _).mp (hins i)
      let tv : Fin k → Nat := fun i => Classical.choose (hex i)
      have htv : ∀ i, tv i ∈ U := fun i => (Classical.choose_spec (hex i)).1
      have hve : ∀ i, ev i = e.left (tv i) := fun i => (Classical.choose_spec (hex i)).2.symm
      refine ⟨tv, htv, ?_⟩
      apply (ih (Fin.addCases tv tenv) (Fin.addCases ev eenv) tsets esets
        (fun i => Fin.addCases (fun j => by simpa [endpointModel] using htv j)
          (fun j => by simpa using hdom j) i) ?_ hsets).mp hf
      intro i; exact Fin.addCases (fun j => by simpa using hve j)
        (fun j => by simpa using henv j) i
    · rintro ⟨tv, htv, hf⟩
      let ev : Fin k → Nat := fun i => e.left (tv i)
      refine ⟨ev, (fun i => enc.left_mem _ (htv i)), ?_, ?_⟩
      · intro i; exact (enc.insert_iff _).mpr ⟨tv i, htv i, rfl⟩
      · apply (ih (Fin.addCases tv tenv) (Fin.addCases ev eenv) tsets esets
          (fun i => Fin.addCases (fun j => by simpa [endpointModel] using htv j)
          (fun j => by simpa using hdom j) i) ?_ hsets).mpr hf
        intro i; exact Fin.addCases (fun j => by simp [ev])
          (fun j => by simpa using henv j) i
  | @allSet a b f ih =>
    simp only [translate, Eval]
    constructor
    · intro h X hX
      let Y := liftSet e U X
      have hY : ∀ x, Y x → x ∈ D.domain := by
        rintro x ⟨v, hv, _, rfl⟩; exact enc.left_mem v hv
      have hI : Eval D (onlyInsertions 0) eenv (Fin.cases Y esets) := by
        apply (eval_onlyInsertions _ _ _ _).mpr
        intro x _ hx; obtain ⟨v, hv, _, he⟩ := hx
        exact (enc.insert_iff x).mpr ⟨v, hv, he⟩
      apply (ih tenv eenv (Fin.cases X tsets) (Fin.cases Y esets) hdom henv ?_).mp (h Y hY hI)
      intro Z v hv
      exact Fin.cases (liftSet_at_left enc X hv) (fun Z => hsets Z v hv) Z
    · intro h Y hY hI
      have hIns := (eval_onlyInsertions D 0 eenv (Fin.cases Y esets)).mp hI
      let X : Nat → Prop := fun v => v ∈ U ∧ Y (e.left v)
      have hX : ∀ v, X v → v ∈ U := fun _ hv => hv.1
      apply (ih tenv eenv (Fin.cases X tsets) (Fin.cases Y esets) hdom henv ?_).mpr (h X hX)
      intro Z v hv
      exact Fin.cases (by simp [X, hv]) (fun Z => hsets Z v hv) Z

theorem satisfies_translate {D : Model} {e : Endpoints} {U : List Nat}
    (enc : Encoding D e U) (f : EndpointMSO.Formula 0 0) :
    Satisfies D (translate f) ↔ EndpointMSO.Satisfies (endpointModel e U) f :=
  eval_translate enc f Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun X => Fin.elim0 X)

def eligibilitySentence (r s : Nat) : Formula 0 0 :=
  translate (EndpointMSO.eligibilitySentence r s)

end StackSorting.SparseEndpointMSO
