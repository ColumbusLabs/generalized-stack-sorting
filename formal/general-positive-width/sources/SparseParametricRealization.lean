import SparseParametricFlattening
import SparseFiniteCopyRealization

namespace StackSorting.SparseEndpointMSO.FiniteCopy.Parametric

/-- Obligations for interpreting the real universe. They are pointwise domain,
bijection, and atomic-formula facts, never a whole-sentence recognition premise. -/
structure Realization (J : Interpretation Atom c d) (D : Model) (params : Fin d → Nat → Prop) (α : Type)
    (atoms : {r : Nat} → Atom r → (Fin r → α) → Prop) where
  rep : Element c → α → Prop
  valid : ∀ v x, rep v x → InDomain J D params v
  cover : ∀ x, ∃ v, rep v x
  complete : ∀ v, InDomain J D params v → ∃ x, rep v x
  equal : ∀ v w x y, rep v x → rep w y → (v = w ↔ x = y)
  atom : ∀ {r} (A : Atom r) (env : Fin r → Element c) (actual : Fin r → α),
    (∀ i, rep (env i) (actual i)) →
    (Eval D (J.atom A (fun i => (env i).1)) (fun i => (env i).2) params ↔
      atoms A actual)

variable {J : Interpretation Atom c d} {D : Model} {params : Fin d → Nat → Prop} {α : Type}
  {atoms : {r : Nat} → Atom r → (Fin r → α) → Prop}

def Realization.liftSet (R : Realization J D params α atoms) (X : α → Prop) : Element c → Prop :=
  fun v => ∃ x, R.rep v x ∧ X x

def Realization.lowerSet (R : Realization J D params α atoms) (X : Element c → Prop) : α → Prop :=
  fun x => ∃ v, R.rep v x ∧ X v

theorem Realization.liftSet_supported (R : Realization J D params α atoms) (X : α → Prop) :
    Supported J D params (R.liftSet X) := by
  rintro v ⟨x, hx, _⟩
  exact R.valid v x hx

theorem Realization.liftSet_iff (R : Realization J D params α atoms) (X : α → Prop)
    {v : Element c} {x : α} (h : R.rep v x) : R.liftSet X v ↔ X x := by
  constructor
  · rintro ⟨y, hy, hY⟩
    have he := (R.equal v v y x hy h).mp rfl
    simpa only [he] using hY
  · intro hx
    exact ⟨x, h, hx⟩

theorem Realization.lowerSet_iff (R : Realization J D params α atoms) (X : Element c → Prop)
    {v : Element c} {x : α} (h : R.rep v x) : X v ↔ R.lowerSet X x := by
  constructor
  · intro hx
    exact ⟨v, h, hx⟩
  · rintro ⟨w, hw, hW⟩
    have he := (R.equal w v x x hw h).mpr rfl
    simpa only [he] using hW

theorem Realization.lower_lift (R : Realization J D params α atoms) (X : α → Prop) :
    R.lowerSet (R.liftSet X) = X := by
  funext x
  obtain ⟨v, hv⟩ := R.cover x
  apply propext
  exact (R.lowerSet_iff (R.liftSet X) hv).symm.trans (R.liftSet_iff X hv)

theorem Realization.lift_lower (R : Realization J D params α atoms) (X : Element c → Prop)
    (hs : Supported J D params X) : R.liftSet (R.lowerSet X) = X := by
  funext v
  apply propext
  constructor
  · rintro ⟨x, hx, hX⟩
    exact (R.lowerSet_iff X hx).mpr hX
  · intro hx
    obtain ⟨x, hr⟩ := R.complete v (hs v hx)
    exact ⟨x, hr, (R.lowerSet_iff X hr).mp hx⟩

/-- All actual incidence sets, with no exclusions, correspond exactly to
supported sets of copy codes. Combined with supportedSetEquiv this gives the
claimed fixed original-vertex-set tuple representation. -/
def Realization.setEquiv (R : Realization J D params α atoms) :
    (α → Prop) ≃ {X : Element c → Prop // Supported J D params X} where
  toFun X := ⟨R.liftSet X, R.liftSet_supported X⟩
  invFun X := R.lowerSet X.val
  left_inv X := R.lower_lift X
  right_inv X := by apply Subtype.ext; exact R.lift_lower X.val X.property

/-- Direct equivalence between arbitrary actual incidence sets and the fixed
original-node set tuple, with the exact per-copy support condition. -/
def Realization.vertexTupleEquiv (R : Realization J D params α atoms) :
    (α → Prop) ≃ {X : Fin c → Nat → Prop // CanonicalChoice.SupportedTuple D X ∧
      ∀ t x, X t x → Eval D (J.domain t) (fun _ => x) params} :=
  R.setEquiv.trans (supportedSetEquiv J D params)

/-- Full formula transport from finite-copy semantics to actual incidence MSO. -/
theorem Realization.eval (R : Realization J D params α atoms) (p : CopyFormula Atom a b)
    (env : Fin a → Element c) (actual : Fin a → α)
    (sets : Fin b → Element c → Prop) (actualSets : Fin b → α → Prop)
    (hr : ∀ i, R.rep (env i) (actual i))
    (hs : ∀ i v x, R.rep v x → (sets i v ↔ actualSets i x)) :
    CopyEval J D params p env sets ↔ ActualEval atoms p actual actualSets := by
  induction p with
  | truth => rfl
  | equal i j => exact R.equal _ _ _ _ (hr i) (hr j)
  | member i X => exact hs X _ _ (hr i)
  | atom A args => exact R.atom A _ _ (fun i => hr (args i))
  | neg p ih => exact not_congr (ih env actual sets actualSets hr hs)
  | conj p q ihp ihq =>
    exact and_congr (ihp env actual sets actualSets hr hs) (ihq env actual sets actualSets hr hs)
  | implies p q ihp ihq =>
    exact imp_congr (ihp env actual sets actualSets hr hs) (ihq env actual sets actualSets hr hs)
  | existsFO p ih =>
    constructor
    · rintro ⟨v, hv, hp⟩
      obtain ⟨x, hx⟩ := R.complete v hv
      refine ⟨x, (ih _ _ sets actualSets ?_ hs).mp hp⟩
      intro i
      exact Fin.cases hx hr i
    · rintro ⟨x, hp⟩
      obtain ⟨v, hv⟩ := R.cover x
      refine ⟨v, R.valid v x hv, (ih _ _ sets actualSets ?_ hs).mpr hp⟩
      intro i
      exact Fin.cases hv hr i
  | allFO p ih =>
    constructor
    · intro h x
      obtain ⟨v, hv⟩ := R.cover x
      apply (ih _ _ sets actualSets ?_ hs).mp (h v (R.valid v x hv))
      intro i
      exact Fin.cases hv hr i
    · intro h v hv
      obtain ⟨x, hx⟩ := R.complete v hv
      apply (ih _ _ sets actualSets ?_ hs).mpr (h x)
      intro i
      exact Fin.cases hx hr i
  | allSet p ih =>
    constructor
    · intro h X
      apply (ih env actual _ _ hr ?_).mp (h (R.liftSet X) (R.liftSet_supported X))
      intro i
      refine Fin.cases ?_ (fun j => hs j) i
      intro v x hx
      exact R.liftSet_iff X hx
    · intro h X _
      apply (ih env actual _ _ hr ?_).mpr (h (R.lowerSet X))
      intro i
      refine Fin.cases ?_ (fun j => hs j) i
      intro v x hx
      exact R.lowerSet_iff X hx

/-- Exact original-vocabulary transport for actual interpreted elements and
arbitrary actual free sets. Atomic correctness is required pointwise. -/
theorem Realization.pullback_actual (R : Realization J D params α atoms)
    (p : CopyFormula Atom a b) (tags : Fin a → Fin c) (env : Fin a → Nat)
    (actual : Fin a → α) (sets : Fin b → α → Prop)
    (hr : ∀ i, R.rep (tags i,env i) (actual i)) :
    Eval D (pullback J p tags) env (flattenedSets params (fun i => R.liftSet (sets i))) ↔
      ActualEval atoms p actual sets := by
  rw [eval_pullback]
  exact R.eval p _ actual _ sets hr (fun i v x hx => R.liftSet_iff (sets i) hx)

theorem Realization.flattened_actual_supported (R : Realization J D params α atoms)
    (hp : CanonicalChoice.SupportedTuple D params) (sets : Fin b → α → Prop) :
    CanonicalChoice.SupportedTuple D
      (flattenedSets params (fun i => R.liftSet (sets i))) :=
  flattenedSets_supported J D params _ hp (fun i => R.liftSet_supported (sets i))

#print axioms Realization.vertexTupleEquiv
#print axioms Realization.eval
#print axioms Realization.pullback_actual
#print axioms Realization.flattened_actual_supported
end StackSorting.SparseEndpointMSO.FiniteCopy.Parametric
