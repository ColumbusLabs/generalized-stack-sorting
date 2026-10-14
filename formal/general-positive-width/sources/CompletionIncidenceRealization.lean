import CompletionIncidenceSyntax

namespace StackSorting.CapturedLinkExtraction.MultiMargin.CompletionIncidence
open SparseEndpointMSO SparseEndpointMSO.Guidance SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.IncidenceOwnership GraphWidth GraphWidth.Nested
variable {D : Model} {n t k : Nat} {G : Graph n} {T : FinitePort.RootedTree t}
variable (dec : Decomposition G T) (names : Fin n ≃ Vertex D)

def vertex : Actual (D := D) dec → Prop
  | .inl x => IsVertex x
  | .inr _ => False

def edge : Actual (D := D) dec → Prop
  | .inl x => IsEdge x
  | .inr _ => True

def originalEdge : Actual (D := D) dec → Prop
  | .inl x => IsEdge x
  | .inr _ => False

def extraEdge : Actual (D := D) dec → Prop
  | .inl _ => False
  | .inr _ => True

def incident : Actual (D := D) dec → Actual (D := D) dec → Prop
  | .inl x, .inl e => ElementIncident x e
  | .inl x, .inr e => x=namedVertex names e.val.1 ∨ x=namedVertex names e.val.2
  | .inr _, _ => False

def originalIncident : Actual (D := D) dec → Actual (D := D) dec → Prop
  | .inl x, .inl e => ElementIncident x e
  | _, _ => False

def insert : Actual (D := D) dec → Prop
  | .inl x => ElementInsert x
  | .inr _ => False

def remove : Actual (D := D) dec → Prop
  | .inl x => ElementRemove x
  | .inr _ => False

def actualAtom : {r : Nat} → Atom r → (Fin r → Actual (D := D) dec) → Prop
  | _, .vertex, env => vertex dec (env 0)
  | _, .edge, env => edge dec (env 0)
  | _, .originalEdge, env => originalEdge dec (env 0)
  | _, .extraEdge, env => extraEdge dec (env 0)
  | _, .incidence, env => incident dec names (env 0) (env 1)
  | _, .originalIncidence, env => originalIncident dec (env 0) (env 1)
  | _, .insert, env => insert dec (env 0)
  | _, .remove, env => remove dec (env 0)

variable (C : Colors D k) (hc : C.Valid) (hcap : Captured dec names C)

include hc in
theorem endpoint_chosen (e : ExtraEdge dec) (x : IncidenceOwnership.Element D) :
    let q := chosenCandidate names C hcap e
    ActualEval AtomEval (endpoint (fixedIndices k) q.1 q.2.1 (0 : Fin 2) 1)
      (Fin.cases x (fun _ => q.2.2)) (sets dec names C hcap) ↔
      x=namedVertex names e.val.1 ∨ x=namedVertex names e.val.2 := by
  dsimp only
  have hr := chosenCandidate_spec names C hcap e
  simp only [endpoint,orFormula,ActualEval,not_and_or,not_not,eval_rootFormula,
    sets_color,Fin.cases_zero]
  change (ColorRoot C (chosenCandidate names C hcap e).1
      (chosenCandidate names C hcap e).2.2 x ∨
    ColorRoot C (chosenCandidate names C hcap e).2.1
      (chosenCandidate names C hcap e).2.2 x) ↔ _
  constructor
  · rintro (hx | hx)
    · exact Or.inl (colors_root_unique hc _ hx hr.1)
    · exact Or.inr (colors_root_unique hc _ hx hr.2)
  · rintro (rfl | rfl)
    · exact Or.inl hr.1
    · exact Or.inr hr.2

include hc in
/-- The actual atom semantics follows directly from the two physical
endpoints and the explicitly chosen representative, for every atom. -/
theorem encoded_atoms {r : Nat} (A : Atom r) (env : Fin r → Actual (D := D) dec) :
    Parametric.stepAtoms (copies k) AtomEval (sets dec names C hcap) A
      (fun i => encode dec names C hcap (env i)) ↔ actualAtom dec names A env := by
  cases A with
  | vertex =>
    cases h : env 0 <;>
      simp [Parametric.stepAtoms,copies,atom,encode,h,actualAtom,vertex,
        vertexFormula,AtomEval,ActualEval]
  | edge =>
    cases h : env 0 <;>
      simp [Parametric.stepAtoms,copies,atom,encode,h,actualAtom,edge,
        edgeFormula,AtomEval,ActualEval]
  | originalEdge =>
    cases h : env 0 <;>
      simp [Parametric.stepAtoms,copies,atom,encode,h,actualAtom,originalEdge,
        edgeFormula,AtomEval,ActualEval]
  | extraEdge =>
    cases h : env 0 <;>
      simp [Parametric.stepAtoms,copies,atom,encode,h,actualAtom,extraEdge,ActualEval]
  | insert =>
    cases h : env 0 <;>
      simp [Parametric.stepAtoms,copies,atom,encode,h,actualAtom,insert,AtomEval,ActualEval]
  | remove =>
    cases h : env 0 <;>
      simp [Parametric.stepAtoms,copies,atom,encode,h,actualAtom,remove,AtomEval,ActualEval]
  | originalIncidence =>
    cases h0 : env 0 <;> cases h1 : env 1 <;>
      simp [Parametric.stepAtoms,copies,atom,encode,h0,h1,actualAtom,originalIncident,
        incidentFormula,AtomEval,ActualEval]
  | incidence =>
    cases h0 : env 0 with
    | inr e =>
      simp [Parametric.stepAtoms,copies,atom,encode,h0,actualAtom,incident,ActualEval]
    | inl x =>
      cases h1 : env 1 with
      | inl y =>
        simp [Parametric.stepAtoms,copies,atom,encode,h0,h1,actualAtom,incident,
          incidentFormula,AtomEval,ActualEval]
      | inr e =>
        have hh := endpoint_chosen dec names C hc hcap e x
        simpa [Parametric.stepAtoms,copies,atom,encode,h0,h1,actualAtom,incident,
          endpoint,orFormula,ActualEval,eval_rootFormula,sets_color] using hh

/-- Zero-parameter promotion does not add semantic assumptions. -/
def physicalRealization (hD : Laws D) :
    Parametric.Realization (Parametric.ofPlain IncidenceOwnership.interpretation)
      D Fin.elim0 (IncidenceOwnership.Element D) AtomEval where
  rep := (IncidenceOwnership.realization hD).rep
  valid := (IncidenceOwnership.realization hD).valid
  cover := (IncidenceOwnership.realization hD).cover
  complete := (IncidenceOwnership.realization hD).complete
  equal := (IncidenceOwnership.realization hD).equal
  atom := (IncidenceOwnership.realization hD).atom

noncomputable def params (hD : Laws D) : Fin (0+parameterCount k*3) → Nat → Prop :=
  Parametric.flattenedSets Fin.elim0
    (fun i => (physicalRealization hD).liftSet (sets dec names C hcap i))

theorem params_supported (hD : Laws D) :
    CanonicalChoice.SupportedTuple D (params dec names C hcap hD) := by
  exact Parametric.flattenedSets_supported _ _ _ _
    (fun i => Fin.elim0 i)
    (fun i => (physicalRealization hD).liftSet_supported (sets dec names C hcap i))

/-- Actual simple completion-incidence realization. Equality is equality
of originals or of actual ordered extra edges, never a compiler quotient. -/
noncomputable def realization (hD : Laws D) :
    Parametric.Realization (interpretation k) D (params dec names C hcap hD)
      (Actual (D := D) dec) (actualAtom dec names) := by
  let R := (physicalRealization hD).compose (copies k) (sets dec names C hcap)
  let E := codeEquiv dec names C hcap hc
  exact {
    rep := fun v x => R.rep v (E x)
    valid := fun v x hx => R.valid v (E x) hx
    cover := fun x => R.cover (E x)
    complete := fun v hv => by
      obtain ⟨x,hx⟩ := R.complete v hv
      exact ⟨E.symm x,by simpa only [Equiv.apply_symm_apply] using hx⟩
    equal := fun v w x y hx hy => (R.equal v w (E x) (E y) hx hy).trans
      ⟨fun h => E.injective h,fun h => congrArg E h⟩
    atom := fun A env actual hr => (R.atom A env (fun i => E (actual i)) hr).trans
      (encoded_atoms dec names C hc hcap A actual)
  }

/-- All actual incidence sets, including synthetic-edge-only sets, are
represented by exactly 3+3*k*k supported original vertex-set copies. -/
noncomputable def setEquiv (hD : Laws D) :=
  (realization dec names C hc hcap hD).vertexTupleEquiv

theorem compiled_actual (hD : Laws D) (p : CopyFormula Atom a b)
    (tags : Fin a → Fin (count k*3)) (env : Fin a → Nat)
    (actual : Fin a → Actual (D := D) dec) (X : Fin b → Actual (D := D) dec → Prop)
    (hr : ∀ i, (realization dec names C hc hcap hD).rep (tags i,env i) (actual i)) :
    Eval D (Parametric.pullback (interpretation k) p tags) env
      (Parametric.flattenedSets (params dec names C hcap hD)
        (fun i => (realization dec names C hc hcap hD).liftSet (X i))) ↔
      ActualEval (actualAtom dec names) p actual X :=
  (realization dec names C hc hcap hD).pullback_actual p tags env actual X hr

#print axioms endpoint_chosen
#print axioms encoded_atoms
#print axioms realization
#print axioms compiled_actual
end StackSorting.CapturedLinkExtraction.MultiMargin.CompletionIncidence
