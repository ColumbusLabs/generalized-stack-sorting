import CanonicalSparseEndpoint

/-! Reconstruction from genuine sparse structures. No permutation, physical
history, endpoint encoding, or semantic preservation property is a premise.
The first stage uses the insertion vertex itself as a temporary token name.
-/
namespace StackSorting.SparseEndpointMSO
open Generalized IntervalCritical

/-- Remove irrelevant interpretations outside the finite first-order domain. -/
def supported (D : Model) : Model where
  domain := D.domain
  I x := x ∈ D.domain ∧ D.I x
  R x := x ∈ D.domain ∧ D.R x
  S x y := x ∈ D.domain ∧ y ∈ D.domain ∧ D.S x y
  M x y := x ∈ D.domain ∧ y ∈ D.domain ∧ D.M x y

theorem eval_supported (D : Model) (f : Formula a b)
    (env : Fin a → Nat) (sets : Fin b → Nat → Prop)
    (henv : ∀ i, env i ∈ D.domain) :
    Eval (supported D) f env sets ↔ Eval D f env sets := by
  induction f with
  | truth => rfl
  | equal => rfl
  | member => rfl
  | insert i => simp [Eval, supported, henv i]
  | remove i => simp [Eval, supported, henv i]
  | successor i j => simp [Eval, supported, henv i, henv j]
  | matching i j => simp [Eval, supported, henv i, henv j]
  | neg f ih => exact not_congr (ih env sets henv)
  | conj f g ihf ihg => exact and_congr (ihf env sets henv) (ihg env sets henv)
  | implies f g ihf ihg => exact imp_congr (ihf env sets henv) (ihg env sets henv)
  | existsFO k f ih =>
    simp only [Eval, supported]
    constructor <;> rintro ⟨v, hv, hf⟩ <;> refine ⟨v, hv, ?_⟩
    · exact (ih _ sets (fun i => Fin.addCases (fun j => by simpa using hv j)
        (fun j => by simpa using henv j) i)).mp hf
    · exact (ih _ sets (fun i => Fin.addCases (fun j => by simpa using hv j)
        (fun j => by simpa using henv j) i)).mpr hf
  | allFO k f ih =>
    simp only [Eval, supported]
    constructor <;> intro h v hv
    · exact (ih _ sets (fun i => Fin.addCases (fun j => by simpa using hv j)
        (fun j => by simpa using henv j) i)).mp (h v hv)
    · exact (ih _ sets (fun i => Fin.addCases (fun j => by simpa using hv j)
        (fun j => by simpa using henv j) i)).mpr (h v hv)
  | allSet f ih =>
    constructor <;> intro h X hX
    · exact (ih env _ henv).mp (h X hX)
    · exact (ih env _ henv).mpr (h X hX)

theorem satisfies_supported (D : Model) (f : Formula 0 0) :
    Satisfies (supported D) f ↔ Satisfies D f :=
  eval_supported D f Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i)

/-- Structural axioms of a forward perfect two-colored matching. These make
no assumption about a decoded permutation or about stack feasibility. -/
structure MatchingAxioms (D : Model) : Prop where
  partition : ∀ x ∈ D.domain, (D.I x ∨ D.R x) ∧ ¬ (D.I x ∧ D.R x)
  symmetric : ∀ x ∈ D.domain, ∀ y ∈ D.domain, D.M x y → D.M y x
  perfect : ∀ x ∈ D.domain, ∃ y ∈ D.domain, D.M x y ∧
    ∀ z ∈ D.domain, D.M x z → z = y
  opposite : ∀ x ∈ D.domain, ∀ y ∈ D.domain, D.M x y → (D.I x ↔ D.R y)
  forward : ∀ x ∈ D.domain, ∀ y ∈ D.domain, D.I x → D.M x y → x < y

/-- The manuscript's adjacent insertion/removal condition, independently of
the decoding construction. -/
def LazyBoundary (D : Model) : Prop :=
  ∀ x ∈ D.domain, ∀ y ∈ D.domain, D.I x → D.R y → D.S x y → D.M x y

noncomputable def partner (D : Model) (x : Nat) : Nat := by
  classical
  exact if h : ∃ y ∈ D.domain, D.M x y then Classical.choose h else 0

theorem partner_spec {D : Model} (h : MatchingAxioms D) {x : Nat}
    (hx : x ∈ D.domain) :
    partner D x ∈ D.domain ∧ D.M x (partner D x) := by
  classical
  obtain ⟨y, hy, hm, _⟩ := h.perfect x hx
  have he : ∃ y ∈ D.domain, D.M x y := ⟨y, hy, hm⟩
  simp only [partner, dite_eq_left he]
  exact Classical.choose_spec he

theorem partner_unique {D : Model} (h : MatchingAxioms D) {x y : Nat}
    (hx : x ∈ D.domain) (hy : y ∈ D.domain) (hm : D.M x y) :
    y = partner D x := by
  obtain ⟨z, _, _, hz⟩ := h.perfect x hx
  exact (hz y hy hm).trans (hz _ (partner_spec h hx).1 (partner_spec h hx).2).symm

theorem partner_involutive {D : Model} (h : MatchingAxioms D) {x : Nat}
    (hx : x ∈ D.domain) : partner D (partner D x) = x := by
  obtain ⟨hy, hm⟩ := partner_spec h hx
  exact (partner_unique h hy hx (h.symmetric x hx _ hy hm)).symm

noncomputable def insertionTokens (D : Model) : List Nat := by
  classical
  exact D.domain.filter (fun x => decide (D.I x))

@[simp] theorem mem_insertionTokens (D : Model) (x : Nat) :
    x ∈ insertionTokens D ↔ x ∈ D.domain ∧ D.I x := by
  classical
  simp [insertionTokens]

noncomputable def modelEndpoints (D : Model) : Endpoints where
  left := id
  right := partner D

theorem insertionTokens_nodup {D : Model} {length : Nat}
    (hp : TimePath D length) : (insertionTokens D).Nodup := by
  classical
  exact (hp.1 ▸ List.nodup_range).filter _

theorem modelEndpoints_wellFormed {D : Model} {length : Nat}
    (hp : TimePath D length) (h : MatchingAxioms D) :
    WellFormed (modelEndpoints D) (insertionTokens D) := by
  refine ⟨insertionTokens_nodup hp, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨hm, hi⟩ := (mem_insertionTokens D v).mp hv
    exact h.forward v hm _ (partner_spec h hm).1 hi (partner_spec h hm).2
  · intro u _ v _ he; exact he
  · intro u hu v hv he
    have hu' := ((mem_insertionTokens D u).mp hu).1
    have hv' := ((mem_insertionTokens D v).mp hv).1
    change partner D u = partner D v at he
    have hh := congrArg (partner D) he
    simpa [partner_involutive h hu', partner_involutive h hv'] using hh
  · intro u hu v hv he
    obtain ⟨hum, hui⟩ := (mem_insertionTokens D u).mp hu
    obtain ⟨hvm, hvi⟩ := (mem_insertionTokens D v).mp hv
    obtain ⟨hpm, hmatch⟩ := partner_spec h hvm
    have hpr := (h.opposite v hvm _ hpm hmatch).mp hvi
    change u = partner D v at he
    exact (h.partition u hum).2 ⟨hui, he.symm ▸ hpr⟩

/-- A genuine encoding extracted from arbitrary sparse matching axioms. -/
noncomputable def reconstructedEncoding {D : Model} {length : Nat}
    (hp : TimePath D length) (h : MatchingAxioms D) :
    Encoding (supported D) (modelEndpoints D) (insertionTokens D) where
  length := length
  path := ⟨hp.1, by
    intro x hx y hy
    change x ∈ D.domain at hx
    change y ∈ D.domain at hy
    change (x ∈ D.domain ∧ y ∈ D.domain ∧ D.S x y) ↔ x + 1 = y
    simpa only [hx, hy, true_and] using hp.2 x hx y hy⟩
  left_mem v hv := ((mem_insertionTokens D v).mp hv).1
  right_mem v hv := (partner_spec h ((mem_insertionTokens D v).mp hv).1).1
  left_inj _ _ _ _ he := he
  insert_iff x := by
    change (x ∈ D.domain ∧ D.I x) ↔ ∃ v ∈ insertionTokens D, v = x
    simp
  remove_right v hv := by
    obtain ⟨hm, hi⟩ := (mem_insertionTokens D v).mp hv
    obtain ⟨hpm, hmatch⟩ := partner_spec h hm
    exact ⟨hpm, (h.opposite v hm _ hpm hmatch).mp hi⟩
  matching_iff v hv y hy := by
    have hm := ((mem_insertionTokens D v).mp hv).1
    change (v ∈ D.domain ∧ y ∈ D.domain ∧ D.M v y) ↔ y = partner D v
    constructor
    · intro he; exact partner_unique h hm hy he.2.2
    · intro he; subst y
      exact ⟨hm, (partner_spec h hm).1, (partner_spec h hm).2⟩

/-- Every dense endpoint formula is interpreted correctly after reconstruction;
the original sparse model may have arbitrary irrelevant off-domain predicates. -/
theorem reconstructed_truth_preservation {D : Model} {length : Nat}
    (hp : TimePath D length) (h : MatchingAxioms D) (f : EndpointMSO.Formula 0 0) :
    Satisfies D (translate f) ↔ EndpointMSO.Satisfies
      (EndpointMSO.endpointModel (modelEndpoints D) (insertionTokens D)) f :=
  (satisfies_supported D (translate f)).symm.trans
    (satisfies_translate (reconstructedEncoding hp h) f)

/-- Width feasibility for arbitrary time-indexed sparse models, before any
permutation or lazy-normalization premise. Width zero and the empty domain are
included. This closes the arbitrary-model endpoint reconstruction layer only. -/
theorem sparseModel_eligibility_iff_peelable {D : Model} {length r s : Nat}
    (hp : TimePath D length) (h : MatchingAxioms D) :
    Satisfies D (eligibilitySentence r s) ↔
      Peelable (modelEndpoints D) r s (insertionTokens D) := by
  rw [eligibilitySentence, reconstructed_truth_preservation hp h]
  exact (EndpointMSO.satisfies_iff_everySubsetEligible _ _
    (insertionTokens_nodup hp) _ _).trans
      (peelable_iff_everySubsetEligible (insertionTokens_nodup hp)).symm

#print axioms eval_supported
#print axioms partner_involutive
#print axioms modelEndpoints_wellFormed
#print axioms reconstructedEncoding
#print axioms reconstructed_truth_preservation
#print axioms sparseModel_eligibility_iff_peelable
end StackSorting.SparseEndpointMSO
