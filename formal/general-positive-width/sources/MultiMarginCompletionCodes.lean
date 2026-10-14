import MultiMarginGeometry
import CapturedAdhesionWitness

namespace StackSorting.CapturedLinkExtraction.MultiMargin
open SparseEndpointMSO SparseEndpointMSO.Guidance SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.IncidenceOwnership GraphWidth GraphWidth.Nested
variable {A : Model} {n t k : Nat} {G : Graph n} {T : FinitePort.RootedTree t}
variable {dec : Decomposition G T}

/-- Capture of the actual original adhesions, with no condition on outer bags. -/
def Captured (dec : Decomposition G T) (names : Fin n ≃ Vertex A) (C : Colors A k) : Prop :=
  ∀ x, (∃ u, outerAdhesion dec x u) → ∃ z,
    ∀ u, outerAdhesion dec x u → ∃ i, ColorRoot C i z (namedVertex names u)

theorem completion_available (hA : Laws A) (dec : Decomposition G T)
    (names : Fin n ≃ Vertex A) (C : Colors A k)
    (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
    (hc : Captured dec names C) {u v} (he : (GraphWidth.MultiMargin.Completion dec).Adj u v) :
    Available names C u v := by
  rcases he.2 with h | ⟨x,hu,hv⟩
  · exact Or.inl (incidence_edge_of_named_graph hA names G hG u v h)
  · obtain ⟨z,hz⟩ := hc x ⟨u,hu⟩
    obtain ⟨i,hi⟩ := hz u hu
    obtain ⟨j,hj⟩ := hz v hv
    exact Or.inr ⟨i,j,z,hi,hj⟩

/-- One actual extra edge per unordered nonoriginal completed pair. The
strict original vertex numbering is used only for this carrier, not in syntax. -/
abbrev ExtraEdge (dec : Decomposition G T) :=
  {p : Fin n × Fin n // p.1.val<p.2.val ∧
    (GraphWidth.MultiMargin.Completion dec).Adj p.1 p.2 ∧ ¬ G.Adj p.1 p.2}

/-- Fixed color-pair copies of actual incidence elements. The later sparse
presentation uses three original copies for each such incidence base. -/
abbrev Candidate (A : Model) (k : Nat) := Fin k × Fin k × IncidenceOwnership.Element A

def CandidateRep (names : Fin n ≃ Vertex A) (C : Colors A k)
    (q : Candidate A k) (e : ExtraEdge dec) : Prop :=
  ColorRoot C q.1 q.2.2 (namedVertex names e.val.1) ∧
    ColorRoot C q.2.1 q.2.2 (namedVertex names e.val.2)

/-- Root uniqueness makes each candidate code denote at most one actual edge. -/
theorem candidate_functional (names : Fin n ≃ Vertex A) (C : Colors A k) (hc : C.Valid)
    {q : Candidate A k} {e f : ExtraEdge dec}
    (he : CandidateRep names C q e) (hf : CandidateRep names C q f) : e=f := by
  apply Subtype.ext
  apply Prod.ext
  · exact namedVertex_injective names (colors_root_unique hc q.1 he.1 hf.1)
  · exact namedVertex_injective names (colors_root_unique hc q.2.1 he.2 hf.2)

/-- Every actual extra edge has at least one real captured-color code. -/
theorem extra_has_candidate (names : Fin n ≃ Vertex A) (C : Colors A k)
    (hcap : Captured dec names C) (e : ExtraEdge dec) :
    ∃ q : Candidate A k, CandidateRep names C q e := by
  rcases e.property.2.1.2 with h | ⟨x,hu,hv⟩
  · exact (e.property.2.2 h).elim
  · obtain ⟨z,hz⟩ := hcap x ⟨e.val.1,hu⟩
    obtain ⟨i,hi⟩ := hz e.val.1 hu
    obtain ⟨j,hj⟩ := hz e.val.2 hv
    exact ⟨(i,j,z),hi,hj⟩

noncomputable def chosenCandidate (names : Fin n ≃ Vertex A) (C : Colors A k)
    (hcap : Captured dec names C) (e : ExtraEdge dec) : Candidate A k :=
  Classical.choose (extra_has_candidate names C hcap e)

theorem chosenCandidate_spec (names : Fin n ≃ Vertex A) (C : Colors A k)
    (hcap : Captured dec names C) (e : ExtraEdge dec) :
    CandidateRep names C (chosenCandidate names C hcap e) e :=
  Classical.choose_spec (extra_has_candidate names C hcap e)

theorem chosenCandidate_injective (names : Fin n ≃ Vertex A) (C : Colors A k)
    (hc : C.Valid) (hcap : Captured dec names C) :
    Function.Injective (chosenCandidate names C hcap) := by
  intro e f he
  have hf := chosenCandidate_spec names C hcap f
  rw [← he] at hf
  exact candidate_functional names C hc (chosenCandidate_spec names C hcap e) hf

/-- Exactly one unary selected-base predicate for every fixed color pair. -/
def chosenCandidateSets (names : Fin n ≃ Vertex A) (C : Colors A k)
    (hcap : Captured dec names C) (i j : Fin k) : IncSet A :=
  fun z => ∃ e, chosenCandidate names C hcap e=(i,j,z)

/-- Duplicate elimination is an explicit selection, never an implicit quotient
inside the finite-copy compiler. Both completeness and uniqueness are proved. -/
theorem selected_candidate_exact (names : Fin n ≃ Vertex A) (C : Colors A k)
    (hc : C.Valid) (hcap : Captured dec names C) (q : Candidate A k) (e : ExtraEdge dec) :
    chosenCandidate names C hcap e=q ↔
      chosenCandidateSets names C hcap q.1 q.2.1 q.2.2 ∧ CandidateRep names C q e := by
  constructor
  · intro he
    refine ⟨⟨e,he⟩,?_⟩
    exact he ▸ chosenCandidate_spec names C hcap e
  · rintro ⟨⟨f,hf⟩,he⟩
    have hr := chosenCandidate_spec names C hcap f
    rw [hf] at hr
    have ef := candidate_functional names C hc he hr
    exact ef ▸ hf

/-- Actual selected codes and actual extra edges are bijective. -/
noncomputable def selectedCandidateEquiv (names : Fin n ≃ Vertex A) (C : Colors A k)
    (hc : C.Valid) (hcap : Captured dec names C) :
    ExtraEdge dec ≃ {q : Candidate A k // chosenCandidateSets names C hcap q.1 q.2.1 q.2.2} :=
  Equiv.ofBijective (fun e => ⟨chosenCandidate names C hcap e,⟨e,rfl⟩⟩) ⟨
    fun e f he => chosenCandidate_injective names C hc hcap (congrArg Subtype.val he),
    by rintro ⟨q,e,he⟩; exact ⟨e,Subtype.ext he⟩⟩

/-- No original vertex or edge count occurs in the copying bound. -/
def completionCopyCount (k : Nat) : Nat := 3+3*k*k

#print axioms completion_available
#print axioms candidate_functional
#print axioms selected_candidate_exact
#print axioms selectedCandidateEquiv
end StackSorting.CapturedLinkExtraction.MultiMargin
