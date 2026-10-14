import MultiMarginOuterRealization
import CompletionIncidenceGraph

namespace StackSorting.GraphWidth.MultiMargin
open FinitePort Nested
open SparseEndpointMSO SparseEndpointMSO.Guidance SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.IncidenceOwnership
namespace ActualC2
open CapturedLinkExtraction
open CapturedLinkExtraction.MultiMargin

variable {A : Model} {n t k : Nat} {G : Graph n} {T : RootedTree t}
variable (D : Decomposition G T) (names : Fin n ≃ Vertex A)

def relations : Syntax.Relations (CapturedLinkExtraction.MultiMargin.CompletionIncidence.Actual (D := A) D) where
  vertex := CapturedLinkExtraction.MultiMargin.CompletionIncidence.vertex D
  originalEdge := CapturedLinkExtraction.MultiMargin.CompletionIncidence.originalEdge D
  edge := CapturedLinkExtraction.MultiMargin.CompletionIncidence.edge D
  incidence := CapturedLinkExtraction.MultiMargin.CompletionIncidence.incident D names

/-- All local incidence obligations are discharged on the actual completed
carrier; original graph adjacency is related by the explicit names equivalence. -/
def completed (hA : Laws A)
    (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val) :
    CompletedIncidence D (CapturedLinkExtraction.MultiMargin.CompletionIncidence.Actual (D := A) D) where
  rel := relations D names
  vertex := CapturedLinkExtraction.MultiMargin.CompletionIncidence.named D names
  injective := CapturedLinkExtraction.MultiMargin.CompletionIncidence.named_injective D names
  vertex_exact := CapturedLinkExtraction.MultiMargin.CompletionIncidence.vertex_exact D names
  incidence_vertex := CapturedLinkExtraction.MultiMargin.CompletionIncidence.incidence_vertex D names
  completed_pair u v hn := (CapturedLinkExtraction.MultiMargin.CompletionIncidence.pair_coverage D names hA hG u v hn).symm
  original_pair u v := by
    constructor
    · rintro ⟨hne,e,he,hu,hv⟩
      have hn : u≠v := fun h => hne (congrArg (CapturedLinkExtraction.MultiMargin.CompletionIncidence.named D names) h)
      cases e with
      | inr e => exact he.elim
      | inl e => exact (CapturedLinkExtraction.MultiMargin.CompletionIncidence.original_pair names hA hG u v hn).mp ⟨e,he,hu,hv⟩
    · intro he
      have hn : u≠v := by intro h; subst v; exact G.loopless u he
      obtain ⟨e,hE,hu,hv⟩ := (CapturedLinkExtraction.MultiMargin.CompletionIncidence.original_pair names hA hG u v hn).mpr he
      exact ⟨fun h => hn (CapturedLinkExtraction.MultiMargin.CompletionIncidence.named_injective D names h),.inl e,hE,hu,hv⟩
  rigid e u v a b he hn hab hu hv ha hb := CapturedLinkExtraction.MultiMargin.CompletionIncidence.pair_rigid D names e he hn hab hu hv ha hb

def retained (hA : Laws A)
    (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val) :
    Retained (completed D names hA hG) (IncidenceOwnership.Element A) where
  embed := Sum.inl
  injective := Sum.inl_injective
  retained_exact z := by
    cases z with
    | inr e => simp [completed,relations,CapturedLinkExtraction.MultiMargin.CompletionIncidence.vertex,CapturedLinkExtraction.MultiMargin.CompletionIncidence.originalEdge]
    | inl a => cases a <;> simp [completed,relations,CapturedLinkExtraction.MultiMargin.CompletionIncidence.vertex,CapturedLinkExtraction.MultiMargin.CompletionIncidence.originalEdge,IsVertex,IsEdge] <;> exact ⟨_,rfl⟩

def atomMap : {r : Nat} → Syntax.InputAtom r → CapturedLinkExtraction.MultiMargin.CompletionIncidence.Atom r
  | _, .vertex => .vertex
  | _, .originalEdge => .originalEdge
  | _, .edge => .edge
  | _, .incidence => .incidence

/-- Signature projection changes neither domain, copies, nor fixed parameters. -/
noncomputable def projected (k : Nat) :
    Parametric.Interpretation Syntax.InputAtom (CapturedLinkExtraction.MultiMargin.CompletionIncidence.count k*3) (0+parameterCount k*3) where
  domain := (CapturedLinkExtraction.MultiMargin.CompletionIncidence.interpretation k).domain
  atom a := (CapturedLinkExtraction.MultiMargin.CompletionIncidence.interpretation k).atom (atomMap a)

variable (C : Colors A k) (hc : C.Valid) (hcap : Captured D names C)

noncomputable def projectedRealization (hA : Laws A) :
    Parametric.Realization (projected k) A (CapturedLinkExtraction.MultiMargin.CompletionIncidence.params D names C hcap hA)
      (CapturedLinkExtraction.MultiMargin.CompletionIncidence.Actual (D := A) D) (Syntax.atoms (relations D names)) where
  rep := (CapturedLinkExtraction.MultiMargin.CompletionIncidence.realization D names C hc hcap hA).rep
  valid := (CapturedLinkExtraction.MultiMargin.CompletionIncidence.realization D names C hc hcap hA).valid
  cover := (CapturedLinkExtraction.MultiMargin.CompletionIncidence.realization D names C hc hcap hA).cover
  complete := (CapturedLinkExtraction.MultiMargin.CompletionIncidence.realization D names C hc hcap hA).complete
  equal := (CapturedLinkExtraction.MultiMargin.CompletionIncidence.realization D names C hc hcap hA).equal
  atom a env actual hr := by
    have h := (CapturedLinkExtraction.MultiMargin.CompletionIncidence.realization D names C hc hcap hA).atom (atomMap a) env actual hr
    cases a <;> exact h

/-- Fixed literal extraction syntax, depending only on the guidance-color
count. Actual decomposition size occurs only in its proved realization. -/
noncomputable def interpretation (k : Nat) := Parametric.compose (projected k) Syntax.interpretation

noncomputable def realization (hA : Laws A)
    (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
    (s : Sane D) (ht : 0<t) :=
  (retained D names hA hG).realization s ht (projectedRealization D names C hc hcap hA)

/-- Uniform copy count for the final original-graph-plus-outer-nodes structure. -/
theorem copy_count (k : Nat) : 2*(CapturedLinkExtraction.MultiMargin.CompletionIncidence.count k*3)=6+6*k*k := by
  rw [CapturedLinkExtraction.MultiMargin.CompletionIncidence.count_eq]
  simp only [Nat.mul_assoc]
  omega

/-- Uniform fixed-set arity before any free output sets are supplied. -/
theorem parameter_count (k : Nat) :
    (0+parameterCount k*3)+4*(CapturedLinkExtraction.MultiMargin.CompletionIncidence.count k*3)=(k*3+k*k+2)*3+12+12*k*k := by
  rw [parameterCount_eq,CapturedLinkExtraction.MultiMargin.CompletionIncidence.count_eq]
  simp only [Nat.mul_assoc]
  omega

#print axioms completed
#print axioms projectedRealization
#print axioms realization
#print axioms copy_count
#print axioms parameter_count
end ActualC2
end StackSorting.GraphWidth.MultiMargin
