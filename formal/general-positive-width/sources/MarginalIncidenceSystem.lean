import MarginalOwnerFibers
import MarginalSelectionValidity
import MarginalLocalGuidance
import GenericGuidanceIncidence

namespace StackSorting.GraphWidth.MarginalA2.Incidence
open SparseEndpointMSO SparseEndpointMSO.IncidenceOwnership FinitePort Nested
open GuidedPathwidth
variable {A : Model} {n t q W : Nat} {G : Graph n} {T : RootedTree t}
variable (D : Decomposition G T) (names : Fin n ≃ Vertex A)
variable (x : Fin t) (localNames : Fin q ≃ {v : Fin n // introductionNode D v=x})

def originalLeft (e : IncidenceOwnership.Edge A) : Fin n := names.symm ⟨e.val.1,e.property.2.1⟩
def originalRight (e : IncidenceOwnership.Edge A) : Fin n := names.symm ⟨e.val.2,e.property.2.2.1⟩

@[simp] theorem named_originalLeft (e : IncidenceOwnership.Edge A) :
    (names (originalLeft names e)).val=e.val.1 := by
  exact congrArg Subtype.val (names.apply_symm_apply _)
@[simp] theorem named_originalRight (e : IncidenceOwnership.Edge A) :
    (names (originalRight names e)).val=e.val.2 := by
  exact congrArg Subtype.val (names.apply_symm_apply _)

theorem original_distinct (e : IncidenceOwnership.Edge A) : originalLeft names e≠originalRight names e := by
  intro h
  have he := congrArg (fun u => (names u).val) h
  exact e.property.1.1 (by simpa only [named_originalLeft,named_originalRight] using he)

abbrev OriginalLocalEdge := {e : IncidenceOwnership.Edge A //
  introductionNode D (originalLeft names e)=x ∧ introductionNode D (originalRight names e)=x}
abbrev SyntheticLocalEdge := {e : ExtraEdge D // introductionNode D e.val.1=x}
abbrev Edge := OriginalLocalEdge D names x ⊕ SyntheticLocalEdge D x

noncomputable def left : Edge D names x → Fin q
  | .inl e => localNames.symm ⟨originalLeft names e.val,e.property.1⟩
  | .inr e => localNames.symm ⟨e.val.val.1,e.property⟩
noncomputable def right : Edge D names x → Fin q
  | .inl e => localNames.symm ⟨originalRight names e.val,e.property.2⟩
  | .inr e => localNames.symm ⟨e.val.val.2,(extra_same_owner D e.val).trans e.property⟩

variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)

include hG in
theorem edge_sound (e : Edge D names x) :
    (marginalGraph D x localNames).Adj (left D names x localNames e) (right D names x localNames e) := by
  rw [marginalGraph_exact]
  cases e with
  | inl e =>
    simp only [left,right,Equiv.apply_symm_apply]
    refine ⟨e.property.1,e.property.2,original_distinct names e.val,Or.inl ?_⟩
    apply (hG _ _).mpr
    simpa only [named_originalLeft,named_originalRight] using e.val.property.2
  | inr e =>
    simp only [left,right,Equiv.apply_symm_apply]
    simpa only [e.property] using e.val.property.2.2

include hA hG in
/-- Original edge coverage uses the actual C.2 incidence edge IDs. -/
theorem original_complete {u v : Fin q}
    (h : G.Adj (localNames u).val (localNames v).val) :
    ∃ e : Edge D names x,
      (left D names x localNames e=u ∧ right D names x localNames e=v) ∨
      (left D names x localNames e=v ∧ right D names x localNames e=u) := by
  obtain ⟨e,he | he⟩ := (edge_coverage hA _ _).mp ((hG _ _).mp h)
  · have hl : originalLeft names e=(localNames u).val := by
      apply names.injective
      apply Subtype.ext
      simpa only [named_originalLeft] using he.1
    have hr : originalRight names e=(localNames v).val := by
      apply names.injective
      apply Subtype.ext
      simpa only [named_originalRight] using he.2
    let E : OriginalLocalEdge D names x := ⟨e,by simpa only [hl] using (localNames u).property,by simpa only [hr] using (localNames v).property⟩
    refine ⟨.inl E,Or.inl ⟨?_,?_⟩⟩
    · apply localNames.injective; apply Subtype.ext
      simpa only [left,Equiv.apply_symm_apply] using hl
    · apply localNames.injective; apply Subtype.ext
      simpa only [right,Equiv.apply_symm_apply] using hr
  · have hl : originalLeft names e=(localNames v).val := by
      apply names.injective
      apply Subtype.ext
      simpa only [named_originalLeft] using he.1
    have hr : originalRight names e=(localNames u).val := by
      apply names.injective
      apply Subtype.ext
      simpa only [named_originalRight] using he.2
    let E : OriginalLocalEdge D names x := ⟨e,by simpa only [hl] using (localNames v).property,by simpa only [hr] using (localNames u).property⟩
    refine ⟨.inl E,Or.inr ⟨?_,?_⟩⟩
    · apply localNames.injective; apply Subtype.ext
      simpa only [left,Equiv.apply_symm_apply] using hl
    · apply localNames.injective; apply Subtype.ext
      simpa only [right,Equiv.apply_symm_apply] using hr

/-- Every synthetic missing marginal pair uses the already constructed actual
unordered pair carrier. Color codes select representatives only later. -/
theorem synthetic_complete (C : AdhesionColoring D W) {u v : Fin q}
    (h : (marginalGraph D x localNames).Adj u v)
    (hn : ¬G.Adj (localNames u).val (localNames v).val) :
    ∃ e : Edge D names x,
      (left D names x localNames e=u ∧ right D names x localNames e=v) ∨
      (left D names x localNames e=v ∧ right D names x localNames e=u) := by
  have hm := (marginalGraph_exact D x localNames u v).mp h
  rcases hm.2.2.2 with ho | ⟨y,hy,hp,hu,hv⟩
  · exact (hn ho).elim
  have hp' : PairAt D C (C.color (localNames u).val,C.color (localNames v).val,y)
      (localNames u).val (localNames v).val :=
    ⟨hm.2.2.1,hn,hy,hm.1.trans hp.symm,hm.2.1.trans hp.symm,hu,hv,rfl,rfl⟩
  obtain ⟨e,he | he⟩ := pair_has_edge D C hp'
  · have ho : introductionNode D e.val.1=x := by simpa only [he] using hm.1
    refine ⟨.inr ⟨e,ho⟩,Or.inl ⟨?_,?_⟩⟩
    · apply localNames.injective; apply Subtype.ext
      simp only [left,Equiv.apply_symm_apply,he]
    · apply localNames.injective; apply Subtype.ext
      simp only [right,Equiv.apply_symm_apply,he]
  · have ho : introductionNode D e.val.1=x := by simpa only [he] using hm.2.1
    refine ⟨.inr ⟨e,ho⟩,Or.inr ⟨?_,?_⟩⟩
    · apply localNames.injective; apply Subtype.ext
      simp only [left,Equiv.apply_symm_apply,he]
    · apply localNames.injective; apply Subtype.ext
      simp only [right,Equiv.apply_symm_apply,he]

/-- Concrete generic-incidence graph for one actual marginal. There is no
sparse-model, guidance, extraction, or simple-edge-quotient premise. -/
noncomputable def system (C : AdhesionColoring D W) :
    GenericIncidence.System (Local.graphOriginal (marginalGraph D x localNames)).simple where
  Edge := Edge D names x
  left := left D names x localNames
  right := right D names x localNames
  sound := edge_sound D names x localNames hG
  complete := by
    intro u v h
    by_cases ho : G.Adj (localNames u).val (localNames v).val
    · exact original_complete D names x localNames hA hG ho
    · exact synthetic_complete D names x localNames C h ho

/-- Retain actual original edge IDs, actual selected missing-edge pairs, and
exact original vertices. Owner fibers use this map to merge local sets. -/
def embed (z : Fin q ⊕ Edge D names x) : Carrier.Actual (A := A) D :=
  match z with
  | .inl u => .inl (Actual.vertex names (localNames u).val)
  | .inr (.inl e) => .inl (.inl (.inr e.val))
  | .inr (.inr e) => .inr e.val

theorem embed_injective : Function.Injective (embed D names x localNames) := by
  intro u v h
  cases u with
  | inl u => cases v with
    | inl v =>
      have he := (Actual.vertex_inj names).mp (Sum.inl.inj h)
      exact congrArg Sum.inl (localNames.injective (Subtype.ext he))
    | inr v => cases v <;> cases h
  | inr u => cases u with
    | inl u => cases v with
      | inl v => cases h
      | inr v => cases v with
        | inl v => exact congrArg (fun e => Sum.inr (Sum.inl e)) (Subtype.ext (Sum.inr.inj (Sum.inl.inj (Sum.inl.inj h))))
        | inr v => cases h
    | inr u => cases v with
      | inl v => cases h
      | inr v => cases v with
        | inl v => cases h
        | inr v => exact congrArg (fun e => Sum.inr (Sum.inr e)) (Subtype.ext (Sum.inr.inj h))

#print axioms edge_sound
#print axioms system
#print axioms embed_injective
end StackSorting.GraphWidth.MarginalA2.Incidence
