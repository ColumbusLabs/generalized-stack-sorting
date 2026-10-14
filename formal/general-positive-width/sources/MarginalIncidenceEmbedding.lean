import MarginalIncidenceSystem

namespace StackSorting.GraphWidth.MarginalA2.Incidence
open SparseEndpointMSO SparseEndpointMSO.IncidenceOwnership FinitePort Nested
open SparseEndpointMSO.FiniteCopy Actual
variable {A : Model} {n t q : Nat} {G : Graph n} {T : RootedTree t}
variable (D : Decomposition G T) (names : Fin n ≃ Vertex A)

/-- Exact original edge endpoints in original vertex names. -/
theorem original_incidence_named (u : Fin n) (e : IncidenceOwnership.Edge A) :
    OriginalIncidence D names (Actual.vertex (t := t) names u) (.inl (.inr e)) ↔
      u=originalLeft names e ∨ u=originalRight names e := by
  change (True ∧ ((names u).val=e.val.1 ∨ (names u).val=e.val.2)) ↔ _
  rw [true_and]
  constructor
  · rintro (h | h)
    · left; apply names.injective; apply Subtype.ext
      simpa only [named_originalLeft] using h
    · right; apply names.injective; apply Subtype.ext
      simpa only [named_originalRight] using h
  · rintro (rfl | rfl)
    · exact Or.inl (named_originalLeft names e)
    · exact Or.inr (named_originalRight names e)

theorem incidence_vertex {z : Actual.Base (A := A) (t := t)} (e : IncidenceOwnership.Edge A)
    (h : OriginalIncidence D names z (.inl (.inr e))) : ∃ u, z=Actual.vertex names u := by
  cases z with
  | inr z => exact h.elim
  | inl z => cases z with
    | inr z => exact h.2.elim
    | inl z => exact ⟨names.symm z,by simp [Actual.vertex]⟩

theorem original_owner_exact (e : IncidenceOwnership.Edge A) (x : Fin t) :
    OldEdgeOwner D names (.inl (.inr e)) (Actual.node x) ↔
      introductionNode D (originalLeft names e)=x ∧ introductionNode D (originalRight names e)=x := by
  constructor
  · rintro ⟨_,u,v,hne,hu,hv,hxu,hxv⟩
    obtain ⟨u,rfl⟩ := incidence_vertex D names e hu
    obtain ⟨v,rfl⟩ := incidence_vertex D names e hv
    have hx := (Actual.margin_named D names x u).mp hxu
    have hy := (Actual.margin_named D names x v).mp hxv
    rcases (original_incidence_named D names u e).mp hu with hu | hu <;>
      rcases (original_incidence_named D names v e).mp hv with hv | hv
    · exact (hne (congrArg (Actual.vertex names) (hu.trans hv.symm))).elim
    · exact ⟨hu ▸ hx,hv ▸ hy⟩
    · exact ⟨hv ▸ hy,hu ▸ hx⟩
    · exact (hne (congrArg (Actual.vertex names) (hu.trans hv.symm))).elim
  · rintro ⟨hl,hr⟩
    exact ⟨trivial,Actual.vertex names (originalLeft names e),Actual.vertex names (originalRight names e),
      fun h => original_distinct names e ((Actual.vertex_inj names).mp h),
      (original_incidence_named D names _ e).mpr (Or.inl rfl),
      (original_incidence_named D names _ e).mpr (Or.inr rfl),
      (Actual.margin_named D names x _).mpr hl,(Actual.margin_named D names x _).mpr hr⟩

theorem original_actual_owner (e : IncidenceOwnership.Edge A) (x : Fin t) :
    outputAtoms D names .owner (Fin.cases (.inl (.inl (.inr e))) (fun _ => .inl (Actual.node x))) ↔
      introductionNode D (originalLeft names e)=x ∧ introductionNode D (originalRight names e)=x := by
  change (Margin D names (Actual.node x) (.inl (.inr e)) ∨ OldEdgeOwner D names (.inl (.inr e)) (Actual.node x)) ↔ _
  have hn : ¬Margin D names (Actual.node x) (.inl (.inr e)) := by
    intro h
    exact Actual.margin_not_edge D names h trivial
  rw [or_iff_right hn,original_owner_exact]

variable (x : Fin t) (localNames : Fin q ≃ {v : Fin n // introductionNode D v=x})

theorem embed_owned (z : Fin q ⊕ Edge D names x) :
    outputAtoms D names .owner (Fin.cases (embed D names x localNames z) (fun _ => .inl (Actual.node x))) := by
  cases z with
  | inl u => exact Or.inl ((Actual.margin_named D names x _).mpr (localNames u).property)
  | inr e => cases e with
    | inl e => exact (original_actual_owner D names e.val x).mpr e.property
    | inr e => exact congrArg Actual.node e.property.symm

theorem owner_vertex_exact (z : Vertex A) :
    outputAtoms D names .owner (Fin.cases (.inl (.inl (.inl z))) (fun _ => .inl (Actual.node x))) ↔
      introductionNode D (names.symm z)=x := by
  change (Margin D names (Actual.node x) (.inl (.inl z)) ∨ OldEdgeOwner D names (.inl (.inl z)) (Actual.node x)) ↔ _
  have hz : (Actual.vertex (t := t) names (names.symm z))=.inl (.inl z) := by simp [Actual.vertex]
  rw [←hz]
  have hn : ¬OldEdgeOwner D names (Actual.vertex names (names.symm z)) (Actual.node x) := by
    intro h
    exact h.1.elim
  rw [or_iff_left hn,Actual.margin_named]

/-- Coverage of the actual owner fiber. No extraneous original edge, outer
node or synthetic pair is included, even for an empty local vertex domain. -/
theorem owner_covered (z : Carrier.Actual (A := A) D)
    (hz : outputAtoms D names .owner (Fin.cases z (fun _ => .inl (Actual.node x)))) :
    ∃ u : Fin q ⊕ Edge D names x, embed D names x localNames u=z := by
  cases z with
  | inr e =>
    have he : introductionNode D e.val.1=x := (Sum.inr.inj hz).symm
    exact ⟨.inr (.inr ⟨e,he⟩),rfl⟩
  | inl z => cases z with
    | inr y =>
      rcases hz with h | h
      · exact h.elim
      · exact h.1.elim
    | inl z => cases z with
      | inr e => exact ⟨.inr (.inl ⟨e,(original_actual_owner D names e x).mp hz⟩),rfl⟩
      | inl v =>
        have hv := (owner_vertex_exact D names x v).mp hz
        let u := localNames.symm ⟨names.symm v,hv⟩
        refine ⟨.inl u,?_⟩
        simp [embed,u,Actual.vertex]

/-- A literal equivalence onto the disjoint owner fiber, with exact embedding. -/
noncomputable def fiberEquiv : (Fin q ⊕ Edge D names x) ≃ Actual.LocalCarrier D names x :=
  Equiv.ofBijective (fun z => ⟨embed D names x localNames z,embed_owned D names x localNames z⟩) ⟨
    fun u v h => embed_injective D names x localNames (congrArg Subtype.val h),
    by
      rintro ⟨z,hz⟩
      obtain ⟨u,hu⟩ := owner_covered D names x localNames z hz
      exact ⟨u,Subtype.ext hu⟩⟩

#print axioms original_owner_exact
#print axioms embed_owned
#print axioms owner_covered
#print axioms fiberEquiv
end StackSorting.GraphWidth.MarginalA2.Incidence
