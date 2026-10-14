import MarginalIncidenceEmbedding
import MarginalNestedProjection
import ActualFormulaEquiv

namespace StackSorting.GraphWidth.MarginalA2.Incidence
open SparseEndpointMSO SparseEndpointMSO.IncidenceOwnership SparseEndpointMSO.FiniteCopy
open FinitePort Nested Actual GuidedPathwidth
variable {A : Model} {n t q W : Nat} {G : Graph n} {T : RootedTree t}
variable (D : Decomposition G T) (names : Fin n ≃ Vertex A)
variable (x : Fin t) (localNames : Fin q ≃ {v : Fin n // introductionNode D v=x})

 theorem original_localEdge (e : OriginalLocalEdge D names x) :
    OldLocalEdge D names (.inl (.inr e.val)) :=
  ⟨Actual.node x,(original_owner_exact D names e.val x).mpr e.property⟩

 theorem no_vertex_localEdge (u : Fin n) : ¬OldLocalEdge D names (Actual.vertex names u) := by
  rintro ⟨_,h,_⟩
  exact h.elim

 theorem embed_vertex (z : Fin q ⊕ Edge D names x) :
    outputAtoms D names .vertex (fun _ => embed D names x localNames z) ↔
      ∃ u, z=Sum.inl u := by
  cases z with
  | inl u => exact ⟨fun _ => ⟨u,rfl⟩,fun _ => trivial⟩
  | inr e => cases e <;> simp [embed,outputAtoms,outerAtoms,IsVertex]

 theorem embed_edge (z : Fin q ⊕ Edge D names x) :
    outputAtoms D names .localEdge (fun _ => embed D names x localNames z) ↔
      ∃ e, z=Sum.inr e := by
  cases z with
  | inl u =>
    change OldLocalEdge D names (Actual.vertex names (localNames u).val) ↔ _
    simp only [reduceCtorEq,exists_false]
    exact iff_false_intro (no_vertex_localEdge D names (localNames u).val)
  | inr e => cases e with
    | inl e => exact ⟨fun _ => ⟨.inl e,rfl⟩,fun _ => original_localEdge D names x e⟩
    | inr e => exact ⟨fun _ => ⟨.inr e,rfl⟩,fun _ => trivial⟩

 theorem local_endpoint {u : Fin q} {v : Fin n} {hv : introductionNode D v=x} :
    (localNames u).val=v ↔ u=localNames.symm ⟨v,hv⟩ := by
  constructor
  · intro h
    apply localNames.injective
    simpa only [Equiv.apply_symm_apply] using (Subtype.ext h : localNames u=⟨v,hv⟩)
  · intro h
    subst u
    simp only [Equiv.apply_symm_apply]

 theorem embed_incident (u v : Fin q ⊕ Edge D names x) :
    outputAtoms D names .incidence
      (Fin.cases (embed D names x localNames u) (fun _ => embed D names x localNames v)) ↔
      (match u,v with
      | .inl a,.inr e => a=left D names x localNames e ∨ a=right D names x localNames e
      | _,_ => False) := by
  cases u with
  | inr e => cases e <;> cases v with
    | inl v => simp [embed,outputAtoms,OriginalIncidence,outerAtoms,ElementIncident,Actual.vertex]
    | inr v => cases v <;> simp [embed,outputAtoms,OriginalIncidence,outerAtoms,ElementIncident,Actual.vertex]
        <;> try { constructor <;> intro h <;> cases h }
  | inl u => cases v with
    | inl v =>
      change (OldLocalEdge D names (Actual.vertex names (localNames v).val) ∧ _) ↔ False
      exact iff_false_intro (fun h => no_vertex_localEdge D names _ h.1)
    | inr e => cases e with
      | inl e =>
        change (OldLocalEdge D names (.inl (.inr e.val)) ∧
          OriginalIncidence D names (Actual.vertex names (localNames u).val) (.inl (.inr e.val))) ↔ _
        rw [and_iff_right (original_localEdge D names x e),original_incidence_named]
        exact or_congr (local_endpoint D x localNames) (local_endpoint D x localNames)
      | inr e =>
        change (Actual.vertex names (localNames u).val=Actual.vertex names e.val.val.1 ∨
          Actual.vertex names (localNames u).val=Actual.vertex names e.val.val.2) ↔ _
        rw [Actual.vertex_inj,Actual.vertex_inj]
        exact or_congr (local_endpoint D x localNames) (local_endpoint D x localNames)

variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

/-- All projected local atoms agree pointwise on the literal incidence carrier. -/
theorem embedded_atoms {r : Nat} (a : IncidenceAtom r)
    (env : Fin r → Fin q ⊕ Edge D names x) :
    NestedSyntax.incidenceAtoms (outputAtoms D names) a
      (fun i => embed D names x localNames (env i)) ↔
      (system D names x localNames hA hG C).atoms a env := by
  cases a with
  | vertex =>
    change outputAtoms D names .vertex (fun i => embed D names x localNames (env i)) ↔ _
    have he : (fun i : Fin 1 => embed D names x localNames (env i))=(fun _ => embed D names x localNames (env 0)) := by
      funext i; fin_cases i; rfl
    rw [he,embed_vertex]
    cases hz : env 0 <;> simp [GenericIncidence.System.atoms,GenericIncidence.System.isVertex,hz]
  | edge =>
    change outputAtoms D names .localEdge (fun i => embed D names x localNames (env i)) ↔ _
    have he : (fun i : Fin 1 => embed D names x localNames (env i))=(fun _ => embed D names x localNames (env 0)) := by
      funext i; fin_cases i; rfl
    rw [he,embed_edge]
    cases hz : env 0 <;> simp [GenericIncidence.System.atoms,GenericIncidence.System.isEdge,hz]
  | incidence =>
    have he : (fun i : Fin 2 => embed D names x localNames (env i))=
        Fin.cases (embed D names x localNames (env 0)) (fun _ => embed D names x localNames (env 1)) := by
      funext i; fin_cases i <;> rfl
    simp only [NestedSyntax.incidenceAtoms]
    rw [he,embed_incident]
    cases h0 : env 0 <;> cases h1 : env 1 <;>
      simp [GenericIncidence.System.atoms,GenericIncidence.System.incident,system,h0,h1]
  | insert => rfl
  | remove => rfl

#print axioms embedded_atoms
end StackSorting.GraphWidth.MarginalA2.Incidence
