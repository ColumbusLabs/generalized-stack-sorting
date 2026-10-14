import CapturedLinkParameters
import EmbeddedRootSeparator
import CapturedAdhesionConnectors

namespace StackSorting.CapturedLinkExtraction
open SparseEndpointMSO SparseEndpointMSO.Guidance SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.IncidenceOwnership GraphWidth SameVertexForest
open ConnectedConeNormalization
variable {D : Model} {n k : Nat}

/-- An actual edge has only its two endpoints, including when several
candidate representations eventually denote the same undirected pair. -/
theorem incident_pair_rigid {e x y u v : IncidenceOwnership.Element D}
    (he : IsEdge e) (hxy : x ≠ y) (huv : u ≠ v)
    (hx : ElementIncident x e) (hy : ElementIncident y e)
    (hu : ElementIncident u e) (hv : ElementIncident v e) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  cases e with
  | inl e => exact he.elim
  | inr e =>
    let a : IncidenceOwnership.Element D := .inl ⟨e.val.1,e.property.2.1⟩
    let b : IncidenceOwnership.Element D := .inl ⟨e.val.2,e.property.2.2.1⟩
    have classify : ∀ z, ElementIncident z (.inr e) → z = a ∨ z = b := by
      intro z hz
      cases z with
      | inr z => exact hz.elim
      | inl z =>
        rcases hz with hz | hz
        · exact Or.inl (congrArg Sum.inl (Subtype.ext hz))
        · exact Or.inr (congrArg Sum.inl (Subtype.ext hz))
    rcases classify x hx with hx | hx <;> rcases classify y hy with hy | hy <;>
      rcases classify u hu with hu | hu <;> rcases classify v hv with hv | hv <;> simp_all

def namedVertex (names : Fin n ≃ Vertex D) (u : Fin n) : IncidenceOwnership.Element D :=
  .inl (names u)

theorem namedVertex_injective (names : Fin n ≃ Vertex D) : Function.Injective (namedVertex names) :=
  fun _ _ h => names.injective (Sum.inl.inj h)

def ColorRoot (C : Colors D k) (i : Fin k) : IncidenceOwnership.Element D → IncidenceOwnership.Element D → Prop :=
  RootRelation (C i).vertices (C i).edges (C i).roots

def Available (names : Fin n ≃ Vertex D) (C : Colors D k) (u v : Fin n) : Prop :=
  (∃ e, IsEdge e ∧ ElementIncident (namedVertex names u) e ∧ ElementIncident (namedVertex names v) e) ∨
    ∃ i j x, ColorRoot C i x (namedVertex names u) ∧ ColorRoot C j x (namedVertex names v)

def forestSelection (names : Fin n ≃ Vertex D) (C : Colors D k) (O : RankedOrder n) : Selection D k where
  original e := ∃ u v, ParentAdj O u v ∧
    ElementIncident (namedVertex names u) e ∧ ElementIncident (namedVertex names v) e
  candidate i j x := ∃ u v, ParentAdj O u v ∧
    ColorRoot C i x (namedVertex names u) ∧ ColorRoot C j x (namedVertex names v)
  roots := LiftRoot O (namedVertex names)

theorem parentAdj_ne (O : RankedOrder n) {u v} (h : ParentAdj O u v) : u ≠ v := by
  intro he
  subst v
  rcases h with ⟨hn,hp⟩ | ⟨hn,hp⟩ <;> exact hn hp

/-- Both selected-link directions are proved. Selection is only unary on
original edges and candidate bases, never a binary parent parameter. -/
theorem forestSelection_link_exact (names : Fin n ≃ Vertex D) (C : Colors D k)
    (hc : C.Valid) (O : RankedOrder n)
    (ha : ∀ u v, ParentAdj O u v → Available names C u v)
    (x y : IncidenceOwnership.Element D) :
    RawLink (fixedIndices k) (chosenSets C (forestSelection names C O)) x y ↔
      LiftLink O (namedVertex names) x y := by
  simp only [RawLink,chosenSets_color,chosenSets_candidate,chosenSets_original]
  change (x ≠ y ∧ ((∃ e, IsEdge e ∧ (forestSelection names C O).original e ∧
      ElementIncident x e ∧ ElementIncident y e) ∨
    ∃ i j z, (forestSelection names C O).candidate i j z ∧ ColorRoot C i z x ∧ ColorRoot C j z y)) ↔ _
  constructor
  · rintro ⟨hxy,⟨e,he,⟨u,v,huv,hu,hv⟩,hx,hy⟩ | ⟨i,j,z,⟨u,v,huv,hu,hv⟩,hx,hy⟩⟩
    · have huv' : namedVertex names u ≠ namedVertex names v :=
        fun h => parentAdj_ne O huv (namedVertex_injective names h)
      rcases incident_pair_rigid he hxy huv' hx hy hu hv with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · exact ⟨u,v,hx,hy,huv⟩
      · exact ⟨v,u,hx,hy,parentAdj_symm O huv⟩
    · exact ⟨u,v,colors_root_unique hc i hx hu,colors_root_unique hc j hy hv,huv⟩
  · rintro ⟨u,v,rfl,rfl,huv⟩
    refine ⟨fun h => parentAdj_ne O huv (namedVertex_injective names h),?_⟩
    rcases ha u v huv with ⟨e,he,hu,hv⟩ | ⟨i,j,z,hu,hv⟩
    · exact Or.inl ⟨e,he,⟨u,v,huv,hu,hv⟩,hu,hv⟩
    · exact Or.inr ⟨i,j,z,⟨u,v,huv,hu,hv⟩,hu,hv⟩

/-- Original-vocabulary earlier formula for an available actual forest. The
availability premise is subsequently supplied by sane captured adhesions. -/
theorem sparseEarlier_forest_exact (hD : Laws D) (names : Fin n ≃ Vertex D)
    (C : Colors D k) (hc : C.Valid) (O : RankedOrder n)
    (ha : ∀ u v, ParentAdj O u v → Available names C u v) (u v : Fin n) :
    Eval D (sparseEarlier k) (Fin.cases (names u).val (fun _ => (names v).val))
      (originalSets hD (chosenSets C (forestSelection names C O))) ↔ O.rel u v := by
  rw [eval_sparseEarlier]
  have hl : RawLink (fixedIndices k) (chosenSets C (forestSelection names C O)) =
      LiftLink O (namedVertex names) := by
    funext x y
    exact propext (forestSelection_link_exact names C hc O ha x y)
  unfold RawRootSeparator
  rw [hl,chosenSets_roots]
  change ((∀ r, LiftRoot O (namedVertex names) r →
    Walk (LiftLink O (namedVertex names)) (fun _ => True) (namedVertex names v) r →
      ¬ Walk (LiftLink O (namedVertex names)) (fun z => z ≠ namedVertex names u) (namedVertex names v) r) ∧
    names u ≠ names v) ↔ O.rel u v
  rw [lifted_rootSeparator_iff O _ (namedVertex_injective names)]
  constructor
  · rintro ⟨h,hne⟩
    exact h.resolve_right (fun he => hne (congrArg names he))
  · intro h
    refine ⟨Or.inl h,?_⟩
    intro he
    exact O.irrefl v (names.injective he ▸ h)

#print axioms incident_pair_rigid
#print axioms forestSelection_link_exact
#print axioms sparseEarlier_forest_exact
end StackSorting.CapturedLinkExtraction
