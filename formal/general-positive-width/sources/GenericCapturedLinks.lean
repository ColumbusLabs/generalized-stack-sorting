import GenericGuidanceFormula
import CapturedLinkSelection

namespace StackSorting.GuidedPathwidth.GenericIncidence.System
open SparseEndpointMSO SparseEndpointMSO.Guidance SparseEndpointMSO.FiniteCopy
open GraphWidth SameVertexForest ConnectedConeNormalization CapturedLinkExtraction
variable {n k : Nat} {H : SimpleGraph (Fin n)} (S : System H)

structure Selection where
  original : S.IncSet
  candidate : Fin k → Fin k → S.IncSet
  roots : S.IncSet

def parameterSets (C : Fin k → S.ColorData) (F : S.Selection (k := k)) : Parameter k → S.IncSet
  | .inl (i,j) => Fin.cases (C i).vertices (Fin.cases (C i).edges (fun _ => (C i).roots)) j
  | .inr (.inl (i,j)) => F.candidate i j
  | .inr (.inr j) => Fin.cases F.original (fun _ => F.roots) j

noncomputable def chosenSets (C : Fin k → S.ColorData) (F : S.Selection (k := k)) :
    Fin (parameterCount k) → S.IncSet :=
  fun j => S.parameterSets C F ((Fintype.equivFin (Parameter k)).symm j)

@[simp] theorem chosenSets_color (C : Fin k → S.ColorData) (F : S.Selection (k := k))
    (i : Fin k) (j : Fin 3) :
    S.chosenSets C F ((fixedIndices k).color i j) =
      Fin.cases (C i).vertices (Fin.cases (C i).edges (fun _ => (C i).roots)) j := by
  simp only [chosenSets,fixedIndices,Equiv.symm_apply_apply,parameterSets]
@[simp] theorem chosenSets_candidate (C : Fin k → S.ColorData) (F : S.Selection (k := k))
    (i j : Fin k) : S.chosenSets C F ((fixedIndices k).candidate i j)=F.candidate i j := by
  simp only [chosenSets,fixedIndices,Equiv.symm_apply_apply,parameterSets]
@[simp] theorem chosenSets_original (C : Fin k → S.ColorData) (F : S.Selection (k := k)) :
    S.chosenSets C F (fixedIndices k).original=F.original := by
  simp only [chosenSets,fixedIndices,Equiv.symm_apply_apply,parameterSets,Fin.cases_zero]
@[simp] theorem chosenSets_roots (C : Fin k → S.ColorData) (F : S.Selection (k := k)) :
    S.chosenSets C F (fixedIndices k).roots=F.roots := by
  simp only [chosenSets,fixedIndices,Equiv.symm_apply_apply,parameterSets]
  rfl

def RawLink (I : LinkIndices k b) (sets : Fin b → S.IncSet) (u v : S.Element) : Prop :=
  u≠v ∧ ((∃ e, S.isEdge e ∧ sets I.original e ∧ S.incident u e ∧ S.incident v e) ∨
    ∃ i j x, sets (I.candidate i j) x ∧
      S.rootRelation (sets (I.color i 0)) (sets (I.color i 1)) (sets (I.color i 2)) x u ∧
      S.rootRelation (sets (I.color j 0)) (sets (I.color j 1)) (sets (I.color j 2)) x v)

@[simp] theorem eval_allColorFormulas (fs : Fin k → IFormula a b)
    (env : Fin a → S.Element) (sets : Fin b → S.IncSet) :
    ActualEval S.atoms (allColorFormulas fs) env sets ↔
      ∀ i, ActualEval S.atoms (fs i) env sets := by
  induction k with
  | zero => simp [allColorFormulas,ActualEval]
  | succ k ih => simp [allColorFormulas,ActualEval,ih,Fin.forall_fin_succ]

@[simp] theorem eval_anyColorFormulas (fs : Fin k → IFormula a b)
    (env : Fin a → S.Element) (sets : Fin b → S.IncSet) :
    ActualEval S.atoms (anyColorFormulas fs) env sets ↔
      ∃ i, ActualEval S.atoms (fs i) env sets := by
  classical
  simp only [anyColorFormulas,ActualEval,S.eval_allColorFormulas,not_forall,not_not]

@[simp] theorem eval_capturedLinkFormula (I : LinkIndices k b) (u v : Fin a)
    (env : Fin a → S.Element) (sets : Fin b → S.IncSet) :
    ActualEval S.atoms (capturedLinkFormula I u v) env sets ↔ S.RawLink I sets (env u) (env v) := by
  classical
  simp only [capturedLinkFormula,ActualEval,orFormula,not_and_or,not_not,
    originalLinkFormula,edgeFormula,incidentFormula,atoms,Fin.cases_zero,
    Fin.cases_succ,S.eval_anyColorFormulas,pairLinkFormula,S.eval_rootFormula]
  rfl

@[simp] theorem rawLink_lift (I : LinkIndices k b) (sets : Fin b → S.IncSet)
    (X : S.IncSet) (u v : S.Element) : S.RawLink I.lift (Fin.cases X sets) u v ↔ S.RawLink I sets u v := Iff.rfl

@[simp] theorem eval_rawAvoidFormula (cut : Option (Fin a)) (u : Fin a)
    (env : Fin a → S.Element) (sets : Fin b → S.IncSet) :
    ActualEval S.atoms (rawAvoidFormula cut u) env sets ↔ Avoid (vertexCutValue env cut) (env u) := by
  cases cut <;> rfl

@[simp] theorem eval_capturedConnectedFormula (I : LinkIndices k b) (cut : Option (Fin a))
    (u v : Fin a) (env : Fin a → S.Element) (sets : Fin b → S.IncSet) :
    ActualEval S.atoms (capturedConnectedFormula I cut u v) env sets ↔
      Walk (S.RawLink I sets) (Avoid (vertexCutValue env cut)) (env u) (env v) := by
  simp only [capturedConnectedFormula,ActualEval,S.eval_rawAvoidFormula,
    S.eval_capturedLinkFormula,S.rawLink_lift,vertexCutValue_lift,Fin.cases_zero,and_imp]
  exact closedWithin_iff_walk (S.RawLink I sets) (Avoid (vertexCutValue env cut)) (env u) (env v)

def RawRootSeparator (I : LinkIndices k b) (sets : Fin b → S.IncSet) (x y : S.Element) : Prop :=
  ∀ r, sets I.roots r → Walk (S.RawLink I sets) (fun _ => True) y r →
    ¬Walk (S.RawLink I sets) (fun z => z≠x) y r

@[simp] theorem eval_capturedPreorderFormula (I : LinkIndices k b) (x y : Fin a)
    (env : Fin a → S.Element) (sets : Fin b → S.IncSet) :
    ActualEval S.atoms (capturedPreorderFormula I x y) env sets ↔ S.RawRootSeparator I sets (env x) (env y) := by
  simp only [capturedPreorderFormula,ActualEval,S.eval_capturedConnectedFormula,
    Fin.cases_zero,Fin.cases_succ,vertexCutValue,Option.map]
  rfl

def ColorRoot (C : Fin k → S.ColorData) (i : Fin k) : S.Element → S.Element → Prop :=
  S.rootRelation (C i).vertices (C i).edges (C i).roots

theorem color_root_unique (C : Fin k → S.ColorData) (hc : ∀ i, (C i).Valid)
    (i : Fin k) {x r s : S.Element} (hr : S.ColorRoot C i x r) (hs : S.ColorRoot C i x s) : r=s := by
  obtain ⟨q,_,hq⟩ := (hc i).2.1 x hr.2.1
  exact (hq r hr).trans (hq s hs).symm

theorem incident_pair_rigid {e x y u v : S.Element} (he : S.isEdge e)
    (hxy : x≠y) (huv : u≠v) (hx : S.incident x e) (hy : S.incident y e)
    (hu : S.incident u e) (hv : S.incident v e) :
    (x=u ∧ y=v) ∨ (x=v ∧ y=u) := by
  cases e with
  | inl e => exact he.elim
  | inr e =>
    have classify : ∀ z, S.incident z (.inr e) → z=Sum.inl (S.left e) ∨ z=Sum.inl (S.right e) := by
      intro z hz
      cases z with
      | inr z => exact hz.elim
      | inl z => exact hz.elim (fun h => Or.inl (congrArg Sum.inl h)) (fun h => Or.inr (congrArg Sum.inl h))
    rcases classify x hx with hx | hx <;> rcases classify y hy with hy | hy <;>
      rcases classify u hu with hu | hu <;> rcases classify v hv with hv | hv <;> simp_all

def Available (C : Fin k → S.ColorData) (u v : Fin n) : Prop :=
  (∃ e, S.isEdge e ∧ S.incident (.inl u) e ∧ S.incident (.inl v) e) ∨
    ∃ i j x, S.ColorRoot C i x (.inl u) ∧ S.ColorRoot C j x (.inl v)

def forestSelection (C : Fin k → S.ColorData) (O : RankedOrder n) : S.Selection (k := k) where
  original e := ∃ u v, ParentAdj O u v ∧ S.incident (.inl u) e ∧ S.incident (.inl v) e
  candidate i j x := ∃ u v, ParentAdj O u v ∧ S.ColorRoot C i x (.inl u) ∧ S.ColorRoot C j x (.inl v)
  roots := LiftRoot O Sum.inl

theorem forestSelection_link_exact (C : Fin k → S.ColorData) (hc : ∀ i, (C i).Valid)
    (O : RankedOrder n) (ha : ∀ u v, ParentAdj O u v → S.Available C u v) (x y : S.Element) :
    S.RawLink (fixedIndices k) (S.chosenSets C (S.forestSelection C O)) x y ↔ LiftLink O Sum.inl x y := by
  simp only [RawLink,S.chosenSets_color,S.chosenSets_candidate,S.chosenSets_original]
  change (x≠y ∧ ((∃ e, S.isEdge e ∧ (S.forestSelection C O).original e ∧
    S.incident x e ∧ S.incident y e) ∨ ∃ i j z,
      (S.forestSelection C O).candidate i j z ∧ S.ColorRoot C i z x ∧ S.ColorRoot C j z y)) ↔ _
  constructor
  · rintro ⟨hxy,⟨e,he,⟨u,v,huv,hu,hv⟩,hx,hy⟩ | ⟨i,j,z,⟨u,v,huv,hu,hv⟩,hx,hy⟩⟩
    · have huv' : (Sum.inl u : S.Element)≠.inl v := fun h => parentAdj_ne O huv (Sum.inl.inj h)
      rcases S.incident_pair_rigid he hxy huv' hx hy hu hv with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · exact ⟨u,v,hx,hy,huv⟩
      · exact ⟨v,u,hx,hy,parentAdj_symm O huv⟩
    · exact ⟨u,v,S.color_root_unique C hc i hx hu,S.color_root_unique C hc j hy hv,huv⟩
  · rintro ⟨u,v,rfl,rfl,huv⟩
    refine ⟨fun h => parentAdj_ne O huv (Sum.inl.inj h),?_⟩
    rcases ha u v huv with ⟨e,he,hu,hv⟩ | ⟨i,j,z,hu,hv⟩
    · exact Or.inl ⟨e,he,⟨u,v,huv,hu,hv⟩,hu,hv⟩
    · exact Or.inr ⟨i,j,z,⟨u,v,huv,hu,hv⟩,hu,hv⟩

/-- Exact generic-incidence preorder, before owner relativization and original
finite-copy pullback. No sparse graph model or chronology is needed locally. -/
theorem earlier_forest_exact (C : Fin k → S.ColorData) (hc : ∀ i, (C i).Valid)
    (O : RankedOrder n) (ha : ∀ u v, ParentAdj O u v → S.Available C u v) (u v : Fin n) :
    ActualEval S.atoms (capturedEarlierFormula (fixedIndices k) (0 : Fin 2) 1)
      (Fin.cases (.inl u) (fun _ => .inl v)) (S.chosenSets C (S.forestSelection C O)) ↔ O.rel u v := by
  simp only [capturedEarlierFormula,ActualEval,S.eval_capturedPreorderFormula]
  have hl : S.RawLink (fixedIndices k) (S.chosenSets C (S.forestSelection C O))=LiftLink O Sum.inl := by
    funext x y
    exact propext (S.forestSelection_link_exact C hc O ha x y)
  unfold RawRootSeparator
  rw [hl,S.chosenSets_roots]
  simp only [forestSelection,Fin.cases_zero,Guidance.cases_one]
  rw [lifted_rootSeparator_iff O Sum.inl Sum.inl_injective]
  change (Cone O u v ∧ (Sum.inl u : S.Element)≠Sum.inl v) ↔ O.rel u v
  constructor
  · rintro ⟨h,hne⟩
    exact h.resolve_right (fun he => hne (congrArg Sum.inl he))
  · intro h
    exact ⟨Or.inl h,fun he => O.irrefl v (Sum.inl.inj he ▸ h)⟩

#print axioms forestSelection_link_exact
#print axioms earlier_forest_exact
end StackSorting.GuidedPathwidth.GenericIncidence.System
