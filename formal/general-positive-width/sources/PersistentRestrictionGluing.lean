import PersistentRestrictionCode

namespace StackSorting.BiInterface.RepeatedColumn
variable {k : ℕ} {V W : Type*}
variable (G : Graph k V) (H : Graph k W)
variable (hmask : ∀ i, PersistentAt G i ↔ PersistentAt H i)
include hmask

/-- A persistent name in both factors is a single actual shared seam vertex. -/
theorem persistent_glue_left (v : V) :
    inLeft G H v ∈ Persistent (glue G H) ↔ v ∈ Persistent G := by
  constructor
  · rintro ⟨i,hi,hj⟩
    obtain ⟨u,hu,he⟩ := Option.map_eq_some_iff.mp hi
    have huv : u = v := inLeft_injective G H he
    subst u
    obtain ⟨w,hw,hew⟩ := Option.map_eq_some_iff.mp hj
    obtain ⟨j,hj,_⟩ := (inLeft_eq_inRight G H v w).mp hew.symm
    have hij := G.cross i j v hu hj
    subst j
    exact ⟨i,hu,hj⟩
  · rintro ⟨i,hi,hj⟩
    obtain ⟨w,hwl,hwr⟩ := (hmask i).mp ⟨v,hi,hj⟩
    have he : inLeft G H v = inRight G H w := (inLeft_eq_inRight G H v w).mpr ⟨i,hj,hwl⟩
    refine ⟨i,?_,?_⟩
    · change (G.left i).map (inLeft G H) = _
      rw [hi]; rfl
    · change (H.right i).map (inRight G H) = _
      rw [hwr,Option.map_some,he]

theorem persistent_glue_right (w : W) :
    inRight G H w ∈ Persistent (glue G H) ↔ w ∈ Persistent H := by
  constructor
  · rintro ⟨i,hi,hj⟩
    obtain ⟨v,hv,hev⟩ := Option.map_eq_some_iff.mp hi
    obtain ⟨u,hu,he⟩ := Option.map_eq_some_iff.mp hj
    have huw : u = w := inRight_injective G H he
    subst u
    obtain ⟨j,_,hj⟩ := (inLeft_eq_inRight G H v w).mp hev
    have hij := H.cross j i w hj hu
    subst j
    exact ⟨i,hj,hu⟩
  · rintro ⟨i,hi,hj⟩
    obtain ⟨v,hvl,hvr⟩ := (hmask i).mpr ⟨w,hi,hj⟩
    have he : inLeft G H v = inRight G H w := (inLeft_eq_inRight G H v w).mpr ⟨i,hvr,hi⟩
    refine ⟨i,?_,?_⟩
    · change (G.left i).map (inLeft G H) = _
      rw [hvl,Option.map_some,he]
    · change (H.right i).map (inRight G H) = _
      rw [hj]; rfl

private noncomputable def retainedLeft (v : ↥((Persistent G)ᶜ)) : ↥((Persistent (glue G H))ᶜ) :=
  ⟨inLeft G H v.val,fun hm => v.property ((persistent_glue_left G H hmask v.val).mp hm)⟩
private noncomputable def retainedRight (w : ↥((Persistent H)ᶜ)) : ↥((Persistent (glue G H))ᶜ) :=
  ⟨inRight G H w.val,fun hm => w.property ((persistent_glue_right G H hmask w.val).mp hm)⟩

/-- The concrete quotient map that commutes persistent-vertex deletion past
one gluing. Its values are actual surviving vertices of the original quotient. -/
noncomputable def restrictionGlueMap : Glued (removePersistent G) (removePersistent H) →
    ↥((Persistent (glue G H))ᶜ) :=
  glueLift (removePersistent G) (removePersistent H)
    (retainedLeft G H hmask) (retainedRight G H hmask) (by
      rintro v w ⟨i,hi,hj⟩
      apply Subtype.ext
      exact (inLeft_eq_inRight G H v.val w.val).mpr
        ⟨i,(restrictPort_eq_some _ _ v).mp hi,(restrictPort_eq_some _ _ w).mp hj⟩)

@[simp] theorem restrictionGlueMap_left (v : ↥((Persistent G)ᶜ)) :
    restrictionGlueMap G H hmask (inLeft (removePersistent G) (removePersistent H) v) =
      retainedLeft G H hmask v := rfl
@[simp] theorem restrictionGlueMap_right (w : ↥((Persistent H)ᶜ)) :
    restrictionGlueMap G H hmask (inRight (removePersistent G) (removePersistent H) w) =
      retainedRight G H hmask w := rfl

theorem restrictionGlueMap_injective : Function.Injective (restrictionGlueMap G H hmask) := by
  apply glueLift_injective
  · intro v w h
    exact Subtype.ext (inLeft_injective G H (congrArg Subtype.val h))
  · intro v w h
    exact Subtype.ext (inRight_injective G H (congrArg Subtype.val h))
  · intro v w h
    obtain ⟨i,hi,hj⟩ := (inLeft_eq_inRight G H v.val w.val).mp (congrArg Subtype.val h)
    exact ⟨i,(restrictPort_eq_some _ _ v).mpr hi,(restrictPort_eq_some _ _ w).mpr hj⟩

theorem restrictionGlueMap_surjective : Function.Surjective (restrictionGlueMap G H hmask) := by
  rintro ⟨q,hq⟩
  revert hq
  induction q using Quotient.inductionOn with | h q =>
    intro hq
    cases q with
    | inl v =>
      have hv : v ∉ Persistent G := fun hm => hq ((persistent_glue_left G H hmask v).mpr hm)
      exact ⟨inLeft (removePersistent G) (removePersistent H) ⟨v,hv⟩,Subtype.ext rfl⟩
    | inr w =>
      have hw : w ∉ Persistent H := fun hm => hq ((persistent_glue_right G H hmask w).mpr hm)
      exact ⟨inRight (removePersistent G) (removePersistent H) ⟨w,hw⟩,Subtype.ext rfl⟩

theorem restrictionGlueMap_adj (a b : Glued (removePersistent G) (removePersistent H)) :
    (removePersistent (glue G H)).Adj (restrictionGlueMap G H hmask a)
      (restrictionGlueMap G H hmask b) ↔
      (glue (removePersistent G) (removePersistent H)).Adj a b := by
  constructor
  · intro h
    rcases h with ⟨v,w,hvw,hv,hw⟩ | ⟨v,w,hvw,hv,hw⟩
    · have hv' : v ∉ Persistent G := by
        intro hm
        apply (restrictionGlueMap G H hmask a).property
        exact hv ▸ (persistent_glue_left G H hmask v).mpr hm
      have hw' : w ∉ Persistent G := by
        intro hm
        apply (restrictionGlueMap G H hmask b).property
        exact hw ▸ (persistent_glue_left G H hmask w).mpr hm
      refine Or.inl ⟨⟨v,hv'⟩,⟨w,hw'⟩,hvw,?_,?_⟩
      · apply restrictionGlueMap_injective G H hmask
        exact Subtype.ext hv
      · apply restrictionGlueMap_injective G H hmask
        exact Subtype.ext hw
    · have hv' : v ∉ Persistent H := by
        intro hm
        apply (restrictionGlueMap G H hmask a).property
        exact hv ▸ (persistent_glue_right G H hmask v).mpr hm
      have hw' : w ∉ Persistent H := by
        intro hm
        apply (restrictionGlueMap G H hmask b).property
        exact hw ▸ (persistent_glue_right G H hmask w).mpr hm
      refine Or.inr ⟨⟨v,hv'⟩,⟨w,hw'⟩,hvw,?_,?_⟩
      · apply restrictionGlueMap_injective G H hmask
        exact Subtype.ext hv
      · apply restrictionGlueMap_injective G H hmask
        exact Subtype.ext hw
  · intro h
    rcases h with ⟨v,w,hvw,rfl,rfl⟩ | ⟨v,w,hvw,rfl,rfl⟩
    · exact Or.inl ⟨v.val,w.val,hvw,rfl,rfl⟩
    · exact Or.inr ⟨v.val,w.val,hvw,rfl,rfl⟩

private theorem restrictionGlueMap_left_port (i : Fin k) :
    ((glue (removePersistent G) (removePersistent H)).left i).map (restrictionGlueMap G H hmask) =
      (removePersistent (glue G H)).left i := by
  apply Option.ext
  intro q
  change (((removePersistent G).left i).map
    (inLeft (removePersistent G) (removePersistent H))).map _ = some q ↔ _
  rw [Option.map_map, Option.map_eq_some_iff]
  constructor
  · rintro ⟨v,hv,hq⟩
    apply (restrictPort_eq_some (Persistent (glue G H))ᶜ ((glue G H).left i) q).mpr
    have hv' := (restrictPort_eq_some _ _ v).mp hv
    change (G.left i).map (inLeft G H) = some q.val
    exact Option.map_eq_some_iff.mpr ⟨v.val,hv',congrArg Subtype.val hq⟩
  · intro hq
    have hq' := (restrictPort_eq_some (Persistent (glue G H))ᶜ ((glue G H).left i) q).mp hq
    obtain ⟨v,hv,he⟩ := Option.map_eq_some_iff.mp hq'
    have hnv : v ∉ Persistent G := by
      intro hm
      exact q.property (he ▸ (persistent_glue_left G H hmask v).mpr hm)
    exact ⟨⟨v,hnv⟩,(restrictPort_eq_some _ _ ⟨v,hnv⟩).mpr hv,Subtype.ext he⟩

private theorem restrictionGlueMap_right_port (i : Fin k) :
    ((glue (removePersistent G) (removePersistent H)).right i).map (restrictionGlueMap G H hmask) =
      (removePersistent (glue G H)).right i := by
  apply Option.ext
  intro q
  change (((removePersistent H).right i).map
    (inRight (removePersistent G) (removePersistent H))).map _ = some q ↔ _
  rw [Option.map_map, Option.map_eq_some_iff]
  constructor
  · rintro ⟨v,hv,hq⟩
    apply (restrictPort_eq_some (Persistent (glue G H))ᶜ ((glue G H).right i) q).mpr
    have hv' := (restrictPort_eq_some _ _ v).mp hv
    change (H.right i).map (inRight G H) = some q.val
    exact Option.map_eq_some_iff.mpr ⟨v.val,hv',congrArg Subtype.val hq⟩
  · intro hq
    have hq' := (restrictPort_eq_some (Persistent (glue G H))ᶜ ((glue G H).right i) q).mp hq
    obtain ⟨v,hv,he⟩ := Option.map_eq_some_iff.mp hq'
    have hnv : v ∉ Persistent H := by
      intro hm
      exact q.property (he ▸ (persistent_glue_right G H hmask v).mpr hm)
    exact ⟨⟨v,hnv⟩,(restrictPort_eq_some _ _ ⟨v,hnv⟩).mpr hv,Subtype.ext he⟩

/-- Actual interface-preserving isomorphism: deleting the shared persistent
names before gluing or after gluing gives the same graph. Matching persistent
names are the sole input; no adjacency/path/decomposition witness is assumed. -/
noncomputable def restrictionGlueIso :
    Iso (glue (removePersistent G) (removePersistent H)) (removePersistent (glue G H)) where
  vertex := Equiv.ofBijective (restrictionGlueMap G H hmask)
    ⟨restrictionGlueMap_injective G H hmask,restrictionGlueMap_surjective G H hmask⟩
  adj := restrictionGlueMap_adj G H hmask
  left := restrictionGlueMap_left_port G H hmask
  right := restrictionGlueMap_right_port G H hmask

#print axioms restrictionGlueIso
end StackSorting.BiInterface.RepeatedColumn
