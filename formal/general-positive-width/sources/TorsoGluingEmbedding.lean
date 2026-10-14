import TorsoGraph
import GluingTorsoPaths
import CompressionPaths

namespace StackSorting.BiInterface
variable {k : ℕ} {V W : Type*} (G : Graph k V) (H : Graph k W)

private theorem torso_seam_iff (v : G.boundary) (w : H.boundary) :
    Seam (torso G) (torso H) v w ↔ Seam G H v.val w.val := by
  constructor
  · rintro ⟨i,hi,hj⟩
    exact ⟨i,(boundaryPort_eq_some G (true,i) v).mp hi,
      (boundaryPort_eq_some H (false,i) w).mp hj⟩
  · rintro ⟨i,hi,hj⟩
    exact ⟨i,(boundaryPort_eq_some G (true,i) v).mpr hi,
      (boundaryPort_eq_some H (false,i) w).mpr hj⟩

/-- Embeds the glued actual torso vertices into the original glued graph. -/
def torsoGlueEmbed : Glued (torso G) (torso H) → Glued G H :=
  glueLift (torso G) (torso H)
    (fun v => inLeft G H v.val) (fun w => inRight G H w.val) (by
      intro v w h
      exact (inLeft_eq_inRight G H v.val w.val).mpr ((torso_seam_iff G H v w).mp h))

@[simp] theorem torsoGlueEmbed_left (v : G.boundary) :
    torsoGlueEmbed G H (inLeft (torso G) (torso H) v) = inLeft G H v.val := rfl
@[simp] theorem torsoGlueEmbed_right (w : H.boundary) :
    torsoGlueEmbed G H (inRight (torso G) (torso H) w) = inRight G H w.val := rfl

theorem torsoGlueEmbed_injective : Function.Injective (torsoGlueEmbed G H) := by
  apply glueLift_injective
  · exact (inLeft_injective G H).comp Subtype.val_injective
  · exact (inRight_injective G H).comp Subtype.val_injective
  · intro v w h
    exact (torso_seam_iff G H v w).mpr ((inLeft_eq_inRight G H v.val w.val).mp h)

private theorem left_boundary_of_range (v : V)
    (h : inLeft G H v ∈ Set.range (torsoGlueEmbed G H)) : v ∈ G.boundary := by
  obtain ⟨q,hq⟩ := h
  induction q using Quotient.inductionOn with | h q =>
    cases q with
    | inl u =>
      have he : u.val = v := inLeft_injective G H hq
      exact he ▸ u.property
    | inr u =>
      obtain ⟨i,hi,_⟩ := (inLeft_eq_inRight G H v u.val).mp hq.symm
      exact ⟨(true,i),hi⟩

private theorem right_boundary_of_range (v : W)
    (h : inRight G H v ∈ Set.range (torsoGlueEmbed G H)) : v ∈ H.boundary := by
  obtain ⟨q,hq⟩ := h
  induction q using Quotient.inductionOn with | h q =>
    cases q with
    | inl u =>
      obtain ⟨i,_,hi⟩ := (inLeft_eq_inRight G H u.val v).mp hq
      exact ⟨(false,i),hi⟩
    | inr u =>
      have he : u.val = v := inRight_injective G H hq
      exact he ▸ u.property

theorem oldInterior_eq_compl_range :
    oldInterior G H = (Set.range (torsoGlueEmbed G H))ᶜ := by
  ext q
  constructor
  · rintro (⟨v,hv,hi⟩ | ⟨v,hv,hi⟩) hr
    · exact hi (left_boundary_of_range G H v (hv.symm ▸ hr))
    · exact hi (right_boundary_of_range G H v (hv.symm ▸ hr))
  · intro hn
    induction q using Quotient.inductionOn with | h q =>
      cases q with
      | inl v =>
        refine Or.inl ⟨v,rfl,?_⟩
        intro hv
        exact hn ⟨inLeft (torso G) (torso H) ⟨v,hv⟩,rfl⟩
      | inr v =>
        refine Or.inr ⟨v,rfl,?_⟩
        intro hv
        exact hn ⟨inRight (torso G) (torso H) ⟨v,hv⟩,rfl⟩

theorem torsoGlueEmbed_port (p : Port k) :
    ((glue (torso G) (torso H)).port p).map (torsoGlueEmbed G H) =
      (glue G H).port p := by
  obtain ⟨b,i⟩ := p
  cases b
  · change ((boundaryPort G (false,i)).map (inLeft (torso G) (torso H))).map
      (torsoGlueEmbed G H) = (G.left i).map (inLeft G H)
    rw [Option.map_map]
    change (boundaryPort G (false,i)).map (fun v => inLeft G H v.val) = _
    simpa only [Option.map_map,Function.comp_def,Graph.port] using
      congrArg (Option.map (inLeft G H)) (boundaryPort_val G (false,i))
  · change ((boundaryPort H (true,i)).map (inRight (torso G) (torso H))).map
      (torsoGlueEmbed G H) = (H.right i).map (inRight G H)
    rw [Option.map_map]
    change (boundaryPort H (true,i)).map (fun v => inRight G H v.val) = _
    simpa only [Option.map_map,Function.comp_def,Graph.port] using
      congrArg (Option.map (inRight G H)) (boundaryPort_val H (true,i))

theorem outer_boundary_subset_range :
    (glue G H).boundary ⊆ Set.range (torsoGlueEmbed G H) := by
  rintro q ⟨p,hp⟩
  rw [← torsoGlueEmbed_port G H p] at hp
  obtain ⟨s,_,hs⟩ := Option.map_eq_some_iff.mp hp
  exact ⟨s,hs⟩

theorem torsoGlueEmbed_boundary (q : Glued (torso G) (torso H)) :
    torsoGlueEmbed G H q ∈ (glue G H).boundary ↔
      q ∈ (glue (torso G) (torso H)).boundary := by
  constructor
  · rintro ⟨p,hp⟩
    rw [← torsoGlueEmbed_port G H p] at hp
    obtain ⟨s,hs,he⟩ := Option.map_eq_some_iff.mp hp
    have he' := torsoGlueEmbed_injective G H he
    exact ⟨p,he' ▸ hs⟩
  · rintro ⟨p,hp⟩
    refine ⟨p,?_⟩
    rw [← torsoGlueEmbed_port G H p,hp]
    rfl

/-- The glued torso graph has exactly the edges obtained by eliminating the
original unnamed interiors, after dropping reflexive pairs. -/
theorem torsoGlueEmbed_adj (a b : Glued (torso G) (torso H)) :
    (glue (torso G) (torso H)).Adj a b ↔ a ≠ b ∧
      Through (glue G H).Adj (Set.range (torsoGlueEmbed G H))ᶜ
        (torsoGlueEmbed G H a) (torsoGlueEmbed G H b) := by
  rw [← oldInterior_eq_compl_range, eliminate_original_interiors]
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro he
      subst b
      exact (glue (torso G) (torso H)).loopless a h
    · rcases h with ⟨v,w,hvw,rfl,rfl⟩ | ⟨v,w,hvw,rfl,rfl⟩
      · exact Or.inr (Or.inl ⟨v.val,w.val,rfl,rfl,hvw.2⟩)
      · exact Or.inr (Or.inr ⟨v.val,w.val,rfl,rfl,hvw.2⟩)
  · rintro ⟨hne,h⟩
    rcases h with he | ⟨v,w,hv,hw,hp⟩ | ⟨v,w,hv,hw,hp⟩
    · exact (hne (torsoGlueEmbed_injective G H he)).elim
    · have hvB := left_boundary_of_range G H v ⟨a,hv.symm⟩
      have hwB := left_boundary_of_range G H w ⟨b,hw.symm⟩
      have hv' : inLeft (torso G) (torso H) ⟨v,hvB⟩ = a := torsoGlueEmbed_injective G H hv
      have hw' : inLeft (torso G) (torso H) ⟨w,hwB⟩ = b := torsoGlueEmbed_injective G H hw
      refine Or.inl ⟨⟨v,hvB⟩,⟨w,hwB⟩,⟨?_,hp⟩,hv',hw'⟩
      intro he
      exact hne (hv'.symm.trans ((congrArg (inLeft (torso G) (torso H)) he).trans hw'))
    · have hvB := right_boundary_of_range G H v ⟨a,hv.symm⟩
      have hwB := right_boundary_of_range G H w ⟨b,hw.symm⟩
      have hv' : inRight (torso G) (torso H) ⟨v,hvB⟩ = a := torsoGlueEmbed_injective G H hv
      have hw' : inRight (torso G) (torso H) ⟨w,hwB⟩ = b := torsoGlueEmbed_injective G H hw
      refine Or.inr ⟨⟨v,hvB⟩,⟨w,hwB⟩,⟨?_,hp⟩,hv',hw'⟩
      intro he
      exact hne (hv'.symm.trans ((congrArg (inRight (torso G) (torso H)) he).trans hw'))

theorem torsoGlueEmbed_through (a b : Glued (torso G) (torso H)) :
    Through (glue (torso G) (torso H)).Adj (glue (torso G) (torso H)).boundaryᶜ a b ↔
      Through (glue G H).Adj (glue G H).boundaryᶜ
        (torsoGlueEmbed G H a) (torsoGlueEmbed G H b) := by
  have hr : (glue (torso G) (torso H)).Adj =
      (fun x y => x ≠ y ∧ Through (glue G H).Adj (Set.range (torsoGlueEmbed G H))ᶜ
        (torsoGlueEmbed G H x) (torsoGlueEmbed G H y)) := by
    funext x y
    exact propext (torsoGlueEmbed_adj G H x y)
  have hi : (glue (torso G) (torso H)).boundaryᶜ =
      (torsoGlueEmbed G H) ⁻¹' (glue G H).boundaryᶜ := by
    ext x
    exact not_congr (torsoGlueEmbed_boundary G H x).symm
  rw [hr,hi]
  exact Through.compress_then_eliminate (torsoGlueEmbed G H) (torsoGlueEmbed_injective G H)
    (glue G H).boundary (outer_boundary_subset_range G H) a b

#print axioms torsoGlueEmbed_through
end StackSorting.BiInterface
