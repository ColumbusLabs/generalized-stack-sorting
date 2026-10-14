import TorsoGluingEmbedding
import TorsoCodeIso
import GluingIso

/-!
Exact finite-walk replacement of one side of an actual quotient gluing.
Unlike torso-code congruence alone, the fixed side retains every vertex,
including unnamed interior vertices. This is the local mechanism used to
shorten idempotent padding around a selected column.
-/

namespace StackSorting.BiInterface.RepeatedColumn
variable {k : ℕ} {U V W : Type*}

abbrev Reach {A : Type*} (R : A → A → Prop) := Through R Set.univ

/-- The identity isomorphism, with no change of ports. -/
def identIso (G : Graph k V) : Iso G G where
  vertex := Equiv.refl V
  adj := by intros; rfl
  left := by intro i; simp
  right := by intro i; simp

/-- All finite walks, rather than just boundary-avoiding walks, transport
through an actual graph isomorphism. -/
theorem reach_iso_iff {G : Graph k U} {H : Graph k V} (e : Iso G H) (x y : U) :
    Reach H.Adj (e.vertex x) (e.vertex y) ↔ Reach G.Adj x y := by
  constructor
  · intro h
    have hh := h.map (J := Set.univ) e.vertex.symm
      (by intro a b hab; exact (e.adj _ _).mp (by simpa using hab))
      (by intros; trivial)
    simpa using hh
  · intro h
    exact h.map e.vertex (by intro a b hab; exact (e.adj a b).mpr hab)
      (by intros; trivial)

variable (G : Graph k U) (H : Graph k V)

private def leftInterior : Set (Glued G H) :=
  {q | ∃ v, inLeft G H v = q ∧ v ∉ G.boundary}

/-- Compress only the left factor; all vertices of the right factor survive. -/
def leftTorsoEmbed : Glued (torso G) H → Glued G H :=
  glueLift (torso G) H (fun v => inLeft G H v.val) (inRight G H) (by
    rintro v w ⟨i,hi,hj⟩
    exact (inLeft_eq_inRight G H v.val w).mpr
      ⟨i,(boundaryPort_eq_some G (true,i) v).mp hi,hj⟩)

@[simp] theorem leftTorsoEmbed_left (v : G.boundary) :
    leftTorsoEmbed G H (inLeft (torso G) H v) = inLeft G H v.val := rfl
@[simp] theorem leftTorsoEmbed_right (v : V) :
    leftTorsoEmbed G H (inRight (torso G) H v) = inRight G H v := rfl

theorem leftTorsoEmbed_injective : Function.Injective (leftTorsoEmbed G H) := by
  apply glueLift_injective
  · exact (inLeft_injective G H).comp Subtype.val_injective
  · exact inRight_injective G H
  · intro v w h
    obtain ⟨i,hi,hj⟩ := (inLeft_eq_inRight G H v.val w).mp h
    exact ⟨i,(boundaryPort_eq_some G (true,i) v).mpr hi,hj⟩

private theorem left_boundary_of_retained (v : U)
    (h : inLeft G H v ∈ Set.range (leftTorsoEmbed G H)) : v ∈ G.boundary := by
  obtain ⟨q,hq⟩ := h
  induction q using Quotient.inductionOn with | h q =>
    cases q with
    | inl u =>
      have he : u.val = v := inLeft_injective G H hq
      exact he ▸ u.property
    | inr u =>
      obtain ⟨i,hi,_⟩ := (inLeft_eq_inRight G H v u).mp hq.symm
      exact ⟨(true,i),hi⟩

private theorem leftInterior_eq_compl_range :
    leftInterior G H = (Set.range (leftTorsoEmbed G H))ᶜ := by
  ext q
  constructor
  · rintro ⟨v,hv,hi⟩ hr
    exact hi (left_boundary_of_retained G H v (hv.symm ▸ hr))
  · intro hn
    induction q using Quotient.inductionOn with | h q =>
      cases q with
      | inl v =>
        refine ⟨v,rfl,?_⟩
        intro hv
        exact hn ⟨inLeft (torso G) H ⟨v,hv⟩,rfl⟩
      | inr v => exact (hn ⟨inRight (torso G) H v,rfl⟩).elim

private def LeftCollapsed (x y : Glued G H) : Prop :=
  x = y ∨
  (∃ v w, inLeft G H v = x ∧ inLeft G H w = y ∧
    Through G.Adj G.boundaryᶜ v w) ∨
  (∃ v w, inRight G H v = x ∧ inRight G H w = y ∧ H.Adj v w)

private theorem leftCollapsed_symm {x y} (h : LeftCollapsed G H x y) :
    LeftCollapsed G H y x := by
  rcases h with h | ⟨v,w,hv,hw,hp⟩ | ⟨v,w,hv,hw,hp⟩
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl ⟨w,v,hw,hv,hp.reverse (by intros; apply G.symm; assumption)⟩)
  · exact Or.inr (Or.inr ⟨w,v,hw,hv,H.symm hp⟩)

private theorem leftCollapsed_to_left {x v} (hi : v ∉ G.boundary)
    (h : LeftCollapsed G H x (inLeft G H v)) :
    ∃ u, inLeft G H u = x ∧ Through G.Adj G.boundaryᶜ u v := by
  rcases h with h | ⟨u,w,hu,hw,hp⟩ | ⟨u,w,hu,hw,hp⟩
  · exact ⟨v,h.symm,.refl v⟩
  · have he := inLeft_injective G H hw
    subst w
    exact ⟨u,hu,hp⟩
  · obtain ⟨i,hiv,_⟩ := (inLeft_eq_inRight G H v w).mp hw.symm
    exact (hi ⟨(true,i),hiv⟩).elim

private theorem eliminate_left_interior (x y : Glued G H) :
    Through (glue G H).Adj (leftInterior G H) x y ↔ LeftCollapsed G H x y := by
  constructor
  · intro h
    induction h with
    | refl a => exact Or.inl rfl
    | edge h =>
      rcases h with ⟨v,w,hvw,hv,hw⟩ | ⟨v,w,hvw,hv,hw⟩
      · exact Or.inr (Or.inl ⟨v,w,hv,hw,.edge hvw⟩)
      · exact Or.inr (Or.inr ⟨v,w,hv,hw,hvw⟩)
    | join _ hm _ ih₁ ih₂ =>
      obtain ⟨v,hv,hi⟩ := hm
      subst_vars
      obtain ⟨u,hu,hp⟩ := leftCollapsed_to_left G H hi ih₁
      obtain ⟨w,hw,hq⟩ := leftCollapsed_to_left G H hi (leftCollapsed_symm G H ih₂)
      exact Or.inr (Or.inl ⟨u,w,hu,hw,.join hp hi
        (hq.reverse (by intros; apply G.symm; assumption))⟩)
  · rintro (rfl | ⟨v,w,hv,hw,hp⟩ | ⟨v,w,hv,hw,hp⟩)
    · exact .refl _
    · subst_vars
      exact hp.map (inLeft G H)
        (by intro a b hab; exact Or.inl ⟨a,b,hab,rfl,rfl⟩)
        (by intro a ha; exact ⟨a,rfl,ha⟩)
    · subst_vars
      exact .edge (Or.inr ⟨v,w,hp,rfl,rfl⟩)

/-- Exact finite-walk compression of the left side of the genuine quotient. -/
theorem leftTorsoEmbed_adj (a b : Glued (torso G) H) :
    (glue (torso G) H).Adj a b ↔ a ≠ b ∧
      Through (glue G H).Adj (Set.range (leftTorsoEmbed G H))ᶜ
        (leftTorsoEmbed G H a) (leftTorsoEmbed G H b) := by
  rw [← leftInterior_eq_compl_range, eliminate_left_interior]
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro he
      subst b
      exact (glue (torso G) H).loopless a h
    · rcases h with ⟨v,w,hvw,rfl,rfl⟩ | ⟨v,w,hvw,rfl,rfl⟩
      · exact Or.inr (Or.inl ⟨v.val,w.val,rfl,rfl,hvw.2⟩)
      · exact Or.inr (Or.inr ⟨v,w,rfl,rfl,hvw⟩)
  · rintro ⟨hne,h⟩
    rcases h with he | ⟨v,w,hv,hw,hp⟩ | ⟨v,w,hv,hw,hp⟩
    · exact (hne (leftTorsoEmbed_injective G H he)).elim
    · have hvB := left_boundary_of_retained G H v ⟨a,hv.symm⟩
      have hwB := left_boundary_of_retained G H w ⟨b,hw.symm⟩
      have hv' : inLeft (torso G) H ⟨v,hvB⟩ = a := leftTorsoEmbed_injective G H hv
      have hw' : inLeft (torso G) H ⟨w,hwB⟩ = b := leftTorsoEmbed_injective G H hw
      refine Or.inl ⟨⟨v,hvB⟩,⟨w,hwB⟩,⟨?_,hp⟩,hv',hw'⟩
      intro he
      exact hne (hv'.symm.trans ((congrArg (inLeft (torso G) H) he).trans hw'))
    · have hv' : inRight (torso G) H v = a := leftTorsoEmbed_injective G H hv
      have hw' : inRight (torso G) H w = b := leftTorsoEmbed_injective G H hw
      exact Or.inr ⟨v,w,hp,hv',hw'⟩

theorem leftTorsoEmbed_reach (a b : Glued (torso G) H) :
    Reach (glue (torso G) H).Adj a b ↔
      Reach (glue G H).Adj (leftTorsoEmbed G H a) (leftTorsoEmbed G H b) := by
  have hr : (glue (torso G) H).Adj =
      (fun x y => x ≠ y ∧ Through (glue G H).Adj (Set.range (leftTorsoEmbed G H))ᶜ
        (leftTorsoEmbed G H x) (leftTorsoEmbed G H y)) := by
    funext x y
    exact propext (leftTorsoEmbed_adj G H x y)
  change Through (glue (torso G) H).Adj Set.univ a b ↔ _
  rw [hr]
  simpa using (Through.compress_then_eliminate (R := (glue G H).Adj)
    (leftTorsoEmbed G H) (leftTorsoEmbed_injective G H) ∅ (by simp) a b)

/-- Equal codes allow arbitrary left padding to be replaced while preserving
connectivity between every pair of actual vertices on the unchanged side. -/
theorem replace_left_padding (G' : Graph k W) (h : abstraction G = abstraction G')
    (x y : V) :
    Reach (glue G H).Adj (inRight G H x) (inRight G H y) ↔
      Reach (glue G' H).Adj (inRight G' H x) (inRight G' H y) := by
  let e := (torsoIsoOfCode h).glue (identIso H)
  have he := reach_iso_iff e (inRight (torso G) H x) (inRight (torso G) H y)
  have he' : Reach (glue (torso G') H).Adj
      (inRight (torso G') H x) (inRight (torso G') H y) ↔
      Reach (glue (torso G) H).Adj
        (inRight (torso G) H x) (inRight (torso G) H y) := he
  exact (leftTorsoEmbed_reach G H _ _).symm.trans
    (he'.symm.trans (leftTorsoEmbed_reach G' H _ _))

/-- Reversing the interfaces does not alter the underlying graph. -/
def reverseGraph (G : Graph k U) : Graph k U where
  Adj := G.Adj
  symm := G.symm
  loopless := G.loopless
  left := G.right
  right := G.left
  left_inj := G.right_inj
  right_inj := G.left_inj
  cross := by intro i j x hi hj; exact (G.cross j i x hj hi).symm

@[simp] theorem reverseGraph_reverseGraph (G : Graph k U) : reverseGraph (reverseGraph G) = G := rfl

/-- The quotient obtained by exchanging the two factors and their interfaces. -/
def swapGlue : Glued G H → Glued (reverseGraph H) (reverseGraph G) :=
  glueLift G H (inRight (reverseGraph H) (reverseGraph G))
    (inLeft (reverseGraph H) (reverseGraph G)) (by
      rintro v w ⟨i,hi,hj⟩
      exact ((inLeft_eq_inRight (reverseGraph H) (reverseGraph G) w v).mpr
        ⟨i,hj,hi⟩).symm)

private theorem swapGlue_inverse (q : Glued G H) :
    swapGlue (reverseGraph H) (reverseGraph G) (swapGlue G H q) = q := by
  induction q using Quotient.inductionOn with | h q => cases q <;> rfl

private theorem swapGlue_adj {a b : Glued G H} (h : (glue G H).Adj a b) :
    (glue (reverseGraph H) (reverseGraph G)).Adj (swapGlue G H a) (swapGlue G H b) := by
  rcases h with ⟨x,y,hxy,rfl,rfl⟩ | ⟨x,y,hxy,rfl,rfl⟩
  · exact Or.inr ⟨x,y,hxy,rfl,rfl⟩
  · exact Or.inl ⟨x,y,hxy,rfl,rfl⟩

private theorem swapGlue_reach (a b : Glued G H) :
    Reach (glue (reverseGraph H) (reverseGraph G)).Adj (swapGlue G H a) (swapGlue G H b) ↔
      Reach (glue G H).Adj a b := by
  constructor
  · intro h
    have hh := h.map (J := Set.univ) (swapGlue (reverseGraph H) (reverseGraph G))
      (by intros; apply swapGlue_adj; assumption) (by intros; trivial)
    simpa only [swapGlue_inverse, reverseGraph_reverseGraph] using hh
  · intro h
    exact h.map (swapGlue G H) (by intros; apply swapGlue_adj; assumption) (by intros; trivial)

private theorem reverseGraph_boundary {A : Type*} (K : Graph k A) :
    (reverseGraph K).boundary = K.boundary := by
  ext v
  constructor <;> rintro ⟨⟨b,i⟩,hi⟩
  · cases b
    · exact ⟨(true,i),hi⟩
    · exact ⟨(false,i),hi⟩
  · cases b
    · exact ⟨(true,i),hi⟩
    · exact ⟨(false,i),hi⟩

private theorem reverseGraph_port {A : Type*} (K : Graph k A) (p : Port k) :
    (reverseGraph K).port p = K.port (!p.1,p.2) := by
  obtain ⟨b,i⟩ := p
  cases b <;> rfl

private theorem reverseGraph_abstraction_congr {G' : Graph k W}
    (h : abstraction G = abstraction G') :
    abstraction (reverseGraph G) = abstraction (reverseGraph G') := by
  apply Prod.ext
  · funext p
    apply Bool.eq_iff_iff.mpr
    rw [abstraction_presence, abstraction_presence, reverseGraph_port, reverseGraph_port,
      ← abstraction_presence, ← abstraction_presence, h]
  · apply Prod.ext
    · funext p q
      apply Bool.eq_iff_iff.mpr
      rw [abstraction_identity, abstraction_identity, reverseGraph_port, reverseGraph_port, reverseGraph_port, reverseGraph_port,
        ← abstraction_identity, ← abstraction_identity, h]
    · funext p q
      apply Bool.eq_iff_iff.mpr
      rw [abstraction_edge, abstraction_edge, reverseGraph_port, reverseGraph_port, reverseGraph_port, reverseGraph_port, reverseGraph_boundary, reverseGraph_boundary]
      change (∃ v w, G.port (!p.1,p.2) = some v ∧ G.port (!q.1,q.2) = some w ∧
        v ≠ w ∧ Through G.Adj G.boundaryᶜ v w) ↔
        (∃ v w, G'.port (!p.1,p.2) = some v ∧ G'.port (!q.1,q.2) = some w ∧
        v ≠ w ∧ Through G'.Adj G'.boundaryᶜ v w)
      rw [← abstraction_edge, ← abstraction_edge, h]

/-- Symmetric padding replacement, preserving every vertex of the left side. -/
theorem replace_right_padding (H' : Graph k W) (h : abstraction H = abstraction H')
    (x y : U) :
    Reach (glue G H).Adj (inLeft G H x) (inLeft G H y) ↔
      Reach (glue G H').Adj (inLeft G H' x) (inLeft G H' y) := by
  have hr := replace_left_padding (reverseGraph H) (reverseGraph G) (reverseGraph H')
    (reverseGraph_abstraction_congr H h) x y
  exact (swapGlue_reach G H (inLeft G H x) (inLeft G H y)).symm.trans
    (hr.trans (swapGlue_reach G H' (inLeft G H' x) (inLeft G H' y)))

#print axioms replace_left_padding
#print axioms replace_right_padding
end StackSorting.BiInterface.RepeatedColumn
