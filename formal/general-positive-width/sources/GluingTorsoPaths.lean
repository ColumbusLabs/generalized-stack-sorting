import TorsoAbstraction

namespace StackSorting.BiInterface
variable {k : ℕ} {V W : Type*} (G : Graph k V) (H : Graph k W)

def oldInterior : Set (Glued G H) :=
  {q | (∃ v, inLeft G H v = q ∧ v ∉ G.boundary) ∨
       (∃ w, inRight G H w = q ∧ w ∉ H.boundary)}

private theorem seam_left_boundary {v w} (h : Seam G H v w) : v ∈ G.boundary := by
  obtain ⟨i,hi,_⟩ := h
  exact ⟨(true,i),hi⟩
private theorem seam_right_boundary {v w} (h : Seam G H v w) : w ∈ H.boundary := by
  obtain ⟨i,_,hi⟩ := h
  exact ⟨(false,i),hi⟩

/-- The disjoint alternatives after eliminating the original interiors.
A walk cannot change sides internally without meeting an original interface. -/
def Collapsed (x y : Glued G H) : Prop :=
  x = y ∨
  (∃ v w, inLeft G H v = x ∧ inLeft G H w = y ∧
    Through G.Adj G.boundaryᶜ v w) ∨
  (∃ v w, inRight G H v = x ∧ inRight G H w = y ∧
    Through H.Adj H.boundaryᶜ v w)

private theorem collapsed_symm {x y} (h : Collapsed G H x y) : Collapsed G H y x := by
  rcases h with h | ⟨v,w,hv,hw,hp⟩ | ⟨v,w,hv,hw,hp⟩
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl ⟨w,v,hw,hv,hp.reverse (by intros; apply G.symm; assumption)⟩)
  · exact Or.inr (Or.inr ⟨w,v,hw,hv,hp.reverse (by intros; apply H.symm; assumption)⟩)

private theorem collapsed_to_left {x v} (hi : v ∉ G.boundary)
    (h : Collapsed G H x (inLeft G H v)) :
    ∃ u, inLeft G H u = x ∧ Through G.Adj G.boundaryᶜ u v := by
  rcases h with h | ⟨u,w,hu,hw,hp⟩ | ⟨u,w,hu,hw,hp⟩
  · exact ⟨v,h.symm,.refl v⟩
  · have he := inLeft_injective G H hw
    subst w
    exact ⟨u,hu,hp⟩
  · exact (hi (seam_left_boundary G H
      ((inLeft_eq_inRight G H v w).mp hw.symm))).elim

private theorem collapsed_to_right {x v} (hi : v ∉ H.boundary)
    (h : Collapsed G H x (inRight G H v)) :
    ∃ u, inRight G H u = x ∧ Through H.Adj H.boundaryᶜ u v := by
  rcases h with h | ⟨u,w,hu,hw,hp⟩ | ⟨u,w,hu,hw,hp⟩
  · exact ⟨v,h.symm,.refl v⟩
  · exact (hi (seam_right_boundary G H
      ((inLeft_eq_inRight G H w v).mp hw))).elim
  · have he := inRight_injective G H hw
    subst w
    exact ⟨u,hu,hp⟩

/-- Actual path compositionality before the old interface vertices are removed.
This lemma uses the real quotient graph and real internal-vertex restriction. -/
theorem eliminate_original_interiors (x y : Glued G H) :
    Through (glue G H).Adj (oldInterior G H) x y ↔ Collapsed G H x y := by
  constructor
  · intro h
    induction h with
    | refl a => exact Or.inl rfl
    | edge h =>
      rcases h with ⟨v,w,hvw,hv,hw⟩ | ⟨v,w,hvw,hv,hw⟩
      · exact Or.inr (Or.inl ⟨v,w,hv,hw,.edge hvw⟩)
      · exact Or.inr (Or.inr ⟨v,w,hv,hw,.edge hvw⟩)
    | join _ hm _ ih₁ ih₂ =>
      rcases hm with ⟨v,hv,hi⟩ | ⟨v,hv,hi⟩
      · subst_vars
        obtain ⟨u,hu,hp⟩ := collapsed_to_left G H hi ih₁
        obtain ⟨w,hw,hq⟩ := collapsed_to_left G H hi (collapsed_symm G H ih₂)
        exact Or.inr (Or.inl ⟨u,w,hu,hw,.join hp hi
          (hq.reverse (by intros; apply G.symm; assumption))⟩)
      · subst_vars
        obtain ⟨u,hu,hp⟩ := collapsed_to_right G H hi ih₁
        obtain ⟨w,hw,hq⟩ := collapsed_to_right G H hi (collapsed_symm G H ih₂)
        exact Or.inr (Or.inr ⟨u,w,hu,hw,.join hp hi
          (hq.reverse (by intros; apply H.symm; assumption))⟩)
  · rintro (rfl | ⟨v,w,hv,hw,hp⟩ | ⟨v,w,hv,hw,hp⟩)
    · exact .refl _
    · subst_vars
      exact hp.map (inLeft G H)
        (by intro a b hab; exact Or.inl ⟨a,b,hab,rfl,rfl⟩)
        (by intro a ha; exact Or.inl ⟨a,rfl,ha⟩)
    · subst_vars
      exact hp.map (inRight G H)
        (by intro a b hab; exact Or.inr ⟨a,b,hab,rfl,rfl⟩)
        (by intro a ha; exact Or.inr ⟨a,rfl,ha⟩)

#print axioms eliminate_original_interiors
end StackSorting.BiInterface
