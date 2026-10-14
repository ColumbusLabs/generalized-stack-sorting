import TorsoPaths

namespace StackSorting.BiInterface.Through
variable {V W : Type*} {R : V → V → Prop} {I : Set V} {a b : V}

/-- Adding or deleting reflexive edges changes no interface-avoiding walk. -/
theorem remove_diagonal :
    Through (fun x y => x ≠ y ∧ R x y) I a b ↔ Through R I a b := by
  classical
  constructor
  · intro h
    exact h.mono (by intro x y h; exact h.2) (by intro x hx; exact hx)
  · intro h
    induction h with
    | refl x => exact .refl x
    | @edge x y h =>
      by_cases he : x = y
      · subst_vars; exact .refl _
      · exact .edge ⟨he,h⟩
    | join _ hm _ ih₁ ih₂ => exact .join ih₁ hm ih₂

private theorem lift_through (f : W → V) (hf : Function.Injective f)
    (h : Through R (Set.range f ∩ I) a b) :
    ∀ x y, a = f x → b = f y →
      Through (fun x y => R (f x) (f y)) (f ⁻¹' I) x y := by
  induction h with
  | refl v =>
    intro x y hx hy
    have he := hf (hx.symm.trans hy)
    subst y
    exact .refl x
  | edge h =>
    intro x y hx hy
    exact .edge (by simpa [hx,hy] using h)
  | join _ hm _ ih₁ ih₂ =>
    intro x y hx hy
    obtain ⟨z,hz⟩ := hm.1
    exact .join (ih₁ x z hx hz.symm) (by simpa [hz] using hm.2) (ih₂ z y hz.symm hy)

theorem embedding_iff (f : W → V) (hf : Function.Injective f) (x y : W) :
    Through (fun x y => R (f x) (f y)) (f ⁻¹' I) x y ↔
      Through R (Set.range f ∩ I) (f x) (f y) := by
  constructor
  · intro h
    exact h.map f (by intros; assumption) (by intro z hz; exact ⟨⟨z,rfl⟩,hz⟩)
  · intro h
    exact lift_through f hf h x y rfl rfl

/-- Exact torso-of-torso path law, allowing a different vertex type for the
retained vertices. It is based on actual paths, not an assumed congruence. -/
theorem compress_then_eliminate (f : W → V) (hf : Function.Injective f)
    (B : Set V) (hB : B ⊆ Set.range f) (x y : W) :
    Through (fun x y => x ≠ y ∧ Through R (Set.range f)ᶜ (f x) (f y))
      (f ⁻¹' Bᶜ) x y ↔ Through R Bᶜ (f x) (f y) := by
  rw [remove_diagonal, embedding_iff f hf, eliminate_union]
  have hsets : (Set.range f)ᶜ ∪ (Set.range f ∩ Bᶜ) = Bᶜ := by
    ext v
    constructor
    · rintro (h | ⟨_,h⟩)
      · exact fun hv => h (hB hv)
      · exact h
    · intro h
      by_cases hr : v ∈ Set.range f
      · exact Or.inr ⟨hr,h⟩
      · exact Or.inl hr
  rw [hsets]

end StackSorting.BiInterface.Through
