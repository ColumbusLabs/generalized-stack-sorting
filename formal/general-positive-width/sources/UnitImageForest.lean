import GroupForest
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.Units.Fintype

namespace StackSorting.Simon
open FactorizationTree

namespace FactorizationTree

variable {A M N : Type*} [Monoid M] [Monoid N]

theorem value_monoidHom (φ : A → M) (f : M →* N) (t : FactorizationTree A) :
    value (fun a => f (φ a)) t = f (value φ t) := by
  simp only [value, MonoidHom.map_list_prod, List.map_map, Function.comp_def]

theorem Valid.monoidHom {φ : A → M} {t : FactorizationTree A}
    (hv : Valid φ t) (f : M →* N) : Valid (fun a => f (φ a)) t := by
  induction hv with
  | leaf a => exact Valid.leaf a
  | node ts hc ha hb ih =>
    apply Valid.node ts ih ha
    rcases hb with htwo | ⟨e,he,hval⟩
    · exact Or.inl htwo
    · right
      refine ⟨f e, ?_, ?_⟩
      · rw [← f.map_mul, he]
      · intro r hr
        rw [value_monoidHom, hval r hr]

theorem hasTree_monoidHom (φ : A → M) (f : M →* N) (w : List A)
    (h : ℕ) (ht : HasTree φ w h) : HasTree (fun a => f (φ a)) w h := by
  obtain ⟨t,hw,hv,hh⟩ := ht
  exact ⟨t,hw,hv.monoidHom f,hh⟩

end FactorizationTree

/-- A word whose letter images are units admits the group-case height bound,
without assuming that the whole ambient monoid is a group. -/
theorem exists_unit_image_forest {A M : Type*} [Monoid M] [Fintype M]
    (φ : A → M) (w : List A) (hne : w ≠ [])
    (hunits : ∀ a ∈ w, IsUnit (φ a)) : HasTree φ w (3 * Fintype.card M) := by
  classical
  let unitLetter : A → Mˣ := fun a => if h : IsUnit (φ a) then h.unit else 1
  have ht := exists_finite_group_factorization_tree unitLetter w hne
  have hm := hasTree_monoidHom unitLetter (Units.coeHom M) w (3 * Fintype.card Mˣ) ht
  have hlabels : ∀ a ∈ w, φ (id a) = Units.coeHom M (unitLetter a) := by
    intro a ha
    simp [unitLetter, hunits a ha, IsUnit.unit_spec]
  have hr := hasTree_map (fun a => Units.coeHom M (unitLetter a)) φ id w
    (3 * Fintype.card Mˣ) hm hlabels
  have hc : Fintype.card Mˣ ≤ Fintype.card M :=
    Fintype.card_le_of_injective Units.val Units.val_injective
  apply hasTree_mono (by simpa using hr)
  omega

#print axioms exists_unit_image_forest
end StackSorting.Simon
