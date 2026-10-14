import Mathlib.RingTheory.Polynomial.GaussLemma

/-! Degree-preserving specialization of a primitive polynomial. Unlike the
usual monic lemma, this supports the nonmonic scalar stack polynomial. -/
namespace StackSorting.DegreeTwelve
open Polynomial

theorem primitive_unit_of_specialized_unit {R S : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (φ : R →+* S) (f : R[X]) (hp : f.IsPrimitive)
    (hl : φ f.leadingCoeff ≠ 0) (hu : IsUnit (f.map φ)) : IsUnit f := by
  have hd : f.degree = 0 :=
    (degree_map_eq_of_leadingCoeff_ne_zero φ hl).symm.trans
      (degree_eq_zero_of_isUnit hu)
  have he : f = C (f.coeff 0) := eq_C_of_degree_le_zero hd.le
  have hc : IsUnit (f.coeff 0) :=
    (isPrimitive_iff_isUnit_of_C_dvd.mp hp) _ (he ▸ dvd_rfl)
  rw [he]
  exact isUnit_C.mpr hc

theorem primitive_irreducible_of_specialization {R S : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (φ : R →+* S) (f : R[X]) (hp : f.IsPrimitive)
    (hl : φ f.leadingCoeff ≠ 0) (hi : Irreducible (f.map φ)) : Irreducible f := by
  refine ⟨fun hu => hi.not_isUnit (hu.map (mapRingHom φ)), ?_⟩
  intro a b hab
  have hlead : φ a.leadingCoeff * φ b.leadingCoeff ≠ 0 := by
    simpa only [hab, leadingCoeff_mul, map_mul] using hl
  have hm : f.map φ = a.map φ * b.map φ := by rw [hab, Polynomial.map_mul]
  rcases hi.isUnit_or_isUnit hm with ha | hb
  · exact Or.inl (primitive_unit_of_specialized_unit φ a
      (isPrimitive_of_dvd hp ⟨b, hab⟩) (left_ne_zero_of_mul hlead) ha)
  · exact Or.inr (primitive_unit_of_specialized_unit φ b
      (isPrimitive_of_dvd hp ⟨a, hab.trans (mul_comm a b)⟩)
      (right_ne_zero_of_mul hlead) hb)

theorem primitive_of_coprime_coefficients {R : Type*} [CommRing R]
    (f : R[X]) (m n : Nat) (h : IsCoprime (f.coeff m) (f.coeff n)) :
    f.IsPrimitive := by
  intro r hr
  have hd := (C_dvd_iff_dvd_coeff r f).mp hr
  exact h.isUnit_of_dvd' (hd m) (hd n)

#print axioms primitive_of_coprime_coefficients
#print axioms primitive_unit_of_specialized_unit
#print axioms primitive_irreducible_of_specialization
end StackSorting.DegreeTwelve
