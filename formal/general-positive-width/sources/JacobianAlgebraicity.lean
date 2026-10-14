import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Algebraic.Integral

/-!
Algebraicity from a finite square polynomial presentation after inverting its Jacobian. This module is separate from concrete degree twelve.

The original source passed the independent final 607-module review on 2026-10-14.
This publication revision, dated 2026-10-14, changes only this header;
declarations and proofs are unchanged.
Original accepted source SHA-256: 010334d4de7a89401c0347bc0b176ac2dc633e0bbeaeff07fb28c007a4602bc9
-/
namespace StackSorting.GeneralAlgebraicity
open Algebra
noncomputable section

/-- A square presentation becomes submersive after its Jacobian is inverted. -/
def localizedSquarePresentation {K A : Type*} [CommRing K] [CommRing A]
    [Algebra K A] {ι : Type*} [Finite ι]
    (P : PreSubmersivePresentation K A ι ι)
    (S : Type*) [CommRing S] [Algebra A S] [Algebra K S] [IsScalarTower K A S]
    [IsLocalization.Away P.jacobian S] :
    SubmersivePresentation K S (Unit ⊕ ι) (Unit ⊕ ι) where
  __ := (PreSubmersivePresentation.localizationAway S P.jacobian).comp P
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.smul_def, PreSubmersivePresentation.localizationAway_jacobian]
    exact (IsLocalization.Away.algebraMap_isUnit P.jacobian).mul
      (IsLocalization.Away.algebraMap_isUnit P.jacobian)

/-- Every element of a nonsingular evaluated finite square presentation over
a field is integral. No algebraicity of the coordinates is assumed. -/
theorem squarePresentation_integral_image {K A L : Type*}
    [Field K] [CommRing A] [CommRing L] [Algebra K A] [Algebra K L]
    {ι : Type*} [Finite ι] (P : PreSubmersivePresentation K A ι ι)
    (e : A →ₐ[K] L) (hj : IsUnit (e P.jacobian)) (a : A) :
    IsIntegral K (e a) := by
  let S := Localization.Away P.jacobian
  let Q := localizedSquarePresentation P S
  let : IsStandardSmoothOfRelativeDimension 0 K S :=
    Q.isStandardSmoothOfRelativeDimension (by simp [Presentation.dimension])
  let : Module.Finite K S := Algebra.FormallyUnramified.finite_of_free K S
  let e' : S →ₐ[K] L := IsLocalization.Away.liftAlgHom P.jacobian hj
  have hi := (IsIntegral.of_finite K (algebraMap A S a)).map e'
  simpa [e'] using hi

theorem squarePresentation_algebraic_image {K A L : Type*}
    [Field K] [CommRing A] [CommRing L] [Algebra K A] [Algebra K L]
    {ι : Type*} [Finite ι] (P : PreSubmersivePresentation K A ι ι)
    (e : A →ₐ[K] L) (hj : IsUnit (e P.jacobian)) (a : A) :
    IsAlgebraic K (e a) :=
  (squarePresentation_integral_image P e hj a).isAlgebraic

#print axioms localizedSquarePresentation
#print axioms squarePresentation_integral_image
#print axioms squarePresentation_algebraic_image
end
end StackSorting.GeneralAlgebraicity
