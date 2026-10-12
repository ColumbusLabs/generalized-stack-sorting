import ReducedActualChart
import RationalConstraint0
import RationalConstraint1
import RationalConstraint2
import RationalConstraint3
import RationalConstraint4
import RationalConstraint5
import ReducedWitnessUse_comb0
import ReducedWitnessUse_comb1
import ReducedWitnessUse_comb2
import ReducedWitnessUse_comb3
import ReducedWitnessUse_c_equation
import ReducedWitnessUse_last
import ReducedWitnessUse_empty
import ReducedWitnessUse_output
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.FPSDivision StackSorting.FiniteGraph
open StackSorting.ConcreteScalar
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem lifted_cDen_cancellable : Cancellable lifted_cDen := by
  intro b c h
  exact mul_cancel_left lifted_cDen
    (by rw [lifted_cDen_constant]; decide +kernel) h

theorem lifted_raw0 : reducedResidual reducedLift X 0=0 := by
  have h := reduced_last reducedLift X G
  change lifted_cDen*reducedResidual reducedLift X 0 =
    -4*lifted_a*lifted_q^2*lifted_u*
      (changedP4 lifted_a lifted_t lifted_u lifted_i lifted_q X G)+
      12*lifted_a*lifted_q^2*lifted_u*X*(2*lifted_u-1)*
      (lifted_cDen*lifted_c-lifted_cNum) at h
  rw [map_constraint4, lifted_c_cross] at h
  apply cancellable_zero lifted_cDen_cancellable
  grind

theorem lifted_raw1 : reducedResidual reducedLift X 1=0 := by
  have h := reduced_comb0 reducedLift X G
  change reducedResidual reducedLift X 1-(lifted_i-lifted_a)*reducedResidual reducedLift X 0 =
    -2*lifted_q*lifted_u*(inv lifted_t)*
      (changedP0 lifted_a lifted_t lifted_u lifted_i lifted_q X G) at h
  rw [map_constraint0, lifted_raw0] at h
  grind

theorem lifted_raw2 : reducedResidual reducedLift X 2=0 := by
  have h := reduced_c_equation reducedLift X
  change reducedResidual reducedLift X 2 = -3*lifted_q*lifted_u*(inv lifted_t)*
    (lifted_cDen*lifted_c-lifted_cNum) at h
  rw [lifted_c_cross] at h
  grind

theorem lifted_raw3 : reducedResidual reducedLift X 3=0 := by
  have h := reduced_comb1 reducedLift X G
  change reducedResidual reducedLift X 3 = -lifted_q*lifted_u*(inv lifted_t)*
    (changedP1 lifted_a lifted_t lifted_u lifted_i lifted_q X G) at h
  rw [map_constraint1] at h
  grind

theorem lifted_raw4 : reducedResidual reducedLift X 4=0 := by
  have h := reduced_comb3 reducedLift X G
  change reducedResidual reducedLift X 4-
    (lifted_i*(lifted_i-lifted_a)-inv lifted_q)*reducedResidual reducedLift X 0-
    lifted_i*(reducedResidual reducedLift X 1-
      (lifted_i-lifted_a)*reducedResidual reducedLift X 0) =
    -4*lifted_q*lifted_u*(inv lifted_t)*
      (changedP3 lifted_a lifted_t lifted_u lifted_i lifted_q X G) at h
  rw [map_constraint3, lifted_raw0, lifted_raw1] at h
  grind

theorem lifted_raw5 : reducedResidual reducedLift X 5=0 := by
  have h := reduced_comb2 reducedLift X G
  change reducedResidual reducedLift X 5-lifted_i*reducedResidual reducedLift X 3 =
    -lifted_q*lifted_u*(inv lifted_t)*
      (changedP2 lifted_a lifted_t lifted_u lifted_i lifted_q X G) at h
  rw [map_constraint2, lifted_raw3] at h
  grind

/-- All six terminal equations are proved, rather than supplied as lift
hypotheses. Every denominator used above was explicitly certified. -/
theorem lifted_all_six (j : Fin 6) : reducedResidual reducedLift X j=0 := by
  exact Fin.cases lifted_raw0 (fun j => Fin.cases lifted_raw1
    (fun j => Fin.cases lifted_raw2 (fun j => Fin.cases lifted_raw3
      (fun j => Fin.cases lifted_raw4 (fun j => Fin.cases lifted_raw5
        (fun j => Fin.elim0 j) j) j) j) j) j) j

theorem lifted_empty :
    dot (reduced_alpha reducedLift 0) (mv (reduced_K reducedLift) lifted_direction)-
      mv (reduced_K reducedLift) lifted_direction 0=0 :=
  reduced_empty reducedLift

theorem lifted_raw_output : reducedOutputResidual reducedLift X G=0 := by
  have h := reduced_output reducedLift X G
  change lifted_cDen*reducedOutputResidual reducedLift X G =
    4*lifted_a*lifted_q^2*lifted_u*
      (changedP5 lifted_a lifted_t lifted_u lifted_i lifted_q X G)+
    12*lifted_a*lifted_q^2*lifted_u*X*(2*lifted_u-1)*(G-1-X)*
      (lifted_cDen*lifted_c-lifted_cNum) at h
  rw [map_constraint5, lifted_c_cross] at h
  apply cancellable_zero lifted_cDen_cancellable
  grind

/-- The recovered normalized output is the literal scalar branch G at every
degree. No coefficient fit appears as an assumption. -/
theorem lifted_output : G = 1+X+2*X^2*inv lifted_norm := by
  have h := lifted_raw_output
  change (G-1-X)*(lifted_D-X*lifted_direction 2)-2*X^2*lifted_D=0 at h
  have hd := lifted_D_unit
  have hn := lifted_norm_unit
  have hv : lifted_D*lifted_v 2=lifted_direction 2 := by
    change lifted_D*(inv lifted_D*lifted_direction 2)=lifted_direction 2
    grind
  have hc : lifted_D*((G-1-X)*lifted_norm-2*X^2)=0 := by
    unfold lifted_norm
    grind
  have hz : (G-1-X)*lifted_norm-2*X^2=0 := by
    exact cancellable_zero (fun b c hh => mul_cancel_left lifted_D
      (by rw [lifted_D_constant]; decide +kernel) hh) hc
  grind

theorem lifted_output_beta : G=1+X+X^2*lifted_beta 0 := by
  rw [lifted_beta_zero]
  have h := lifted_output
  grind

#print axioms lifted_all_six
#print axioms lifted_empty
#print axioms lifted_output_beta
end StackSorting.RationalLift
