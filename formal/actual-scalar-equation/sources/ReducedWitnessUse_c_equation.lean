import ReducedWitnessReversal_c_equation
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.FiniteGraph

theorem reduced_c_equation (z : ReducedChart FPS) (x : FPS) :
    reducedResidual z x 2 = -3*z.q*z.u*z.ti*(cDen z.a z.t z.u z.i z.q x*z.c-cNum z.a z.t z.u z.i z.q x) := by
  have h := reversalCertificate_c_equation (reversalVars z x 0)
  change 1*(reducedResidual z x 2+3*z.q*z.u*z.ti*(cDen (z.a) (z.t) (z.u) (z.i) (z.q) (x)*z.c-cNum (z.a) (z.t) (z.u) (z.i) (z.q) (x))) = (2*z.half-1)*exprEval (reversalVars z x 0) revWitness_c_equation_0 + (z.u*z.ui-1)*exprEval (reversalVars z x 0) revWitness_c_equation_1 + (z.t*z.ti-1)*exprEval (reversalVars z x 0) revWitness_c_equation_2 + (z.q*z.qi-1)*exprEval (reversalVars z x 0) revWitness_c_equation_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

#print axioms reduced_c_equation
end StackSorting.RationalLift
