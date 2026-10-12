import ReducedWitnessReversal_comb0
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.FiniteGraph

theorem reduced_comb0 (z : ReducedChart FPS) (x y : FPS) :
    reducedResidual z x 1-(z.i-z.a)*reducedResidual z x 0 = -2*z.q*z.u*z.ti*(changedP0 z.a z.t z.u z.i z.q x y) := by
  have h := reversalCertificate_comb0 (reversalVars z x y)
  change 1*(reducedResidual z x 1-(z.i-z.a)*reducedResidual z x 0+2*z.q*z.u*z.ti*(changedP0 (z.a) (z.t) (z.u) (z.i) (z.q) (x) (y))) = (2*z.half-1)*exprEval (reversalVars z x y) revWitness_comb0_0 + (z.u*z.ui-1)*exprEval (reversalVars z x y) revWitness_comb0_1 + (z.t*z.ti-1)*exprEval (reversalVars z x y) revWitness_comb0_2 + (z.q*z.qi-1)*exprEval (reversalVars z x y) revWitness_comb0_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

#print axioms reduced_comb0
end StackSorting.RationalLift
