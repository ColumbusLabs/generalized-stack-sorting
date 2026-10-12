import ReducedWitnessReversal_comb3
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.FiniteGraph

theorem reduced_comb3 (z : ReducedChart FPS) (x y : FPS) :
    reducedResidual z x 4-(z.i*(z.i-z.a)-z.qi)*reducedResidual z x 0-z.i*(reducedResidual z x 1-(z.i-z.a)*reducedResidual z x 0) = -4*z.q*z.u*z.ti*(changedP3 z.a z.t z.u z.i z.q x y) := by
  have h := reversalCertificate_comb3 (reversalVars z x y)
  change 1*(reducedResidual z x 4-(z.i*(z.i-z.a)-z.qi)*reducedResidual z x 0-z.i*(reducedResidual z x 1-(z.i-z.a)*reducedResidual z x 0)+4*z.q*z.u*z.ti*(changedP3 (z.a) (z.t) (z.u) (z.i) (z.q) (x) (y))) = (2*z.half-1)*exprEval (reversalVars z x y) revWitness_comb3_0 + (z.u*z.ui-1)*exprEval (reversalVars z x y) revWitness_comb3_1 + (z.t*z.ti-1)*exprEval (reversalVars z x y) revWitness_comb3_2 + (z.q*z.qi-1)*exprEval (reversalVars z x y) revWitness_comb3_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

#print axioms reduced_comb3
end StackSorting.RationalLift
