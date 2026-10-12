import ReducedWitnessReversal_comb2
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.FiniteGraph

theorem reduced_comb2 (z : ReducedChart FPS) (x y : FPS) :
    reducedResidual z x 5-z.i*reducedResidual z x 3 = -z.q*z.u*z.ti*(changedP2 z.a z.t z.u z.i z.q x y) := by
  have h := reversalCertificate_comb2 (reversalVars z x y)
  change 1*(reducedResidual z x 5-z.i*reducedResidual z x 3+z.q*z.u*z.ti*(changedP2 (z.a) (z.t) (z.u) (z.i) (z.q) (x) (y))) = (2*z.half-1)*exprEval (reversalVars z x y) revWitness_comb2_0 + (z.u*z.ui-1)*exprEval (reversalVars z x y) revWitness_comb2_1 + (z.t*z.ti-1)*exprEval (reversalVars z x y) revWitness_comb2_2 + (z.q*z.qi-1)*exprEval (reversalVars z x y) revWitness_comb2_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

#print axioms reduced_comb2
end StackSorting.RationalLift
