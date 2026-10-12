import ReducedWitnessReversal_comb1
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.FiniteGraph

theorem reduced_comb1 (z : ReducedChart FPS) (x y : FPS) :
    reducedResidual z x 3 = -z.q*z.u*z.ti*(changedP1 z.a z.t z.u z.i z.q x y) := by
  have h := reversalCertificate_comb1 (reversalVars z x y)
  change 1*(reducedResidual z x 3+z.q*z.u*z.ti*(changedP1 (z.a) (z.t) (z.u) (z.i) (z.q) (x) (y))) = (2*z.half-1)*exprEval (reversalVars z x y) revWitness_comb1_0 + (z.u*z.ui-1)*exprEval (reversalVars z x y) revWitness_comb1_1 + (z.t*z.ti-1)*exprEval (reversalVars z x y) revWitness_comb1_2 + (z.q*z.qi-1)*exprEval (reversalVars z x y) revWitness_comb1_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

#print axioms reduced_comb1
end StackSorting.RationalLift
