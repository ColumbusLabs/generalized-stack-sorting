import ReducedWitnessReversal_last
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.FiniteGraph

theorem reduced_last (z : ReducedChart FPS) (x y : FPS) :
    cDen z.a z.t z.u z.i z.q x*reducedResidual z x 0 = -4*z.a*z.q^2*z.u*(changedP4 z.a z.t z.u z.i z.q x y)+12*z.a*z.q^2*z.u*x*(2*z.u-1)*(cDen z.a z.t z.u z.i z.q x*z.c-cNum z.a z.t z.u z.i z.q x) := by
  have h := reversalCertificate_last (reversalVars z x y)
  change 1*(cDen (z.a) (z.t) (z.u) (z.i) (z.q) (x)*reducedResidual z x 0+4*z.a*(z.q)^2*z.u*(changedP4 (z.a) (z.t) (z.u) (z.i) (z.q) (x) (y))-12*z.a*(z.q)^2*z.u*x*(2*z.u-1)*(cDen (z.a) (z.t) (z.u) (z.i) (z.q) (x)*z.c-cNum (z.a) (z.t) (z.u) (z.i) (z.q) (x))) = (2*z.half-1)*exprEval (reversalVars z x y) revWitness_last_0 + (z.u*z.ui-1)*exprEval (reversalVars z x y) revWitness_last_1 + (z.t*z.ti-1)*exprEval (reversalVars z x y) revWitness_last_2 + (z.q*z.qi-1)*exprEval (reversalVars z x y) revWitness_last_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

#print axioms reduced_last
end StackSorting.RationalLift
