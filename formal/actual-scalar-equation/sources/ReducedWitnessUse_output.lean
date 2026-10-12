import ReducedWitnessReversal_output
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.FiniteGraph
def reducedOutputResidual (z : ReducedChart FPS) (x y : FPS) : FPS :=
  (y-1-x)*(reduced_den z 0 0-x*reduced_direction z 2 0)-2*x^2*reduced_den z 0 0


theorem reduced_output (z : ReducedChart FPS) (x y : FPS) :
    cDen z.a z.t z.u z.i z.q x*reducedOutputResidual z x y =
      4*z.a*z.q^2*z.u*(changedP5 z.a z.t z.u z.i z.q x y)+
      12*z.a*z.q^2*z.u*x*(2*z.u-1)*(y-1-x)*(cDen z.a z.t z.u z.i z.q x*z.c-cNum z.a z.t z.u z.i z.q x) := by
  have h := reversalCertificate_output (reversalVars z x y)
  change 1*(cDen (z.a) (z.t) (z.u) (z.i) (z.q) (x)*((y-1-x)*(reduced_den z 0 0-x*reduced_direction z 2 0)-2*(x)^2*reduced_den z 0 0)-4*z.a*(z.q)^2*z.u*(changedP5 (z.a) (z.t) (z.u) (z.i) (z.q) (x) (y))-12*z.a*(z.q)^2*z.u*x*(2*z.u-1)*(y-1-x)*(cDen (z.a) (z.t) (z.u) (z.i) (z.q) (x)*z.c-cNum (z.a) (z.t) (z.u) (z.i) (z.q) (x))) = (2*z.half-1)*exprEval (reversalVars z x y) revWitness_output_0 + (z.u*z.ui-1)*exprEval (reversalVars z x y) revWitness_output_1 + (z.t*z.ti-1)*exprEval (reversalVars z x y) revWitness_output_2 + (z.q*z.qi-1)*exprEval (reversalVars z x y) revWitness_output_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  unfold reducedOutputResidual
  grind

#print axioms reduced_output
end StackSorting.RationalLift
