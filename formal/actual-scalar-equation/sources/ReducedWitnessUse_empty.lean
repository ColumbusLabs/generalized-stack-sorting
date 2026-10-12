import ReducedWitnessReversal_empty
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.FiniteGraph

theorem reduced_empty (z : ReducedChart FPS) :
    dot (reduced_alpha z 0) (mv (reduced_K z) (fun j => reduced_direction z j 0))-
      mv (reduced_K z) (fun j => reduced_direction z j 0) 0=0 := by
  have h := reversalCertificate_empty (reversalVars z 0 0)
  change 1*(dot (reduced_alpha z 0) (mv (reduced_K z) (fun j => reduced_direction z j 0))-mv (reduced_K z) (fun j => reduced_direction z j 0) 0) = (2*z.half-1)*exprEval (reversalVars z 0 0) revWitness_empty_0 + (z.u*z.ui-1)*exprEval (reversalVars z 0 0) revWitness_empty_1 + (z.t*z.ti-1)*exprEval (reversalVars z 0 0) revWitness_empty_2 + (z.q*z.qi-1)*exprEval (reversalVars z 0 0) revWitness_empty_3 at h
  rw [z.half_unit, z.u_unit, z.t_unit, z.q_unit] at h
  grind

#print axioms reduced_empty
end StackSorting.RationalLift
