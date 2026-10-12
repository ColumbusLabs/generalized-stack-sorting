import ReducedMatrices
import GraphLiterals
noncomputable section
namespace StackSorting.RationalLift
open StackSorting.FiniteGraph
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
variable {R : Type} [Lean.Grind.CommRing R]

/-- The original seven parameters and every original inverse are explicit.
This adapter adds no graph identity or scalar equation as a premise. -/
def originalChart (z : ReducedChart R) : Chart R where
  g := z.u*z.qi*z.ti
  i := z.i
  p := -(z.i*z.q)
  q := z.q
  s := z.t*z.qi
  c := z.c
  o := z.i-z.a
  gi := z.q*z.t*z.ui
  qi := z.qi
  si := z.q*z.ti
  half := z.half
  g_unit := by
    have hq := z.q_unit
    have ht := z.t_unit
    have hu := z.u_unit
    grind
  q_unit := z.q_unit
  s_unit := by
    have hq := z.q_unit
    have ht := z.t_unit
    grind
  half_unit := z.half_unit

end StackSorting.RationalLift
