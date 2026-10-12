import ReducedChartAdapter
noncomputable section
namespace StackSorting.RationalLift
open StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
variable {R : Type} [Lean.Grind.CommRing R]
def reducedVars (z : ReducedChart R) : Nat → R
  | 0 => z.a
  | 1 => z.t
  | 2 => z.u
  | 3 => z.i
  | 4 => z.q
  | 5 => z.c
  | 6 => z.qi
  | 7 => z.ti
  | 8 => z.ui
  | 9 => z.half
  | _ => 0

def reducedOriginalVars (env : Nat → R) : Nat → R
  | 0 => env 2*env 6*env 7
  | 1 => env 3
  | 2 => -(env 3*env 4)
  | 3 => env 4
  | 4 => env 1*env 6
  | 5 => env 5
  | 6 => env 3-env 0
  | 7 => env 4*env 1*env 8
  | 8 => env 6
  | 9 => env 4*env 7
  | 10 => env 9
  | _ => 0
theorem half_cancel_two (half v : R) (hh : 2*half=1) (hv : 2*v=0) : v=0 := by
  calc
    v = (2*half)*v := by rw [hh]; grind
    _ = half*(2*v) := by grind
    _ = 0 := by rw [hv]; grind

theorem half_cancel_four (half v : R) (hh : 2*half=1) (hv : 4*v=0) : v=0 := by
  apply half_cancel_two half v hh
  apply half_cancel_two half (2*v) hh
  calc
    2*(2*v) = 4*v := by grind
    _ = 0 := hv
end StackSorting.RationalLift
