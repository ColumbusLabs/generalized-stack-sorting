import RingReflection
import LiteralEntryData
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]
attribute [local instance] Lean.Grind.Ring.intCast

def directionContext (y : Chart R) (scale : R) : Lean.RArray R :=
  let env : Nat → R := fun n => if n=17 then scale else chartVars y (fun _ => 0) n
  (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (env 0)) (.leaf (env 1))) (.branch 3 (.leaf (env 2)) (.leaf (env 3)))) (.branch 6 (.branch 5 (.leaf (env 4)) (.leaf (env 5))) (.branch 7 (.leaf (env 6)) (.branch 8 (.leaf (env 7)) (.leaf (env 8)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (env 9)) (.leaf (env 10))) (.branch 12 (.leaf (env 11)) (.leaf (env 12)))) (.branch 15 (.branch 14 (.leaf (env 13)) (.leaf (env 14))) (.branch 16 (.leaf (env 15)) (.branch 17 (.leaf (env 16)) (.leaf (env 17)))))))

def directionSubstitution : Nat → RingExpr
  | 0 => .var 0
  | 1 => .var 1
  | 2 => .var 2
  | 3 => .var 3
  | 4 => .var 4
  | 5 => .var 5
  | 6 => .var 6
  | 7 => .var 7
  | 8 => .var 8
  | 9 => .var 9
  | 10 => .var 10
  | 11 => .mul (.var 17) datadirection_0_0
  | 12 => .mul (.var 17) datadirection_1_0
  | 13 => .mul (.var 17) datadirection_2_0
  | 14 => .mul (.var 17) datadirection_3_0
  | 15 => .mul (.var 17) datadirection_4_0
  | 16 => .mul (.var 17) datadirection_5_0
  | _ => .int 0

theorem directionSubstitution_environment (y : Chart R) (scale : R) :
    (fun n => exprEval (fun j => (directionContext y scale).get j) (directionSubstitution n))=
      chartVars y (betaDirection y scale) := by
  funext n
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | 13 => rfl
  | 14 => rfl
  | 15 => rfl
  | 16 => rfl
  | n+17 =>
    change IntCast.intCast (R := R) 0=0
    exact Lean.Grind.Ring.intCast_zero

theorem eval_directionSubstitution (y : Chart R) (scale : R) (e : RingExpr) :
    exprEval (fun j => (directionContext y scale).get j) (substituteRing directionSubstitution e)=
      exprEval (chartVars y (betaDirection y scale)) e := by
  rw [eval_substituteRing, directionSubstitution_environment]

#print axioms eval_directionSubstitution
end StackSorting.FiniteGraph
