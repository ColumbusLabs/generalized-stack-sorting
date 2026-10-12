import LiftedCoordinates
import ReducedMatrices
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.FPSDivision StackSorting.FiniteGraph
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- All entries come from the five explicitly regular rational maps. -/
def reducedLift : ReducedChart FPS where
  a := lifted_a
  t := lifted_t
  u := lifted_u
  i := lifted_i
  q := lifted_q
  c := lifted_c
  qi := inv lifted_q
  ti := inv lifted_t
  ui := inv lifted_u
  half := C (1/2)
  q_unit := lifted_q_unit
  t_unit := lifted_t_unit
  u_unit := lifted_u_unit
  half_unit := by
    change C (2 : Rat)*C (1/2 : Rat)=C 1
    rw [← C_mul]
    congr 1
    decide +kernel

def lifted_D : FPS := reduced_den reducedLift 0 0

def lifted_direction : Vec FPS 6 := fun j => reduced_direction reducedLift j 0

theorem lifted_D_constant : lifted_D 0=(1/729 : Rat) := by
  change (((((-8) * lifted_u * (lifted_q^2)) + (16 * (lifted_q^2) * (lifted_u^2)) + ((-48) * lifted_a * lifted_t * (lifted_q^2) * (lifted_u^2)) + (24 * lifted_a * lifted_t * lifted_u * (lifted_q^2)))) : FPS) 0=(1/729 : Rat)
  simp only [add_constant, mul_constant,
    neg_constant, pow_constant,
    lifted_a_constant, lifted_t_constant, lifted_u_constant, lifted_q_constant]
  decide +kernel

theorem lifted_D_unit : lifted_D*inv lifted_D=1 := by
  apply mul_inv
  rw [lifted_D_constant]
  decide +kernel

theorem lifted_direction_zero : lifted_direction 0=lifted_D := rfl

def lifted_v : Vec FPS 6 := fun j => inv lifted_D * lifted_direction j

theorem lifted_v_zero : lifted_v 0=1 := by
  change inv lifted_D*lifted_direction 0=1
  rw [lifted_direction_zero]
  have hd := lifted_D_unit
  grind

def lifted_norm : FPS := 1-X*lifted_v 2

theorem lifted_norm_constant : lifted_norm 0=1 := by
  simp only [lifted_norm, sub_constant, mul_constant, X_constant]
  change (1 : Rat)-0*(lifted_v 2) 0=1
  grind

theorem lifted_norm_unit : lifted_norm*inv lifted_norm=1 := by
  exact mul_inv lifted_norm (by rw [lifted_norm_constant]; decide +kernel)

def lifted_beta : Vec FPS 6 := fun j => 2*inv lifted_norm*lifted_v j

theorem lifted_beta_zero : lifted_beta 0=2*inv lifted_norm := by
  unfold lifted_beta
  rw [lifted_v_zero]
  grind

#print axioms reducedLift
#print axioms lifted_D_unit
#print axioms lifted_norm_unit
end StackSorting.RationalLift
