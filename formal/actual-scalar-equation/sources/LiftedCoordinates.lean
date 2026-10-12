import FPSConstant
import CoordinatePolynomials
import RationalRegularity_a
import RationalRegularity_t
import RationalRegularity_u
import RationalRegularity_i
import RationalRegularity_q
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.FPSDivision
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def lifted_g : FPS := lifted_u * inv (lifted_q*lifted_t)
def lifted_s : FPS := lifted_t * inv lifted_q
def lifted_o : FPS := lifted_i-lifted_a
def lifted_p : FPS := -(lifted_i*lifted_q)
def lifted_cDen : FPS := cDen lifted_a lifted_t lifted_u lifted_i lifted_q X
def lifted_cNum : FPS := cNum lifted_a lifted_t lifted_u lifted_i lifted_q X
def lifted_c : FPS := lifted_cNum * inv lifted_cDen

theorem lifted_g_constant : lifted_g 0=12 := by
  simp only [lifted_g, mul_constant, inv_constant, lifted_u_constant, lifted_q_constant, lifted_t_constant]
  decide +kernel

theorem lifted_s_constant : lifted_s 0=(9/2 : Rat) := by
  simp only [lifted_s, mul_constant, inv_constant, lifted_t_constant, lifted_q_constant]
  decide +kernel

theorem lifted_o_constant : lifted_o 0=6 := by
  simp only [lifted_o, sub_constant, lifted_i_constant, lifted_a_constant]
  decide +kernel

theorem lifted_p_constant : lifted_p 0=(-4/9 : Rat) := by
  simp only [lifted_p, neg_constant, mul_constant, lifted_i_constant, lifted_q_constant]
  decide +kernel

theorem lifted_cDen_constant : lifted_cDen 0=(-2/27 : Rat) := by
  simp only [lifted_cDen, cDen, cDenExpr, IExpr.eval, polyArgs, add_constant, mul_constant, X_constant, lifted_a_constant, lifted_t_constant, lifted_u_constant, lifted_i_constant, lifted_q_constant]
  decide +kernel

theorem lifted_cNum_constant : lifted_cNum 0=(-4/27 : Rat) := by
  simp only [lifted_cNum, cNum, cNumExpr, IExpr.eval, polyArgs, add_constant, mul_constant, pow_constant, X_constant, lifted_a_constant, lifted_t_constant, lifted_u_constant, lifted_i_constant, lifted_q_constant]
  decide +kernel

theorem lifted_c_constant : lifted_c 0=2 := by
  simp only [lifted_c, lifted_cNum_constant, lifted_cDen_constant, mul_constant, inv_constant]
  decide +kernel

theorem lifted_c_cross : lifted_cDen*lifted_c=lifted_cNum := by
  have hu : lifted_cDen 0≠0 := by rw [lifted_cDen_constant]; decide +kernel
  have hi := mul_inv lifted_cDen hu
  unfold lifted_c
  grind

theorem lifted_q_unit : lifted_q*inv lifted_q=1 := by
  apply mul_inv
  rw [lifted_q_constant]
  decide +kernel

theorem lifted_t_unit : lifted_t*inv lifted_t=1 := by
  apply mul_inv
  rw [lifted_t_constant]
  decide +kernel

theorem lifted_u_unit : lifted_u*inv lifted_u=1 := by
  apply mul_inv
  rw [lifted_u_constant]
  decide +kernel

theorem lifted_g_unit : lifted_g*inv lifted_g=1 := by
  apply mul_inv
  rw [lifted_g_constant]
  decide +kernel

theorem lifted_s_unit : lifted_s*inv lifted_s=1 := by
  apply mul_inv
  rw [lifted_s_constant]
  decide +kernel

theorem lifted_g_cross : lifted_g*(lifted_q*lifted_t)=lifted_u := by
  have hu : (lifted_q*lifted_t) 0≠0 := by
    rw [mul_constant, lifted_q_constant, lifted_t_constant]
    decide +kernel
  have hi := mul_inv (lifted_q*lifted_t) hu
  unfold lifted_g
  grind

theorem lifted_s_cross : lifted_s*lifted_q=lifted_t := by
  have hi := lifted_q_unit
  unfold lifted_s
  grind

#print axioms lifted_c_cross
#print axioms lifted_g_cross
end StackSorting.RationalLift
