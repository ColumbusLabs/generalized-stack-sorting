import ScalarLiftTerminal
import ReducedWitnessBind_T
import ReducedWitnessBind_K
import ReducedWitnessBind_direction
import ReducedWitnessBind_den
import ReducedWitnessBind_alpha
import ChartScalars
noncomputable section
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.FPSDivision StackSorting.FiniteGraph
open StackSorting.ConcreteScalar
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def liftedChart : Chart FPS := originalChart reducedLift

/-- Every inverse witness carried by the original chart is explicit and is
proved from the genuinely reconstructed regular scalar maps. -/
theorem literal_G_chart_units :
    liftedChart.g*liftedChart.gi=1 ∧ liftedChart.q*liftedChart.qi=1 ∧
    liftedChart.s*liftedChart.si=1 ∧ 2*liftedChart.half=1 := by
  exact ⟨liftedChart.g_unit, liftedChart.q_unit, liftedChart.s_unit,
    liftedChart.half_unit⟩

theorem literal_G_chart_inverse_data :
    liftedChart.gi=lifted_q*lifted_t*inv lifted_u ∧
    liftedChart.qi=inv lifted_q ∧
    liftedChart.si=lifted_q*inv lifted_t ∧ liftedChart.half=C (1/2) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The concrete original chart has the independently derived constant data. -/
theorem literal_G_chart_constants :
    liftedChart.g 0=12 ∧ liftedChart.i 0=8 ∧
    liftedChart.p 0=(-4/9 : Rat) ∧ liftedChart.q 0=(1/18 : Rat) ∧
    liftedChart.s 0=(9/2 : Rat) ∧ liftedChart.c 0=2 ∧ liftedChart.o 0=6 := by
  have hg : liftedChart.g 0=12 := by
    change (lifted_u*inv lifted_q*inv lifted_t) 0=12
    simp only [mul_constant, inv_constant, lifted_u_constant,
      lifted_q_constant, lifted_t_constant]
    decide +kernel
  exact ⟨hg, lifted_i_constant, lifted_p_constant, lifted_q_constant,
    lifted_s_constant, lifted_c_constant, lifted_o_constant⟩

theorem liftedChart_den : litden liftedChart 0 0=lifted_D := by
  exact congrFun (congrFun (original_den reducedLift) 0) 0

theorem liftedChart_direction : (fun j => litdirection liftedChart j 0)=lifted_direction := by
  funext j
  exact congrFun (congrFun (original_direction reducedLift) j) 0

theorem liftedChart_v : normalizedDirection liftedChart (inv lifted_D)=lifted_v := by
  funext j
  change inv lifted_D*litdirection liftedChart j 0=inv lifted_D*lifted_direction j
  rw [congrFun liftedChart_direction j]

theorem liftedChart_raw_six : SixScalarEquations liftedChart X lifted_direction := by
  intro j
  change lifted_direction j+mv (litK (originalChart reducedLift)) lifted_direction j-
    X*mv (litT (originalChart reducedLift))
      (fun k => lifted_direction k+mv (litK (originalChart reducedLift)) lifted_direction k) j-
    X*lifted_direction j=0
  rw [original_K, original_T]
  exact lifted_all_six j

theorem liftedChart_empty :
    dot (litalpha liftedChart 0) (mv (litK liftedChart) lifted_v)-
      mv (litK liftedChart) lifted_v 0=0 := by
  change dot (litalpha (originalChart reducedLift) 0)
    (mv (litK (originalChart reducedLift)) (fun j => inv lifted_D*lifted_direction j))-
    mv (litK (originalChart reducedLift)) (fun j => inv lifted_D*lifted_direction j) 0=0
  rw [original_alpha, original_K, mv_scale]
  unfold dot
  have hf : (fun j : Fin 6 => reduced_alpha reducedLift 0 j*
      (inv lifted_D*mv (reduced_K reducedLift) lifted_direction j)) =
      (fun j => inv lifted_D*(reduced_alpha reducedLift 0 j*
        mv (reduced_K reducedLift) lifted_direction j)) := by
    funext j
    grind
  rw [hf, mul_sumFin]
  have he := lifted_empty
  unfold dot at he
  grind

/-- The complete seven-equation normalized graph certificate is obtained
from the literal scalar G and its actual regular rational maps. -/
theorem literal_G_seven_equations :
    SevenScalarEquations liftedChart X (normalizedDirection liftedChart (inv lifted_D)) := by
  rw [liftedChart_v]
  constructor
  · exact scalar_equations_scale liftedChart X (inv lifted_D)
      lifted_direction liftedChart_raw_six
  · exact liftedChart_empty

theorem literal_G_graph_den_unit : litden liftedChart 0 0*inv lifted_D=1 := by
  rw [liftedChart_den]
  exact lifted_D_unit

theorem literal_G_graph_norm_unit :
    (1-X*normalizedDirection liftedChart (inv lifted_D) 2)*inv lifted_norm=1 := by
  rw [liftedChart_v]
  exact lifted_norm_unit

theorem literal_G_graph_beta :
    betaDirection liftedChart (normalizedScale (inv lifted_D) (inv lifted_norm))=lifted_beta := by
  funext j
  change (2*inv lifted_norm*inv lifted_D)*litdirection liftedChart j 0=
    2*inv lifted_norm*(inv lifted_D*lifted_direction j)
  rw [congrFun liftedChart_direction j]
  grind

theorem literal_G_graph_output :
    G=1+X+X^2*betaDirection liftedChart
      (normalizedScale (inv lifted_D) (inv lifted_norm)) 0 := by
  rw [literal_G_graph_beta]
  exact lifted_output_beta

theorem literal_G_beta_boundary : lifted_beta 0-X*lifted_beta 2=2 := by
  have h := normalized_beta_relation liftedChart X (inv lifted_D) (inv lifted_norm)
    literal_G_graph_den_unit literal_G_graph_norm_unit
  rw [literal_G_graph_beta] at h
  exact h

theorem literal_G_beta_seven : SevenScalarEquations liftedChart X lifted_beta := by
  have hs := literal_G_seven_equations
  rw [liftedChart_v] at hs
  exact seven_equations_scale liftedChart X (2*inv lifted_norm) lifted_v hs

def lifted_record : Vec FPS 6 :=
  recordFromScalar (litT liftedChart) (litK liftedChart) lifted_beta

/-- The actual resolvent record is explicitly constructed from the proved
scalar equations; no formal-resolvent existence hypothesis is supplied. -/
theorem literal_G_constructed_record :
    (∀ i, X*lifted_record i=lifted_beta i+mv (litK liftedChart) lifted_beta i) ∧
    (∀ i, lifted_record i=lifted_beta i+X*mv (litT liftedChart) lifted_record i) := by
  exact scalar_constructs_record X (litT liftedChart) (litK liftedChart)
    lifted_beta literal_G_beta_seven.1

theorem literal_G_constructed_terminal (i : Fin 6) :
    lifted_beta i-X*lifted_record i+mv (litK liftedChart) lifted_beta i=0 := by
  exact scalar_constructs_terminal X (litT liftedChart) (litK liftedChart)
    lifted_beta literal_G_beta_seven.1 i

#print axioms literal_G_chart_units
#print axioms literal_G_chart_constants
#print axioms literal_G_seven_equations
#print axioms literal_G_constructed_record
#print axioms literal_G_graph_output
end StackSorting.RationalLift
