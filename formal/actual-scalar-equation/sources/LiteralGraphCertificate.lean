import LiteralResidualDefinitions
import GraphTransition_z0
import GraphTransition_z1
import GraphTransition_z2
import GraphTransition_z3
import GraphTransition_z4
import GraphTransition_z5
import GraphTransition_b0
import GraphTransition_b1
import GraphTransition_b2
import GraphTransition_b3
import GraphTransition_b4
import GraphTransition_b5
import GraphTransition_t0
import GraphTransition_t1
import GraphTransition_t2
import GraphTransition_t3
import GraphTransition_t4
import GraphTransition_t5
import GraphInitial_Bz
import GraphInitial_Bb
import GraphInitial_Bt
import GraphInitial_Zz
import GraphInitial_Zb
import GraphInitial_Zt
import GraphTerminalK
import FormalResolvent
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem graph_transition_z (y : Chart R) (scale : R) :
    mm (litZ y) (litH y (betaDirection y scale)) =
      fun i j => mm (litH y (betaDirection y scale)) (litN9z y (betaDirection y scale)) i j -
        litCSz y (betaDirection y scale) i j := by
  funext i j
  exact (Fin.cases ((Fin.cases (trans_z_0_0 y scale) (fun j => (Fin.cases (trans_z_0_1 y scale) (fun j => (Fin.cases (trans_z_0_2 y scale) (fun j => (Fin.cases (trans_z_0_3 y scale) (fun j => (Fin.cases (trans_z_0_4 y scale) (fun j => (Fin.cases (trans_z_0_5 y scale) (fun j => (Fin.cases (trans_z_0_6 y scale) (fun j => (Fin.cases (trans_z_0_7 y scale) (fun j => (Fin.cases (trans_z_0_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)) (fun i => (Fin.cases ((Fin.cases (trans_z_1_0 y scale) (fun j => (Fin.cases (trans_z_1_1 y scale) (fun j => (Fin.cases (trans_z_1_2 y scale) (fun j => (Fin.cases (trans_z_1_3 y scale) (fun j => (Fin.cases (trans_z_1_4 y scale) (fun j => (Fin.cases (trans_z_1_5 y scale) (fun j => (Fin.cases (trans_z_1_6 y scale) (fun j => (Fin.cases (trans_z_1_7 y scale) (fun j => (Fin.cases (trans_z_1_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)) (fun i => (Fin.cases ((Fin.cases (trans_z_2_0 y scale) (fun j => (Fin.cases (trans_z_2_1 y scale) (fun j => (Fin.cases (trans_z_2_2 y scale) (fun j => (Fin.cases (trans_z_2_3 y scale) (fun j => (Fin.cases (trans_z_2_4 y scale) (fun j => (Fin.cases (trans_z_2_5 y scale) (fun j => (Fin.cases (trans_z_2_6 y scale) (fun j => (Fin.cases (trans_z_2_7 y scale) (fun j => (Fin.cases (trans_z_2_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)) (fun i => (Fin.cases ((Fin.cases (trans_z_3_0 y scale) (fun j => (Fin.cases (trans_z_3_1 y scale) (fun j => (Fin.cases (trans_z_3_2 y scale) (fun j => (Fin.cases (trans_z_3_3 y scale) (fun j => (Fin.cases (trans_z_3_4 y scale) (fun j => (Fin.cases (trans_z_3_5 y scale) (fun j => (Fin.cases (trans_z_3_6 y scale) (fun j => (Fin.cases (trans_z_3_7 y scale) (fun j => (Fin.cases (trans_z_3_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)) (fun i => (Fin.cases ((Fin.cases (trans_z_4_0 y scale) (fun j => (Fin.cases (trans_z_4_1 y scale) (fun j => (Fin.cases (trans_z_4_2 y scale) (fun j => (Fin.cases (trans_z_4_3 y scale) (fun j => (Fin.cases (trans_z_4_4 y scale) (fun j => (Fin.cases (trans_z_4_5 y scale) (fun j => (Fin.cases (trans_z_4_6 y scale) (fun j => (Fin.cases (trans_z_4_7 y scale) (fun j => (Fin.cases (trans_z_4_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)) (fun i => (Fin.cases ((Fin.cases (trans_z_5_0 y scale) (fun j => (Fin.cases (trans_z_5_1 y scale) (fun j => (Fin.cases (trans_z_5_2 y scale) (fun j => (Fin.cases (trans_z_5_3 y scale) (fun j => (Fin.cases (trans_z_5_4 y scale) (fun j => (Fin.cases (trans_z_5_5 y scale) (fun j => (Fin.cases (trans_z_5_6 y scale) (fun j => (Fin.cases (trans_z_5_7 y scale) (fun j => (Fin.cases (trans_z_5_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)) (fun i => (Fin.elim0 i)) i)) i)) i)) i)) i)) i)

theorem graph_transition_b (y : Chart R) (scale : R) :
    mm (litB y) (litH y (betaDirection y scale)) =
      fun i j => mm (litH y (betaDirection y scale)) (litN9b y (betaDirection y scale)) i j -
        litCSb y (betaDirection y scale) i j := by
  funext i j
  exact (Fin.cases ((Fin.cases (trans_b_0_0 y scale) (fun j => (Fin.cases (trans_b_0_1 y scale) (fun j => (Fin.cases (trans_b_0_2 y scale) (fun j => (Fin.cases (trans_b_0_3 y scale) (fun j => (Fin.cases (trans_b_0_4 y scale) (fun j => (Fin.cases (trans_b_0_5 y scale) (fun j => (Fin.cases (trans_b_0_6 y scale) (fun j => (Fin.cases (trans_b_0_7 y scale) (fun j => (Fin.cases (trans_b_0_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)) (fun i => (Fin.cases ((Fin.cases (trans_b_1_0 y scale) (fun j => (Fin.cases (trans_b_1_1 y scale) (fun j => (Fin.cases (trans_b_1_2 y scale) (fun j => (Fin.cases (trans_b_1_3 y scale) (fun j => (Fin.cases (trans_b_1_4 y scale) (fun j => (Fin.cases (trans_b_1_5 y scale) (fun j => (Fin.cases (trans_b_1_6 y scale) (fun j => (Fin.cases (trans_b_1_7 y scale) (fun j => (Fin.cases (trans_b_1_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)) (fun i => (Fin.cases ((Fin.cases (trans_b_2_0 y scale) (fun j => (Fin.cases (trans_b_2_1 y scale) (fun j => (Fin.cases (trans_b_2_2 y scale) (fun j => (Fin.cases (trans_b_2_3 y scale) (fun j => (Fin.cases (trans_b_2_4 y scale) (fun j => (Fin.cases (trans_b_2_5 y scale) (fun j => (Fin.cases (trans_b_2_6 y scale) (fun j => (Fin.cases (trans_b_2_7 y scale) (fun j => (Fin.cases (trans_b_2_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)) (fun i => (Fin.cases ((Fin.cases (trans_b_3_0 y scale) (fun j => (Fin.cases (trans_b_3_1 y scale) (fun j => (Fin.cases (trans_b_3_2 y scale) (fun j => (Fin.cases (trans_b_3_3 y scale) (fun j => (Fin.cases (trans_b_3_4 y scale) (fun j => (Fin.cases (trans_b_3_5 y scale) (fun j => (Fin.cases (trans_b_3_6 y scale) (fun j => (Fin.cases (trans_b_3_7 y scale) (fun j => (Fin.cases (trans_b_3_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)) (fun i => (Fin.cases ((Fin.cases (trans_b_4_0 y scale) (fun j => (Fin.cases (trans_b_4_1 y scale) (fun j => (Fin.cases (trans_b_4_2 y scale) (fun j => (Fin.cases (trans_b_4_3 y scale) (fun j => (Fin.cases (trans_b_4_4 y scale) (fun j => (Fin.cases (trans_b_4_5 y scale) (fun j => (Fin.cases (trans_b_4_6 y scale) (fun j => (Fin.cases (trans_b_4_7 y scale) (fun j => (Fin.cases (trans_b_4_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)) (fun i => (Fin.cases ((Fin.cases (trans_b_5_0 y scale) (fun j => (Fin.cases (trans_b_5_1 y scale) (fun j => (Fin.cases (trans_b_5_2 y scale) (fun j => (Fin.cases (trans_b_5_3 y scale) (fun j => (Fin.cases (trans_b_5_4 y scale) (fun j => (Fin.cases (trans_b_5_5 y scale) (fun j => (Fin.cases (trans_b_5_6 y scale) (fun j => (Fin.cases (trans_b_5_7 y scale) (fun j => (Fin.cases (trans_b_5_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)) (fun i => (Fin.elim0 i)) i)) i)) i)) i)) i)) i)

theorem graph_transition_t (y : Chart R) (scale : R) :
    mm (litT y) (litH y (betaDirection y scale)) =
      fun i j => mm (litH y (betaDirection y scale)) (litN9t y (betaDirection y scale)) i j -
        litCSt y (betaDirection y scale) i j := by
  funext i j
  exact (Fin.cases ((Fin.cases (trans_t_0_0 y scale) (fun j => (Fin.cases (trans_t_0_1 y scale) (fun j => (Fin.cases (trans_t_0_2 y scale) (fun j => (Fin.cases (trans_t_0_3 y scale) (fun j => (Fin.cases (trans_t_0_4 y scale) (fun j => (Fin.cases (trans_t_0_5 y scale) (fun j => (Fin.cases (trans_t_0_6 y scale) (fun j => (Fin.cases (trans_t_0_7 y scale) (fun j => (Fin.cases (trans_t_0_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)) (fun i => (Fin.cases ((Fin.cases (trans_t_1_0 y scale) (fun j => (Fin.cases (trans_t_1_1 y scale) (fun j => (Fin.cases (trans_t_1_2 y scale) (fun j => (Fin.cases (trans_t_1_3 y scale) (fun j => (Fin.cases (trans_t_1_4 y scale) (fun j => (Fin.cases (trans_t_1_5 y scale) (fun j => (Fin.cases (trans_t_1_6 y scale) (fun j => (Fin.cases (trans_t_1_7 y scale) (fun j => (Fin.cases (trans_t_1_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)) (fun i => (Fin.cases ((Fin.cases (trans_t_2_0 y scale) (fun j => (Fin.cases (trans_t_2_1 y scale) (fun j => (Fin.cases (trans_t_2_2 y scale) (fun j => (Fin.cases (trans_t_2_3 y scale) (fun j => (Fin.cases (trans_t_2_4 y scale) (fun j => (Fin.cases (trans_t_2_5 y scale) (fun j => (Fin.cases (trans_t_2_6 y scale) (fun j => (Fin.cases (trans_t_2_7 y scale) (fun j => (Fin.cases (trans_t_2_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)) (fun i => (Fin.cases ((Fin.cases (trans_t_3_0 y scale) (fun j => (Fin.cases (trans_t_3_1 y scale) (fun j => (Fin.cases (trans_t_3_2 y scale) (fun j => (Fin.cases (trans_t_3_3 y scale) (fun j => (Fin.cases (trans_t_3_4 y scale) (fun j => (Fin.cases (trans_t_3_5 y scale) (fun j => (Fin.cases (trans_t_3_6 y scale) (fun j => (Fin.cases (trans_t_3_7 y scale) (fun j => (Fin.cases (trans_t_3_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)) (fun i => (Fin.cases ((Fin.cases (trans_t_4_0 y scale) (fun j => (Fin.cases (trans_t_4_1 y scale) (fun j => (Fin.cases (trans_t_4_2 y scale) (fun j => (Fin.cases (trans_t_4_3 y scale) (fun j => (Fin.cases (trans_t_4_4 y scale) (fun j => (Fin.cases (trans_t_4_5 y scale) (fun j => (Fin.cases (trans_t_4_6 y scale) (fun j => (Fin.cases (trans_t_4_7 y scale) (fun j => (Fin.cases (trans_t_4_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)) (fun i => (Fin.cases ((Fin.cases (trans_t_5_0 y scale) (fun j => (Fin.cases (trans_t_5_1 y scale) (fun j => (Fin.cases (trans_t_5_2 y scale) (fun j => (Fin.cases (trans_t_5_3 y scale) (fun j => (Fin.cases (trans_t_5_4 y scale) (fun j => (Fin.cases (trans_t_5_5 y scale) (fun j => (Fin.cases (trans_t_5_6 y scale) (fun j => (Fin.cases (trans_t_5_7 y scale) (fun j => (Fin.cases (trans_t_5_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)) (fun i => (Fin.elim0 i)) i)) i)) i)) i)) i)) i)

theorem graph_transitions (y : Chart R) (scale : R) (a : Letter) :
    mm (transitions y a) (litH y (betaDirection y scale)) =
      fun i j => mm (litH y (betaDirection y scale)) (suffix9 y (betaDirection y scale) a) i j-
        deleted9 y (betaDirection y scale) a i j := by
  cases a with
  | z => exact graph_transition_z y scale
  | b => exact graph_transition_b y scale
  | t => exact graph_transition_t y scale

theorem graph_initial_Bz (y : Chart R) (scale : R) :
      vm (litZ y 0) (litH y (betaDirection y scale))=litinitialBz y (betaDirection y scale) 0 := by
  funext j
  exact (Fin.cases (initial_B_z_0 y scale) (fun j => (Fin.cases (initial_B_z_1 y scale) (fun j => (Fin.cases (initial_B_z_2 y scale) (fun j => (Fin.cases (initial_B_z_3 y scale) (fun j => (Fin.cases (initial_B_z_4 y scale) (fun j => (Fin.cases (initial_B_z_5 y scale) (fun j => (Fin.cases (initial_B_z_6 y scale) (fun j => (Fin.cases (initial_B_z_7 y scale) (fun j => (Fin.cases (initial_B_z_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)

theorem graph_initial_Bb (y : Chart R) (scale : R) :
      vm (litB y 0) (litH y (betaDirection y scale))=litinitialBb y (betaDirection y scale) 0 := by
  funext j
  exact (Fin.cases (initial_B_b_0 y scale) (fun j => (Fin.cases (initial_B_b_1 y scale) (fun j => (Fin.cases (initial_B_b_2 y scale) (fun j => (Fin.cases (initial_B_b_3 y scale) (fun j => (Fin.cases (initial_B_b_4 y scale) (fun j => (Fin.cases (initial_B_b_5 y scale) (fun j => (Fin.cases (initial_B_b_6 y scale) (fun j => (Fin.cases (initial_B_b_7 y scale) (fun j => (Fin.cases (initial_B_b_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)

theorem graph_initial_Bt (y : Chart R) (scale : R) :
      vm (litT y 0) (litH y (betaDirection y scale))=litinitialBt y 0 := by
  funext j
  exact (Fin.cases (initial_B_t_0 y scale) (fun j => (Fin.cases (initial_B_t_1 y scale) (fun j => (Fin.cases (initial_B_t_2 y scale) (fun j => (Fin.cases (initial_B_t_3 y scale) (fun j => (Fin.cases (initial_B_t_4 y scale) (fun j => (Fin.cases (initial_B_t_5 y scale) (fun j => (Fin.cases (initial_B_t_6 y scale) (fun j => (Fin.cases (initial_B_t_7 y scale) (fun j => (Fin.cases (initial_B_t_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)

theorem graph_initial_Zz (y : Chart R) (scale : R) :
      vm (vm (litalpha y 0) (litZ y)) (litH y (betaDirection y scale))=litinitialZz y (betaDirection y scale) 0 := by
  funext j
  exact (Fin.cases (initial_Z_z_0 y scale) (fun j => (Fin.cases (initial_Z_z_1 y scale) (fun j => (Fin.cases (initial_Z_z_2 y scale) (fun j => (Fin.cases (initial_Z_z_3 y scale) (fun j => (Fin.cases (initial_Z_z_4 y scale) (fun j => (Fin.cases (initial_Z_z_5 y scale) (fun j => (Fin.cases (initial_Z_z_6 y scale) (fun j => (Fin.cases (initial_Z_z_7 y scale) (fun j => (Fin.cases (initial_Z_z_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)

theorem graph_initial_Zb (y : Chart R) (scale : R) :
      vm (vm (litalpha y 0) (litB y)) (litH y (betaDirection y scale))=litinitialZb y (betaDirection y scale) 0 := by
  funext j
  exact (Fin.cases (initial_Z_b_0 y scale) (fun j => (Fin.cases (initial_Z_b_1 y scale) (fun j => (Fin.cases (initial_Z_b_2 y scale) (fun j => (Fin.cases (initial_Z_b_3 y scale) (fun j => (Fin.cases (initial_Z_b_4 y scale) (fun j => (Fin.cases (initial_Z_b_5 y scale) (fun j => (Fin.cases (initial_Z_b_6 y scale) (fun j => (Fin.cases (initial_Z_b_7 y scale) (fun j => (Fin.cases (initial_Z_b_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)

theorem graph_initial_Zt (y : Chart R) (scale : R) :
      vm (vm (litalpha y 0) (litT y)) (litH y (betaDirection y scale))=litinitialZt y (betaDirection y scale) 0 := by
  funext j
  exact (Fin.cases (initial_Z_t_0 y scale) (fun j => (Fin.cases (initial_Z_t_1 y scale) (fun j => (Fin.cases (initial_Z_t_2 y scale) (fun j => (Fin.cases (initial_Z_t_3 y scale) (fun j => (Fin.cases (initial_Z_t_4 y scale) (fun j => (Fin.cases (initial_Z_t_5 y scale) (fun j => (Fin.cases (initial_Z_t_6 y scale) (fun j => (Fin.cases (initial_Z_t_7 y scale) (fun j => (Fin.cases (initial_Z_t_8 y scale) (fun j => (Fin.elim0 j)) j)) j)) j)) j)) j)) j)) j)) j)) j)

theorem all6initialrows (y : Chart R) (scale : R) (f : Family) (a : Letter) :
    initial9 y (betaDirection y scale) f a=
      graph (litH y (betaDirection y scale)) (initialPrefix y f a) := by
  apply Prod.ext
  · rfl
  · cases f <;> cases a
    · exact (graph_initial_Bz y scale).symm
    · exact (graph_initial_Bb y scale).symm
    · exact (graph_initial_Bt y scale).symm
    · exact (graph_initial_Zz y scale).symm
    · exact (graph_initial_Zb y scale).symm
    · exact (graph_initial_Zt y scale).symm

theorem literal_terminal_K (y : Chart R) (beta : Vec R 6) :
    mv (litH y beta) (fun j => litnu9 y beta j 0)=mv (litK y) beta := by
  funext i
  exact (Fin.cases (terminal_K_0 y beta) (fun i => (Fin.cases (terminal_K_1 y beta) (fun i => (Fin.cases (terminal_K_2 y beta) (fun i => (Fin.cases (terminal_K_3 y beta) (fun i => (Fin.cases (terminal_K_4 y beta) (fun i => (Fin.cases (terminal_K_5 y beta) (fun i => (Fin.elim0 i)) i)) i)) i)) i)) i)) i)

theorem literal_terminal_annihilation (y : Chart R) (x : R) (beta : Vec R 6)
    (hscalar : SixScalarEquations y x beta) :
    ∀ i, kappa y x beta i+mv (litH y beta) (fun j => litnu9 y beta j 0) i=0 := by
  rw [literal_terminal_K]
  exact scalar_constructs_terminal x (litT y) (litK y) beta hscalar

/-- Literal all-word residual theorem. Central graph identities are proved
from the matrix literals; none is a hypothesis of this theorem. -/
theorem literal_allwordzero (y : Chart R) (x scale : R)
    (hscalar : SixScalarEquations y x (betaDirection y scale))
    (f : Family) (a : Letter) (w : List Letter) :
    terminal (kappa y x (betaDirection y scale))
      (fun j => litnu9 y (betaDirection y scale) j 0)
      (run (transitions y) (suffix9 y (betaDirection y scale))
        (deleted9 y (betaDirection y scale)) w
        (initial9 y (betaDirection y scale) f a))=0 := by
  rw [all6initialrows]
  exact allwordzero (transitions y) (suffix9 y (betaDirection y scale))
    (deleted9 y (betaDirection y scale)) (litH y (betaDirection y scale))
    (kappa y x (betaDirection y scale))
    (fun j => litnu9 y (betaDirection y scale) j 0)
    (graph_transitions y scale) (literal_terminal_annihilation y x _ hscalar) w _

/-- Specialization to actual formal coefficient sequences and their Cauchy product. -/
theorem formal_series_allwordzero (y : Chart StackSorting.CauchyRing.FPS)
    (scale : StackSorting.CauchyRing.FPS)
    (hscalar : SixScalarEquations y StackSorting.CauchyRing.X (betaDirection y scale))
    (f : Family) (a : Letter) (w : List Letter) :
    terminal (kappa y StackSorting.CauchyRing.X (betaDirection y scale))
      (fun j => litnu9 y (betaDirection y scale) j 0)
      (run (transitions y) (suffix9 y (betaDirection y scale))
        (deleted9 y (betaDirection y scale)) w
        (initial9 y (betaDirection y scale) f a))=0 :=
  literal_allwordzero y StackSorting.CauchyRing.X scale hscalar f a w

#print axioms graph_transitions
#print axioms all6initialrows
#print axioms literal_terminal_annihilation
#print axioms literal_allwordzero
#print axioms formal_series_allwordzero
end StackSorting.FiniteGraph
