import SuffixStep_z
import SuffixStep_b
import SuffixStep_t
import SuffixBaseSelection
noncomputable section
namespace StackSorting.FiniteGraph
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem literal_channel_step_z (y : Chart R) (beta : Vec R 6) (s : SuffixChannels R) :
    mv (litN19z y beta) (packChannels s)=packChannels (channelStep y beta .z s) := by
  funext i
  exact (Fin.cases ((channel_step_z_0 y beta s).symm) (fun i => (Fin.cases ((channel_step_z_1 y beta s).symm) (fun i => (Fin.cases ((channel_step_z_2 y beta s).symm) (fun i => (Fin.cases ((channel_step_z_3 y beta s).symm) (fun i => (Fin.cases ((channel_step_z_4 y beta s).symm) (fun i => (Fin.cases ((channel_step_z_5 y beta s).symm) (fun i => (Fin.cases ((channel_step_z_6 y beta s).symm) (fun i => (Fin.cases ((channel_step_z_7 y beta s).symm) (fun i => (Fin.cases ((channel_step_z_8 y beta s).symm) (fun i => (Fin.cases ((channel_step_z_9 y beta s).symm) (fun i => (Fin.cases ((channel_step_z_10 y beta s).symm) (fun i => (Fin.cases ((channel_step_z_11 y beta s).symm) (fun i => (Fin.cases ((channel_step_z_12 y beta s).symm) (fun i => (Fin.cases ((channel_step_z_13 y beta s).symm) (fun i => (Fin.cases ((channel_step_z_14 y beta s).symm) (fun i => (Fin.cases ((channel_step_z_15 y beta s).symm) (fun i => (Fin.cases ((channel_step_z_16 y beta s).symm) (fun i => (Fin.cases ((channel_step_z_17 y beta s).symm) (fun i => (Fin.cases ((channel_step_z_18 y beta s).symm) (fun i => (Fin.elim0 i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)

theorem literal_selected_z (y : Chart R) (s : SuffixChannels R) :
    mv (litCz y) (packChannels s)=s.f := by
  funext i
  exact (Fin.cases (selected_z_0 y s) (fun i => (Fin.cases (selected_z_1 y s) (fun i => (Fin.cases (selected_z_2 y s) (fun i => (Fin.cases (selected_z_3 y s) (fun i => (Fin.cases (selected_z_4 y s) (fun i => (Fin.cases (selected_z_5 y s) (fun i => (Fin.elim0 i)) i)) i)) i)) i)) i)) i)

theorem literal_channel_step_b (y : Chart R) (beta : Vec R 6) (s : SuffixChannels R) :
    mv (litN19b y beta) (packChannels s)=packChannels (channelStep y beta .b s) := by
  funext i
  exact (Fin.cases ((channel_step_b_0 y beta s).symm) (fun i => (Fin.cases ((channel_step_b_1 y beta s).symm) (fun i => (Fin.cases ((channel_step_b_2 y beta s).symm) (fun i => (Fin.cases ((channel_step_b_3 y beta s).symm) (fun i => (Fin.cases ((channel_step_b_4 y beta s).symm) (fun i => (Fin.cases ((channel_step_b_5 y beta s).symm) (fun i => (Fin.cases ((channel_step_b_6 y beta s).symm) (fun i => (Fin.cases ((channel_step_b_7 y beta s).symm) (fun i => (Fin.cases ((channel_step_b_8 y beta s).symm) (fun i => (Fin.cases ((channel_step_b_9 y beta s).symm) (fun i => (Fin.cases ((channel_step_b_10 y beta s).symm) (fun i => (Fin.cases ((channel_step_b_11 y beta s).symm) (fun i => (Fin.cases ((channel_step_b_12 y beta s).symm) (fun i => (Fin.cases ((channel_step_b_13 y beta s).symm) (fun i => (Fin.cases ((channel_step_b_14 y beta s).symm) (fun i => (Fin.cases ((channel_step_b_15 y beta s).symm) (fun i => (Fin.cases ((channel_step_b_16 y beta s).symm) (fun i => (Fin.cases ((channel_step_b_17 y beta s).symm) (fun i => (Fin.cases ((channel_step_b_18 y beta s).symm) (fun i => (Fin.elim0 i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)

theorem literal_selected_b (y : Chart R) (s : SuffixChannels R) :
    mv (litCb y) (packChannels s)=(fun i => s.f i+s.k i) := by
  funext i
  exact (Fin.cases (selected_b_0 y s) (fun i => (Fin.cases (selected_b_1 y s) (fun i => (Fin.cases (selected_b_2 y s) (fun i => (Fin.cases (selected_b_3 y s) (fun i => (Fin.cases (selected_b_4 y s) (fun i => (Fin.cases (selected_b_5 y s) (fun i => (Fin.elim0 i)) i)) i)) i)) i)) i)) i)

theorem literal_channel_step_t (y : Chart R) (beta : Vec R 6) (s : SuffixChannels R) :
    mv (litN19t y beta) (packChannels s)=packChannels (channelStep y beta .t s) := by
  funext i
  exact (Fin.cases ((channel_step_t_0 y beta s).symm) (fun i => (Fin.cases ((channel_step_t_1 y beta s).symm) (fun i => (Fin.cases ((channel_step_t_2 y beta s).symm) (fun i => (Fin.cases ((channel_step_t_3 y beta s).symm) (fun i => (Fin.cases ((channel_step_t_4 y beta s).symm) (fun i => (Fin.cases ((channel_step_t_5 y beta s).symm) (fun i => (Fin.cases ((channel_step_t_6 y beta s).symm) (fun i => (Fin.cases ((channel_step_t_7 y beta s).symm) (fun i => (Fin.cases ((channel_step_t_8 y beta s).symm) (fun i => (Fin.cases ((channel_step_t_9 y beta s).symm) (fun i => (Fin.cases ((channel_step_t_10 y beta s).symm) (fun i => (Fin.cases ((channel_step_t_11 y beta s).symm) (fun i => (Fin.cases ((channel_step_t_12 y beta s).symm) (fun i => (Fin.cases ((channel_step_t_13 y beta s).symm) (fun i => (Fin.cases ((channel_step_t_14 y beta s).symm) (fun i => (Fin.cases ((channel_step_t_15 y beta s).symm) (fun i => (Fin.cases ((channel_step_t_16 y beta s).symm) (fun i => (Fin.cases ((channel_step_t_17 y beta s).symm) (fun i => (Fin.cases ((channel_step_t_18 y beta s).symm) (fun i => (Fin.elim0 i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)

theorem literal_selected_t (y : Chart R) (s : SuffixChannels R) :
    mv (litCt y) (packChannels s)=(fun i => s.f i+s.k i) := by
  funext i
  exact (Fin.cases (selected_t_0 y s) (fun i => (Fin.cases (selected_t_1 y s) (fun i => (Fin.cases (selected_t_2 y s) (fun i => (Fin.cases (selected_t_3 y s) (fun i => (Fin.cases (selected_t_4 y s) (fun i => (Fin.cases (selected_t_5 y s) (fun i => (Fin.elim0 i)) i)) i)) i)) i)) i)) i)

theorem literal_channel_base (y : Chart R) (beta : Vec R 6) :
    (fun i => litnu19 y beta i 0)=packChannels (channelBase beta) := by
  funext i
  exact (Fin.cases (channel_base_0 y beta) (fun i => (Fin.cases (channel_base_1 y beta) (fun i => (Fin.cases (channel_base_2 y beta) (fun i => (Fin.cases (channel_base_3 y beta) (fun i => (Fin.cases (channel_base_4 y beta) (fun i => (Fin.cases (channel_base_5 y beta) (fun i => (Fin.cases (channel_base_6 y beta) (fun i => (Fin.cases (channel_base_7 y beta) (fun i => (Fin.cases (channel_base_8 y beta) (fun i => (Fin.cases (channel_base_9 y beta) (fun i => (Fin.cases (channel_base_10 y beta) (fun i => (Fin.cases (channel_base_11 y beta) (fun i => (Fin.cases (channel_base_12 y beta) (fun i => (Fin.cases (channel_base_13 y beta) (fun i => (Fin.cases (channel_base_14 y beta) (fun i => (Fin.cases (channel_base_15 y beta) (fun i => (Fin.cases (channel_base_16 y beta) (fun i => (Fin.cases (channel_base_17 y beta) (fun i => (Fin.cases (channel_base_18 y beta) (fun i => (Fin.elim0 i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)) i)

#print axioms literal_channel_step_z
#print axioms literal_channel_step_b
#print axioms literal_channel_step_t
#print axioms literal_selected_z
#print axioms literal_selected_b
#print axioms literal_selected_t
#print axioms literal_channel_base
end StackSorting.FiniteGraph
