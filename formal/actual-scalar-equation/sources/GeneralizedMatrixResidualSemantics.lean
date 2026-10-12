import SignedWordMatrixEvaluation
import LiteralResidualDefinitions
import LiteralSuffixEvaluation
import DualMatrixEvaluation

/-! The literal 6+19 residual machine expands to the concrete signed held
operator, on every word. No graph-zero or counting identity is assumed here. -/
noncomputable section
namespace StackSorting.SignedWord
open StackSorting.FiniteGraph
variable {R : Type} [Lean.Grind.CommRing R]

theorem transitions_eq_letterMatrix (y : Chart R) (a : Letter) :
    transitions y a = letterMatrix y a := by cases a <;> rfl

theorem suffix19_channel_step (y : Chart R) (beta : Vec R 6) (a : Letter)
    (s : SuffixChannels R) :
    mv (suffix19 y beta a) (packChannels s)=packChannels (channelStep y beta a s) := by
  cases a with
  | z => exact literal_channel_step_z y beta s
  | b => exact literal_channel_step_b y beta s
  | t => exact literal_channel_step_t y beta s

theorem deleted19_selected (y : Chart R) (a : Letter) (s : SuffixChannels R) :
    mv (deleted19 y a) (packChannels s)=selectedColumn a s := by
  cases a with
  | z => exact literal_selected_z y s
  | b => exact literal_selected_b y s
  | t => exact literal_selected_t y s

theorem literal_dual_signed (y : Chart R) (beta kappa : Vec R 6) (word : Word) :
    dual19 (transitions y) (suffix19 y beta) (deleted19 y) kappa
      (fun i => litnu19 y beta i 0) word =
    ((fun i => wordColumn y kappa word i - polyColumn y beta (heldDelete word) i),
      packChannels (evalChannels y beta word)) := by
  induction word with
  | nil =>
    apply Prod.ext
    · funext i
      simp only [dual19, wordColumn, heldDelete, polyColumn_nil]
      grind
    · exact literal_channel_base y beta
  | cons a word ih =>
    rw [dual19, ih]
    apply Prod.ext
    · funext i
      simp only [transitions_eq_letterMatrix, wordColumn, heldDelete_matrix_step]
      rw [FiniteGraph.mv_sub, deleted19_selected]
      grind
    · exact suffix19_channel_step y beta a (evalChannels y beta word)

theorem literal_run_signed (y : Chart R) (beta kappa : Vec R 6) (word : Word)
    (row : Vec R 6 × Vec R 19) :
    terminal19 kappa (fun i => litnu19 y beta i 0)
      (run19 (transitions y) (suffix19 y beta) (deleted19 y) word row) =
      dot row.1 (wordColumn y kappa word) - dot row.1 (polyColumn y beta (heldDelete word)) +
      dot row.2 (packChannels (evalChannels y beta word)) := by
  rw [run19_dual_evaluation, literal_dual_signed, dot_sub_right]

#print axioms literal_dual_signed
#print axioms literal_run_signed
end StackSorting.SignedWord
