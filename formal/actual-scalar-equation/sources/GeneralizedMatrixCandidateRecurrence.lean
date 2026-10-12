import GeneralizedMatrixInitialResidual
import GeneralizedCompletionRoot

/-! All-length coefficient recurrence for the explicit literal matrix candidate.
The displayed residual premise is exactly the finite graph theorem's conclusion;
the machine-count recurrence itself was proved independently and is not assumed. -/
noncomputable section
namespace StackSorting.Generalized.Decorated.SignedCompletion
open StackSorting.SignedWord StackSorting.FiniteGraph StackSorting.CauchyRing

variable {R : Type} [Lean.Grind.CommRing R]

theorem wordColumn_kappa (y : Chart R) (x : R) (beta : Vec R 6) (word : Word) :
    wordColumn y (kappa y x beta) word = fun i =>
      wordColumn y beta word i-x*wordColumn y (recordFromScalar (litT y) (litK y) beta) word i := by
  induction word with
  | nil => rfl
  | cons a word ih =>
    simp only [wordColumn]
    rw [ih, FiniteGraph.mv_sub, mv_scale]

theorem matrixCandidate_family_kappa (y : Chart R) (x : R) (beta : Vec R 6)
    (f : Family) (word : Word) :
    dot (familyRow y f) (wordColumn y (kappa y x beta) word) =
      matrixCandidate y x beta (familyWord f word)-x*matrixRecord y x beta (familyWord f word) := by
  rw [wordColumn_kappa, dot_sub_right, FiniteGraph.dot_scale_right,
    matrixCandidate_family, matrixRecord_family]

theorem boundaryRemoval_empty (y : Chart R) (x : R) (beta : Vec R 6) (f : Family) :
    boundaryRemoval y x beta f []=2*d0 x beta := by
  cases f <;> simp only [boundaryRemoval, U, F, J, K, eval_append, eval_one, eval_nil, boundaryValue]
  all_goals grind

theorem matrixCandidate_held_family_empty (y : Chart R) (x : R) (beta : Vec R 6) (f : Family) :
    eval (matrixCandidate y x beta) (heldDelete (familyWord f []))=2*d0 x beta := by
  rw [matrixCandidate_held_family, boundaryRemoval_empty]
  simp only [heldDelete, polyColumn_nil, dot_zero]
  grind

theorem matrixCandidate_family_base (y : Chart R) (x : R) (beta : Vec R 6)
    (hs : SevenScalarEquations y x beta) (hn : beta 0-x*beta 2=2) (f : Family) :
    matrixCandidate y x beta (familyWord f []) =
      eval (matrixCandidate y x beta) (heldDelete (familyWord f [])) +
        x*matrixRecord y x beta (familyWord f []) := by
  have hk := matrixCandidate_family_kappa y x beta f []
  have hb : dot (familyRow y f) (wordColumn y (kappa y x beta) []) = 2*d0 x beta := by
    cases f with
    | b => simp only [familyRow, dot_originRow]; exact empty_B_boundary y x beta hn
    | z => exact empty_Z_boundary y x beta hs hn
  rw [hb] at hk
  rw [matrixCandidate_held_family_empty]
  grind

theorem matrixCandidate_family_step (y : Chart R) (x : R) (beta : Vec R 6)
    (f : Family) (a : Letter) (word : Word)
    (hz : terminal19 (kappa y x beta) (fun i => litnu19 y beta i 0)
      (run19 (transitions y) (suffix19 y beta) (deleted19 y) word (initial19 y beta f a))=0) :
    matrixCandidate y x beta (familyWord f (a::word)) =
      eval (matrixCandidate y x beta) (heldDelete (familyWord f (a::word))) +
        x*matrixRecord y x beta (familyWord f (a::word)) := by
  rw [literal_initial_signed y x beta, matrixCandidate_family_kappa] at hz
  rw [matrixCandidate_held_family]
  grind

theorem matrixCandidate_series_equation (y : Chart FPS) (beta : Vec FPS 6)
    (hs : SevenScalarEquations y X beta) (hn : beta 0-X*beta 2=2)
    (hz : ∀ f a word, terminal19 (kappa y X beta) (fun i => litnu19 y beta i 0)
      (run19 (transitions y) (suffix19 y beta) (deleted19 y) word (initial19 y beta f a))=0)
    (word : Word) (hv : Valid (decodeWord word)) :
    matrixCandidate y X beta word = (if word=[] then 1 else 0) +
      eval (matrixCandidate y X beta) (heldDelete word) + X*matrixRecord y X beta word := by
  rcases admissibleWord_of_valid hv with he | he | ⟨a,rest,ha,he⟩
  · subst word
    have hb := height_one_boundary y X beta hn
    simp only [matrixCandidate, matrixRecord, heldDelete, eval_nil, ite_true]
    unfold generatingFunction at *
    grind
  · subst word
    have hb := height_one_boundary y X beta hn
    simp only [matrixCandidate, matrixRecord, heldDelete, selected, F, prefix_nil,
      List.append_nil, eval_one, boundaryValue, ite_false, List.cons_ne_nil]
    unfold generatingFunction at *
    grind
  · subst word
    have hf : ∃ f, a=(match f with | Family.b => Letter.b | Family.z => Letter.z) := by
      rcases ha with ha | ha
      · exact ⟨.z,ha⟩
      · exact ⟨.b,ha⟩
    rcases hf with ⟨f,rfl⟩
    change matrixCandidate y X beta (familyWord f rest) = 0+
      eval (matrixCandidate y X beta) (heldDelete (familyWord f rest)) +
        X*matrixRecord y X beta (familyWord f rest)
    have heq : matrixCandidate y X beta (familyWord f rest) =
        eval (matrixCandidate y X beta) (heldDelete (familyWord f rest)) +
          X*matrixRecord y X beta (familyWord f rest) := by
      cases rest with
      | nil => exact matrixCandidate_family_base y X beta hs hn f
      | cons a rest => exact matrixCandidate_family_step y X beta f a rest (hz f a rest)
    grind

/-- Exact recurrence of candidate coefficients, ready for decreasing-measure
uniqueness against the already-proved physical counting recurrence. -/
theorem matrixCandidate_countRecurrence (y : Chart FPS) (beta : Vec FPS 6)
    (hs : SevenScalarEquations y X beta) (hn : beta 0-X*beta 2=2)
    (hz : ∀ f a word, terminal19 (kappa y X beta) (fun i => litnu19 y beta i 0)
      (run19 (transitions y) (suffix19 y beta) (deleted19 y) word (initial19 y beta f a))=0) :
    CountRecurrence (fun word n => matrixCandidate y X beta word n) := by
  exact formal_series_recurrence_coefficients (matrixCandidate y X beta) (matrixRecord y X beta)
    (matrixRecord_equation y beta hs.1) (matrixCandidate_series_equation y beta hs hn hz)

/-- Identification with distinct physical outputs, once the explicit literal
algebraic graph residuals are supplied. -/
theorem matrixCandidate_equals_completionCount (y : Chart FPS) (beta : Vec FPS 6)
    (hs : SevenScalarEquations y X beta) (hn : beta 0-X*beta 2=2)
    (hz : ∀ f a word, terminal19 (kappa y X beta) (fun i => litnu19 y beta i 0)
      (run19 (transitions y) (suffix19 y beta) (deleted19 y) word (initial19 y beta f a))=0)
    (word : Word) (n : Nat) (hv : Valid (decodeWord word)) :
    matrixCandidate y X beta word n = (completionCount (decodeWord word) n : Rat) :=
  candidate_equals_actual _ (matrixCandidate_countRecurrence y beta hs hn hz) word n hv

/-- Root attachment to the unrestricted (3,3) distinct-permutation count. -/
theorem matrixGeneratingFunction_actual_counts (y : Chart FPS) (beta : Vec FPS 6)
    (hs : SevenScalarEquations y X beta) (hn : beta 0-X*beta 2=2)
    (hz : ∀ f a word, terminal19 (kappa y X beta) (fun i => litnu19 y beta i 0)
      (run19 (transitions y) (suffix19 y beta) (deleted19 y) word (initial19 y beta f a))=0)
    (n : Nat) :
    generatingFunction X beta n = (ActualCounting.threeThreeCounts n : Rat) := by
  have hc := matrixCandidate_equals_completionCount y beta hs hn hz [] n empty_valid
  change generatingFunction X beta n = (completionCount [] n : Rat) at hc
  rw [completionCount_empty] at hc
  exact hc

#print axioms matrixCandidate_equals_completionCount
#print axioms matrixGeneratingFunction_actual_counts
#print axioms matrixCandidate_countRecurrence
end StackSorting.Generalized.Decorated.SignedCompletion
