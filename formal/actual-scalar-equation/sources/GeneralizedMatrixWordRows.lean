import SignedWordMatrixEvaluation
import GeneralizedMatrixRecordCoefficients

/-! Row/column duality for literal words, including the exact order of record
appends. These are finite matrix identities, independent of any counting claim. -/
noncomputable section
namespace StackSorting.SignedWord
open StackSorting.FiniteGraph StackSorting.FiniteGraph.RecordCoefficients
variable {R : Type} [Lean.Grind.CommRing R]

def wordRow (y : Chart R) (row : Vec R 6) : Word → Vec R 6
  | [] => row
  | a::w => wordRow y (vm row (letterMatrix y a)) w

theorem wordRow_dot (y : Chart R) (beta row : Vec R 6) (w : Word) :
    dot (wordRow y row w) beta = dot row (wordColumn y beta w) := by
  induction w generalizing row with
  | nil => rfl
  | cons a w ih =>
    simp only [wordRow, wordColumn]
    rw [ih, dot_vm]

theorem wordRow_append (y : Chart R) (row : Vec R 6) (u v : Word) :
    wordRow y row (u++v) = wordRow y (wordRow y row u) v := by
  induction u generalizing row with
  | nil => rfl
  | cons a u ih => exact ih _

theorem wordColumn_append (y : Chart R) (beta : Vec R 6) (u v : Word) :
    wordColumn y beta (u++v) = wordColumn y (wordColumn y beta v) u := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, wordColumn, ih]

open StackSorting.CauchyRing in
theorem wordRow_replicate_t (y : Chart FPS) (row : Vec FPS 6) (k : Nat) :
    wordRow y row (List.replicate k .t) = readRow (litT y) row k := by
  induction k generalizing row with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, wordRow, letterMatrix, readRow]
    exact ih _

open StackSorting.CauchyRing in
theorem recordCoeff_word_sum (y : Chart FPS) (beta row : Vec FPS 6) (w : Word) (n : Nat) :
    recordCoeff (litT y) beta (wordRow y row w) n =
      ((List.range' 1 n).map (fun batch =>
        dot row (wordColumn y beta (w++List.replicate (batch-1) .t)) (n-batch))).sum := by
  rw [recordCoeff_eq_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro batch _
  rw [←wordRow_replicate_t, ←wordRow_append, wordRow_dot]

#print axioms wordRow_dot
#print axioms wordRow_append
#print axioms recordCoeff_word_sum
end StackSorting.SignedWord
