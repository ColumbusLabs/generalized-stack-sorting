import GeneralizedMatrixWordRows
import GeneralizedWordRecordSeries
import SignedWordLiteralBoundary
import GraphBoundary

/-! The candidate is the literal six-state matrix series, with explicit empty
and height-one values. Its record resolvent is constructed from the six scalar
equations, not postulated as a counting function. -/
noncomputable section
namespace StackSorting.Generalized.Decorated.SignedCompletion
open StackSorting.SignedWord StackSorting.FiniteGraph StackSorting.CauchyRing

variable {R : Type} [Lean.Grind.CommRing R]

def familyWord (f : Family) (word : Word) : Word :=
  .z :: (match f with | .b => .b | .z => .z) :: word

def familyRow (y : Chart R) : Family → Vec R 6
  | .b => originRow
  | .z => litalpha y 0

def matrixCandidate (y : Chart R) (x : R) (beta : Vec R 6) : Word → R
  | [] => generatingFunction x beta
  | .z::word => boundaryValue y beta (litalpha y 0) originRow (d0 x beta) word
  | _::_ => 0

def matrixRecord (y : Chart R) (x : R) (beta : Vec R 6) : Word → R
  | [] => generatingFunction x beta + x*(d0 x beta+x*recordFromScalar (litT y) (litK y) beta 0)
  | [.z] => d0 x beta+x*recordFromScalar (litT y) (litK y) beta 0
  | .z::.b::word => wordColumn y (recordFromScalar (litT y) (litK y) beta) word 0
  | .z::.z::word => dot (litalpha y 0) (wordColumn y (recordFromScalar (litT y) (litK y) beta) word)
  | _ => 0

theorem matrixCandidate_family (y : Chart R) (x : R) (beta : Vec R 6)
    (f : Family) (word : Word) :
    matrixCandidate y x beta (familyWord f word) = dot (familyRow y f) (wordColumn y beta word) := by
  cases f <;> rfl

theorem matrixRecord_family (y : Chart R) (x : R) (beta : Vec R 6)
    (f : Family) (word : Word) :
    matrixRecord y x beta (familyWord f word) =
      dot (familyRow y f) (wordColumn y (recordFromScalar (litT y) (litK y) beta) word) := by
  cases f with
  | b => exact (dot_originRow _).symm
  | z => rfl

theorem pushWord_family (f : Family) (word : Word) :
    pushWord (familyWord f word) = familyWord f (word++[.t]) := by
  cases f <;> simp [pushWord, pushLetter, familyWord]

theorem wordColumn_resolvent (y : Chart R) (x : R) (beta gamma : Vec R 6)
    (hgamma : ∀ i, gamma i=beta i+x*mv (litT y) gamma i) (word : Word) :
    wordColumn y gamma word = fun i =>
      wordColumn y beta word i+x*wordColumn y gamma (word++[.t]) i := by
  induction word with
  | nil => exact funext hgamma
  | cons a word ih =>
    simp only [wordColumn, List.cons_append]
    rw [ih, FiniteGraph.mv_add, mv_scale]

theorem matrixRecord_family_equation (y : Chart R) (x : R) (beta : Vec R 6)
    (hs : SixScalarEquations y x beta) (f : Family) (word : Word) :
    matrixRecord y x beta (familyWord f word) =
      matrixCandidate y x beta (familyWord f word) +
        x*matrixRecord y x beta (pushWord (familyWord f word)) := by
  rw [pushWord_family, matrixRecord_family, matrixCandidate_family, matrixRecord_family]
  rw [wordColumn_resolvent y x beta _ (scalar_constructs_record x (litT y) (litK y) beta hs).2,
    dot_add, FiniteGraph.dot_scale_right]

theorem matrixRecord_equation (y : Chart FPS) (beta : Vec FPS 6)
    (hs : SixScalarEquations y X beta) (word : Word) (hv : Valid (decodeWord word)) :
    matrixRecord y X beta word = matrixCandidate y X beta word +
      X*matrixRecord y X beta (pushWord word) := by
  rcases admissibleWord_of_valid hv with he | he | ⟨a,rest,ha,he⟩
  · subst word
    rfl
  · subst word
    rfl
  · subst word
    rcases ha with ha | ha
    · subst a
      exact matrixRecord_family_equation y X beta hs .z rest
    · subst a
      exact matrixRecord_family_equation y X beta hs .b rest

#print axioms matrixRecord_equation
end StackSorting.Generalized.Decorated.SignedCompletion
