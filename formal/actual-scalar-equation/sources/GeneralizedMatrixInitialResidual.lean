import GeneralizedMatrixResidualSemantics
import GeneralizedMatrixCandidate

/-! Expansion of the six literal initial residual rows into boundary deletion
and internal held deletion, with B-boundary multiplicity two kept explicit. -/
noncomputable section
namespace StackSorting.Generalized.Decorated.SignedCompletion
open StackSorting.SignedWord StackSorting.FiniteGraph StackSorting.CauchyRing
variable {R : Type} [Lean.Grind.CommRing R]

def boundaryRemoval (y : Chart R) (x : R) (beta : Vec R 6) (f : Family) (word : Word) : R :=
  let phi := boundaryValue y beta (litalpha y 0) originRow (d0 x beta)
  match f with
  | .b => 2*eval phi (U word)
  | .z => eval phi (F word)+eval phi (J word)

theorem dot_negative_three {n : Nat} (v f g s : Vec R n) (c d : R) :
    dot (fun i => -v i-c*f i-d*g i) s =
      -dot v s-c*dot f s-d*dot g s := by
  unfold dot
  have h : (fun i => (-v i-c*f i-d*g i)*s i) =
      (fun i => -(v i*s i)+ -(c*(f i*s i))+ -(d*(g i*s i))) := by
    funext i
    grind
  rw [h, sumFin_add, sumFin_add, sumFin_neg, sumFin_neg, sumFin_neg,
    mul_sumFin, mul_sumFin]
  grind

theorem dot_negative_three_one {n : Nat} (v f g s : Vec R n) :
    dot (fun i => -v i-f i-g i) s = -dot v s-dot f s-dot g s := by
  have h : (fun i => -v i-f i-g i) = (fun i => -v i-1*f i-1*g i) := by
    funext i
    grind
  rw [h, dot_negative_three]
  grind

theorem initialPrefix_dot (y : Chart R) (f : Family) (a : Letter) (v : Vec R 6) :
    dot (initialPrefix y f a) v = dot (familyRow y f) (mv (letterMatrix y a) v) := by
  cases f with
  | b => simp only [familyRow, dot_originRow]; rfl
  | z => exact dot_vm _ _ _

theorem literal_initial_signed (y : Chart R) (x : R) (beta kappa : Vec R 6)
    (f : Family) (a : Letter) (word : Word) :
    terminal19 kappa (fun i => litnu19 y beta i 0)
      (run19 (transitions y) (suffix19 y beta) (deleted19 y) word (initial19 y beta f a)) =
      dot (familyRow y f) (wordColumn y kappa (a::word)) -
      dot (familyRow y f) (polyColumn y beta (heldDelete (a::word))) -
      boundaryRemoval y x beta f (a::word) := by
  rw [literal_run_signed]
  change dot (initialPrefix y f a) (wordColumn y kappa word) -
    dot (initialPrefix y f a) (polyColumn y beta (heldDelete word)) +
    dot (initial19 y beta f a).2 (packChannels (evalChannels y beta word)) = _
  rw [initialPrefix_dot, initialPrefix_dot, heldDelete_matrix_step, dot_add]
  cases f with
  | b =>
    simp only [initial19, familyRow, dot_originRow, boundaryRemoval, eval_U]
    rw [dot_negative_three]
    change _ + (-mv (deleted19 y a) (packChannels (evalChannels y beta word)) 0 -
      2*dot (boundaryF y a) (packChannels (evalChannels y beta word)) -
      2*dot (boundaryK y beta a) (packChannels (evalChannels y beta word))) = _
    rw [deleted19_selected, literal_boundary_F_concrete y beta (d0 x beta),
      literal_boundary_K_concrete y beta (d0 x beta)]
    simp only [wordColumn]
    grind
  | z =>
    change _ + dot (fun j => -vm (litalpha y 0) (deleted19 y a) j -
      boundaryF y a j-boundaryJ y beta a j)
      (packChannels (evalChannels y beta word)) = _
    rw [dot_negative_three_one, dot_vm, deleted19_selected,
      literal_boundary_F_concrete y beta (d0 x beta),
      literal_boundary_J_concrete y beta (d0 x beta)]
    simp only [familyRow, boundaryRemoval, wordColumn]
    grind

theorem matrixCandidate_held_family (y : Chart R) (x : R) (beta : Vec R 6)
    (f : Family) (word : Word) :
    eval (matrixCandidate y x beta) (heldDelete (familyWord f word)) =
      boundaryRemoval y x beta f word +
        dot (familyRow y f) (polyColumn y beta (heldDelete word)) := by
  cases f with
  | b =>
    rw [familyWord, heldDelete_zb]
    change 2*eval (boundaryValue y beta (litalpha y 0) originRow (d0 x beta)) (U word) +
      eval (fun w => dot originRow (wordColumn y beta w)) (heldDelete word) = _
    rw [eval_dot]
    rfl
  | z =>
    rw [familyWord, heldDelete_zz]
    change eval (boundaryValue y beta (litalpha y 0) originRow (d0 x beta)) (J word) +
      eval (boundaryValue y beta (litalpha y 0) originRow (d0 x beta)) (F word) +
      eval (fun w => dot (litalpha y 0) (wordColumn y beta w)) (heldDelete word) = _
    rw [eval_dot]
    simp only [boundaryRemoval, familyRow]
    grind

#print axioms literal_initial_signed
#print axioms matrixCandidate_held_family
end StackSorting.Generalized.Decorated.SignedCompletion
