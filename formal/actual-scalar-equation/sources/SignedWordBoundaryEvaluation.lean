import SignedWordMatrixEvaluation

/-! Boundary derivatives evaluated on the actual signed polynomial operators.
The unavailable initial T transition is set to zero and is never used below. -/
noncomputable section
namespace StackSorting.SignedWord
open StackSorting.FiniteGraph
attribute [local instance] Lean.Grind.Ring.intCast
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
variable {R : Type} [Lean.Grind.CommRing R]

def boundaryValue (y : Chart R) (beta az ab : Vec R 6) (d0 : R) : Word → R
  | [] => d0
  | .z::w => dot az (wordColumn y beta w)
  | .b::w => dot ab (wordColumn y beta w)
  | .t::_ => 0

theorem eval_dot (y : Chart R) (beta row : Vec R 6) (p : Poly) :
    eval (fun w => dot row (wordColumn y beta w)) p = dot row (polyColumn y beta p) := by
  simp only [dot, polyColumn, eval_sumFin, eval_mul]

theorem boundary_prefix_z (y : Chart R) (beta az ab : Vec R 6) (d0 : R) (p : Poly) :
    eval (boundaryValue y beta az ab d0) (prefixLetter .z p) = dot az (polyColumn y beta p) := by
  simp only [eval_prefix, boundaryValue, eval_dot]

theorem boundary_prefix_b (y : Chart R) (beta az ab : Vec R 6) (d0 : R) (p : Poly) :
    eval (boundaryValue y beta az ab d0) (prefixLetter .b p) = dot ab (polyColumn y beta p) := by
  simp only [eval_prefix, boundaryValue, eval_dot]

theorem dot_sub_left (a b v : Vec R 6) :
    dot (fun i => a i-b i) v = dot a v-dot b v := by
  unfold dot
  have he : (fun i => (a i-b i)*v i) = (fun i => a i*v i+ -(b i*v i)) := by
    funext i
    grind
  rw [he, sumFin_add, sumFin_neg]
  grind

theorem boundary_difference (y : Chart R) (beta az ab : Vec R 6) (d0 : R) (p : Poly) :
    eval (boundaryValue y beta az ab d0) (difference p) =
      dot (fun i => ab i-az i) (polyColumn y beta p) := by
  simp only [difference, eval_append, eval_negative, boundary_prefix_z, boundary_prefix_b,
    dot_sub_left]
  grind

theorem dot_E (y : Chart R) (beta row : Vec R 6) (w : Word) :
    dot row (polyColumn y beta (E w)) = dot row beta * emptyIndicator w := by
  rw [polyColumn_E]
  unfold dot
  have he : (fun i => row i*(beta i*emptyIndicator w)) =
      (fun i => (row i*beta i)*emptyIndicator w) := by funext i; grind
  rw [he, sumFin_mul]

/-- The pF_z, pF_b, pF_t derivative formulas. -/
theorem boundary_F_cons (y : Chart R) (beta az ab : Vec R 6) (d0 : R)
    (a : Letter) (w : Word) :
    eval (boundaryValue y beta az ab d0) (F (a::w)) =
      match a with
      | .z => dot az (polyColumn y beta (J w))
      | .b => dot az (polyColumn y beta (F w)) + dot az (polyColumn y beta (K w))
      | .t => dot ab (polyColumn y beta (F w)) + dot az (polyColumn y beta (K w)) := by
  cases a <;> simp only [F, eval_append, boundary_prefix_z, boundary_prefix_b]

/-- The pJ_z, pJ_b, pJ_t derivative formulas, used only after Z. -/
theorem boundary_J_cons (y : Chart R) (beta az ab : Vec R 6) (d0 : R)
    (a : Letter) (w : Word) :
    eval (boundaryValue y beta az ab d0) (J (a::w)) =
      match a with
      | .z => dot az beta * emptyIndicator w
      | .b => dot ab beta * emptyIndicator w
      | .t => dot az (polyColumn y beta (J w)) +
        dot (fun i => ab i-az i) beta * emptyIndicator w := by
  cases a <;> simp only [J, eval_append, boundary_prefix_z, boundary_prefix_b,
    boundary_difference, dot_E]

/-- The pK_z, pK_b, pK_t derivative formulas with the correct sign. -/
theorem boundary_K_cons (y : Chart R) (beta az ab : Vec R 6) (d0 : R)
    (a : Letter) (w : Word) :
    eval (boundaryValue y beta az ab d0) (K (a::w)) =
      match a with
      | .z => 0
      | .b => dot (fun i => ab i-az i) beta * emptyIndicator w
      | .t => dot (fun i => ab i-az i) (polyColumn y beta (K w)) := by
  cases a <;> simp only [K, eval_nil, boundary_difference, dot_E]

theorem boundary_terminal (y : Chart R) (beta az ab : Vec R 6) (d0 : R) :
    eval (boundaryValue y beta az ab d0) (F []) = d0 ∧
    eval (boundaryValue y beta az ab d0) (J []) = d0 ∧
    eval (boundaryValue y beta az ab d0) (K []) = 0 := by
  simp only [F, J, K, eval_one, eval_nil, boundaryValue, and_self]

#print axioms boundary_F_cons
#print axioms boundary_J_cons
#print axioms boundary_K_cons
#print axioms boundary_terminal
end StackSorting.SignedWord
