import FiniteMatrix

/-! Concrete signed finite word sums for the (3,3) unary suffix reduction.
Terms are a list, not a set: repeated output words retain their multiplicity.
J is only a counting surrogate for the old O-producing channel when preceded
by Z. This module makes no unrestricted physical O-to-Z identification. -/
namespace StackSorting.SignedWord
open StackSorting.FiniteGraph
attribute [local instance] Lean.Grind.Ring.intCast
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

abbrev Word := List Letter
abbrev Poly := List (Int × Word)

def one : Poly := [(1, [])]
def prefixLetter (a : Letter) (p : Poly) : Poly := p.map fun term => (term.1, a :: term.2)
def prepend (w : Word) (p : Poly) : Poly := p.map fun term => (term.1, w ++ term.2)
def negative (p : Poly) : Poly := p.map fun term => (-term.1, term.2)
/-- Left multiplication by the signed polynomial b-z. -/
def difference (p : Poly) : Poly := prefixLetter .b p ++ negative (prefixLetter .z p)

def E : Word → Poly
  | [] => one
  | _ :: _ => []
def J : Word → Poly
  | [] => one
  | .z :: v => prefixLetter .z (E v)
  | .b :: v => prefixLetter .b (E v)
  | .t :: v => prefixLetter .z (J v) ++ difference (E v)
def K : Word → Poly
  | [] => []
  | .z :: _ => []
  | .b :: v => difference (E v)
  | .t :: v => difference (K v)
def F : Word → Poly
  | [] => one
  | .z :: v => prefixLetter .z (J v)
  | .b :: v => prefixLetter .z (F v) ++ prefixLetter .z (K v)
  | .t :: v => prefixLetter .b (F v) ++ prefixLetter .z (K v)
def U (w : Word) : Poly := F w ++ K w

def eval {R : Type} [Lean.Grind.CommRing R] (phi : Word → R) : Poly → R
  | [] => 0
  | (c,w) :: p => (IntCast.intCast c : R) * phi w + eval phi p

variable {R : Type} [Lean.Grind.CommRing R]

@[simp] theorem eval_nil (phi : Word → R) : eval phi [] = 0 := rfl
@[simp] theorem eval_one (phi : Word → R) : eval phi one = phi [] := by
  simp only [one, eval]
  grind

theorem eval_append (phi : Word → R) (p q : Poly) :
    eval phi (p ++ q) = eval phi p + eval phi q := by
  induction p with
  | nil => simp only [List.nil_append, eval]; grind
  | cons term p ih => simp only [List.cons_append, eval, ih]; grind

theorem eval_prefix (phi : Word → R) (a : Letter) (p : Poly) :
    eval phi (prefixLetter a p) = eval (fun w => phi (a::w)) p := by
  induction p with
  | nil => rfl
  | cons term p ih => simp only [prefixLetter, List.map_cons, eval] at *; rw [ih]

theorem eval_prepend (phi : Word → R) (w : Word) (p : Poly) :
    eval phi (prepend w p) = eval (fun v => phi (w++v)) p := by
  induction p with
  | nil => rfl
  | cons term p ih => simp only [prepend, List.map_cons, eval] at *; rw [ih]

theorem eval_negative (phi : Word → R) (p : Poly) :
    eval phi (negative p) = -eval phi p := by
  induction p with
  | nil => simp only [negative, List.map_nil, eval]; grind
  | cons term p ih => simp only [negative, List.map_cons, eval] at *; rw [ih]; grind

theorem eval_difference (phi : Word → R) (p : Poly) :
    eval phi (difference p) =
      eval (fun w => phi (.b::w)) p - eval (fun w => phi (.z::w)) p := by
  simp only [difference, eval_append, eval_negative, eval_prefix]
  grind

theorem eval_mul (phi : Word → R) (a : R) (p : Poly) :
    eval (fun w => a * phi w) p = a * eval phi p := by
  induction p with
  | nil => simp only [eval]; grind
  | cons term p ih => simp only [eval, ih]; grind

theorem eval_add (phi psi : Word → R) (p : Poly) :
    eval (fun w => phi w + psi w) p = eval phi p + eval psi p := by
  induction p with
  | nil => simp only [eval]; grind
  | cons term p ih => simp only [eval, ih]; grind

theorem eval_zero (p : Poly) : eval (fun _ => (0:R)) p = 0 := by
  induction p with
  | nil => rfl
  | cons term p ih => simp only [eval, ih]; grind

theorem eval_sumFin {n : Nat} (phi : Fin n → Word → R) (p : Poly) :
    eval (fun w => sumFin (fun i => phi i w)) p =
      sumFin (fun i => eval (phi i) p) := by
  induction n with
  | zero => simpa only [sumFin] using eval_zero p
  | succ n ih => simp only [sumFin, eval_add, ih]

theorem eval_U (phi : Word → R) (w : Word) :
    eval phi (U w) = eval phi (F w) + eval phi (K w) := eval_append _ _ _

@[simp] theorem prefix_nil (a : Letter) : prefixLetter a [] = [] := rfl
@[simp] theorem negative_nil : negative [] = [] := rfl
@[simp] theorem difference_nil : difference [] = [] := rfl
@[simp] theorem prefix_append (a : Letter) (p q : Poly) :
    prefixLetter a (p++q) = prefixLetter a p ++ prefixLetter a q := List.map_append

def lambdaPow : Nat → Poly
  | 0 => one
  | n+1 => difference (lambdaPow n)

/-- The subtractive exceptional channel is exactly (b-z)^(q+1). -/
theorem K_exceptional_b (q : Nat) :
    K (List.replicate q .t ++ [.b]) = lambdaPow (q+1) := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [List.replicate_succ, List.cons_append, K, ih, lambdaPow]

theorem K_pure_t (q : Nat) : K (List.replicate q .t) = [] := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [List.replicate_succ, K, ih, difference_nil]

theorem K_exceptional_z (q : Nat) : K (List.replicate q .t ++ [.z]) = [] := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [List.replicate_succ, List.cons_append, K, ih, difference_nil]

/-- No word outside t* b contributes to K. -/
theorem K_support (w : Word) : K w = [] ∨ ∃ q, w = List.replicate q .t ++ [.b] := by
  induction w with
  | nil => exact Or.inl rfl
  | cons a w ih =>
    cases a with
    | z => exact Or.inl rfl
    | b =>
      cases w with
      | nil => exact Or.inr ⟨0, rfl⟩
      | cons a w => exact Or.inl rfl
    | t =>
      rcases ih with ih | ⟨q, rfl⟩
      · exact Or.inl (by simp only [K, ih, difference_nil])
      · exact Or.inr ⟨q+1, by simp only [List.replicate_succ, List.cons_append]⟩

/-- Exceptional means a terminal single letter preceded only by T's. -/
def Exceptional (w : Word) : Prop := w = [] ∨ ∃ q a, w = List.replicate q .t ++ [a]

theorem J_support (w : Word) : J w = [] ∨ Exceptional w := by
  induction w with
  | nil => exact Or.inr (Or.inl rfl)
  | cons a w ih =>
    cases a with
    | z =>
      cases w with
      | nil => exact Or.inr (Or.inr ⟨0, .z, rfl⟩)
      | cons a w => exact Or.inl rfl
    | b =>
      cases w with
      | nil => exact Or.inr (Or.inr ⟨0, .b, rfl⟩)
      | cons a w => exact Or.inl rfl
    | t =>
      cases w with
      | nil => exact Or.inr (Or.inr ⟨0, .t, rfl⟩)
      | cons a w =>
        rcases ih with ih | he
        · exact Or.inl (by simp only [J, ih, E, prefix_nil, difference_nil, List.nil_append])
        · rcases he with h | ⟨q, c, h⟩
          · cases h
          · exact Or.inr (Or.inr ⟨q+1, c, by rw [h]; rfl⟩)

/-- All coefficients, including coincident words, are retained in the sum. -/
theorem duplicate_multiplicity (phi : Word → R) (w : Word) :
    eval phi [(1,w),(1,w)] = 2 * phi w := by simp only [eval]; grind

theorem F_exceptional_b (phi : Word → R) (q : Nat) :
    eval phi (F (List.replicate q .t ++ [.b])) =
      phi (List.replicate (q+1) .b) - eval phi (lambdaPow (q+1)) := by
  induction q generalizing phi with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, F, K, prefix_nil, List.append_nil,
      eval_prefix, eval_one, lambdaPow, eval_difference, List.replicate_succ]
    grind
  | succ q ih =>
    simp only [List.replicate_succ, List.cons_append, F, eval_append, eval_prefix,
      K_exceptional_b, ih, lambdaPow, eval_difference]
    grind

theorem F_pure_t (phi : Word → R) (q : Nat) :
    eval phi (F (List.replicate q .t)) = phi (List.replicate q .b) := by
  induction q generalizing phi with
  | zero => exact eval_one phi
  | succ q ih =>
    simp only [List.replicate_succ, F, K_pure_t, prefix_nil, List.append_nil, eval_prefix, ih]

theorem F_exceptional_z (phi : Word → R) (q : Nat) :
    eval phi (F (List.replicate q .t ++ [.z])) =
      phi (List.replicate q .b ++ [.z]) := by
  induction q generalizing phi with
  | zero => exact eval_one (fun w => phi (.z::w))
  | succ q ih =>
    simp only [List.replicate_succ, List.cons_append, F, K_exceptional_z,
      prefix_nil, List.append_nil, eval_prefix, ih]

theorem J_exceptional_z (phi : Word → R) (q : Nat) :
    eval phi (J (List.replicate q .t ++ [.z])) = phi (List.replicate (q+1) .z) := by
  induction q generalizing phi with
  | zero => exact eval_one (fun w => phi (.z::w))
  | succ q ih =>
    have he : E (List.replicate q .t ++ [.z]) = [] := by cases q <;> rfl
    simp only [List.replicate_succ, List.cons_append, J, he, difference_nil,
      List.append_nil, eval_prefix, ih]

theorem J_exceptional_b (phi : Word → R) (q : Nat) :
    eval phi (J (List.replicate q .t ++ [.b])) = phi (List.replicate q .z ++ [.b]) := by
  induction q generalizing phi with
  | zero => exact eval_one (fun w => phi (.b::w))
  | succ q ih =>
    have he : E (List.replicate q .t ++ [.b]) = [] := by cases q <;> rfl
    simp only [List.replicate_succ, List.cons_append, J, he, difference_nil,
      List.append_nil, eval_prefix, ih]

/-- J's pure-T formula is a signed cancellation, not a physical O quotient. -/
theorem J_pure_t_succ (phi : Word → R) (q : Nat) :
    eval phi (J (List.replicate (q+1) .t)) = phi (List.replicate q .z ++ [.b]) := by
  induction q generalizing phi with
  | zero =>
    simp only [List.replicate_succ, List.replicate_zero, J, E, eval_append,
      eval_prefix, eval_one, eval_difference, List.nil_append]
    grind
  | succ q ih =>
    simp only [List.replicate_succ, J, E, difference_nil, List.append_nil,
      eval_prefix, List.cons_append] at *
    exact ih (fun w => phi (.z::w))

/-- Boundary deletion of the first two coordinates of zbw yields two distinct
held-output ranks, even though their signed successor sums agree. -/
def boundaryB (w : Word) : Poly := F (.b::w) ++ prefixLetter .z (U w)
def boundaryZ (w : Word) : Poly := F (.z::w) ++ prefixLetter .z (F w)

theorem boundaryB_exact (w : Word) :
    boundaryB w = prefixLetter .z (U w) ++ prefixLetter .z (U w) := by
  simp only [boundaryB, F, U, prefix_append]

theorem boundaryB_eval (phi : Word → R) (w : Word) :
    eval phi (boundaryB w) = 2 * eval (fun v => phi (.z::v)) (U w) := by
  rw [boundaryB_exact, eval_append, eval_prefix]
  grind

theorem boundaryZ_eval (phi : Word → R) (w : Word) :
    eval phi (boundaryZ w) = eval (fun v => phi (.z::v)) (J w) +
      eval (fun v => phi (.z::v)) (F w) := by
  simp only [boundaryZ, F, eval_append, eval_prefix]

theorem empty_channels (phi : Word → R) :
    eval phi (F []) = phi [] ∧ eval phi (J []) = phi [] ∧
      eval phi (K []) = 0 ∧ eval phi (E []) = phi [] := by
  simp only [F, J, K, E, eval_one, eval_nil, and_self]

theorem empty_boundaries (phi : Word → R) :
    eval phi (boundaryB []) = 2 * phi [.z] ∧
      eval phi (boundaryZ []) = 2 * phi [.z] := by
  simp only [boundaryB_eval, boundaryZ_eval, eval_U, F, J, K, eval_one, eval_nil]
  constructor <;> grind

#print axioms eval_negative
#print axioms F_exceptional_b
#print axioms K_support
#print axioms J_pure_t_succ
#print axioms boundaryB_eval
#print axioms boundaryZ_eval
#print axioms empty_boundaries
end StackSorting.SignedWord
