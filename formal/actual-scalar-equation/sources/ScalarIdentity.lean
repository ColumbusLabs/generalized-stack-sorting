import ScalarInputs

namespace StackSorting.ConcreteScalar
open StackSorting.ProperSeries StackSorting.ConcreteEquation
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

def centerValue (x : Rat) := QPoly.eval center x

def scalarPolynomial (x g : Rat) := pointEval f0 x (fun _ => g)

/-- Exact degree-twelve Taylor/binomial identity, with all coefficient
polynomials left symbolic in this proof. -/
theorem scalar_taylor (x c t : Rat) :
    scalarPolynomial x (c+t) =
      pointEval f0 x (fun _ => c) * t^0 +
      pointEval f1 x (fun _ => c) * t^1 +
      pointEval f2 x (fun _ => c) * t^2 +
      pointEval f3 x (fun _ => c) * t^3 +
      pointEval f4 x (fun _ => c) * t^4 +
      pointEval f5 x (fun _ => c) * t^5 +
      pointEval f6 x (fun _ => c) * t^6 +
      pointEval f7 x (fun _ => c) * t^7 +
      pointEval f8 x (fun _ => c) * t^8 +
      pointEval f9 x (fun _ => c) * t^9 +
      pointEval f10 x (fun _ => c) * t^10 +
      pointEval f11 x (fun _ => c) * t^11 +
      pointEval f12 x (fun _ => c) * t^12 := by
  simp only [scalarPolynomial, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, pointEval, QPoly.expression_eval]
  grind

theorem f0_exact (x : Rat) (u : Fin 7 → Rat) :
    scalarPolynomial x (centerValue x) = x^22 * pointEval a0 x u := by
  exact splitAt_divisible 22 centerFamily f0 remainder0 x u

theorem f1_exact (x : Rat) (u : Fin 7 → Rat) :
    pointEval f1 x (fun _ => centerValue x) =
      -576*x^11 + x^12*pointEval a1 x u := by
  have h := splitAt_exact 12 centerFamily f1 x u
  rw [remainder1] at h
  have hz : QPoly.eval (List.replicate 11 0 ++ [(-576 : Rat)]) x = -576*x^11 := by
    simp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append, QPoly.eval]
    grind
  rw [hz] at h
  exact h

theorem f2_exact (x : Rat) (u : Fin 7 → Rat) :
    pointEval f2 x (fun _ => centerValue x) = x^2*pointEval a2 x u := by
  exact splitAt_divisible 2 centerFamily f2 remainder2 x u

/-- Completely explicit scalar polynomial right-hand side. The splitter
produces finite expression trees, including the unexpanded high quotients. -/
def rExpr : Expr := .mul (.scalar ((1 : Rat)/576)) (sumExpr [
    a0,
    .mul (.unknown ⟨0, by decide⟩) a1,
    .mul (powExpr (.unknown ⟨0, by decide⟩) 2) a2,
    .mul (powExpr .x 8) (.mul (powExpr (.unknown ⟨0, by decide⟩) 3) (substitute f3 (fun _ => QPoly.expression center))),
    .mul (powExpr .x 18) (.mul (powExpr (.unknown ⟨0, by decide⟩) 4) (substitute f4 (fun _ => QPoly.expression center))),
    .mul (powExpr .x 28) (.mul (powExpr (.unknown ⟨0, by decide⟩) 5) (substitute f5 (fun _ => QPoly.expression center))),
    .mul (powExpr .x 38) (.mul (powExpr (.unknown ⟨0, by decide⟩) 6) (substitute f6 (fun _ => QPoly.expression center))),
    .mul (powExpr .x 48) (.mul (powExpr (.unknown ⟨0, by decide⟩) 7) (substitute f7 (fun _ => QPoly.expression center))),
    .mul (powExpr .x 58) (.mul (powExpr (.unknown ⟨0, by decide⟩) 8) (substitute f8 (fun _ => QPoly.expression center))),
    .mul (powExpr .x 68) (.mul (powExpr (.unknown ⟨0, by decide⟩) 9) (substitute f9 (fun _ => QPoly.expression center))),
    .mul (powExpr .x 78) (.mul (powExpr (.unknown ⟨0, by decide⟩) 10) (substitute f10 (fun _ => QPoly.expression center))),
    .mul (powExpr .x 88) (.mul (powExpr (.unknown ⟨0, by decide⟩) 11) (substitute f11 (fun _ => QPoly.expression center))),
    .mul (powExpr .x 98) (.mul (powExpr (.unknown ⟨0, by decide⟩) 12) (substitute f12 (fun _ => QPoly.expression center)))])

theorem powExpr_eval (e : Expr) (n : Nat) (x : Rat) (u : Fin 7 → Rat) :
    pointEval (powExpr e n) x u = (pointEval e x u)^n := by
  induction n with
  | zero => simp only [powExpr, pointEval]; grind
  | succ n ih => simp only [powExpr, pointEval, ih]; grind

/-- Exact reconstruction identity for the reviewed scalar polynomial.
This is universal in x and w, not a finite coefficient agreement. -/
theorem scalar_reconstruction (x w : Rat) :
    scalarPolynomial x (centerValue x + x^10*w) =
      x^21*(-576*w + 576*x*pointEval rExpr x (fun _ => w)) := by
  have ht := scalar_taylor x (centerValue x) (x^10*w)
  have h0 := f0_exact x (fun _ => w)
  have h1 := f1_exact x (fun _ => w)
  have h2 := f2_exact x (fun _ => w)
  unfold scalarPolynomial at h0
  rw [h0, h1, h2] at ht
  simp only [rExpr, sumExpr, pointEval, powExpr_eval, substitute_eval, QPoly.expression_eval]
  simp only [centerValue] at *
  grind

/-- Rename the sole active unknown to the singleton index type. -/
def scalarize : Expr → PolyExpr Unit Rat
  | .scalar c => .scalar c
  | .x => .x
  | .unknown _ => .unknown ()
  | .add a b => .add (scalarize a) (scalarize b)
  | .mul a b => .mul (scalarize a) (scalarize b)
  | .neg a => .neg (scalarize a)

def scalarR : Unit → PolyExpr Unit Rat := fun _ => scalarize rExpr

/-- Kernel-certified existence and uniqueness for this literal scalar R.
The all-word combinatorial interpretation remains a separate bridge. -/
theorem scalar_proper_exists_unique :
    ∃ a : Family Unit Rat,
      (∀ j, a j = shift ((scalarR j).eval a)) ∧
      ∀ b, (∀ j, b j = shift ((scalarR j).eval b)) → b = a :=
  proper_exists_unique scalarR

#print axioms scalar_taylor
#print axioms scalar_reconstruction
#print axioms scalar_proper_exists_unique
end StackSorting.ConcreteScalar
