import ScalarJetInputs

namespace StackSorting.ScalarJet
open StackSorting.ProperSeries StackSorting.ConcreteEquation StackSorting.CauchyRing
open StackSorting.SeriesPolynomialSemantics
open StackSorting.ConcreteScalar
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

def jetCenter (x : FPS) : FPS := polyEval center12 x

theorem F0_exact (x : FPS) (u : Fin 7 → FPS) :
    scalarPolynomialRing x (jetCenter x) = x^24 * ringEval A0 x u := by
  exact splitAt_ring_divisible 24 family12 f0 low0 x u

theorem F1_exact (x : FPS) (u : Fin 7 → FPS) :
    ringEval f1 x (fun _ => jetCenter x) =
      -576*x^11 + x^12*ringEval A1 x u := by
  have h := splitAt_ring_exact 12 family12 f1 x u
  rw [low1] at h
  have hz : polyEval (List.replicate 11 0 ++ [(-576 : Rat)]) x = -576*x^11 := by
    simp only [List.replicate_succ, List.replicate_zero, List.cons_append,
      List.nil_append, polyEval, C_neg, C_zero]
    have hc : C (576 : Rat) = (576 : FPS) := rfl
    rw [hc]
    grind
  rw [hz] at h
  exact h

theorem F2_exact (x : FPS) (u : Fin 7 → FPS) :
    ringEval f2 x (fun _ => jetCenter x) = x^2*ringEval A2 x u := by
  exact splitAt_ring_divisible 2 family12 f2 low2 x u

def rJet : Expr := .mul (.scalar ((1 : Rat)/576)) (sumExpr [
    A0,
    .mul (.unknown ⟨0, by decide⟩) A1,
    .mul (powExpr .x 2) (.mul (powExpr (.unknown ⟨0, by decide⟩) 2) A2),
    .mul (powExpr .x 12) (.mul (powExpr (.unknown ⟨0, by decide⟩) 3) (substitute f3 (fun _ => QPoly.expression center12))),
    .mul (powExpr .x 24) (.mul (powExpr (.unknown ⟨0, by decide⟩) 4) (substitute f4 (fun _ => QPoly.expression center12))),
    .mul (powExpr .x 36) (.mul (powExpr (.unknown ⟨0, by decide⟩) 5) (substitute f5 (fun _ => QPoly.expression center12))),
    .mul (powExpr .x 48) (.mul (powExpr (.unknown ⟨0, by decide⟩) 6) (substitute f6 (fun _ => QPoly.expression center12))),
    .mul (powExpr .x 60) (.mul (powExpr (.unknown ⟨0, by decide⟩) 7) (substitute f7 (fun _ => QPoly.expression center12))),
    .mul (powExpr .x 72) (.mul (powExpr (.unknown ⟨0, by decide⟩) 8) (substitute f8 (fun _ => QPoly.expression center12))),
    .mul (powExpr .x 84) (.mul (powExpr (.unknown ⟨0, by decide⟩) 9) (substitute f9 (fun _ => QPoly.expression center12))),
    .mul (powExpr .x 96) (.mul (powExpr (.unknown ⟨0, by decide⟩) 10) (substitute f10 (fun _ => QPoly.expression center12))),
    .mul (powExpr .x 108) (.mul (powExpr (.unknown ⟨0, by decide⟩) 11) (substitute f11 (fun _ => QPoly.expression center12))),
    .mul (powExpr .x 120) (.mul (powExpr (.unknown ⟨0, by decide⟩) 12) (substitute f12 (fun _ => QPoly.expression center12)))])

theorem jet_reconstruction_ring (x w : FPS) :
    scalarPolynomialRing x (jetCenter x + x^12*w) =
      x^23*(-576*w + 576*x*ringEval rJet x (fun _ => w)) := by
  have ht := scalar_taylor_ring x (jetCenter x) (x^12*w)
  have h0 := F0_exact x (fun _ => w)
  have h1 := F1_exact x (fun _ => w)
  have h2 := F2_exact x (fun _ => w)
  unfold scalarPolynomialRing at h0
  rw [h0, h1, h2] at ht
  simp only [rJet, sumExpr, ringEval, powExpr_ringEval, substitute_ringEval,
    expression_ringEval, C_zero]
  simp only [jetCenter] at *
  have hcancel := reciprocal576
  grind

def jetR : Unit → PolyExpr Unit Rat := fun _ => scalarize rJet
def jetW : FPS := ⟨properSolution jetR ()⟩

theorem jetW_fixed : jetW = X*ringEval rJet X (fun _ => jetW) := by
  apply FPS.ext
  have hf : (fun i : Unit => (⟨properSolution jetR i⟩ : FPS)) = (fun _ => jetW) := by
    funext i
    cases i
    rfl
  have hs := ringEval_coefficient_semantics (jetR ()) (properSolution jetR)
  rw [hf] at hs
  change (ringEval (scalarize rJet) X (fun _ => jetW)).coeff = _ at hs
  rw [scalarize_ringEval] at hs
  rw [X_mul_coeff, hs]
  exact properSolution_equation jetR ()

def jetG : FPS := jetCenter X + X^12*jetW

theorem jetG_equation : scalarPolynomialRing X jetG = 0 := by
  change scalarPolynomialRing X (jetCenter X+X^12*jetW) = 0
  rw [jet_reconstruction_ring]
  have hw := jetW_fixed
  grind

theorem center12_split : jetCenter X = centerRing X +
    X^10 * polyEval [0,26225388,244673064] X := by
  simp only [jetCenter, centerRing, center12, center, polyEval,
    C_zero, C_one]
  grind

theorem jetG_eq_G : jetG = G := by
  have hc : jetG = centerRing X +
      X^10*(polyEval [0,26225388,244673064] X + X^2*jetW) := by
    unfold jetG
    rw [center12_split]
    grind
  rw [hc]
  apply formal_G_branch_unique
  rw [← hc]
  exact jetG_equation

/-- Literal scalar branch coefficients through degree twelve. This is
proved by constructing an exact second branch and invoking uniqueness,
not by trusting a finite numerical substitution. -/
theorem G_prefix13 (n : Nat) (hn : n≤12) : G n = center12.getD n 0 := by
  rw [← jetG_eq_G]
  change (jetCenter X) n + (X^12*jetW) n = _
  rw [X_pow_mul_coeff]
  have hw : jetW 0=0 := properSolution_zero jetR ()
  have hp : (jetCenter X) n = center12.getD n 0 := polyEval_X_coeff center12 n
  rw [hp]
  by_cases h : n<12
  · rw [ite_eq_left h]; grind
  · have he : n=12 := by omega
    subst n
    simp only [Nat.lt_irrefl, ite_false, Nat.sub_self, hw]
    grind

#print axioms jetG_eq_G
#print axioms G_prefix13
end StackSorting.ScalarJet
