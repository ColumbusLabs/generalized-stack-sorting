import ScalarJetCertificate

namespace StackSorting.RationalLift
open StackSorting.ProperSeries StackSorting.ConcreteEquation StackSorting.CauchyRing
open StackSorting.SeriesPolynomialSemantics StackSorting.ConcreteScalar StackSorting.ScalarJet
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- The finite splitter computes the actual first thirteen coefficients of
any polynomial in the certified scalar series. -/
theorem scalar_map_jet (e : Expr) (n : Nat) (hn : n<13) :
    (ringEval e X (fun _ => G)) n = (splitAt 13 family12 e).low.getD n 0 := by
  have hs1 := ringEval_coefficient_semantics e (fun _ : Fin 7 => G.coeff)
  have hs2 := ringEval_coefficient_semantics e
    (fun _ : Fin 7 => (polyEval center12 X).coeff)
  have hagree : AgreeBelow 13 (fun _ : Fin 7 => G.coeff)
      (fun _ : Fin 7 => (polyEval center12 X).coeff) := by
    intro i k hk
    change G k=(polyEval center12 X) k
    rw [G_prefix13 k (by omega), polyEval_X_coeff]
  have hc := e.eval_causal hagree n hn
  rw [← hs1, ← hs2] at hc
  have he := splitAt_ring_exact 13 family12 e X (fun _ => (0 : FPS))
  have hec := congrArg (fun a : FPS => a n) he
  change (ringEval e X (fun _ => polyEval center12 X)) n =
    (polyEval (splitAt 13 family12 e).low X) n +
    (X^13 * ringEval (splitAt 13 family12 e).high X (fun _ => 0)) n at hec
  rw [polyEval_X_coeff, X_pow_mul_coeff, ite_eq_left hn] at hec
  change (ringEval e X (fun _ => G)) n = _ at hc
  rw [hc, hec]
  grind

#print axioms scalar_map_jet
end StackSorting.RationalLift
