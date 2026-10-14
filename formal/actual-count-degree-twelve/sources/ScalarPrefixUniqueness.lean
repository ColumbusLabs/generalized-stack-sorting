import ScalarBranchUnique

/-! Translate the certified affine formal-series ball into a literal
coefficient-prefix condition. No analytic convergence is used. -/
namespace StackSorting.ConcreteScalar
open StackSorting.CauchyRing StackSorting.SeriesPolynomialSemantics

/-- Agreement below degree k is precisely divisibility of the difference by X^k. -/
theorem prefix_eq_iff_affine_ball (a b : FPS) (k : Nat) :
    (∀ n, n < k → a n = b n) ↔ ∃ w : FPS, a = b + X^k*w := by
  constructor
  · intro h
    refine ⟨⟨fun n => a (n+k) - b (n+k)⟩, ?_⟩
    apply FPS.ext
    funext n
    change a n = b n + (X^k*⟨fun m => a (m+k) - b (m+k)⟩) n
    rw [X_pow_mul_coeff]
    by_cases hn : n < k
    · rw [ite_eq_left hn, h n hn]
      grind
    · rw [ite_eq_right hn]
      have he : n-k+k=n := by omega
      change a n = b n + (a (n-k+k) - b (n-k+k))
      rw [he]
      grind
  · rintro ⟨w, rfl⟩ n hn
    change b n + (X^k*w) n = b n
    rw [X_pow_mul_coeff, ite_eq_left hn]
    grind

/-- The displayed algebraic branch is uniquely determined by the literal
scalar equation and the first ten coefficients (degrees zero through nine). -/
theorem formal_G_unique_of_prefix (a : FPS)
    (hroot : scalarPolynomialRing X a = 0)
    (hprefix : ∀ n, n < 10 → a n = center.getD n 0) : a = G := by
  have hp : ∀ n, n < 10 → a n = (centerRing X) n := by
    intro n hn
    rw [hprefix n hn]
    exact (polyEval_X_coeff center n).symm
  obtain ⟨w, hw⟩ := (prefix_eq_iff_affine_ball a (centerRing X) 10).mp hp
  rw [hw] at hroot
  exact hw.trans (formal_G_branch_unique w hroot)

#print axioms prefix_eq_iff_affine_ball
#print axioms formal_G_unique_of_prefix
end StackSorting.ConcreteScalar
