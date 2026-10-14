import ScalarLiteral
import ScalarPrefixUniqueness

namespace StackSorting.ConcreteScalar
open StackSorting.CauchyRing StackSorting.SeriesPolynomialSemantics
/-- The exact displayed scalar literal has one root with the specified prefix. -/
theorem literalQ_root_unique_of_prefix (a : FPS)
    (hroot : ringEval literalQ X (fun _ => a) = 0)
    (hprefix : ∀ n, n < 10 → a n = center.getD n 0) : a = G := by
  rw [literalQ_reification] at hroot
  exact formal_G_unique_of_prefix a hroot hprefix
#print axioms literalQ_root_unique_of_prefix
end StackSorting.ConcreteScalar
