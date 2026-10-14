import DegreeTwelveRabinCriterion
import Mathlib.Tactic.Ring
namespace StackSorting.DegreeTwelve
open Polynomial

theorem frobenius_congruence_generic {K : Type*} [Field K]
    (q n : Nat) (f a b : K[X]) (h : f ∣ X^(q^n)-a)
    (hs : f ∣ a^q-b) : f ∣ X^(q^(n+1))-b := by
  have hp := dvd_trans h (sub_dvd_pow_sub_pow (X^(q^n)) a q)
  have ht := dvd_add hp hs
  simpa only [Nat.pow_succ, pow_mul, sub_add_sub_cancel] using ht

theorem coprime_frobenius_generic {K : Type*} [Field K]
    (q n : Nat) (f a : K[X]) (h : f ∣ X^(q^n)-a)
    (hc : IsCoprime f (a-X)) : IsCoprime f (X^(q^n)-X) := by
  obtain ⟨c, hcd⟩ := h
  obtain ⟨u, v, huv⟩ := hc
  refine ⟨u-v*c, v, ?_⟩
  calc
    (u-v*c)*f+v*(X^(q^n)-X) = u*f+v*(a-X)+v*(X^(q^n)-a-f*c) := by ring
    _ = 1 := by rw [hcd, sub_self, mul_zero, add_zero, huv]

/-- Rabin's degree-twelve test from twelve bounded polynomial divisions.
The large exponents are handled only abstractly; certificates contain no expanded huge powers. -/
theorem rabin_degree_twelve_from_chain {K : Type*} [Field K] [Finite K]
    (q : Nat) (hq : Nat.card K=q) (f : K[X]) (hdeg : f.natDegree=12)
    (r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : K[X])
    (h0 : f ∣ X^q-r1)
    (h1 : f ∣ r1^q-r2)
    (h2 : f ∣ r2^q-r3)
    (h3 : f ∣ r3^q-r4)
    (h4 : f ∣ r4^q-r5)
    (h5 : f ∣ r5^q-r6)
    (h6 : f ∣ r6^q-r7)
    (h7 : f ∣ r7^q-r8)
    (h8 : f ∣ r8^q-r9)
    (h9 : f ∣ r9^q-r10)
    (h10 : f ∣ r10^q-r11)
    (h11 : f ∣ r11^q-X)
    (hc4 : IsCoprime f (r4-X)) (hc6 : IsCoprime f (r6-X)) : Irreducible f := by
  have hr0 : f ∣ X^(q^0)-X := by simp
  have hr1 := frobenius_congruence_generic q 0 f X r1 hr0 h0
  have hr2 := frobenius_congruence_generic q 1 f r1 r2 hr1 h1
  have hr3 := frobenius_congruence_generic q 2 f r2 r3 hr2 h2
  have hr4 := frobenius_congruence_generic q 3 f r3 r4 hr3 h3
  have hr5 := frobenius_congruence_generic q 4 f r4 r5 hr4 h4
  have hr6 := frobenius_congruence_generic q 5 f r5 r6 hr5 h5
  have hr7 := frobenius_congruence_generic q 6 f r6 r7 hr6 h6
  have hr8 := frobenius_congruence_generic q 7 f r7 r8 hr7 h7
  have hr9 := frobenius_congruence_generic q 8 f r8 r9 hr8 h8
  have hr10 := frobenius_congruence_generic q 9 f r9 r10 hr9 h9
  have hr11 := frobenius_congruence_generic q 10 f r10 r11 hr10 h10
  have hr12 := frobenius_congruence_generic q 11 f r11 X hr11 h11
  exact rabin_degree_twelve_of_card q hq f hdeg hr12
    (coprime_frobenius_generic q 4 f r4 hr4 hc4)
    (coprime_frobenius_generic q 6 f r6 hr6 hc6)

#print axioms rabin_degree_twelve_from_chain
end StackSorting.DegreeTwelve
