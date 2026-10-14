import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! A degree-twelve Rabin criterion. This general lemma does not itself
assert that the literal stack polynomial satisfies the finite certificates. -/
namespace StackSorting.DegreeTwelve
open Polynomial

theorem small_divisor_twelve {d : Nat} (hpos : 0 < d) (hle : d ≤ 6)
    (hd : d ∣ 12) : d ∣ 4 ∨ d ∣ 6 := by
  interval_cases d <;> norm_num at *

theorem rabin_degree_twelve {K : Type*} [Field K] [Finite K]
    (f : K[X]) (hdeg : f.natDegree = 12)
    (h12 : f ∣ X ^ (Nat.card K) ^ 12 - X)
    (h4 : IsCoprime f (X ^ (Nat.card K) ^ 4 - X))
    (h6 : IsCoprime f (X ^ (Nat.card K) ^ 6 - X)) : Irreducible f := by
  have hf : f ≠ 0 := by
    intro he
    simp [he] at hdeg
  have hunit : ¬ IsUnit f := by
    intro hu
    have hz := natDegree_eq_zero_of_isUnit hu
    omega
  apply (irreducible_iff_lt_natDegree_lt hf hunit).mpr
  intro q hmon hqdeg hq
  have hqdeg := Finset.mem_Ioc.mp hqdeg
  have hqpos : 0 < q.natDegree := hqdeg.1
  have hqle : q.natDegree ≤ 6 := by simpa [hdeg] using hqdeg.2
  obtain ⟨g, hgi, hgq⟩ := exists_irreducible_of_natDegree_pos hqpos
  have hgf : g ∣ f := dvd_trans hgq hq
  have hgpos : 0 < g.natDegree := hgi.natDegree_pos
  have hgle : g.natDegree ≤ 6 :=
    (natDegree_le_of_dvd hgq hmon.ne_zero).trans hqle
  have hd : g.natDegree ∣ 12 :=
    hgi.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (dvd_trans hgf h12)
  rcases small_divisor_twelve hgpos hgle hd with hd4 | hd6
  · exact hgi.not_isUnit (h4.isUnit_of_dvd' hgf
      (hgi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp hd4))
  · exact hgi.not_isUnit (h6.isUnit_of_dvd' hgf
      (hgi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp hd6))

theorem rabin_degree_twelve_of_card {K : Type*} [Field K] [Finite K]
    (q : Nat) (hq : Nat.card K = q) (f : K[X]) (hdeg : f.natDegree = 12)
    (h12 : f ∣ X^q^12-X) (h4 : IsCoprime f (X^q^4-X))
    (h6 : IsCoprime f (X^q^6-X)) : Irreducible f := by
  subst q
  exact rabin_degree_twelve f hdeg h12 h4 h6

#print axioms rabin_degree_twelve_of_card
#print axioms small_divisor_twelve
#print axioms rabin_degree_twelve
end StackSorting.DegreeTwelve
