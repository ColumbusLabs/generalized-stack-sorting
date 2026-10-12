import BivariatePolynomial

/-! Bounded rowwise certificates assemble into exact bivariate list equality. -/
namespace StackSorting.RationalLift.BiPoly

theorem eq_of_rows (p q : Poly) (hlen : p.length=q.length)
    (hrow : ∀ k, k<q.length → p.getD k []=q.getD k []) : p=q := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => rfl
    | cons row q => simp at hlen
  | cons row p ih =>
    cases q with
    | nil => simp at hlen
    | cons other q =>
      have hhead : row=other := by
        have h := hrow 0 (by simp)
        simpa using h
      have htail : p=q := by
        apply ih q (by simpa using hlen)
        intro k hk
        have h := hrow (k+1) (by simp; omega)
        simpa using h
      rw [hhead, htail]

#print axioms eq_of_rows
end StackSorting.RationalLift.BiPoly
