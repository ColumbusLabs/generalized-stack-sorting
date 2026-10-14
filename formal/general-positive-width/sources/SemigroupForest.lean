import FiniteMonoidForest
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Data.Fintype.Option

namespace StackSorting.Simon
open FactorizationTree

variable {A S : Type*} [Semigroup S]

/-- Product in the original semigroup, without supplying an identity or a
value for the empty word. -/
def SemigroupWordValue (φ : A → S) (w : List A) (s : S) : Prop :=
  ∃ a tail, w = a :: tail ∧ (tail.map φ).foldl (· * ·) (φ a) = s

private theorem coe_foldl (a : S) (xs : List S) :
    ((xs.foldl (· * ·) a : S) : WithOne S) =
      (a : WithOne S) * (xs.map (fun x : S => (x : WithOne S))).prod := by
  induction xs generalizing a with
  | nil => simp
  | cons b xs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.map_cons, List.prod_cons, WithOne.coe_mul, mul_assoc]

theorem semigroupWordValue_iff_coe_product (φ : A → S) (w : List A)
    (hne : w ≠ []) (s : S) :
    SemigroupWordValue φ w s ↔
      (w.map (fun a => (φ a : WithOne S))).prod = (s : WithOne S) := by
  cases w with
  | nil => exact (hne rfl).elim
  | cons a tail =>
    have hv := coe_foldl (φ a) (tail.map φ)
    simp only [List.map_map, Function.comp_def] at hv
    simp only [List.map_cons, List.prod_cons]
    rw [← hv]
    constructor
    · rintro ⟨b, bs, h, hs⟩
      cases h
      exact congrArg (fun s : S => (s : WithOne S)) hs
    · intro h
      exact ⟨a, tail, rfl, WithOne.coe_injective h⟩

theorem nonempty_product_in_semigroup (φ : A → S) (w : List A) (hne : w ≠ []) :
    ∃ s : S, (w.map (fun a => (φ a : WithOne S))).prod = (s : WithOne S) := by
  cases w with
  | nil => exact (hne rfl).elim
  | cons a tail =>
    refine ⟨(tail.map φ).foldl (· * ·) (φ a), ?_⟩
    exact (semigroupWordValue_iff_coe_product φ (a :: tail) (by simp) _).mp
      ⟨a, tail, rfl, rfl⟩

/-- The branch condition is stated wholly in the original semigroup. -/
inductive SemigroupValid (φ : A → S) : FactorizationTree A → Prop
  | leaf (a : A) : SemigroupValid φ (.leaf a)
  | node (ts : List (FactorizationTree A))
      (children : ∀ t ∈ ts, SemigroupValid φ t)
      (arity : 2 ≤ ts.length)
      (branching : ts.length = 2 ∨ ∃ e : S, e * e = e ∧
        ∀ t ∈ ts, SemigroupWordValue φ t.leaves e) :
      SemigroupValid φ (.node ts)

theorem semigroupValid_of_withOne (φ : A → S) (t : FactorizationTree A)
    (hv : Valid (fun a => (φ a : WithOne S)) t) : SemigroupValid φ t := by
  induction hv with
  | leaf a => exact .leaf a
  | node ts hc ha hb ih =>
    apply SemigroupValid.node ts ih ha
    rcases hb with hbinary | ⟨e, he, hvalues⟩
    · exact Or.inl hbinary
    · right
      have hts : ts ≠ [] := by intro h; simp [h] at ha
      obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil ts hts
      obtain ⟨s, hs⟩ := nonempty_product_in_semigroup φ r.leaves (hc r hr).leaves_ne_nil
      have hes : e = (s : WithOne S) := (hvalues r hr).symm.trans hs
      refine ⟨s, ?_, ?_⟩
      · apply WithOne.coe_injective
        simpa only [WithOne.coe_mul, ← hes] using he
      · intro q hq
        apply (semigroupWordValue_iff_coe_product φ q.leaves (hc q hq).leaves_ne_nil s).mpr
        exact (hvalues q hq).trans hes

/-- Genuine finite-semigroup Simon existence. Adjoining a fresh identity costs
one cardinality unit and cannot create a spurious common identity branch,
because every child word is nonempty and has product in the embedded semigroup. -/
theorem exists_finite_semigroup_factorization_tree [Fintype S]
    (φ : A → S) (w : List A) (hne : w ≠ []) :
    ∃ t : FactorizationTree A, t.leaves = w ∧ SemigroupValid φ t ∧
      t.height ≤ monoidForestBound (Fintype.card S + 1) := by
  let : Fintype (WithOne S) := inferInstanceAs (Fintype (Option S))
  obtain ⟨t, hw, hv, hh⟩ := exists_finite_monoid_factorization_tree
    (fun a => (φ a : WithOne S)) w hne
  refine ⟨t, hw, semigroupValid_of_withOne φ t hv, ?_⟩
  have hcard : Fintype.card (WithOne S) = Fintype.card S + 1 :=
    Fintype.card_option
  simpa only [hcard] using hh

#print axioms exists_finite_semigroup_factorization_tree
end StackSorting.Simon
