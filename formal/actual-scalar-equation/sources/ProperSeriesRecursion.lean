import Std

/-!
Coefficientwise existence and uniqueness for proper systems.

This module uses coefficient functions, not Mathlib's `PowerSeries` type.
Its convergence argument uses only finite prefixes; no analytic or valuation
assumptions, finiteness of the index type, or algebraic axioms are required.
-/
namespace StackSorting.ProperSeries

universe u v

abbrev Series (A : Type u) := Nat → A
abbrev Family (I : Type v) (A : Type u) := I → Series A

/-- Equality strictly below the indicated degree, in every component. -/
def AgreeBelow {I : Type v} {A : Type u} (n : Nat) (a b : Family I A) : Prop :=
  ∀ i k, k < n → a i k = b i k

/-- The output prefix grows by one coefficient at each application. -/
def Contracting {I : Type v} {A : Type u} (F : Family I A → Family I A) : Prop :=
  ∀ n a b, AgreeBelow n a b → AgreeBelow (n + 1) (F a) (F b)

/-- Finite iterates from any chosen seed. -/
def iterate {I : Type v} {A : Type u}
    (F : Family I A → Family I A) (seed : Family I A) : Nat → Family I A
  | 0 => seed
  | n + 1 => F (iterate F seed n)

/-- Once computed, the first n coefficients persist in every later iterate. -/
theorem iterate_agree {I : Type v} {A : Type u}
    {F : Family I A → Family I A} (hF : Contracting F) (seed : Family I A)
    (n m : Nat) (hnm : n ≤ m) :
    AgreeBelow n (iterate F seed n) (iterate F seed m) := by
  induction n generalizing m with
  | zero => intro i k hk; omega
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      exact hF n _ _ (ih m (by omega))

/-- Degree k is taken from the (k+1)-st iterate. -/
def solution {I : Type v} {A : Type u}
    (F : Family I A → Family I A) (seed : Family I A) : Family I A :=
  fun i k => iterate F seed (k + 1) i k

theorem solution_agree_iterate {I : Type v} {A : Type u}
    {F : Family I A → Family I A} (hF : Contracting F) (seed : Family I A)
    (n : Nat) : AgreeBelow n (solution F seed) (iterate F seed n) := by
  intro i k hk
  exact iterate_agree hF seed (k + 1) n (by omega) i k (by omega)

/-- The diagonal of finite iterates is an actual fixed point. -/
theorem solution_fixed {I : Type v} {A : Type u}
    {F : Family I A → Family I A} (hF : Contracting F) (seed : Family I A) :
    F (solution F seed) = solution F seed := by
  funext i k
  exact hF k _ _ (solution_agree_iterate hF seed k) i k (by omega)

/-- A contracting coefficient operator has at most one fixed point. -/
theorem fixed_unique {I : Type v} {A : Type u}
    {F : Family I A → Family I A} (hF : Contracting F)
    {a b : Family I A} (ha : F a = a) (hb : F b = b) : a = b := by
  have hprefix : ∀ n, AgreeBelow n a b := by
    intro n
    induction n with
    | zero => intro i k hk; omega
    | succ n ih =>
      simpa only [ha, hb] using hF n a b ih
  funext i k
  exact hprefix (k + 1) i k (by omega)

/-- Existence and uniqueness, with an arbitrary seed supplied explicitly. -/
theorem exists_unique_fixed {I : Type v} {A : Type u}
    {F : Family I A → Family I A} (hF : Contracting F) (seed : Family I A) :
    ∃ a, F a = a ∧ ∀ b, F b = b → b = a := by
  refine ⟨solution F seed, solution_fixed hF seed, ?_⟩
  intro a ha
  exact fixed_unique hF ha (solution_fixed hF seed)

#print axioms iterate_agree
#print axioms solution_fixed
#print axioms fixed_unique
#print axioms exists_unique_fixed

end StackSorting.ProperSeries
