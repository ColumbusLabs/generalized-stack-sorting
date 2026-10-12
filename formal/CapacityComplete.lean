import CapacitySeries
import CompleteCounting

namespace StackSorting.Capacity
open StackSorting FirstReturn Mark Op PowerSeries

abbrev PathSlice (h n : Nat) := {p : SizedPath n // Valid p.val ∧ pathPeak p.val ≤ h}

noncomputable def pathCount (h n : Nat) : Nat := Fintype.card (PathSlice h n)
noncomputable def pathSeries (h : Nat) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (pathCount h n : ℤ)

abbrev PathCases (h n : Nat) := PathSlice (h+1) n ⊕
  (Σ ij : Split n, Slice h ij.val.1 L none false none × PathSlice (h+1) ij.val.2)

def pathSplit (h n : Nat) : PathSlice (h+1) (n+1) → PathCases h n := by
  rintro ⟨⟨p, hw⟩, ht⟩
  have hp := ht.1
  have hh := ht.2
  cases p with
  | nil => simp [pathWeight] at hw
  | bypass p =>
      exact .inl ⟨⟨p, by simp [pathWeight] at hw; omega⟩, hp,
        by simp [pathPeak] at hh; omega⟩
  | push t p =>
      exact .inr ⟨⟨(weight t, pathWeight p), by
        simp [Finset.mem_antidiagonal]; simp [pathWeight] at hw; omega⟩,
        ⟨⟨⟨t, rfl⟩, hp.1, by change treeExtra t ≤ h; simp [pathPeak] at hh; omega⟩,
         ⟨⟨p, rfl⟩, hp.2, by change pathPeak p ≤ h+1; simp [pathPeak] at hh; omega⟩⟩⟩

def pathJoin (h n : Nat) : PathCases h n → PathSlice (h+1) (n+1)
  | .inl p => ⟨⟨.bypass p.val.val, by simp [pathWeight, p.val.property, Nat.add_comm]⟩,
      p.property.1, by simp [pathPeak, p.property.2]⟩
  | .inr ⟨ij, t, p⟩ => ⟨⟨.push t.val.val p.val.val, by
      have hi := Finset.mem_antidiagonal.mp ij.property
      simp only [pathWeight, t.val.property, p.val.property]; omega⟩,
      ⟨t.property.1, p.property.1⟩, by
        have ht := t.property.2; have hp := p.property.2
        simp only [pathPeak, Nat.max_le]; omega⟩

def pathStepEquiv (h n : Nat) : PathSlice (h+1) (n+1) ≃ PathCases h n where
  toFun := pathSplit h n
  invFun := pathJoin h n
  left_inv p := by
    rcases p with ⟨⟨p, hw⟩, hp, hh⟩
    cases p with
    | nil => simp [pathWeight] at hw
    | bypass p => rfl
    | push t p => rfl
  right_inv c := by
    rcases c with p | ⟨⟨⟨i,j⟩, hij⟩, ⟨⟨t, ht⟩, hte, hth⟩, ⟨⟨p, hp⟩, hpe, hph⟩⟩
    · rcases p with ⟨⟨p, hw⟩, hp, hh⟩; rfl
    · change weight t = i at ht
      change pathWeight p = j at hp
      subst i; subst j; rfl

theorem pathCount_succ (h n : Nat) :
    pathCount (h+1) (n+1) = pathCount (h+1) n +
      ∑ ij ∈ Finset.antidiagonal n, count h ij.1 L none false none * pathCount (h+1) ij.2 := by
  change Fintype.card (PathSlice (h+1) (n+1)) = _
  rw [Fintype.card_congr (pathStepEquiv h n)]
  simp only [PathCases, Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod]
  simp only [pathCount, count]
  congr 1
  exact Finset.sum_attach _ (fun ij : Nat × Nat =>
    Fintype.card (Slice h ij.1 L none false none) * Fintype.card (PathSlice (h+1) ij.2))

theorem pathCount_zero (h : Nat) : pathCount h 0 = 1 := by
  have hnil (p : PathSlice h 0) : p.val.val = .nil := by
    rcases p with ⟨⟨p, hw⟩, hp, hh⟩
    cases p with
    | nil => rfl
    | bypass p => simp [pathWeight] at hw
    | push t p => simp [pathWeight] at hw
  let e : PathSlice h 0 ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => ⟨⟨.nil, rfl⟩, trivial, Nat.zero_le h⟩
    left_inv := fun p => by apply Subtype.ext; apply Subtype.ext; exact (hnil p).symm
    right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans Fintype.card_unit

theorem pathCount_no_space (n : Nat) : pathCount 0 (n+1) = 0 := by
  have : IsEmpty (PathSlice 0 (n+1)) := ⟨by
    rintro ⟨⟨p, hw⟩, hp, hh⟩
    cases p with
    | nil => change 0 = n+1 at hw; omega
    | bypass p => change max 1 (pathPeak p) ≤ 0 at hh; omega
    | push t p => change max (1+treeExtra t) (pathPeak p) ≤ 0 at hh; omega⟩
  exact Fintype.card_eq_zero

@[simp] theorem coeff_pathSeries (h n : Nat) :
    coeff n (pathSeries h) = (pathCount h n : ℤ) := by simp [pathSeries]

theorem pathSeries_equation (h : Nat) :
    pathSeries (h+1) = 1 + X * pathSeries (h+1) +
      X * (series h L none false none * pathSeries (h+1)) := by
  ext n
  cases n with
  | zero => simp [pathCount_zero]
  | succ n =>
      simp only [map_add, coeff_succ_X_mul]
      simp only [coeff_one, Nat.succ_ne_zero, ite_false, zero_add,
        coeff_mul, coeff_series, coeff_pathSeries]
      rw [pathCount_succ]
      simp

theorem pathSeries_no_space : pathSeries 0 = 1 := by
  ext n
  cases n with
  | zero => simp [pathCount_zero]
  | succ n => simp [pathCount_no_space]

@[simp] theorem constantCoeff_pathSeries (h : Nat) : constantCoeff (pathSeries h) = 1 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_pathSeries, pathCount_zero]
  rfl

#print axioms pathSeries_equation
#print axioms pathSeries_no_space
end StackSorting.Capacity
