import CapacityHeight
import GrammarCounting

namespace StackSorting.Capacity
open StackSorting FirstReturn Mark Op

abbrev Slice (h n : Nat) (a : Mark) (b : Option Mark) (flag : Bool) (d : Option Mark) :=
  {t : SizedTree n // eval t.val a b flag = some d ∧ treeExtra t.val ≤ h}

noncomputable def count (h n : Nat) (a : Mark) (b : Option Mark) (flag : Bool)
    (d : Option Mark) : Nat := Fintype.card (Slice h n a b flag d)

noncomputable def series (h : Nat) (a : Mark) (b : Option Mark) (flag : Bool)
    (d : Option Mark) : PowerSeries ℤ := PowerSeries.mk fun n => (count h n a b flag d : ℤ)

abbrev PairSlice (h n : Nat) (c : Mark) (b d : Option Mark) :=
  Σ ij : Split n, Σ e : Mark,
    Slice h ij.val.1 R (some c) false (some e) × Slice (h+1) ij.val.2 e b true d

abbrev StepCases (h n : Nat) (a : Mark) (b d : Option Mark) :=
  Slice (h+1) n a b true d ⊕ (PairSlice h n a b d ⊕ PairSlice h n L b d)

def splitTree (h n : Nat) (a : Mark) (b d : Option Mark) (flag : Bool) :
    Slice (h+1) (n+1) a b flag d → StepCases h n a b d := by
  rintro ⟨⟨t, hw⟩, ht⟩
  have he := ht.1
  have hh := ht.2
  cases t with
  | pop0 => simp [weight] at hw
  | pop1 => simp [weight] at hw
  | bypass t =>
      exact .inl ⟨⟨t, by simp [weight] at hw; omega⟩, he, by simp [treeExtra] at hh; omega⟩
  | push0 s t =>
      exact match hs : eval s R (some a) false with
      | none => False.elim (by simp [eval, hs] at he)
      | some none => False.elim (by simp [eval, hs] at he)
      | some (some e) =>
          .inr (.inl ⟨⟨(weight s, weight t), by simp [Finset.mem_antidiagonal]; simp [weight] at hw; omega⟩,
            e, ⟨⟨⟨s, rfl⟩, hs, by change treeExtra s ≤ h; simp [treeExtra] at hh; omega⟩,
                ⟨⟨t, rfl⟩, by simpa [eval, hs] using he, by change treeExtra t ≤ h+1; simp [treeExtra] at hh; omega⟩⟩⟩)
  | push1 s t =>
      exact match hs : eval s R (some L) false with
      | none => False.elim (by simp [eval, hs] at he)
      | some none => False.elim (by simp [eval, hs] at he)
      | some (some e) =>
          .inr (.inr ⟨⟨(weight s, weight t), by simp [Finset.mem_antidiagonal]; simp [weight] at hw; omega⟩,
            e, ⟨⟨⟨s, rfl⟩, hs, by change treeExtra s ≤ h; simp [treeExtra] at hh; omega⟩,
                ⟨⟨t, rfl⟩, by simpa [eval, hs] using he, by change treeExtra t ≤ h+1; simp [treeExtra] at hh; omega⟩⟩⟩)

def joinTree (h n : Nat) (a : Mark) (b d : Option Mark) (flag : Bool) :
    StepCases h n a b d → Slice (h+1) (n+1) a b flag d
  | .inl t => ⟨⟨.bypass t.val.val, by simp [weight, t.val.property, Nat.add_comm]⟩,
      t.property.1, by simp [treeExtra, t.property.2]⟩
  | .inr (.inl ⟨ij, e, s, t⟩) =>
      ⟨⟨.push0 s.val.val t.val.val, by
        have hi := Finset.mem_antidiagonal.mp ij.property
        simp only [weight, s.val.property, t.val.property]; omega⟩,
        by simp [eval, s.property.1, t.property.1], by
          have hs := s.property.2; have ht := t.property.2
          simp only [treeExtra, Nat.max_le]; omega⟩
  | .inr (.inr ⟨ij, e, s, t⟩) =>
      ⟨⟨.push1 s.val.val t.val.val, by
        have hi := Finset.mem_antidiagonal.mp ij.property
        simp only [weight, s.val.property, t.val.property]; omega⟩,
        by simp [eval, s.property.1, t.property.1], by
          have hs := s.property.2; have ht := t.property.2
          simp only [treeExtra, Nat.max_le]; omega⟩

theorem join_split (h n : Nat) (a : Mark) (b d : Option Mark) (flag : Bool)
    (t : Slice (h+1) (n+1) a b flag d) :
    joinTree h n a b d flag (splitTree h n a b d flag t) = t := by
  rcases t with ⟨⟨t, hw⟩, he, hh⟩
  cases t with
  | pop0 => simp [weight] at hw
  | pop1 => simp [weight] at hw
  | bypass t => rfl
  | push0 s t =>
      cases hs : eval s R (some a) false with
      | none => simp [eval, hs] at he
      | some e =>
          cases e with
          | none => simp [eval, hs] at he
          | some e => simp only [splitTree]; split <;> simp_all [joinTree]
  | push1 s t =>
      cases hs : eval s R (some L) false with
      | none => simp [eval, hs] at he
      | some e =>
          cases e with
          | none => simp [eval, hs] at he
          | some e => simp only [splitTree]; split <;> simp_all [joinTree]

theorem split_join (h n : Nat) (a : Mark) (b d : Option Mark) (flag : Bool)
    (c : StepCases h n a b d) :
    splitTree h n a b d flag (joinTree h n a b d flag c) = c := by
  rcases c with t | c
  · rcases t with ⟨⟨t, hw⟩, he, hh⟩; rfl
  · rcases c with ⟨⟨⟨i,j⟩, hij⟩, e, ⟨⟨s, hs⟩, hse, hsh⟩, ⟨⟨t, ht⟩, hte, hth⟩⟩ |
        ⟨⟨⟨i,j⟩, hij⟩, e, ⟨⟨s, hs⟩, hse, hsh⟩, ⟨⟨t, ht⟩, hte, hth⟩⟩
    all_goals change weight s = i at hs
    all_goals change weight t = j at ht
    all_goals subst i; subst j
    all_goals dsimp only at hse hte
    all_goals dsimp [joinTree, splitTree]
    all_goals split
    all_goals rename_i heq
    all_goals have hh := hse.symm.trans heq
    all_goals simp only [Option.some.injEq, reduceCtorEq] at hh
    all_goals cases hh
    all_goals rfl

def stepEquiv (h n : Nat) (a : Mark) (b d : Option Mark) (flag : Bool) :
    Slice (h+1) (n+1) a b flag d ≃ StepCases h n a b d where
  toFun := splitTree h n a b d flag
  invFun := joinTree h n a b d flag
  left_inv := join_split h n a b d flag
  right_inv := split_join h n a b d flag

theorem count_succ (h n : Nat) (a : Mark) (b d : Option Mark) (flag : Bool) :
    count (h+1) (n+1) a b flag d = count (h+1) n a b true d +
      (∑ ij ∈ Finset.antidiagonal n, ∑ e : Mark,
        count h ij.1 R (some a) false (some e) * count (h+1) ij.2 e b true d) +
      (∑ ij ∈ Finset.antidiagonal n, ∑ e : Mark,
        count h ij.1 R (some L) false (some e) * count (h+1) ij.2 e b true d) := by
  change Fintype.card (Slice (h+1) (n+1) a b flag d) = _
  rw [Fintype.card_congr (stepEquiv h n a b d flag)]
  simp only [StepCases, PairSlice, Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod]
  simp only [count, Nat.add_assoc]
  congr 1
  exact congrArg₂ Nat.add
    (Finset.sum_attach _ (fun ij : Nat × Nat => ∑ e : Mark,
      Fintype.card (Slice h ij.1 R (some a) false (some e)) *
      Fintype.card (Slice (h+1) ij.2 e b true d)))
    (Finset.sum_attach _ (fun ij : Nat × Nat => ∑ e : Mark,
      Fintype.card (Slice h ij.1 R (some L) false (some e)) *
      Fintype.card (Slice (h+1) ij.2 e b true d)))

def zeroEquiv (h : Nat) (a : Mark) (b d : Option Mark) (flag : Bool) :
    Slice h 0 a b flag d ≃ FirstReturn.ZeroCases a b d flag where
  toFun t := by
    rcases t with ⟨⟨t, hw⟩, he, hh⟩
    cases t with
    | pop0 => exact ⟨true, he⟩
    | pop1 => exact ⟨false, he⟩
    | bypass t => simp [weight] at hw
    | push0 s t => simp [weight] at hw
    | push1 s t => simp [weight] at hw
  invFun q := ⟨⟨if q.val then .pop0 else .pop1, by cases q.val <;> rfl⟩,
    q.property, by cases q.val <;> simp [treeExtra]⟩
  left_inv t := by
    rcases t with ⟨⟨t, hw⟩, he, hh⟩
    cases t <;> simp [weight] at hw
    all_goals rfl
  right_inv q := by rcases q with ⟨q, hq⟩; cases q <;> rfl

theorem count_zero (h : Nat) (a : Mark) (b d : Option Mark) (flag : Bool) :
    count h 0 a b flag d =
      (if eval .pop0 a b flag = some d then 1 else 0) +
      (if eval .pop1 a b flag = some d then 1 else 0) := by
  change Fintype.card (Slice h 0 a b flag d) = _
  rw [Fintype.card_congr (zeroEquiv h a b d flag)]
  by_cases h0 : eval .pop0 a b flag = some d <;>
    by_cases h1 : eval .pop1 a b flag = some d <;>
    simp [FirstReturn.ZeroCases, Fintype.card_subtype, Finset.filter_insert,
      Finset.filter_singleton, h0, h1]

theorem count_no_space (n : Nat) (a : Mark) (b d : Option Mark) (flag : Bool) :
    count 0 (n+1) a b flag d = 0 := by
  have : IsEmpty (Slice 0 (n+1) a b flag d) := ⟨by
    rintro ⟨⟨t, hw⟩, he, hh⟩
    cases t with
    | pop0 | pop1 => change 0 = n+1 at hw; omega
    | bypass t => change max 1 (treeExtra t) ≤ 0 at hh; omega
    | push0 s t | push1 s t =>
        change max (1 + treeExtra s) (treeExtra t) ≤ 0 at hh; omega⟩
  exact Fintype.card_eq_zero

#print axioms count_succ
#print axioms count_zero
#print axioms count_no_space
end StackSorting.Capacity
