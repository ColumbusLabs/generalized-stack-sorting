import CompleteGrammar
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Fintype.BigOperators

namespace StackSorting.FirstReturn
open StackSorting Mark Op

instance : Fintype Op where
  elems := {.bypass, .push0, .push1, .pop0, .pop1}
  complete op := by cases op <;> simp

instance : Fintype Mark where
  elems := {L, R}
  complete a := by cases a <;> simp

theorem encode_length_bound (t : Tree) : (encode t).length ≤ 2 * weight t + 1 := by
  induction t <;> simp_all [encode, weight, List.length_append] <;> omega

abbrev SizedTree (n : Nat) := {t : Tree // weight t = n}

instance sizedTreeFinite (n : Nat) : Finite (SizedTree n) := by
  have hf := List.finite_length_le Op (2 * n + 1)
  let : Fintype {xs : List Op // xs.length ≤ 2 * n + 1} := hf.fintype
  let f : SizedTree n → {xs : List Op // xs.length ≤ 2 * n + 1} :=
    fun t => ⟨encode t.val, by simpa [t.property] using encode_length_bound t.val⟩
  have hi : Function.Injective f := by
    intro t u h
    apply Subtype.ext
    apply encode_injective
    exact congrArg Subtype.val h
  exact Finite.of_injective f hi

noncomputable instance sizedTreeFintype (n : Nat) : Fintype (SizedTree n) := Fintype.ofFinite _

abbrev Slice (n : Nat) (a : Mark) (b : Option Mark) (flag : Bool) (d : Option Mark) :=
  {t : SizedTree n // eval t.val a b flag = some d}

noncomputable def count (n : Nat) (a : Mark) (b : Option Mark) (flag : Bool) (d : Option Mark) : Nat :=
  Fintype.card (Slice n a b flag d)

noncomputable def series (a : Mark) (b : Option Mark) (flag : Bool) (d : Option Mark) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (count n a b flag d : ℤ)

abbrev Split (n : Nat) := ↥(Finset.antidiagonal n)

abbrev PairSlice (n : Nat) (c : Mark) (b d : Option Mark) :=
  Σ ij : Split n, Σ e : Mark,
    Slice ij.val.1 R (some c) false (some e) × Slice ij.val.2 e b true d

abbrev StepCases (n : Nat) (a : Mark) (b d : Option Mark) :=
  Slice n a b true d ⊕ (PairSlice n a b d ⊕ PairSlice n L b d)

def splitTree (n : Nat) (a : Mark) (b d : Option Mark) (flag : Bool) :
    Slice (n+1) a b flag d → StepCases n a b d := by
  rintro ⟨⟨t, hw⟩, he⟩
  cases t with
  | pop0 => simp [weight] at hw
  | pop1 => simp [weight] at hw
  | bypass t =>
      exact .inl ⟨⟨t, by simp [weight] at hw; omega⟩, he⟩
  | push0 s t =>
      exact match hs : eval s R (some a) false with
      | none => False.elim (by simp [eval, hs] at he)
      | some none => False.elim (by simp [eval, hs] at he)
      | some (some e) =>
          .inr (.inl ⟨⟨(weight s, weight t), by simp [Finset.mem_antidiagonal]; simp [weight] at hw; omega⟩,
            e, ⟨⟨⟨s, rfl⟩, hs⟩, ⟨⟨t, rfl⟩, by simpa [eval, hs] using he⟩⟩⟩)
  | push1 s t =>
      exact match hs : eval s R (some L) false with
      | none => False.elim (by simp [eval, hs] at he)
      | some none => False.elim (by simp [eval, hs] at he)
      | some (some e) =>
          .inr (.inr ⟨⟨(weight s, weight t), by simp [Finset.mem_antidiagonal]; simp [weight] at hw; omega⟩,
            e, ⟨⟨⟨s, rfl⟩, hs⟩, ⟨⟨t, rfl⟩, by simpa [eval, hs] using he⟩⟩⟩)

def joinTree (n : Nat) (a : Mark) (b d : Option Mark) (flag : Bool) :
    StepCases n a b d → Slice (n+1) a b flag d
  | .inl t => ⟨⟨.bypass t.val.val, by simp [weight, t.val.property, Nat.add_comm]⟩, t.property⟩
  | .inr (.inl ⟨ij, e, s, t⟩) =>
      ⟨⟨.push0 s.val.val t.val.val, by
        have hi := Finset.mem_antidiagonal.mp ij.property
        simp only [weight, s.val.property, t.val.property]; omega⟩,
        by simp [eval, s.property, t.property]⟩
  | .inr (.inr ⟨ij, e, s, t⟩) =>
      ⟨⟨.push1 s.val.val t.val.val, by
        have hi := Finset.mem_antidiagonal.mp ij.property
        simp only [weight, s.val.property, t.val.property]; omega⟩,
        by simp [eval, s.property, t.property]⟩

theorem join_split (n : Nat) (a : Mark) (b d : Option Mark) (flag : Bool)
    (t : Slice (n+1) a b flag d) : joinTree n a b d flag (splitTree n a b d flag t) = t := by
  rcases t with ⟨⟨t, hw⟩, he⟩
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
          | some e =>
              simp only [splitTree]
              split <;> simp_all [joinTree]
  | push1 s t =>
      cases hs : eval s R (some L) false with
      | none => simp [eval, hs] at he
      | some e =>
          cases e with
          | none => simp [eval, hs] at he
          | some e =>
              simp only [splitTree]
              split <;> simp_all [joinTree]

theorem split_join (n : Nat) (a : Mark) (b d : Option Mark) (flag : Bool)
    (c : StepCases n a b d) : splitTree n a b d flag (joinTree n a b d flag c) = c := by
  rcases c with t | c
  · rcases t with ⟨⟨t, hw⟩, he⟩
    rfl
  · rcases c with ⟨⟨⟨i,j⟩, hij⟩, e, ⟨⟨s, hs⟩, hse⟩, ⟨⟨t, ht⟩, hte⟩⟩ |
        ⟨⟨⟨i,j⟩, hij⟩, e, ⟨⟨s, hs⟩, hse⟩, ⟨⟨t, ht⟩, hte⟩⟩
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

def stepEquiv (n : Nat) (a : Mark) (b d : Option Mark) (flag : Bool) :
    Slice (n+1) a b flag d ≃ StepCases n a b d where
  toFun := splitTree n a b d flag
  invFun := joinTree n a b d flag
  left_inv := join_split n a b d flag
  right_inv := split_join n a b d flag


theorem count_succ (n : Nat) (a : Mark) (b d : Option Mark) (flag : Bool) :
    count (n+1) a b flag d = count n a b true d +
      (∑ ij ∈ Finset.antidiagonal n, ∑ e : Mark,
        count ij.1 R (some a) false (some e) * count ij.2 e b true d) +
      (∑ ij ∈ Finset.antidiagonal n, ∑ e : Mark,
        count ij.1 R (some L) false (some e) * count ij.2 e b true d) := by
  change Fintype.card (Slice (n+1) a b flag d) = _
  rw [Fintype.card_congr (stepEquiv n a b d flag)]
  simp [StepCases, PairSlice, count, Split, Fintype.card_sigma, Fintype.card_prod,
    Nat.add_assoc]
  exact congrArg₂ Nat.add
    (Finset.sum_attach _ (fun ij : Nat × Nat => ∑ e : Mark,
      Fintype.card (Slice ij.1 R (some a) false (some e)) * Fintype.card (Slice ij.2 e b true d)))
    (Finset.sum_attach _ (fun ij : Nat × Nat => ∑ e : Mark,
      Fintype.card (Slice ij.1 R (some L) false (some e)) * Fintype.card (Slice ij.2 e b true d)))

abbrev ZeroCases (a : Mark) (b d : Option Mark) (flag : Bool) :=
  {q : Bool // eval (if q then Tree.pop0 else Tree.pop1) a b flag = some d}

def zeroEquiv (a : Mark) (b d : Option Mark) (flag : Bool) :
    Slice 0 a b flag d ≃ ZeroCases a b d flag where
  toFun t := by
    rcases t with ⟨⟨t, hw⟩, he⟩
    cases t with
    | pop0 => exact ⟨true, he⟩
    | pop1 => exact ⟨false, he⟩
    | bypass t => simp [weight] at hw
    | push0 s t => simp [weight] at hw
    | push1 s t => simp [weight] at hw
  invFun q := ⟨⟨if q.val then .pop0 else .pop1, by cases q.val <;> rfl⟩, q.property⟩
  left_inv t := by
    rcases t with ⟨⟨t, hw⟩, he⟩
    cases t <;> simp [weight] at hw
    all_goals rfl
  right_inv q := by rcases q with ⟨q, hq⟩; cases q <;> rfl

theorem count_zero (a : Mark) (b d : Option Mark) (flag : Bool) :
    count 0 a b flag d =
      (if eval .pop0 a b flag = some d then 1 else 0) +
      (if eval .pop1 a b flag = some d then 1 else 0) := by
  change Fintype.card (Slice 0 a b flag d) = _
  rw [Fintype.card_congr (zeroEquiv a b d flag)]
  by_cases h0 : eval .pop0 a b flag = some d <;>
    by_cases h1 : eval .pop1 a b flag = some d <;>
    simp [ZeroCases, Fintype.card_subtype, Finset.filter_insert, Finset.filter_singleton, h0, h1]


#print axioms sizedTreeFinite
#print axioms count_succ
#print axioms count_zero
end StackSorting.FirstReturn
