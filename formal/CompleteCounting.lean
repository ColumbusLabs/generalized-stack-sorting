import GrammarCounting

namespace StackSorting.FirstReturn
open StackSorting Mark Op

theorem pathEncode_length_bound (p : Path) :
    (pathEncode p).length ≤ 2 * pathWeight p := by
  induction p with
  | nil => simp [pathEncode, pathWeight]
  | bypass p ih => simp only [pathEncode, List.length_cons, pathWeight]; omega
  | push t p ih =>
      have ht := encode_length_bound t
      simp only [pathEncode, List.length_cons, List.length_append, pathWeight]
      omega

abbrev SizedPath (n : Nat) := {p : Path // pathWeight p = n}

instance sizedPathFinite (n : Nat) : Finite (SizedPath n) := by
  let : Fintype {xs : List Op // xs.length ≤ 2 * n} := (List.finite_length_le Op (2*n)).fintype
  let f : SizedPath n → {xs : List Op // xs.length ≤ 2*n} :=
    fun p => ⟨pathEncode p.val, by simpa [p.property] using pathEncode_length_bound p.val⟩
  have hi : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    exact pathEncode_injective (congrArg Subtype.val h)
  exact Finite.of_injective f hi

noncomputable instance (n : Nat) : Fintype (SizedPath n) := Fintype.ofFinite _

abbrev PathSlice (n : Nat) := {p : SizedPath n // Valid p.val}

noncomputable def pathCount (n : Nat) : Nat := Fintype.card (PathSlice n)
noncomputable def pathSeries : PowerSeries ℤ := PowerSeries.mk fun n => (pathCount n : ℤ)

abbrev PathCases (n : Nat) := PathSlice n ⊕
  (Σ ij : Split n, Slice ij.val.1 L none false none × PathSlice ij.val.2)

def pathSplit (n : Nat) : PathSlice (n+1) → PathCases n := by
  rintro ⟨⟨p, hw⟩, hp⟩
  cases p with
  | nil => simp [pathWeight] at hw
  | bypass p => exact .inl ⟨⟨p, by simp [pathWeight] at hw; omega⟩, hp⟩
  | push t p =>
      exact .inr ⟨⟨(weight t, pathWeight p), by
        simp [Finset.mem_antidiagonal]; simp [pathWeight] at hw; omega⟩,
        ⟨⟨⟨t, rfl⟩, hp.1⟩, ⟨⟨p, rfl⟩, hp.2⟩⟩⟩

def pathJoin (n : Nat) : PathCases n → PathSlice (n+1)
  | .inl p => ⟨⟨.bypass p.val.val, by simp [pathWeight, p.val.property, Nat.add_comm]⟩, p.property⟩
  | .inr ⟨ij, t, p⟩ => ⟨⟨.push t.val.val p.val.val, by
      have hi := Finset.mem_antidiagonal.mp ij.property
      simp only [pathWeight, t.val.property, p.val.property]; omega⟩,
      ⟨t.property, p.property⟩⟩

def pathStepEquiv (n : Nat) : PathSlice (n+1) ≃ PathCases n where
  toFun := pathSplit n
  invFun := pathJoin n
  left_inv p := by
    rcases p with ⟨⟨p, hw⟩, hp⟩
    cases p with
    | nil => simp [pathWeight] at hw
    | bypass p => rfl
    | push t p => rfl
  right_inv c := by
    rcases c with p | ⟨⟨⟨i,j⟩, hij⟩, ⟨⟨t, ht⟩, hte⟩, ⟨⟨p, hp⟩, hpe⟩⟩
    · rcases p with ⟨⟨p, hw⟩, hp⟩; rfl
    · change weight t = i at ht
      change pathWeight p = j at hp
      subst i
      subst j
      rfl

theorem pathCount_succ (n : Nat) :
    pathCount (n+1) = pathCount n +
      ∑ ij ∈ Finset.antidiagonal n, count ij.1 L none false none * pathCount ij.2 := by
  change Fintype.card (PathSlice (n+1)) = _
  rw [Fintype.card_congr (pathStepEquiv n)]
  simp [PathCases, pathCount, count, Split, Fintype.card_sigma, Fintype.card_prod]
  exact Finset.sum_attach _ (fun ij : Nat × Nat =>
    Fintype.card (Slice ij.1 L none false none) * Fintype.card (PathSlice ij.2))

theorem pathCount_zero : pathCount 0 = 1 := by
  have hnil (p : PathSlice 0) : p.val.val = .nil := by
    rcases p with ⟨⟨p, hw⟩, hp⟩
    cases p with
    | nil => rfl
    | bypass p => simp [pathWeight] at hw
    | push t p => simp [pathWeight] at hw
  let e : PathSlice 0 ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => ⟨⟨.nil, rfl⟩, trivial⟩
    left_inv := fun p => by apply Subtype.ext; apply Subtype.ext; exact (hnil p).symm
    right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_unit)

#print axioms pathCount_succ
#print axioms pathCount_zero
end StackSorting.FirstReturn
