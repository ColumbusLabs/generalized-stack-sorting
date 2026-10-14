import ActualCountsDegreeTwelve
open StackSorting.Generalized
open ActualCounting
example (n : Nat) (input : List Nat) :
    input ∈ oneBasedSortableInputs 2 2 n ↔
      input.Perm (List.range' 1 n) ∧ CanSort 3 3 input :=
  mem_oneBasedSortableInputs_iff (r := 3) (s := 3) (by decide) (by decide) input
