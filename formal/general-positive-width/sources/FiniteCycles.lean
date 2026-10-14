import RectangleDarts

namespace StackSorting.GraphWidth.UCurve.PlaneGrid

/-- Explicit cyclic successor and predecessor without an external permutation
library. The existence of an index itself certifies nonempty cycle length. -/
def cycleNext {n : Nat} (i : Fin n) : Fin n :=
  if h : i.val+1 < n then ⟨i.val+1,h⟩ else ⟨0,by omega⟩

def cyclePrev {n : Nat} (i : Fin n) : Fin n :=
  if h : i.val = 0 then ⟨n-1,by have := i.isLt; omega⟩ else ⟨i.val-1,by omega⟩

theorem cyclePrev_next {n} (i : Fin n) : cyclePrev (cycleNext i) = i := by
  have hi := i.isLt
  apply Fin.ext
  simp only [cycleNext, cyclePrev]
  split <;> split <;> dsimp only at * <;> simp_all <;> omega

theorem cycleNext_prev {n} (i : Fin n) : cycleNext (cyclePrev i) = i := by
  have hi := i.isLt
  apply Fin.ext
  simp only [cycleNext, cyclePrev]
  split <;> split <;> dsimp only at * <;> simp_all <;> omega

theorem cycleNext_injective {n} {i j : Fin n} (h : cycleNext i = cycleNext j) : i = j := by
  have h' := congrArg (@cyclePrev n) h
  simpa only [cyclePrev_next] using h'

theorem cycleNext_at_successor {n} (i : Fin n) (h : i.val+1 < n) :
    (cycleNext i).val = i.val+1 := by simp [cycleNext,h]

end StackSorting.GraphWidth.UCurve.PlaneGrid
