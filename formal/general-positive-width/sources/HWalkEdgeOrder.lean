import HWalkOperations
import Mathlib.Data.List.Basic

namespace FiniteFlow.Hypergraph

variable {E : Type*} [DecidableEq E]

/-- The prefix before the first occurrence of `f` is precisely the set of
elements whose first index is smaller than that of `f`. -/
theorem mem_pre_iff_idxOf_lt (pre suf : List E) (a f : E) (hf : f ∉ pre) :
    a ∈ pre ↔ (pre ++ f :: suf).idxOf a < (pre ++ f :: suf).idxOf f := by
  have hp : pre <+: pre ++ f :: suf := ⟨f :: suf, rfl⟩
  rw [List.idxOf_append_of_notMem hf]
  simp only [List.idxOf_cons_self, Nat.add_zero]
  exact hp.mem_iff_idxOf_lt_length a

/-- A duplicate-free list is strictly ordered by its own first-index map. -/
theorem pairwise_idxOf (l : List E) (h : l.Nodup) :
    l.Pairwise (fun a b => l.idxOf a < l.idxOf b) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simpa only [h.idxOf_getElem] using hij

end FiniteFlow.Hypergraph
