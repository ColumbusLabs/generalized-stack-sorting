import RectangleCotreeConnectivity

namespace StackSorting.GraphWidth.UCurve.PlaneGrid

noncomputable def embeddedList {α : Type} {m : Nat} (f : α → Fin m) : List α := by
  classical
  exact uniqueList ((List.finRange m).filterMap (fun i =>
    if h : ∃ x, f x=i then some (Classical.choose h) else none))

theorem embeddedList_complete {α : Type} {m : Nat} (f : α → Fin m)
    (hf : Function.Injective f) (x : α) : x ∈ embeddedList f := by
  classical
  unfold embeddedList
  apply (mem_uniqueList _ x).mpr
  apply List.mem_filterMap.mpr
  refine ⟨f x,List.mem_finRange _,?_⟩
  have hx : ∃ y, f y=f x := ⟨x,rfl⟩
  simp only [dite_eq_left hx]
  exact congrArg some (hf (Classical.choose_spec hx))

theorem embeddedList_nodup {α : Type} {m : Nat} (f : α → Fin m) :
    (embeddedList f).Nodup := by
  classical
  exact uniqueList_nodup _

/-- An actual injection into a finite target produces a complete finite code
for its domain. No finiteness or enumeration certificate is assumed. -/
noncomputable def embeddedCode {α : Type} {m : Nat} (f : α → Fin m)
    (hf : Function.Injective f) : FiniteCode α (embeddedList f).length := by
  classical
  exact {
    encode := fun x => ⟨(embeddedList f).idxOf x,List.idxOf_lt_length_of_mem (embeddedList_complete f hf x)⟩
    decode := fun i => (embeddedList f)[i.val]
    decode_encode := fun x => List.getElem_idxOf _
    encode_decode := by
      intro i
      apply Fin.ext
      exact (embeddedList_nodup f).idxOf_getElem i.val i.isLt
  }

end StackSorting.GraphWidth.UCurve.PlaneGrid
