import SubtreeFaceConnectivity

namespace StackSorting.GraphWidth.UCurve.PlaneGrid
open FinitePort

/-- The actual parent chain, including the vertex and the root once each. -/
def rootPath {n} (T : RootedTree n) (v : Fin n) : List (Fin n) :=
  if hv : v.val=0 then [v] else v :: rootPath T (T.parent v)
termination_by v.val
decreasing_by all_goals apply T.parent_lt; omega

theorem mem_rootPath {n} (T : RootedTree n) (u v : Fin n) :
    u ∈ rootPath T v ↔ Ancestor T u v := by
  rw [rootPath]
  split
  · rename_i hv
    simp only [List.mem_singleton]
    constructor
    · intro he; subst u; exact .refl _
    · intro he; apply Fin.ext; have := he.val_le; have := u.isLt; omega
  · rename_i hv
    rw [List.mem_cons,mem_rootPath T u (T.parent v)]
    constructor
    · rintro (he | he)
      · subst u; exact .refl _
      · exact .step hv he
    · intro h
      by_cases he : u=v
      · exact Or.inl he
      · exact Or.inr (h.parent_of_ne he)
termination_by v.val
decreasing_by all_goals apply T.parent_lt; omega

theorem rootPath_nodup {n} (T : RootedTree n) (v : Fin n) : (rootPath T v).Nodup := by
  rw [rootPath]
  split
  · simp
  · rename_i hv
    apply List.nodup_cons.mpr
    constructor
    · intro h
      have he := ((mem_rootPath T v (T.parent v)).mp h).val_le
      have hl := T.parent_lt v hv
      omega
    · exact rootPath_nodup T (T.parent v)
termination_by v.val
decreasing_by all_goals apply T.parent_lt; omega

/-- The face has an actual surjective list of three directed incidences.
This is geometric input to be proved by the explicit triangulation. -/
structure TriangularIncidences {α V F} (I : IncidenceMap α V F) where
  dart : Fin F → Fin 3 → α
  face : ∀ f i, I.face (dart f i)=f
  complete : ∀ d, ∃ i, dart (I.face d) i=d

def threeRootBag {α V F} (I : IncidenceMap α V F) (C : TriangularIncidences I)
    (T : RootedTree V) (f : Fin F) : List (Fin V) :=
  uniqueList (rootPath T (I.tail (C.dart f 0)) ++
    rootPath T (I.tail (C.dart f 1)) ++ rootPath T (I.tail (C.dart f 2)))

theorem mem_threeRootBag {α V F} (I : IncidenceMap α V F) (C : TriangularIncidences I)
    (T : RootedTree V) (f : Fin F) (v : Fin V) :
    v ∈ threeRootBag I C T f ↔ SubtreeFace I T v f := by
  simp only [threeRootBag,mem_uniqueList,List.mem_append,mem_rootPath]
  constructor
  · rintro ((h | h) | h)
    · exact ⟨C.dart f 0,C.face f 0,h⟩
    · exact ⟨C.dart f 1,C.face f 1,h⟩
    · exact ⟨C.dart f 2,C.face f 2,h⟩
  · rintro ⟨d,hd,hv⟩
    obtain ⟨i,hi⟩ := C.complete d
    rw [hd] at hi
    have hn := i.isLt
    have hc : i=0 ∨ i=1 ∨ i=2 := by omega
    obtain rfl | rfl | rfl := hc
    · exact Or.inl (Or.inl (hi ▸ hv))
    · exact Or.inl (Or.inr (hi ▸ hv))
    · exact Or.inr (hi ▸ hv)

theorem threeRootBag_nodup {α V F} (I : IncidenceMap α V F) (C : TriangularIncidences I)
    (T : RootedTree V) (f : Fin F) : (threeRootBag I C T f).Nodup := uniqueList_nodup _

theorem threeRootBag_bound {α V F} (I : IncidenceMap α V F) (C : TriangularIncidences I)
    (T : RootedTree V) (k : Nat) (hdepth : ∀ v, (rootPath T v).length≤k) (f : Fin F) :
    (threeRootBag I C T f).length≤3*k := by
  have h := uniqueList_length_le (rootPath T (I.tail (C.dart f 0)) ++
    rootPath T (I.tail (C.dart f 1)) ++ rootPath T (I.tail (C.dart f 2)))
  simp only [List.length_append] at h
  have h0 := hdepth (I.tail (C.dart f 0))
  have h1 := hdepth (I.tail (C.dart f 1))
  have h2 := hdepth (I.tail (C.dart f 2))
  change (uniqueList _).length≤3*k
  omega

end StackSorting.GraphWidth.UCurve.PlaneGrid
