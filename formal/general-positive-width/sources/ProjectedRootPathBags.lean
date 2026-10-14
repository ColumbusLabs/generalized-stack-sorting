import ThreeRootPathDecomposition

namespace StackSorting.GraphWidth.UCurve.PlaneGrid
open FinitePort

def rootPathLabels {V M} (T : RootedTree V) (labels : Fin V → List (Fin M)) (v : Fin V) :
    List (Fin M) := uniqueList ((rootPath T v).flatMap labels)

/-- Distinct projected labels, rather than subdivision length, control the bag.
In particular, an unlabeled apex contributes zero to this bound. -/
theorem projected_threeRootBag_bound {α V F M} (I : IncidenceMap α V F)
    (C : TriangularIncidences I) (T : RootedTree V) (labels : Fin V → List (Fin M))
    (k : Nat) (hk : ∀ v, (rootPathLabels T labels v).length≤k) (f : Fin F) :
    (uniqueList ((threeRootBag I C T f).flatMap labels)).length≤3*k := by
  let a := rootPathLabels T labels (I.tail (C.dart f 0))
  let b := rootPathLabels T labels (I.tail (C.dart f 1))
  let c := rootPathLabels T labels (I.tail (C.dart f 2))
  have hsub : uniqueList ((threeRootBag I C T f).flatMap labels) ⊆ a++b++c := by
    intro v hv
    have hm := (mem_uniqueList _ v).mp hv
    obtain ⟨x,hx,hvx⟩ := List.mem_flatMap.mp hm
    have hp := (mem_uniqueList _ x).mp hx
    simp only [List.mem_append] at hp
    obtain (h | h) | h := hp
    · apply List.mem_append.mpr; left; apply List.mem_append.mpr; left
      exact (mem_uniqueList _ v).mpr (List.mem_flatMap.mpr ⟨x,h,hvx⟩)
    · apply List.mem_append.mpr; left; apply List.mem_append.mpr; right
      exact (mem_uniqueList _ v).mpr (List.mem_flatMap.mpr ⟨x,h,hvx⟩)
    · apply List.mem_append.mpr; right
      exact (mem_uniqueList _ v).mpr (List.mem_flatMap.mpr ⟨x,h,hvx⟩)
  have hn := (uniqueList_nodup ((threeRootBag I C T f).flatMap labels)).length_le_of_subset hsub
  simp only [List.length_append] at hn
  have ha := hk (I.tail (C.dart f 0))
  have hb := hk (I.tail (C.dart f 1))
  have hc := hk (I.tail (C.dart f 2))
  change a.length≤k at ha
  change b.length≤k at hb
  change c.length≤k at hc
  omega

/-- Projecting connected label fibers keeps edge coverage and running
intersection by the existing checked lift, and the three-root-path count is
exactly 3*k with no extra apex label. -/
theorem lifted_threeRootPathDecomposition_bound {α V F M} (I : IncidenceMap α V F)
    (hl : ∀ d, I.tail d≠I.tail (I.reverse d)) (C : TriangularIncidences I)
    (T : RootedTree V) (D : ActualCotree I T)
    (hc : CutContinues I) (rot : α → α) (ht : ∀ d, I.tail (rot d)=I.tail d)
    (hf : ∀ d, I.face (rot d)=I.face (I.reverse d))
    (hv : ∀ d e, I.tail d=I.tail e → Walk (OrbitStep rot) (fun _ => True) d e)
    (hsurj : ∀ x, ∃ d, I.tail d=x)
    (hedge : ∀ x, x.val≠0 → ∃ d, I.tail d=x ∧ I.tail (I.reverse d)=T.parent x)
    (G : Graph M) (L : ConnectedLift (incidenceGraph I hl) G)
    (k : Nat) (hk : ∀ v, (rootPathLabels T L.labels v).length≤k) :
    ((threeRootPathDecomposition I hl C T D hc rot ht hf hv hsurj hedge).lift L).BagBound (3*k) := by
  intro i
  exact projected_threeRootBag_bound I C T L.labels k hk (D.code.decode i)

end StackSorting.GraphWidth.UCurve.PlaneGrid
