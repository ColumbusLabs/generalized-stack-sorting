import EmbeddedTreePrefix
import ProjectedRootPathBags

namespace StackSorting.GraphWidth.UCurve.SubdivisionTree
open FinitePort PlaneGrid

/-- A fresh extension vertex inherits the branch of its actual parent. The
old branch assignments are unchanged, so no new source label is introduced. -/
noncomputable def inheritedBranch {m n} {H : Graph m} {root : Fin m}
    (P : PrescribedPrefix H.Adj root) (E : PreservingSpanningTree P)
    (old : Fin P.vertices.length → Fin n) (i : Fin m) : Fin n :=
  if hi : i.val<P.vertices.length then old ⟨i.val,hi⟩
    else inheritedBranch P E old (E.spanning.tree.parent i)
termination_by i.val
decreasing_by
  apply E.spanning.tree.parent_lt
  have hp := P.length_pos
  omega

theorem inheritedBranch_old {m n} {H : Graph m} {root : Fin m}
    (P : PrescribedPrefix H.Adj root) (E : PreservingSpanningTree P)
    (old : Fin P.vertices.length → Fin n) (i : Fin P.vertices.length) :
    inheritedBranch P E old (P.embed i)=old i := by
  rw [inheritedBranch]
  exact dite_eq_left i.isLt

theorem inheritedBranch_parent_ancestor {m n} {H : Graph m} {root : Fin m}
    (P : PrescribedPrefix H.Adj root) (E : PreservingSpanningTree P)
    (old : Fin P.vertices.length → Fin n) (T : RootedTree n)
    (hparent : ∀ i, Ancestor T (old (P.tree.parent i)) (old i)) (i : Fin m) :
    Ancestor T (inheritedBranch P E old (E.spanning.tree.parent i)) (inheritedBranch P E old i) := by
  by_cases hi : i.val<P.vertices.length
  · let j : Fin P.vertices.length := ⟨i.val,hi⟩
    have hj : P.embed j=i := rfl
    rw [← hj,E.parents,inheritedBranch_old,inheritedBranch_old]
    exact hparent j
  · conv => rhs; rw [inheritedBranch,dite_eq_right hi]
    exact .refl _

theorem inheritedBranch_ancestor {m n} {H : Graph m} {root : Fin m}
    (P : PrescribedPrefix H.Adj root) (E : PreservingSpanningTree P)
    (old : Fin P.vertices.length → Fin n) (T : RootedTree n)
    (hparent : ∀ i, Ancestor T (old (P.tree.parent i)) (old i))
    {i j : Fin m} (h : Ancestor E.spanning.tree i j) :
    Ancestor T (inheritedBranch P E old i) (inheritedBranch P E old j) := by
  induction h with
  | refl => exact .refl _
  | @step v _ _ ih => exact ih.trans (inheritedBranch_parent_ancestor P E old T hparent v)

/-- Every fresh branch reaches an old vertex of the same branch. -/
theorem inheritedBranch_reaches_old {m n} {H : Graph m} {root : Fin m}
    (P : PrescribedPrefix H.Adj root) (E : PreservingSpanningTree P)
    (old : Fin P.vertices.length → Fin n) (i : Fin m) :
    ∃ j : Fin P.vertices.length,
      Walk (TreeAdj E.spanning.tree) (fun z => inheritedBranch P E old z=inheritedBranch P E old i)
        i (P.embed j) ∧ old j=inheritedBranch P E old i := by
  by_cases hi : i.val<P.vertices.length
  · let j : Fin P.vertices.length := ⟨i.val,hi⟩
    have hj : P.embed j=i := rfl
    refine ⟨j,?_,?_⟩
    · rw [hj]; exact .refl rfl
    · rw [← hj,inheritedBranch_old]
  · have hn : i.val≠0 := by have hp := P.length_pos; omega
    have heq : inheritedBranch P E old i=inheritedBranch P E old (E.spanning.tree.parent i) := by
      rw [inheritedBranch,dite_eq_right hi]
    obtain ⟨j,hj,hb⟩ := inheritedBranch_reaches_old P E old (E.spanning.tree.parent i)
    rw [← heq] at hj hb
    exact ⟨j,.step rfl (Or.inl ⟨hn,rfl⟩) hj,hb⟩
termination_by i.val
decreasing_by exact E.spanning.tree.parent_lt i hn

/-- Connected old fibers stay connected after the parent-preserving extension,
since every newly attached branch inherits its attachment's label. -/
theorem inheritedBranch_fiber {m n} {H : Graph m} {root : Fin m}
    (P : PrescribedPrefix H.Adj root) (E : PreservingSpanningTree P)
    (old : Fin P.vertices.length → Fin n)
    (hold : ∀ i j, old i=old j → Walk (TreeAdj P.tree) (fun z => old z=old i) i j)
    {i j : Fin m} (hij : inheritedBranch P E old i=inheritedBranch P E old j) :
    Walk (TreeAdj E.spanning.tree) (fun z => inheritedBranch P E old z=inheritedBranch P E old i) i j := by
  obtain ⟨a,hia,ha⟩ := inheritedBranch_reaches_old P E old i
  obtain ⟨b,hjb,hb⟩ := inheritedBranch_reaches_old P E old j
  have hab : old a=old b := ha.trans (hij.trans hb.symm)
  have oldwalk := hold a b hab
  have mid : Walk (TreeAdj E.spanning.tree)
      (fun z => inheritedBranch P E old z=inheritedBranch P E old i) (P.embed a) (P.embed b) := by
    apply E.walk_preserved
    exact oldwalk.mono (fun z hz => by rw [inheritedBranch_old]; exact hz.trans ha)
  rw [← hij] at hjb
  exact hia.trans (mid.trans (hjb.reverse (treeAdj_symm E.spanning.tree)))

/-- Every projected label on a full root path already labels a source ancestor
of the endpoint branch. Repetition and extension length are irrelevant. -/
theorem inherited_root_label_ancestor {m n k} {H : Graph m} {root : Fin m}
    (P : PrescribedPrefix H.Adj root) (E : PreservingSpanningTree P)
    (old : Fin P.vertices.length → Fin n) (T : RootedTree n)
    (hparent : ∀ i, Ancestor T (old (P.tree.parent i)) (old i))
    (labels : Fin n → List (Fin k)) (i : Fin m) (v : Fin k)
    (hv : v ∈ rootPathLabels E.spanning.tree (fun z => labels (inheritedBranch P E old z)) i) :
    ∃ u, Ancestor T u (inheritedBranch P E old i) ∧ v ∈ labels u := by
  obtain ⟨j,hj,hv⟩ := List.mem_flatMap.mp ((mem_uniqueList _ v).mp hv)
  exact ⟨inheritedBranch P E old j,
    inheritedBranch_ancestor P E old T hparent ((mem_rootPath _ j i).mp hj),hv⟩

end StackSorting.GraphWidth.UCurve.SubdivisionTree
