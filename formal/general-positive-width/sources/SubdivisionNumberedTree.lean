import SubdivisionFibers
import FiniteEmbeddedCode
import RankedParentCode

namespace StackSorting.GraphWidth.UCurve.SubdivisionTree
open FinitePort PlaneGrid

noncomputable def Realization.vertexCode {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) := embeddedCode S.embed S.embed_injective

noncomputable def Realization.ranked {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0) :=
  rankedParentFromCode S.vertexCode (.original root) (parent S.toRouteLengths T he)
    (rank S.toRouteLengths T m)
    (by simp only [parent,dite_eq_left hr])
    (rank_parent_lt S.toRouteLengths T he m (fun e => Nat.le_of_lt (S.length_bound e)) root hr)

noncomputable def Realization.numbered {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0) :=
  (S.ranked T he root hr).numbered

noncomputable def Realization.numberedDecode {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (i : Fin (embeddedList S.embed).length) : Vertex S.toRouteLengths :=
  S.vertexCode.decode ((S.numbered T he root hr).label i)

noncomputable def Realization.numberedEncode {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (x : Vertex S.toRouteLengths) : Fin (embeddedList S.embed).length :=
  (S.numbered T he root hr).index (S.vertexCode.encode x)

theorem Realization.numbered_decode_encode {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (x : Vertex S.toRouteLengths) : S.numberedDecode T he root hr (S.numberedEncode T he root hr x)=x := by
  simp only [numberedDecode,numberedEncode,RankedParent.Numbered.label_index,FiniteCode.decode_encode]

theorem Realization.numbered_encode_decode {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (i : Fin (embeddedList S.embed).length) : S.numberedEncode T he root hr (S.numberedDecode T he root hr i)=i := by
  simp only [numberedDecode,numberedEncode,FiniteCode.encode_decode,RankedParent.Numbered.index_label]

theorem Realization.numbered_parent_exact {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (i : Fin (embeddedList S.embed).length) :
    S.numberedDecode T he root hr ((S.numbered T he root hr).tree.parent i)=
      parent S.toRouteLengths T he (S.numberedDecode T he root hr i) := by
  exact rankedParentFromCode_parent_exact S.vertexCode (.original root) _ _ _ _ i

theorem Realization.numbered_root_iff {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (i : Fin (embeddedList S.embed).length) :
    S.numberedDecode T he root hr i=.original root ↔ i.val=0 := by
  have h := (S.numbered T he root hr).label_eq_root_iff i
  constructor
  · intro hi
    apply h.mp
    change (S.numbered T he root hr).label i=S.vertexCode.encode (.original root)
    have heq := congrArg S.vertexCode.encode hi
    simpa only [numberedDecode,FiniteCode.encode_decode] using heq
  · intro hi
    change S.vertexCode.decode ((S.numbered T he root hr).label i)=.original root
    rw [h.mpr hi]
    exact S.vertexCode.decode_encode _

theorem Realization.numbered_parent_realized {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (i : Fin (embeddedList S.embed).length) (hi : i.val≠0) :
    H.Adj (S.embed (S.numberedDecode T he root hr i))
      (S.embed (S.numberedDecode T he root hr ((S.numbered T he root hr).tree.parent i))) := by
  rw [S.numbered_parent_exact]
  exact S.parent_nonroot_adj T he root hr _ (fun h => hi ((S.numbered_root_iff T he root hr i).mp h))

end StackSorting.GraphWidth.UCurve.SubdivisionTree
