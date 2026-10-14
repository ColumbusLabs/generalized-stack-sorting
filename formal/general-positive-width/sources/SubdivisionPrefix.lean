import SubdivisionNumberedTree
import InheritedBranchLift

namespace StackSorting.GraphWidth.UCurve.SubdivisionTree
open FinitePort PlaneGrid

noncomputable def Realization.numberedEmbedding {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (i : Fin (embeddedList S.embed).length) : Fin m :=
  S.embed (S.numberedDecode T he root hr i)

theorem Realization.numberedDecode_injective {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0) :
    Function.Injective (S.numberedDecode T he root hr) := by
  intro i j hij
  have h := congrArg (S.numberedEncode T he root hr) hij
  simpa only [S.numbered_encode_decode] using h

theorem Realization.numberedEmbedding_injective {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0) :
    Function.Injective (S.numberedEmbedding T he root hr) := by
  intro i j hij
  exact S.numberedDecode_injective T he root hr (S.embed_injective hij)

theorem Realization.numberedEncode_root_val {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0) :
    (S.numberedEncode T he root hr (.original root)).val=0 :=
  (S.numbered_root_iff T he root hr _).mp (S.numbered_decode_encode T he root hr _)

/-- The actual embedded subdivision tree, before extending to unused target vertices.
Its root is literally the image of the source root. -/
noncomputable def Realization.prefix {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0) :
    PrescribedPrefix H.Adj (S.point root) := by
  let P := embeddedTreePrefix H (S.numberedEmbedding T he root hr)
    (S.numberedEmbedding_injective T he root hr) (S.numbered T he root hr).tree
    (S.numberedEncode T he root hr (.original root)) (S.numberedEncode_root_val T he root hr)
    (S.numbered T he root hr).parent_root
    (fun i hi => H.symm (S.numbered_parent_realized T he root hr i hi))
  exact {
    vertices := P.vertices
    nodup := P.nodup
    first := by
      rw [P.first]
      congr 1
      exact congrArg S.embed (S.numbered_decode_encode T he root hr (.original root))
    tree := P.tree
    parent_root := P.parent_root
    parent_edge := P.parent_edge
  }

noncomputable def Realization.prefixEncode {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (x : Vertex S.toRouteLengths) : Fin (S.prefix T he root hr).vertices.length :=
  prefixIndex (S.numberedEmbedding T he root hr) (S.numberedEncode T he root hr x)

noncomputable def Realization.prefixDecode {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (i : Fin (S.prefix T he root hr).vertices.length) : Vertex S.toRouteLengths :=
  S.numberedDecode T he root hr (originalIndex (S.numberedEmbedding T he root hr) i)

@[simp] theorem Realization.prefix_decode_encode {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (x : Vertex S.toRouteLengths) :
    S.prefixDecode T he root hr (S.prefixEncode T he root hr x)=x := by
  exact S.numbered_decode_encode T he root hr x

@[simp] theorem Realization.prefix_encode_decode {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (i : Fin (S.prefix T he root hr).vertices.length) :
    S.prefixEncode T he root hr (S.prefixDecode T he root hr i)=i := by
  simp only [prefixEncode,prefixDecode,S.numbered_encode_decode]
  rfl

@[simp] theorem Realization.prefix_get {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (i : Fin (S.prefix T he root hr).vertices.length) :
    (S.prefix T he root hr).vertices[i.val]=S.embed (S.prefixDecode T he root hr i) :=
  embeddedVertices_get (S.numberedEmbedding T he root hr) i

/-- Old labels are source branches after decoding the actual embedded prefix. -/
noncomputable def Realization.prefixBranch {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (i : Fin (S.prefix T he root hr).vertices.length) : Fin n :=
  branch S.toRouteLengths T (S.prefixDecode T he root hr i)

@[simp] theorem Realization.prefixBranch_encode {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (x : Vertex S.toRouteLengths) :
    S.prefixBranch T he root hr (S.prefixEncode T he root hr x)=branch S.toRouteLengths T x := by
  simp only [prefixBranch,S.prefix_decode_encode]

theorem Realization.prefixBranch_parent_ancestor {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (i : Fin (S.prefix T he root hr).vertices.length) :
    Ancestor T (S.prefixBranch T he root hr ((S.prefix T he root hr).tree.parent i))
      (S.prefixBranch T he root hr i) := by
  change Ancestor T
    (branch S.toRouteLengths T (S.numberedDecode T he root hr
      ((S.numbered T he root hr).tree.parent (originalIndex (S.numberedEmbedding T he root hr) i))))
    (branch S.toRouteLengths T (S.prefixDecode T he root hr i))
  rw [S.numbered_parent_exact]
  exact branch_parent_ancestor S.toRouteLengths T he _

theorem Realization.prefixBranch_cover {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (v : Fin n) : ∃ i, S.prefixBranch T he root hr i=v := by
  exact ⟨S.prefixEncode T he root hr (.original v),S.prefixBranch_encode T he root hr _⟩

theorem Realization.prefixBranch_edge {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    {u v : Fin n} (huv : G.Adj u v) :
    ∃ i j : Fin (S.prefix T he root hr).vertices.length,
      H.Adj (S.prefix T he root hr).vertices[i.val] (S.prefix T he root hr).vertices[j.val] ∧
      S.prefixBranch T he root hr i=u ∧ S.prefixBranch T he root hr j=v := by
  obtain ⟨x,y,hxy,hx,hy⟩ := S.source_edge_branches T he huv
  refine ⟨S.prefixEncode T he root hr x,S.prefixEncode T he root hr y,?_,?_,?_⟩
  · simpa only [S.prefix_get,S.prefix_decode_encode] using hxy
  · simpa only [S.prefixBranch_encode] using hx
  · simpa only [S.prefixBranch_encode] using hy

theorem Realization.numbered_parent_encode {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (x : Vertex S.toRouteLengths) :
    (S.numbered T he root hr).tree.parent (S.numberedEncode T he root hr x)=
      S.numberedEncode T he root hr (parent S.toRouteLengths T he x) := by
  apply S.numberedDecode_injective T he root hr
  rw [S.numbered_parent_exact,S.numbered_decode_encode,S.numbered_decode_encode]

theorem Realization.parentAdj_numbered {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    {x y : Vertex S.toRouteLengths} (h : ParentAdj S.toRouteLengths T he root x y) :
    TreeAdj (S.numbered T he root hr).tree
      (S.numberedEncode T he root hr x) (S.numberedEncode T he root hr y) := by
  have hn : ∀ z : Vertex S.toRouteLengths, z≠.original root →
      (S.numberedEncode T he root hr z).val≠0 := by
    intro z hz hzero
    have hroot := (S.numbered_root_iff T he root hr _).mpr hzero
    rw [S.numbered_decode_encode] at hroot
    exact hz hroot
  obtain ⟨hx,hy⟩ | ⟨hy,hx⟩ := h
  · exact .inl ⟨hn x hx,(S.numbered_parent_encode T he root hr x).trans
      (congrArg (S.numberedEncode T he root hr) hy)⟩
  · exact .inr ⟨hn y hy,(S.numbered_parent_encode T he root hr y).trans
      (congrArg (S.numberedEncode T he root hr) hx)⟩

theorem treeAdj_prefixIndex {l m} (f : Fin l → Fin m) (T : RootedTree l)
    {i j : Fin l} (h : TreeAdj T i j) :
    TreeAdj (prefixTree f T) (prefixIndex f i) (prefixIndex f j) := by
  obtain ⟨hi,hp⟩ | ⟨hj,hp⟩ := h
  · exact .inl ⟨hi,congrArg (prefixIndex f) hp⟩
  · exact .inr ⟨hj,congrArg (prefixIndex f) hp⟩

theorem Realization.parentAdj_prefix {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    {x y : Vertex S.toRouteLengths} (h : ParentAdj S.toRouteLengths T he root x y) :
    TreeAdj (S.prefix T he root hr).tree
      (S.prefixEncode T he root hr x) (S.prefixEncode T he root hr y) :=
  treeAdj_prefixIndex (S.numberedEmbedding T he root hr) (S.numbered T he root hr).tree
    (S.parentAdj_numbered T he root hr h)

/-- Each old branch has a prefix-tree path to the corresponding original vertex. -/
theorem Realization.prefixBranch_reaches_original {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (i : Fin (S.prefix T he root hr).vertices.length) :
    Walk (TreeAdj (S.prefix T he root hr).tree)
      (fun z => S.prefixBranch T he root hr z=S.prefixBranch T he root hr i)
      i (S.prefixEncode T he root hr (.original (S.prefixBranch T he root hr i))) := by
  have hw := S.branch_reaches_original T he root hr (S.prefixDecode T he root hr i)
  have hm := walk_map_predicate
    (Q := fun z => S.prefixBranch T he root hr z=S.prefixBranch T he root hr i)
    (S.prefixEncode T he root hr) (fun h => S.parentAdj_prefix T he root hr h)
    (fun z hz => by simpa only [prefixBranch,S.prefix_decode_encode] using hz) hw
  simpa only [S.prefix_encode_decode,prefixBranch] using hm

/-- Equal old labels have a path inside their branch in the actual prefix tree. -/
theorem Realization.prefixBranch_fiber {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (i j : Fin (S.prefix T he root hr).vertices.length)
    (hij : S.prefixBranch T he root hr i=S.prefixBranch T he root hr j) :
    Walk (TreeAdj (S.prefix T he root hr).tree)
      (fun z => S.prefixBranch T he root hr z=S.prefixBranch T he root hr i) i j := by
  have hi := S.prefixBranch_reaches_original T he root hr i
  have hj := S.prefixBranch_reaches_original T he root hr j
  rw [← hij] at hj
  exact hi.trans (hj.reverse (treeAdj_symm (S.prefix T he root hr).tree))

/-- Full connected lift obtained from an actual subdivision and an extension
preserving its embedded prefix. All branch hypotheses are proved above. -/
noncomputable def Realization.extendedBranchLift {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (E : PreservingSpanningTree (S.prefix T he root hr)) :
    ConnectedLift (reindexGraph H (spanningCode E)) G :=
  inheritedBranchLift H G (S.prefix T he root hr) E (S.prefixBranch T he root hr)
    (S.prefixBranch_cover T he root hr) (S.prefixBranch_edge T he root hr)
    (S.prefixBranch_fiber T he root hr)

/-- The source ancestor witness for every inherited label on a full root path. -/
theorem Realization.extended_root_label_ancestor {n m k} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (root : Fin n) (hr : root.val=0)
    (E : PreservingSpanningTree (S.prefix T he root hr))
    (labels : Fin n → List (Fin k)) (i : Fin m) (v : Fin k)
    (hv : v ∈ rootPathLabels E.spanning.tree
      (fun z => labels (inheritedBranch (S.prefix T he root hr) E (S.prefixBranch T he root hr) z)) i) :
    ∃ u, Ancestor T u (inheritedBranch (S.prefix T he root hr) E (S.prefixBranch T he root hr) i) ∧
      v ∈ labels u :=
  inherited_root_label_ancestor (S.prefix T he root hr) E (S.prefixBranch T he root hr) T
    (S.prefixBranch_parent_ancestor T he root hr) labels i v hv

end StackSorting.GraphWidth.UCurve.SubdivisionTree
