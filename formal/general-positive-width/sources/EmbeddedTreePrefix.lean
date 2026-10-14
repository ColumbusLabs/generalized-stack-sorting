import PreservingSpanningTree
import RootPathBags

namespace StackSorting.GraphWidth.UCurve.SubdivisionTree
open FinitePort PlaneGrid

def embeddedVertices {l m} (f : Fin l → Fin m) : List (Fin m) := (List.finRange l).map f

@[simp] theorem embeddedVertices_length {l m} (f : Fin l → Fin m) :
    (embeddedVertices f).length=l := by simp [embeddedVertices]

def prefixIndex {l m} (f : Fin l → Fin m) (i : Fin l) : Fin (embeddedVertices f).length :=
  ⟨i.val,by simpa only [embeddedVertices_length] using i.isLt⟩

def originalIndex {l m} (f : Fin l → Fin m) (i : Fin (embeddedVertices f).length) : Fin l :=
  ⟨i.val,by simpa only [embeddedVertices_length] using i.isLt⟩

@[simp] theorem original_prefix_index {l m} (f : Fin l → Fin m) (i : Fin l) :
    originalIndex f (prefixIndex f i)=i := rfl

@[simp] theorem prefix_original_index {l m} (f : Fin l → Fin m) (i : Fin (embeddedVertices f).length) :
    prefixIndex f (originalIndex f i)=i := rfl

@[simp] theorem embeddedVertices_get {l m} (f : Fin l → Fin m) (i : Fin (embeddedVertices f).length) :
    (embeddedVertices f)[i.val]=f (originalIndex f i) := by
  simp only [embeddedVertices,List.getElem_map,List.getElem_finRange,originalIndex]
  congr 1

def prefixTree {l m} (f : Fin l → Fin m) (T : RootedTree l) :
    RootedTree (embeddedVertices f).length where
  parent := fun i => prefixIndex f (T.parent (originalIndex f i))
  parent_lt := fun i hi => T.parent_lt (originalIndex f i) hi

@[simp] theorem prefixTree_parent {l m} (f : Fin l → Fin m) (T : RootedTree l) (i : Fin l) :
    (prefixTree f T).parent (prefixIndex f i)=prefixIndex f (T.parent i) := rfl

/-- Turn an injectively embedded actual parent tree into the concrete prefix
expected by the already constructed parent-preserving spanning extension. -/
def embeddedTreePrefix {l m} (H : Graph m) (f : Fin l → Fin m) (hf : Function.Injective f)
    (T : RootedTree l) (r : Fin l) (hr : r.val=0)
    (hroot : ∀ i, i.val=0 → T.parent i=i)
    (hedge : ∀ i, i.val≠0 → H.Adj (f (T.parent i)) (f i)) :
    PrescribedPrefix H.Adj (f r) where
  vertices := embeddedVertices f
  nodup := (List.nodup_finRange _).map f (fun _ _ hn he => hn (hf he))
  first := by
    have hp : 0<(embeddedVertices f).length := by rw [embeddedVertices_length]; have := r.isLt; omega
    rw [List.getElem?_eq_getElem hp]
    congr 1
    have he : (⟨0,hp⟩ : Fin (embeddedVertices f).length)=prefixIndex f r := Fin.ext hr.symm
    exact (embeddedVertices_get f ⟨0,hp⟩).trans
      (congrArg f (Fin.ext hr.symm))
  tree := prefixTree f T
  parent_root := by
    intro i hi
    change prefixIndex f (T.parent (originalIndex f i))=i
    rw [hroot (originalIndex f i) hi,prefix_original_index]
  parent_edge := by
    intro i hi
    rw [embeddedVertices_get,embeddedVertices_get]
    change H.Adj (f (T.parent (originalIndex f i))) (f (originalIndex f i))
    exact hedge (originalIndex f i) hi

end StackSorting.GraphWidth.UCurve.SubdivisionTree
