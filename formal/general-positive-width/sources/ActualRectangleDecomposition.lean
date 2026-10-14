import ActualRectangleGraph

namespace StackSorting.GraphWidth

/-- Change only the graph argument of a decomposition along graph equality.
Keeping the fields explicit makes its bags definitionally unchanged. -/
def Decomposition.transportGraph {n t} {G H : Graph n} {T : FinitePort.RootedTree t}
    (D : Decomposition G T) (h : G=H) : Decomposition H T where
  bag := D.bag
  nodup := D.nodup
  vertex := D.vertex
  edge := by cases h; exact D.edge
  running := D.running

@[simp] theorem Decomposition.transportGraph_bag {n t} {G H : Graph n}
    {T : FinitePort.RootedTree t} (D : Decomposition G T) (h : G=H) (i : Fin t) :
    (D.transportGraph h).bag i=D.bag i := rfl

end StackSorting.GraphWidth

namespace StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle
open FinitePort SubdivisionTree

/-- The reviewed exact three-root-path decomposition, now typed over the
actual reindexed rectangle graph. All bags are literally preserved. -/
noncomputable def actualDecomposition {w h} (hw : 0<w) (hh : 0<h)
    (R : FiniteCode (Fin ((w+1)*(h+1)+1)) ((w+1)*(h+1)+1))
    (T : RootedTree ((w+1)*(h+1)+1))
    (hedge : ∀ x, x.val≠0 → (reindexGraph (actualGraph hw hh) R).Adj x (T.parent x)) :
    Decomposition (reindexGraph (actualGraph hw hh) R)
      (cotree hw hh R T (actual_parent_darts hw hh R T hedge)).tree :=
  (decomposition hw hh R T (actual_parent_darts hw hh R T hedge)).transportGraph
    (reindex_actualGraph_eq hw hh R).symm

@[simp] theorem actualDecomposition_bag {w h} (hw : 0<w) (hh : 0<h)
    (R : FiniteCode (Fin ((w+1)*(h+1)+1)) ((w+1)*(h+1)+1))
    (T : RootedTree ((w+1)*(h+1)+1))
    (hedge : ∀ x, x.val≠0 → (reindexGraph (actualGraph hw hh) R).Adj x (T.parent x))
    (i : Fin (2*w*h+2*w+2*h)) :
    (actualDecomposition hw hh R T hedge).bag i=
      threeRootBag (numberedIncidence hw hh R) (triangles hw hh R) T
        ((cotree hw hh R T (actual_parent_darts hw hh R T hedge)).code.decode i) := rfl

/-- Distinct labels along the actual primal root paths bound the projected
bags; there is no dependence on the lengths of the subdivided grid routes. -/
theorem actualDecomposition_projected_bag_bound {w h M} (hw : 0<w) (hh : 0<h)
    (R : FiniteCode (Fin ((w+1)*(h+1)+1)) ((w+1)*(h+1)+1))
    (T : RootedTree ((w+1)*(h+1)+1))
    (hedge : ∀ x, x.val≠0 → (reindexGraph (actualGraph hw hh) R).Adj x (T.parent x))
    (labels : Fin ((w+1)*(h+1)+1) → List (Fin M))
    (k : Nat) (hk : ∀ v, (rootPathLabels T labels v).length≤k)
    (i : Fin (2*w*h+2*w+2*h)) :
    (uniqueList (((actualDecomposition hw hh R T hedge).bag i).flatMap labels)).length≤3*k :=
  projected_threeRootBag_bound (numberedIncidence hw hh R) (triangles hw hh R)
    T labels k hk ((cotree hw hh R T (actual_parent_darts hw hh R T hedge)).code.decode i)

/-- Any connected-fiber lift of the actual rectangle inherits the projected
three-root-path bound with its exact labels and the constructed dual tree. -/
theorem actualDecomposition_lift_bagBound {w h M} (hw : 0<w) (hh : 0<h)
    (R : FiniteCode (Fin ((w+1)*(h+1)+1)) ((w+1)*(h+1)+1))
    (T : RootedTree ((w+1)*(h+1)+1))
    (hedge : ∀ x, x.val≠0 → (reindexGraph (actualGraph hw hh) R).Adj x (T.parent x))
    (G : Graph M) (L : ConnectedLift (reindexGraph (actualGraph hw hh) R) G)
    (k : Nat) (hk : ∀ v, (rootPathLabels T L.labels v).length≤k) :
    ((actualDecomposition hw hh R T hedge).lift L).BagBound (3*k) := by
  intro i
  exact actualDecomposition_projected_bag_bound hw hh R T hedge L.labels k hk i

/-- The direct existential endpoint for source-graph reconstruction. -/
theorem exists_actual_lift_decomposition {w h M} (hw : 0<w) (hh : 0<h)
    (R : FiniteCode (Fin ((w+1)*(h+1)+1)) ((w+1)*(h+1)+1))
    (T : RootedTree ((w+1)*(h+1)+1))
    (hedge : ∀ x, x.val≠0 → (reindexGraph (actualGraph hw hh) R).Adj x (T.parent x))
    (G : Graph M) (L : ConnectedLift (reindexGraph (actualGraph hw hh) R) G)
    (k : Nat) (hk : ∀ v, (rootPathLabels T L.labels v).length≤k) :
    ∃ D : Decomposition G (cotree hw hh R T (actual_parent_darts hw hh R T hedge)).tree,
      D.BagBound (3*k) :=
  ⟨(actualDecomposition hw hh R T hedge).lift L,
    actualDecomposition_lift_bagBound hw hh R T hedge G L k hk⟩

end StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle
