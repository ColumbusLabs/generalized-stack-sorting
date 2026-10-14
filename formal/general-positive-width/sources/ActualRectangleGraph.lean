import SourceApexRealization
import SubdivisionRelabel

namespace StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle
open SubdivisionTree

/-- Rotating a dart leaves its primal vertex fixed; reversing a dart is an
actual edge of the constructed triangulated rectangle. -/
theorem mapStep_actualGraph_walk {w h} (hw : 0<w) (hh : 0<h)
    {d e : TDart w h} (hs : MapStep hw hh d e) :
    Walk (actualGraph hw hh).Adj (fun _ => True)
      ((incidenceMap hw hh).tail d) ((incidenceMap hw hh).tail e) := by
  obtain hs | hs := hs
  · obtain hs | hs := hs
    · have he := (incidence_rotation_tail hw hh d).symm.trans
        (congrArg (incidenceMap hw hh).tail hs)
      rw [he]
      exact .refl trivial
    · have he := (incidence_rotation_tail hw hh e).symm.trans
        (congrArg (incidenceMap hw hh).tail hs)
      rw [he]
      exact .refl trivial
  · obtain hs | hs := hs
    · exact .step trivial ⟨d,rfl,congrArg (incidenceMap hw hh).tail hs⟩ (.refl trivial)
    · exact .step trivial ((actualGraph hw hh).symm
        ⟨e,rfl,congrArg (incidenceMap hw hh).tail hs⟩) (.refl trivial)

theorem mapWalk_actualGraph_walk {w h} (hw : 0<w) (hh : 0<h)
    {d e : TDart w h} (hp : Walk (MapStep hw hh) (fun _ => True) d e) :
    Walk (actualGraph hw hh).Adj (fun _ => True)
      ((incidenceMap hw hh).tail d) ((incidenceMap hw hh).tail e) := by
  induction hp with
  | refl => exact .refl trivial
  | step _ hs _ ih => exact (mapStep_actualGraph_walk hw hh hs).trans ih

/-- Connectedness is proved from the constructed dart rotations and reversals,
with no assumed plane or graph-connectedness certificate. -/
theorem actualGraph_connected {w h} (hw : 0<w) (hh : 0<h)
    (u v : Fin ((w+1)*(h+1)+1)) :
    Walk (actualGraph hw hh).Adj (fun _ => True) u v := by
  obtain ⟨d,hd⟩ := (vertexOrbitCount hw hh).surjective u
  obtain ⟨e,he⟩ := (vertexOrbitCount hw hh).surjective v
  have hp := mapWalk_actualGraph_walk hw hh (map_connected hw hh d e)
  change (incidenceMap hw hh).tail d=u at hd
  change (incidenceMap hw hh).tail e=v at he
  simpa only [hd,he] using hp

/-- Renumbering the original graph agrees edge-for-edge with renumbering the
actual incidence map. The dart, face, and endpoint data are unchanged. -/
theorem reindex_actualGraph_adj_iff {w h} (hw : 0<w) (hh : 0<h)
    (R : FiniteCode (Fin ((w+1)*(h+1)+1)) ((w+1)*(h+1)+1))
    (u v : Fin ((w+1)*(h+1)+1)) :
    (reindexGraph (actualGraph hw hh) R).Adj u v ↔
      (incidenceGraph (numberedIncidence hw hh R) (numbered_loopless hw hh R)).Adj u v := by
  constructor
  · rintro ⟨d,hd,he⟩
    exact ⟨d,(congrArg R.encode hd).trans (R.encode_decode u),
      (congrArg R.encode he).trans (R.encode_decode v)⟩
  · rintro ⟨d,hd,he⟩
    refine ⟨d,?_,?_⟩
    · exact (R.decode_encode ((incidenceMap hw hh).tail d)).symm.trans (congrArg R.decode hd)
    · exact (R.decode_encode ((incidenceMap hw hh).tail d.reverse)).symm.trans (congrArg R.decode he)

private theorem graph_eq_of_adj_iff {n} (G H : Graph n)
    (h : ∀ u v, G.Adj u v ↔ H.Adj u v) : G=H := by
  cases G with
  | mk a asym aloop =>
    cases H with
    | mk b bsym bloop =>
      have he : a=b := funext (fun u => funext (fun v => propext (h u v)))
      cases he
      rfl

/-- Equality of finite graph structures, not just an isomorphism. -/
theorem reindex_actualGraph_eq {w h} (hw : 0<w) (hh : 0<h)
    (R : FiniteCode (Fin ((w+1)*(h+1)+1)) ((w+1)*(h+1)+1)) :
    reindexGraph (actualGraph hw hh) R=
      incidenceGraph (numberedIncidence hw hh R) (numbered_loopless hw hh R) :=
  graph_eq_of_adj_iff _ _ (reindex_actualGraph_adj_iff hw hh R)

/-- The parent edges of any actual reindexed tree supply the exact dart
witnesses required by the reviewed triangulated-rectangle construction. -/
theorem actual_parent_darts {w h} (hw : 0<w) (hh : 0<h)
    (R : FiniteCode (Fin ((w+1)*(h+1)+1)) ((w+1)*(h+1)+1))
    (T : FinitePort.RootedTree ((w+1)*(h+1)+1))
    (hedge : ∀ x, x.val≠0 → (reindexGraph (actualGraph hw hh) R).Adj x (T.parent x)) :
    ∀ x, x.val≠0 → ∃ d, (numberedIncidence hw hh R).tail d=x ∧
      (numberedIncidence hw hh R).tail d.reverse=T.parent x := by
  intro x hx
  exact (reindex_actualGraph_adj_iff hw hh R x (T.parent x)).mp (hedge x hx)

end StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle
