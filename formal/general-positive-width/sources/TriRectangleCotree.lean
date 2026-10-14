import TriRectangleConnected
import FiniteIncidenceCuts

namespace StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle
open FinitePort

theorem numbered_vertex_exact {w h} (hw : 0<w) (hh : 0<h) (d e : TDart w h) :
    (vertexOrbitCount hw hh).label d=(vertexOrbitCount hw hh).label e ↔ d.tail hw hh=e.tail hw hh :=
  ((vertexOrbitCount hw hh).exact_components d e).symm.trans (vertex_orbits_exact hw hh d e)

def incidenceMap {w h} (hw : 0<w) (hh : 0<h) :
    IncidenceMap (TDart w h) ((w+1)*(h+1)+1) (2*w*h+2*w+2*h) where
  tail := (vertexOrbitCount hw hh).label
  reverse := TDart.reverse
  reverse_reverse := TDart.reverse_reverse
  face := (faceOrbitCount hw hh).label
  endpoints_injective := by
    intro d e ht hh'
    apply TDart.endpoints_injective hw hh
    · exact (numbered_vertex_exact hw hh d e).mp ht
    · exact (numbered_vertex_exact hw hh d.reverse e.reverse).mp hh'

theorem incidence_rotation_tail {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) :
    (incidenceMap hw hh).tail (d.rotate hw hh)=(incidenceMap hw hh).tail d := by
  apply (numbered_vertex_exact hw hh _ _).mpr
  exact TDart.rotate_preserves_vertex hw hh d

theorem incidence_rotation_face {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) :
    (incidenceMap hw hh).face (d.rotate hw hh)=(incidenceMap hw hh).face d.reverse := by
  apply ((faceOrbitCount hw hh).exact_components _ _).mp
  exact .step trivial (Or.inr rfl) (.refl trivial)

theorem cut_continues {w h} (hw : 0<w) (hh : 0<h) : CutContinues (incidenceMap hw hh) := by
  apply incidence_cut_continues (incidenceMap hw hh) (dartCode hw hh) (TDart.rotate hw hh)
  · intro a b h
    have he := congrArg (TDart.unrotate hw hh) h
    simpa only [TDart.unrotate_rotate] using he
  · exact incidence_rotation_tail hw hh
  · exact incidence_rotation_face hw hh

theorem dual_connected {w h} (hw : 0<w) (hh : 0<h) (a b : Fin (2*w*h+2*w+2*h)) :
    Walk (FullDualAdj (incidenceMap hw hh)) (fun _ => True) a b :=
  fullDual_connected_of_map (incidenceMap hw hh) (TDart.rotate hw hh)
    (incidence_rotation_face hw hh) (faceOrbitCount hw hh).surjective (map_connected hw hh) a b

/-- Dual adjacency after removing any actual parent tree is connected.
This instantiates the generic cut theorem with the constructed triangulation. -/
theorem dual_complement_connected {w h} (hw : 0<w) (hh : 0<h)
    (T : RootedTree ((w+1)*(h+1)+1)) (a b : Fin (2*w*h+2*w+2*h)) :
    Walk (CotreeAdj (incidenceMap hw hh) T) (fun _ => True) a b :=
  dual_complement_tree_connected (incidenceMap hw hh) T (cut_continues hw hh)
    (dual_connected hw hh) a b

end StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle
