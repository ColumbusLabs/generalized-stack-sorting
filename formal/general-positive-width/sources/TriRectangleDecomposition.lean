import ProjectedRootPathBags
import TriRectangleCorners

namespace StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle
open FinitePort

/-- Renumber only the primal vertices; darts, edge orbits, and faces stay fixed. -/
def numberedIncidence {w h} (hw : 0<w) (hh : 0<h)
    (R : FiniteCode (Fin ((w+1)*(h+1)+1)) ((w+1)*(h+1)+1)) :
    IncidenceMap (TDart w h) ((w+1)*(h+1)+1) (2*w*h+2*w+2*h) where
  tail := fun d => R.encode ((incidenceMap hw hh).tail d)
  reverse := TDart.reverse
  reverse_reverse := TDart.reverse_reverse
  face := (incidenceMap hw hh).face
  endpoints_injective := fun h h' => (incidenceMap hw hh).endpoints_injective (R.injective h) (R.injective h')

def triangles {w h} (hw : 0<w) (hh : 0<h)
    (R : FiniteCode (Fin ((w+1)*(h+1)+1)) ((w+1)*(h+1)+1)) :
    TriangularIncidences (numberedIncidence hw hh R) where
  dart := corner hw hh
  face := corner_face hw hh
  complete := corner_covers hw hh

theorem numbered_loopless {w h} (hw : 0<w) (hh : 0<h)
    (R : FiniteCode (Fin ((w+1)*(h+1)+1)) ((w+1)*(h+1)+1)) (d : TDart w h) :
    (numberedIncidence hw hh R).tail d≠(numberedIncidence hw hh R).tail d.reverse := by
  intro he
  have h : d=d.reverse := (numberedIncidence hw hh R).endpoints_injective he
    (by change (numberedIncidence hw hh R).tail d.reverse=(numberedIncidence hw hh R).tail d.reverse.reverse; rw [TDart.reverse_reverse]; exact he.symm)
  exact TDart.reverse_ne d h.symm

theorem numbered_rotation_tail {w h} (hw : 0<w) (hh : 0<h)
    (R : FiniteCode (Fin ((w+1)*(h+1)+1)) ((w+1)*(h+1)+1)) (d : TDart w h) :
    (numberedIncidence hw hh R).tail (d.rotate hw hh)=(numberedIncidence hw hh R).tail d :=
  congrArg R.encode (incidence_rotation_tail hw hh d)

theorem numbered_rotation_face {w h} (hw : 0<w) (hh : 0<h)
    (R : FiniteCode (Fin ((w+1)*(h+1)+1)) ((w+1)*(h+1)+1)) (d : TDart w h) :
    (numberedIncidence hw hh R).face (d.rotate hw hh)=(numberedIncidence hw hh R).face d.reverse :=
  incidence_rotation_face hw hh d

theorem numbered_vertex_orbits {w h} (hw : 0<w) (hh : 0<h)
    (R : FiniteCode (Fin ((w+1)*(h+1)+1)) ((w+1)*(h+1)+1)) (d e : TDart w h)
    (he : (numberedIncidence hw hh R).tail d=(numberedIncidence hw hh R).tail e) :
    Walk (OrbitStep (TDart.rotate hw hh)) (fun _ => True) d e :=
  ((vertexOrbitCount hw hh).exact_components d e).mpr (R.injective he)

theorem numbered_vertex_surjective {w h} (hw : 0<w) (hh : 0<h)
    (R : FiniteCode (Fin ((w+1)*(h+1)+1)) ((w+1)*(h+1)+1))
    (v : Fin ((w+1)*(h+1)+1)) : ∃ d, (numberedIncidence hw hh R).tail d=v := by
  obtain ⟨d,hd⟩ := (vertexOrbitCount hw hh).surjective (R.decode v)
  exact ⟨d,by change R.encode ((vertexOrbitCount hw hh).label d)=v; rw [hd,R.encode_decode]⟩

theorem numbered_cut_continues {w h} (hw : 0<w) (hh : 0<h)
    (R : FiniteCode (Fin ((w+1)*(h+1)+1)) ((w+1)*(h+1)+1)) :
    CutContinues (numberedIncidence hw hh R) := by
  apply incidence_cut_continues (numberedIncidence hw hh R) (dartCode hw hh) (TDart.rotate hw hh)
  · intro a b he
    have h := congrArg (TDart.unrotate hw hh) he
    simpa only [TDart.unrotate_rotate] using h
  · exact numbered_rotation_tail hw hh R
  · exact numbered_rotation_face hw hh R

theorem euler_edges_split {w h} (hw : 0<w) (hh : 0<h) :
    ((w+1)*(h+1)+1-1)+(2*w*h+2*w+2*h-1)=3*w*h+3*w+3*h := by
  have he := euler_identity w h
  have hp : 0<2*w*h+2*w+2*h := by omega
  omega

/-- Actual dual parent tree of the explicit triangulation, for any realized
primal parent tree in any vertex numbering. -/
noncomputable def cotree {w h} (hw : 0<w) (hh : 0<h)
    (R : FiniteCode (Fin ((w+1)*(h+1)+1)) ((w+1)*(h+1)+1))
    (T : RootedTree ((w+1)*(h+1)+1))
    (hedge : ∀ x, x.val≠0 → ∃ d, (numberedIncidence hw hh R).tail d=x ∧
      (numberedIncidence hw hh R).tail d.reverse=T.parent x) :
    ActualCotree (numberedIncidence hw hh R) T :=
  actualCotree (numberedIncidence hw hh R) (edgeOrbitCount hw hh) T
    (numbered_cut_continues hw hh R) (dual_connected hw hh) hedge (euler_edges_split hw hh)
    ⟨0,by omega⟩

/-- A fully constructed three-root-path decomposition of the triangulated
rectangle. Only the chosen primal spanning tree and its actual edge realization
are inputs; no plane, cotree, bag coverage, or running-intersection certificate
is assumed. -/
noncomputable def decomposition {w h} (hw : 0<w) (hh : 0<h)
    (R : FiniteCode (Fin ((w+1)*(h+1)+1)) ((w+1)*(h+1)+1))
    (T : RootedTree ((w+1)*(h+1)+1))
    (hedge : ∀ x, x.val≠0 → ∃ d, (numberedIncidence hw hh R).tail d=x ∧
      (numberedIncidence hw hh R).tail d.reverse=T.parent x) :
    Decomposition (incidenceGraph (numberedIncidence hw hh R) (numbered_loopless hw hh R))
      (cotree hw hh R T hedge).tree :=
  threeRootPathDecomposition (numberedIncidence hw hh R) (numbered_loopless hw hh R)
    (triangles hw hh R) T (cotree hw hh R T hedge) (numbered_cut_continues hw hh R)
    (TDart.rotate hw hh) (numbered_rotation_tail hw hh R) (numbered_rotation_face hw hh R)
    (numbered_vertex_orbits hw hh R) (numbered_vertex_surjective hw hh R) hedge

end StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle
