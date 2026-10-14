import FiniteIncidenceCuts

namespace StackSorting.GraphWidth.UCurve.PlaneGrid
open FinitePort

def FiniteCode.transport {α β n} (C : FiniteCode β n) (to : α → β) (of : β → α)
    (hto : ∀ a, of (to a)=a) (hof : ∀ b, to (of b)=b) : FiniteCode α n where
  encode := C.encode ∘ to
  decode := of ∘ C.decode
  decode_encode := by intro a; simp only [Function.comp_apply,C.decode_encode,hto]
  encode_decode := by intro i; simp only [Function.comp_apply,hof,C.encode_decode]

def Dart.signedEdge {w h} : Dart w h →
    Sum (Sum (Fin w × Fin (h+1)) (Fin (w+1) × Fin h))
        (Sum (Fin w × Fin (h+1)) (Fin (w+1) × Fin h))
  | .east x y => .inl (.inl (x,y))
  | .south x y => .inl (.inr (x,y))
  | .west x y => .inr (.inl (x,y))
  | .north x y => .inr (.inr (x,y))

def Dart.ofSignedEdge {w h} :
    Sum (Sum (Fin w × Fin (h+1)) (Fin (w+1) × Fin h))
        (Sum (Fin w × Fin (h+1)) (Fin (w+1) × Fin h)) → Dart w h
  | .inl (.inl (x,y)) => .east x y
  | .inl (.inr (x,y)) => .south x y
  | .inr (.inl (x,y)) => .west x y
  | .inr (.inr (x,y)) => .north x y

def rectangleDartCode {w h} (hh : 0<h) :
    FiniteCode (Dart w h) ((w*(h+1)+(w+1)*h)+(w*(h+1)+(w+1)*h)) :=
  let E := sumCode (productCode w (h+1) (by omega)) (productCode (w+1) h hh)
  (sumCode E E).transport Dart.signedEdge Dart.ofSignedEdge
    (by intro d; cases d <;> rfl)
    (by intro b; rcases b with (⟨x,y⟩ | ⟨x,y⟩) | (⟨x,y⟩ | ⟨x,y⟩) <;> rfl)

theorem rectangle_vertex_label_exact {w h} (hw : 0<w) (hh : 0<h) (d e : Dart w h) :
    (vertexOrbitCount hw hh).label d=(vertexOrbitCount hw hh).label e ↔ d.tail=e.tail :=
  ((vertexOrbitCount hw hh).exact_components d e).symm.trans (Dart.vertex_orbits_exact hw hh d e)

def rectangleIncidenceMap {w h} (hw : 0<w) (hh : 0<h) :
    IncidenceMap (Dart w h) ((w+1)*(h+1)) (w*h+1) where
  tail := (vertexOrbitCount hw hh).label
  reverse := Dart.reverse
  reverse_reverse := Dart.reverse_reverse
  face := (faceOrbitCount hw hh).label
  endpoints_injective := by
    intro d e ht hh'
    apply Dart.endpoints_injective
    · exact (rectangle_vertex_label_exact hw hh d e).mp ht
    · simpa only [Dart.head] using
        (rectangle_vertex_label_exact hw hh d.reverse e.reverse).mp hh'

theorem rectangle_incidence_rotation_tail {w h} (hw : 0<w) (hh : 0<h) (d : Dart w h) :
    (rectangleIncidenceMap hw hh).tail (Dart.rotate hw hh d)=
      (rectangleIncidenceMap hw hh).tail d := by
  apply (rectangle_vertex_label_exact hw hh _ _).mpr
  exact Dart.rotate_preserves_vertex hw hh d

theorem rectangle_incidence_rotation_face {w h} (hw : 0<w) (hh : 0<h) (d : Dart w h) :
    (rectangleIncidenceMap hw hh).face (Dart.rotate hw hh d)=
      (rectangleIncidenceMap hw hh).face d.reverse := by
  apply ((faceOrbitCount hw hh).exact_components _ _).mp
  exact .step trivial (Or.inr rfl) (.refl trivial)

theorem rectangle_cut_continues {w h} (hw : 0<w) (hh : 0<h) :
    CutContinues (rectangleIncidenceMap hw hh) := by
  apply incidence_cut_continues (rectangleIncidenceMap hw hh) (rectangleDartCode hh)
    (Dart.rotate hw hh)
  · intro a b h
    have he := congrArg (Dart.unrotate hw hh) h
    simpa only [Dart.unrotate_rotate] using he
  · exact rectangle_incidence_rotation_tail hw hh
  · exact rectangle_incidence_rotation_face hw hh

/-- The complement of any actual spanning parent tree in the complete
rectangle has connected dual. Every local and global map hypothesis is
supplied by the constructed rectangle; no plane-map certificate is assumed. -/
theorem rectangle_dual_complement_connected {w h} (hw : 0<w) (hh : 0<h)
    (T : RootedTree ((w+1)*(h+1))) (a b : Fin (w*h+1)) :
    Walk (CotreeAdj (rectangleIncidenceMap hw hh) T) (fun _ => True) a b := by
  apply dual_complement_tree_connected (rectangleIncidenceMap hw hh) T
    (rectangle_cut_continues hw hh)
  exact fullDual_connected_of_map (rectangleIncidenceMap hw hh) (Dart.rotate hw hh)
    (rectangle_incidence_rotation_face hw hh) (faceOrbitCount hw hh).surjective
    (rectangle_map_connected hw hh)

end StackSorting.GraphWidth.UCurve.PlaneGrid
