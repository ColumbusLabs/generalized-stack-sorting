import RectangleFaceCycles

namespace StackSorting.GraphWidth.UCurve.PlaneGrid

def Dart.faceNext {w h} (hw : 0 < w) (hh : 0 < h) (d : Dart w h) : Dart w h :=
  (d.toFaceDart.faceNext hw hh).toDart

def Dart.facePrev {w h} (hw : 0 < w) (hh : 0 < h) (d : Dart w h) : Dart w h :=
  (d.toFaceDart.facePrev hw hh).toDart

theorem Dart.facePrev_next {w h} (hw : 0 < w) (hh : 0 < h) (d : Dart w h) :
    (d.faceNext hw hh).facePrev hw hh = d := by
  simp only [Dart.faceNext,Dart.facePrev,FaceDart.dart_roundtrip,FaceDart.facePrev_next,Dart.face_roundtrip]

theorem Dart.faceNext_prev {w h} (hw : 0 < w) (hh : 0 < h) (d : Dart w h) :
    (d.facePrev hw hh).faceNext hw hh = d := by
  simp only [Dart.faceNext,Dart.facePrev,FaceDart.dart_roundtrip,FaceDart.faceNext_prev,Dart.face_roundtrip]

theorem Dart.faceNext_tail {w h} (hw : 0 < w) (hh : 0 < h) (d : Dart w h) :
    (d.faceNext hw hh).tail = d.head := by
  have h := d.toFaceDart.next_starts_at_head hw hh
  simpa only [Dart.face_roundtrip,Dart.faceNext] using h

/-- The cyclic permutation of outgoing darts, derived from the explicit
cell/exterior face successor and reversal. Its orbit classification at
vertices is a separate theorem, not a field or an assumption here. -/
def Dart.rotate {w h} (hw : 0 < w) (hh : 0 < h) (d : Dart w h) : Dart w h :=
  d.reverse.faceNext hw hh

def Dart.unrotate {w h} (hw : 0 < w) (hh : 0 < h) (d : Dart w h) : Dart w h :=
  (d.facePrev hw hh).reverse

theorem Dart.unrotate_rotate {w h} (hw : 0 < w) (hh : 0 < h) (d : Dart w h) :
    (d.rotate hw hh).unrotate hw hh = d := by
  simp only [Dart.rotate,Dart.unrotate,Dart.facePrev_next,Dart.reverse_reverse]

theorem Dart.rotate_unrotate {w h} (hw : 0 < w) (hh : 0 < h) (d : Dart w h) :
    (d.unrotate hw hh).rotate hw hh = d := by
  simp only [Dart.rotate,Dart.unrotate,Dart.reverse_reverse,Dart.faceNext_prev]

theorem Dart.rotate_preserves_vertex {w h} (hw : 0 < w) (hh : 0 < h) (d : Dart w h) :
    (d.rotate hw hh).tail = d.tail := by
  simp only [Dart.rotate,Dart.faceNext_tail,Dart.head_reverse]

theorem Dart.reverse_then_rotate_is_face {w h} (hw : 0 < w) (hh : 0 < h) (d : Dart w h) :
    d.reverse.rotate hw hh = d.faceNext hw hh := by
  simp only [Dart.rotate,Dart.reverse_reverse]

/-- A checked arithmetic identity for the expected counts of a full rectangle.
Orbit enumeration must still identify these numbers with actual vertex,
edge and face orbits before it is an Euler-characteristic theorem. -/
theorem rectangle_count_identity (w h : Nat) :
    (w+1)*(h+1) + (w*h+1) = (w*(h+1)+(w+1)*h) + 2 := by
  simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul,Nat.mul_one]
  omega

end StackSorting.GraphWidth.UCurve.PlaneGrid
