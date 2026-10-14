import TriRectangleCotree

namespace StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle

/-- The three actual dart incidences of each numbered triangular face. -/
def corner {w h} (hw : 0<w) (hh : 0<h)
    (f : Fin (2*w*h+2*w+2*h)) (i : Fin 3) : TDart w h :=
  toDart hw hh ((faceCode hh).decode f,sideCode.decode i)

theorem corner_face {w h} (hw : 0<w) (hh : 0<h)
    (f : Fin (2*w*h+2*w+2*h)) (i : Fin 3) :
    (incidenceMap hw hh).face (corner hw hh f i)=f := by
  change (faceCode hh).encode ((toDart hw hh ((faceCode hh).decode f,sideCode.decode i)).toIncidence hw hh).1=f
  rw [dart_roundtrip]
  exact (faceCode hh).encode_decode f

/-- Every actual dart is one of its numbered face's three explicit incidences. -/
theorem corner_covers {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) :
    ∃ i : Fin 3, corner hw hh ((incidenceMap hw hh).face d) i=d := by
  refine ⟨sideCode.encode (d.toIncidence hw hh).2,?_⟩
  change toDart hw hh ((faceCode hh).decode ((faceCode hh).encode (d.faceLabel hw hh)),
    sideCode.decode (sideCode.encode (d.toIncidence hw hh).2))=d
  rw [(faceCode hh).decode_encode,sideCode.decode_encode]
  exact TDart.incidence_roundtrip hw hh d

theorem corner_exact {w h} (hw : 0<w) (hh : 0<h)
    (f : Fin (2*w*h+2*w+2*h)) (d : TDart w h) :
    (incidenceMap hw hh).face d=f ↔ ∃ i : Fin 3, corner hw hh f i=d := by
  constructor
  · intro he
    simpa only [he] using corner_covers hw hh d
  · intro hi
    obtain ⟨i,rfl⟩ := hi
    exact corner_face hw hh f i

theorem corner_injective {w h} (hw : 0<w) (hh : 0<h)
    (f : Fin (2*w*h+2*w+2*h)) {i j : Fin 3}
    (he : corner hw hh f i=corner hw hh f j) : i=j := by
  have he' := congrArg (TDart.toIncidence hw hh) he
  simp only [corner,dart_roundtrip] at he'
  have hs := congrArg Prod.snd he'
  have hi := congrArg sideCode.encode hs
  simpa only [sideCode.encode_decode] using hi

end StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle
