import TriRectangleDarts

namespace StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle

def TDart.tail {w h} (hw : 0<w) (hh : 0<h) : TDart w h → Option Point
  | .grid d => some d.tail
  | .diagonal x y => some ⟨x.val,y.val⟩
  | .antidiagonal x y => some ⟨x.val+1,y.val+1⟩
  | .toApex i => some (boundaryAt hw hh i).toDart.tail
  | .fromApex _ => none

def TDart.head {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) := d.reverse.tail hw hh

def next {w h} (f : Incidence w h) : Incidence w h := (f.1,f.2.next)
def prev {w h} (f : Incidence w h) : Incidence w h := (f.1,f.2.prev)

theorem prev_next {w h} (f : Incidence w h) : prev (next f)=f := by
  obtain ⟨f,s⟩ := f
  simp only [next,prev,Side.prev_next]

theorem next_prev {w h} (f : Incidence w h) : next (prev f)=f := by
  obtain ⟨f,s⟩ := f
  simp only [next,prev,Side.next_prev]

theorem boundary_head_next {w h} (hw : 0<w) (hh : 0<h) (i : Fin (perimeter w h)) :
    (boundaryAt hw hh (cycleNext i)).toDart.tail=(boundaryAt hw hh i).toDart.head := by
  rw [← boundaryAt_next]
  exact FaceDart.next_starts_at_head hw hh _

theorem next_tail {w h} (hw : 0<w) (hh : 0<h) (f : Incidence w h) :
    (toDart hw hh (next f)).tail hw hh=(toDart hw hh f).head hw hh := by
  obtain ⟨f,s⟩ := f
  cases f with
  | inl f =>
    cases f with
    | inl p | inr p =>
      obtain ⟨x,y⟩ := p
      cases s <;> rfl
  | inr i =>
    cases s with
    | first =>
      change some (boundaryAt hw hh (cycleNext i)).toDart.tail=
        some (boundaryAt hw hh i).toDart.head
      exact congrArg some (boundary_head_next hw hh i)
    | second | third => rfl

def TDart.faceNext {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) :=
  toDart hw hh (next (d.toIncidence hw hh))

def TDart.facePrev {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) :=
  toDart hw hh (prev (d.toIncidence hw hh))

theorem TDart.facePrev_next {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) :
    (d.faceNext hw hh).facePrev hw hh=d := by
  simp only [TDart.faceNext,TDart.facePrev,dart_roundtrip,prev_next,TDart.incidence_roundtrip]

theorem TDart.faceNext_prev {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) :
    (d.facePrev hw hh).faceNext hw hh=d := by
  simp only [TDart.faceNext,TDart.facePrev,dart_roundtrip,next_prev,TDart.incidence_roundtrip]

theorem TDart.faceNext_tail {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) :
    (d.faceNext hw hh).tail hw hh=d.head hw hh := by
  have ht := next_tail hw hh (d.toIncidence hw hh)
  simpa only [TDart.incidence_roundtrip,TDart.faceNext] using ht

def TDart.rotate {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) := d.reverse.faceNext hw hh

def TDart.unrotate {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) := (d.facePrev hw hh).reverse

theorem TDart.unrotate_rotate {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) :
    (d.rotate hw hh).unrotate hw hh=d := by
  simp only [TDart.rotate,TDart.unrotate,TDart.facePrev_next,TDart.reverse_reverse]

theorem TDart.rotate_unrotate {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) :
    (d.unrotate hw hh).rotate hw hh=d := by
  simp only [TDart.rotate,TDart.unrotate,TDart.reverse_reverse,TDart.faceNext_prev]

theorem TDart.rotate_preserves_vertex {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) :
    (d.rotate hw hh).tail hw hh=d.tail hw hh := by
  simp only [TDart.rotate,TDart.faceNext_tail,TDart.head,TDart.reverse_reverse]

theorem TDart.faceNext_cube {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) :
    ((d.faceNext hw hh).faceNext hw hh).faceNext hw hh=d := by
  simp only [TDart.faceNext,dart_roundtrip]
  have ht : next (next (next (d.toIncidence hw hh)))=d.toIncidence hw hh := by
    generalize d.toIncidence hw hh=f
    obtain ⟨f,s⟩ := f
    cases s <;> rfl
  rw [ht,TDart.incidence_roundtrip]

theorem TDart.faceNext_ne {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) :
    d.faceNext hw hh≠d := by
  intro he
  have he' := congrArg (TDart.toIncidence hw hh) he
  simp only [TDart.faceNext,dart_roundtrip] at he'
  have hs := congrArg Prod.snd he'
  change (d.toIncidence hw hh).2.next=(d.toIncidence hw hh).2 at hs
  generalize (d.toIncidence hw hh).2=s at hs
  cases s <;> cases hs

end StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle
