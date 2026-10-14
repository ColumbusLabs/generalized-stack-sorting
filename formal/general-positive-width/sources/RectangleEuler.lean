import FiniteOrbitCounts

namespace StackSorting.GraphWidth.UCurve.PlaneGrid

def vertexLabel {w h} (d : Dart w h) : Fin (w+1) × Fin (h+1) :=
  (⟨d.tail.time,by have := d.tail_bounded; omega⟩,
   ⟨d.tail.depth,by have := d.tail_bounded; omega⟩)

theorem vertexLabel_eq {w h} (d e : Dart w h) : vertexLabel d=vertexLabel e ↔ d.tail=e.tail := by
  constructor
  · intro he
    have hx := congrArg (fun p => p.1.val) he
    have hy := congrArg (fun p => p.2.val) he
    change d.tail.time=e.tail.time at hx
    change d.tail.depth=e.tail.depth at hy
    have : ∀ p q : Point, p.time=q.time → p.depth=q.depth → p=q := by
      intro p q; cases p; cases q; simp_all
    exact this d.tail e.tail hx hy
  · intro he
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Point.time he
    · exact congrArg Point.depth he

def vertexOrbitCount {w h} (hw : 0<w) (hh : 0<h) :
    OrbitCount (Dart.rotate hw hh) ((w+1)*(h+1)) :=
  orbitCountFromCode (Dart.rotate hw hh) vertexLabel (productCode (w+1) (h+1) (by omega))
    (by
      intro b
      obtain ⟨x,y⟩ := b
      refine ⟨vertexRepresentative hw x y,?_⟩
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg Point.time (vertexRepresentative_tail hw x y)
      · exact congrArg Point.depth (vertexRepresentative_tail hw x y))
    (fun d e => (Dart.vertex_orbits_exact hw hh d e).trans (vertexLabel_eq d e).symm)

def edgeLabel {w h} : Dart w h → Sum (Fin w × Fin (h+1)) (Fin (w+1) × Fin h)
  | .east x y | .west x y => .inl (x,y)
  | .south x y | .north x y => .inr (x,y)

theorem edgeLabel_reverse {w h} (d : Dart w h) : edgeLabel d.reverse=edgeLabel d := by
  cases d <;> rfl

theorem edge_same_connected {w h} (d e : Dart w h) (he : edgeLabel d=edgeLabel e) :
    Walk (OrbitStep (@Dart.reverse w h)) (fun _ => True) d e := by
  cases d <;> cases e <;> simp_all [edgeLabel]
  all_goals first
    | exact .refl trivial
    | exact .step trivial (Or.inl rfl) (.refl trivial)

theorem edge_connected_same {w h} {d e : Dart w h}
    (he : Walk (OrbitStep (@Dart.reverse w h)) (fun _ => True) d e) : edgeLabel d=edgeLabel e := by
  induction he with
  | refl => rfl
  | @step a b c _ hs _ ih =>
    have h : edgeLabel a=edgeLabel b := by
      obtain hs | hs := hs
      · exact (edgeLabel_reverse a).symm.trans (congrArg edgeLabel hs)
      · exact (congrArg edgeLabel hs).symm.trans (edgeLabel_reverse b)
    exact h.trans ih

def edgeOrbitCount {w h} (_hw : 0<w) (hh : 0<h) :
    OrbitCount (@Dart.reverse w h) (w*(h+1)+(w+1)*h) :=
  orbitCountFromCode Dart.reverse edgeLabel
    (sumCode (productCode w (h+1) (by omega)) (productCode (w+1) h hh))
    (by
      intro e
      cases e with
      | inl p => exact ⟨.east p.1 p.2,rfl⟩
      | inr p => exact ⟨.south p.1 p.2,rfl⟩)
    (fun d e => ⟨edge_connected_same,edge_same_connected d e⟩)

theorem map_orbit_walk {α β} (f : α → α) (g : β → β) (M : α → β)
    (hm : ∀ a, M (f a)=g (M a)) {a b}
    (h : Walk (OrbitStep f) (fun _ => True) a b) :
    Walk (OrbitStep g) (fun _ => True) (M a) (M b) := by
  apply walk_map M (h := h)
  intro c d he
  obtain he | he := he
  · exact Or.inl ((hm c).symm.trans (congrArg M he))
  · exact Or.inr ((hm d).symm.trans (congrArg M he))

theorem Dart.face_orbits_exact {w h} (hw : 0<w) (hh : 0<h) (d e : Dart w h) :
    Walk (OrbitStep (Dart.faceNext hw hh)) (fun _ => True) d e ↔
      d.toFaceDart.faceId=e.toFaceDart.faceId := by
  constructor
  · intro he
    apply FaceDart.connected_same_face hw hh
    exact map_orbit_walk (Dart.faceNext hw hh) (FaceDart.faceNext hw hh) Dart.toFaceDart
      (fun a => by simp only [Dart.faceNext,FaceDart.dart_roundtrip]) he
  · intro he
    have h := FaceDart.same_face_connected hw hh d.toFaceDart e.toFaceDart he
    have h' := map_orbit_walk (FaceDart.faceNext hw hh) (Dart.faceNext hw hh) FaceDart.toDart
      (fun a => by simp only [Dart.faceNext,FaceDart.dart_roundtrip]) h
    simpa only [Dart.face_roundtrip] using h'

def faceOrbitCount {w h} (hw : 0<w) (hh : 0<h) : OrbitCount (Dart.faceNext hw hh) (w*h+1) :=
  orbitCountFromCode (Dart.faceNext hw hh) (fun d => d.toFaceDart.faceId)
    (optionCode (productCode w h hh))
    (by
      intro f
      cases f with
      | none =>
        refine ⟨(FaceDart.bottom (⟨0,hw⟩ : Fin w)).toDart,?_⟩
        simp only [FaceDart.dart_roundtrip,FaceDart.faceId]
      | some p =>
        refine ⟨(FaceDart.cell p.1 p.2 0).toDart,?_⟩
        simp only [FaceDart.dart_roundtrip,FaceDart.faceId])
    (Dart.face_orbits_exact hw hh)

/-- All three actual permutation-orbit counts for the complete rectangle,
with Euler characteristic two. This is not yet a source-subgraph plane map. -/
structure RectangleEulerData (w h : Nat) (hw : 0<w) (hh : 0<h) where
  vertices : OrbitCount (Dart.rotate hw hh) ((w+1)*(h+1))
  edges : OrbitCount (@Dart.reverse w h) (w*(h+1)+(w+1)*h)
  faces : OrbitCount (Dart.faceNext hw hh) (w*h+1)
  euler : (w+1)*(h+1)+(w*h+1)=(w*(h+1)+(w+1)*h)+2

def rectangleEulerData {w h} (hw : 0<w) (hh : 0<h) : RectangleEulerData w h hw hh where
  vertices := vertexOrbitCount hw hh
  edges := edgeOrbitCount hw hh
  faces := faceOrbitCount hw hh
  euler := rectangle_count_identity w h

end StackSorting.GraphWidth.UCurve.PlaneGrid
