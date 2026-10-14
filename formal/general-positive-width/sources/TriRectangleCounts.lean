import TriRectangleVertexOrbits

namespace StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle

/-- Transport a checked finite encoding along an explicitly proved bijection. -/
def transportCode {α β : Type} {n : Nat} (C : FiniteCode β n)
    (f : α → β) (g : β → α) (hg : ∀ a, g (f a)=a) (hf : ∀ b, f (g b)=b) :
    FiniteCode α n where
  encode := C.encode ∘ f
  decode := g ∘ C.decode
  decode_encode := by intro a; simp only [Function.comp_apply,C.decode_encode,hg]
  encode_decode := by intro i; simp only [Function.comp_apply,hf,C.encode_decode]

def finCode (n : Nat) : FiniteCode (Fin n) n where
  encode := id
  decode := id
  decode_encode := fun _ => rfl
  encode_decode := fun _ => rfl

def codeProduct {α β : Type} {m n : Nat} (A : FiniteCode α m) (B : FiniteCode β n)
    (hn : 0<n) : FiniteCode (α × β) (m*n) :=
  transportCode (productCode m n hn) (fun p => (A.encode p.1,B.encode p.2))
    (fun p => (A.decode p.1,B.decode p.2))
    (by intro p; simp only [A.decode_encode,B.decode_encode])
    (by intro p; simp only [A.encode_decode,B.encode_decode])

def castCode {α : Type} {m n : Nat} (C : FiniteCode α m) (h : m=n) : FiniteCode α n := h ▸ C

def faceCode {w h} (hh : 0<h) : FiniteCode (Face w h) (2*w*h+2*w+2*h) :=
  castCode (sumCode (sumCode (productCode w h hh) (productCode w h hh))
    (finCode (perimeter w h))) (by unfold perimeter; simp only [Nat.mul_assoc]; omega)

def sideCode : FiniteCode Side 3 where
  encode := fun s => match s with | .first => 0 | .second => 1 | .third => 2
  decode := fun i => if i.val=0 then .first else if i.val=1 then .second else .third
  decode_encode := by intro s; cases s <;> rfl
  encode_decode := by
    intro i
    have hi : i.val=0 ∨ i.val=1 ∨ i.val=2 := by omega
    rcases hi with hi | hi | hi
    all_goals apply Fin.ext; simp [hi]

def dartCode {w h} (hw : 0<w) (hh : 0<h) :
    FiniteCode (TDart w h) ((2*w*h+2*w+2*h)*3) :=
  transportCode (codeProduct (faceCode hh) sideCode (by decide))
    (TDart.toIncidence hw hh) (toDart hw hh) (TDart.incidence_roundtrip hw hh) (dart_roundtrip hw hh)

def TDart.vertexLabel {w h} (hw : 0<w) (hh : 0<h) :
    TDart w h → Option (Fin (w+1) × Fin (h+1))
  | .grid d => some (PlaneGrid.vertexLabel d)
  | .diagonal x y => some (⟨x.val,by omega⟩,⟨y.val,by omega⟩)
  | .antidiagonal x y => some (⟨x.val+1,by omega⟩,⟨y.val+1,by omega⟩)
  | .toApex i => some (PlaneGrid.vertexLabel (boundaryAt hw hh i).toDart)
  | .fromApex _ => none

def vertexPoint {w h} : Option (Fin (w+1) × Fin (h+1)) → Option Point
  | none => none
  | some (x,y) => some ⟨x.val,y.val⟩

theorem vertexPoint_injective {w h} {a b : Option (Fin (w+1) × Fin (h+1))}
    (he : vertexPoint a=vertexPoint b) : a=b := by
  cases a with
  | none => cases b <;> simp_all [vertexPoint]
  | some a =>
    cases b with
    | none => simp [vertexPoint] at he
    | some b =>
      simp only [vertexPoint,Option.some.injEq] at he
      apply congrArg some
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg Point.time he
      · exact congrArg Point.depth he

theorem vertexLabel_point {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) :
    vertexPoint (d.vertexLabel hw hh)=d.tail hw hh := by
  cases d <;> rfl

theorem vertexLabel_eq {w h} (hw : 0<w) (hh : 0<h) (d e : TDart w h) :
    d.vertexLabel hw hh=e.vertexLabel hw hh ↔ d.tail hw hh=e.tail hw hh := by
  constructor
  · intro he
    simpa only [vertexLabel_point] using congrArg vertexPoint he
  · intro he
    apply vertexPoint_injective
    simpa only [vertexLabel_point] using he

def vertexOrbitCount {w h} (hw : 0<w) (hh : 0<h) :
    OrbitCount (TDart.rotate hw hh) ((w+1)*(h+1)+1) :=
  orbitCountFromCode (TDart.rotate hw hh) (TDart.vertexLabel hw hh)
    (optionCode (productCode (w+1) (h+1) (by omega)))
    (by
      intro v
      cases v with
      | none => exact ⟨.fromApex ⟨0,by unfold perimeter; omega⟩,rfl⟩
      | some p =>
        obtain ⟨x,y⟩ := p
        refine ⟨.grid (vertexRepresentative hw x y),?_⟩
        apply congrArg some
        apply Prod.ext <;> apply Fin.ext
        · exact congrArg Point.time (vertexRepresentative_tail hw x y)
        · exact congrArg Point.depth (vertexRepresentative_tail hw x y))
    (fun d e => (vertex_orbits_exact hw hh d e).trans (vertexLabel_eq hw hh d e).symm)

def TDart.faceLabel {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) : Face w h :=
  (d.toIncidence hw hh).1

theorem faceLabel_next {w h} (hw : 0<w) (hh : 0<h) (d : TDart w h) :
    (d.faceNext hw hh).faceLabel hw hh=d.faceLabel hw hh := by
  simp only [TDart.faceLabel,TDart.faceNext,dart_roundtrip,next]

theorem connected_same_face {w h} (hw : 0<w) (hh : 0<h) {d e : TDart w h}
    (hp : Walk (OrbitStep (TDart.faceNext hw hh)) (fun _ => True) d e) :
    d.faceLabel hw hh=e.faceLabel hw hh := by
  induction hp with
  | refl => rfl
  | @step a b c _ hs _ ih =>
    have hab : a.faceLabel hw hh=b.faceLabel hw hh := by
      obtain hs | hs := hs
      · exact (faceLabel_next hw hh a).symm.trans (congrArg (TDart.faceLabel hw hh) hs)
      · exact (congrArg (TDart.faceLabel hw hh) hs).symm.trans (faceLabel_next hw hh b)
    exact hab.trans ih

theorem same_face_incidence_connected {w h} (hw : 0<w) (hh : 0<h) (f : Face w h) (s t : Side) :
    Walk (OrbitStep (TDart.faceNext hw hh)) (fun _ => True)
      (toDart hw hh (f,s)) (toDart hw hh (f,t)) := by
  have hs : ∀ s, (toDart hw hh (f,s)).faceNext hw hh=toDart hw hh (f,s.next) := by
    intro s; simp only [TDart.faceNext,dart_roundtrip,next]
  have step : ∀ s, Walk (OrbitStep (TDart.faceNext hw hh)) (fun _ => True)
      (toDart hw hh (f,s)) (toDart hw hh (f,s.next)) :=
    fun s => .step trivial (Or.inl (hs s)) (.refl trivial)
  cases s <;> cases t
  all_goals first
    | exact .refl trivial
    | exact step _
    | exact (step .first).reverse (fun h => h.symm)
    | exact (step .second).reverse (fun h => h.symm)
    | exact (step .third).reverse (fun h => h.symm)

theorem same_face_connected {w h} (hw : 0<w) (hh : 0<h) (d e : TDart w h)
    (he : d.faceLabel hw hh=e.faceLabel hw hh) :
    Walk (OrbitStep (TDart.faceNext hw hh)) (fun _ => True) d e := by
  have hp := same_face_incidence_connected hw hh (d.faceLabel hw hh)
    (d.toIncidence hw hh).2 (e.toIncidence hw hh).2
  have hd : toDart hw hh (d.faceLabel hw hh,(d.toIncidence hw hh).2)=d :=
    TDart.incidence_roundtrip hw hh d
  have he' : toDart hw hh (d.faceLabel hw hh,(e.toIncidence hw hh).2)=e := by
    rw [he]
    exact TDart.incidence_roundtrip hw hh e
  simpa only [hd,he'] using hp

def faceOrbitCount {w h} (hw : 0<w) (hh : 0<h) :
    OrbitCount (TDart.faceNext hw hh) (2*w*h+2*w+2*h) :=
  orbitCountFromCode (TDart.faceNext hw hh) (TDart.faceLabel hw hh) (faceCode hh)
    (by intro f; exact ⟨toDart hw hh (f,.first),by simp only [TDart.faceLabel,dart_roundtrip]⟩)
    (fun d e => ⟨connected_same_face hw hh,same_face_connected hw hh d e⟩)



def Edge (w h : Nat) := Sum
  (Sum (Fin w × Fin (h+1)) (Fin (w+1) × Fin h))
  (Sum (Fin w × Fin h) (Fin (perimeter w h)))

def TDart.edgeLabel {w h} : TDart w h → Edge w h
  | .grid d => .inl (PlaneGrid.edgeLabel d)
  | .diagonal x y | .antidiagonal x y => .inr (.inl (x,y))
  | .toApex i | .fromApex i => .inr (.inr i)

def edgeCode {w h} (hh : 0<h) : FiniteCode (Edge w h) (3*w*h+3*w+3*h) :=
  castCode
    (sumCode (sumCode (productCode w (h+1) (by omega)) (productCode (w+1) h hh))
      (sumCode (productCode w h hh) (finCode (perimeter w h))))
    (by unfold perimeter; simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul,Nat.mul_one,Nat.mul_assoc]; omega)

theorem edgeLabel_reverse {w h} (d : TDart w h) : d.reverse.edgeLabel=d.edgeLabel := by
  cases d <;> simp [TDart.reverse,TDart.edgeLabel,PlaneGrid.edgeLabel_reverse,Edge]

theorem edge_connected_same {w h} {d e : TDart w h}
    (hp : Walk (OrbitStep (@TDart.reverse w h)) (fun _ => True) d e) : d.edgeLabel=e.edgeLabel := by
  induction hp with
  | refl => rfl
  | @step a b c _ hs _ ih =>
    have hab : a.edgeLabel=b.edgeLabel := by
      obtain hs | hs := hs
      · exact (edgeLabel_reverse a).symm.trans (congrArg TDart.edgeLabel hs)
      · exact (congrArg TDart.edgeLabel hs).symm.trans (edgeLabel_reverse b)
    exact hab.trans ih

theorem edge_same_connected {w h} (d e : TDart w h) (he : d.edgeLabel=e.edgeLabel) :
    Walk (OrbitStep (@TDart.reverse w h)) (fun _ => True) d e := by
  cases d <;> cases e <;> simp_all [TDart.edgeLabel,Edge]
  case grid.grid a b =>
    exact map_orbit_walk Dart.reverse TDart.reverse TDart.grid (fun _ => rfl)
      (PlaneGrid.edge_same_connected a b he)
  all_goals first
    | exact .refl trivial
    | exact .step trivial (Or.inl rfl) (.refl trivial)

def edgeOrbitCount {w h} (_hw : 0<w) (hh : 0<h) :
    OrbitCount (@TDart.reverse w h) (3*w*h+3*w+3*h) :=
  orbitCountFromCode TDart.reverse TDart.edgeLabel (edgeCode hh)
    (by
      intro e
      cases e with
      | inl e =>
        cases e with
        | inl p => exact ⟨.grid (.east p.1 p.2),rfl⟩
        | inr p => exact ⟨.grid (.south p.1 p.2),rfl⟩
      | inr e =>
        cases e with
        | inl p => exact ⟨.diagonal p.1 p.2,rfl⟩
        | inr i => exact ⟨.toApex i,rfl⟩)
    (fun d e => ⟨edge_connected_same,edge_same_connected d e⟩)

theorem euler_identity (w h : Nat) :
    ((w+1)*(h+1)+1)+(2*w*h+2*w+2*h)=(3*w*h+3*w+3*h)+2 := by
  simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul,Nat.mul_one,Nat.mul_assoc]
  omega

/-- All component counts are proved from this triangulation's explicit permutations. -/
structure EulerData (w h : Nat) (hw : 0<w) (hh : 0<h) where
  vertices : OrbitCount (TDart.rotate hw hh) ((w+1)*(h+1)+1)
  edges : OrbitCount (@TDart.reverse w h) (3*w*h+3*w+3*h)
  faces : OrbitCount (TDart.faceNext hw hh) (2*w*h+2*w+2*h)
  euler : ((w+1)*(h+1)+1)+(2*w*h+2*w+2*h)=(3*w*h+3*w+3*h)+2

def eulerData {w h} (hw : 0<w) (hh : 0<h) : EulerData w h hw hh where
  vertices := vertexOrbitCount hw hh
  edges := edgeOrbitCount hw hh
  faces := faceOrbitCount hw hh
  euler := euler_identity w h

end StackSorting.GraphWidth.UCurve.PlaneGrid.TriRectangle
