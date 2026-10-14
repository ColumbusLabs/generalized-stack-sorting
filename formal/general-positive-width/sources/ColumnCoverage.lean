import IndexedColumnPorts

namespace StackSorting.BiInterface.RepeatedColumn
open PathWord
variable {k : ℕ}

/-- Every actual product vertex belongs to a literal ordered column. -/
theorem eval_vertex_covered (ps : List (Packed k)) (v : (Packed.eval ps).Vertex) :
    ∃ (P : Packed k) (h : Occurrence P ps) (x : P.Vertex), h.column x = v := by
  induction ps with
  | nil => exact v.elim
  | cons P ps ih =>
    cases ps with
    | nil => exact ⟨P,Occurrence.head [],v,rfl⟩
    | cons Q qs =>
      induction v using Quotient.inductionOn with | h v =>
        cases v with
        | inl x => exact ⟨P,Occurrence.head (Q :: qs),x,rfl⟩
        | inr y =>
          obtain ⟨R,h,x,hx⟩ := ih y
          exact ⟨R,Occurrence.tail h,x,congrArg (inRight P.graph (Packed.eval (Q :: qs)).graph) hx⟩

/-- Every edge is literally an edge of a factor, with both endpoints mapped
by the same actual ordered column injection. -/
theorem eval_edge_covered (ps : List (Packed k)) {v w : (Packed.eval ps).Vertex}
    (hvw : (Packed.eval ps).graph.Adj v w) :
    ∃ (P : Packed k) (h : Occurrence P ps) (x y : P.Vertex),
      P.graph.Adj x y ∧ h.column x = v ∧ h.column y = w := by
  induction ps with
  | nil => exact v.elim
  | cons P ps ih =>
    cases ps with
    | nil => exact ⟨P,Occurrence.head [],v,w,hvw,rfl,rfl⟩
    | cons Q qs =>
      rcases hvw with ⟨x,y,hxy,hx,hy⟩ | ⟨x,y,hxy,hx,hy⟩
      · exact ⟨P,Occurrence.head (Q :: qs),x,y,hxy,hx,hy⟩
      · obtain ⟨R,h,a,b,hab,ha,hb⟩ := ih hxy
        exact ⟨R,Occurrence.tail h,a,b,hab,
          (congrArg (inRight P.graph (Packed.eval (Q :: qs)).graph) ha).trans hx,
          (congrArg (inRight P.graph (Packed.eval (Q :: qs)).graph) hb).trans hy⟩

namespace Occurrence
variable {P Q : Packed k} {ps : List (Packed k)}

/-- A numeric position determines the literal packed graph, even when this
statement is phrased using occurrences with different dependent carriers. -/
theorem piece_eq_of_index_eq (h : Occurrence P ps) (h' : Occurrence Q ps)
    (hi : h.index = h'.index) : P = Q := by
  induction ps generalizing P Q with
  | nil => exact (h.ne_nil rfl).elim
  | cons R ps ih =>
    cases h with
    | head _ =>
      cases h' with
      | head _ => rfl
      | tail h' => simp [index] at hi
    | tail h =>
      cases h' with
      | head _ => simp [index] at hi
      | tail h' => exact ih h h' (by simpa [index] using hi)

/-- A product's outer left port remains a named interface in every column
where it occurs, even when a persistent vertex crosses arbitrarily many seams. -/
theorem left_port_boundary (h : Occurrence P ps) (i : Fin k) (x : P.Vertex)
    (hp : (Packed.eval ps).graph.left i = some (h.column x)) : x ∈ P.graph.boundary := by
  induction h generalizing i with
  | head ps =>
    cases ps with
    | nil => exact ⟨(false,i),hp⟩
    | cons Q qs =>
      obtain ⟨y,hy,he⟩ := Option.map_eq_some_iff.mp hp
      have hyx := inLeft_injective P.graph (Packed.eval (Q :: qs)).graph he
      exact ⟨(false,i),hyx ▸ hy⟩
  | @tail Q ps h ih =>
    cases ps with
    | nil => exact (h.ne_nil rfl).elim
    | cons R rs =>
      obtain ⟨y,_,he⟩ := Option.map_eq_some_iff.mp hp
      obtain ⟨j,_,hj⟩ := (inLeft_eq_inRight Q.graph (Packed.eval (R :: rs)).graph _ _).mp he
      exact ih j hj

/-- Symmetric outer-right port preservation at every occurrence. -/
theorem right_port_boundary (h : Occurrence P ps) (i : Fin k) (x : P.Vertex)
    (hp : (Packed.eval ps).graph.right i = some (h.column x)) : x ∈ P.graph.boundary := by
  induction h generalizing i with
  | head ps =>
    cases ps with
    | nil => exact ⟨(true,i),hp⟩
    | cons Q qs =>
      obtain ⟨y,_,he⟩ := Option.map_eq_some_iff.mp hp
      obtain ⟨j,hj,_⟩ := (inLeft_eq_inRight P.graph (Packed.eval (Q :: qs)).graph x y).mp he.symm
      exact ⟨(true,j),hj⟩
  | @tail Q ps h ih =>
    cases ps with
    | nil => exact (h.ne_nil rfl).elim
    | cons R rs =>
      obtain ⟨y,hy,he⟩ := Option.map_eq_some_iff.mp hp
      have hey := inRight_injective Q.graph (Packed.eval (R :: rs)).graph he
      exact ih i (hey ▸ hy)
end Occurrence

/-- Any shared vertex of distinct columns is an actual interface vertex of
both factors. This does not require disjoint left/right interfaces. -/
theorem column_overlap_boundary {P Q : Packed k} {ps : List (Packed k)}
    (h : Occurrence P ps) (h' : Occurrence Q ps) (hne : h.index ≠ h'.index)
    (x : P.Vertex) (y : Q.Vertex) (he : h.column x = h'.column y) :
    x ∈ P.graph.boundary ∧ y ∈ Q.graph.boundary := by
  induction ps generalizing P Q with
  | nil => exact (h.ne_nil rfl).elim
  | cons A ps ih =>
    cases h with
    | head _ =>
      cases h' with
      | head _ => exact (hne rfl).elim
      | tail h' =>
        cases ps with
        | nil => exact (h'.ne_nil rfl).elim
        | cons B bs =>
          obtain ⟨i,hi,hj⟩ := (inLeft_eq_inRight A.graph (Packed.eval (B :: bs)).graph _ _).mp he
          exact ⟨⟨(true,i),hi⟩,h'.left_port_boundary i y hj⟩
    | tail h =>
      cases h' with
      | head _ =>
        cases ps with
        | nil => exact (h.ne_nil rfl).elim
        | cons B bs =>
          obtain ⟨i,hi,hj⟩ := (inLeft_eq_inRight A.graph (Packed.eval (B :: bs)).graph _ _).mp he.symm
          exact ⟨h.left_port_boundary i x hj,⟨(true,i),hi⟩⟩
      | tail h' =>
        cases ps with
        | nil => exact (h.ne_nil rfl).elim
        | cons B bs =>
          apply ih h h' (by intro hh; apply hne; simp [Occurrence.index,hh]) x y
          exact inRight_injective A.graph (Packed.eval (B :: bs)).graph he

def columnInterior {P : Packed k} {ps : List (Packed k)} (h : Occurrence P ps) :
    Set (Packed.eval ps).Vertex := {v | ∃ x, x ∉ P.graph.boundary ∧ h.column x = v}

def columnBoundary {P : Packed k} {ps : List (Packed k)} (h : Occurrence P ps) :
    Set (Packed.eval ps).Vertex := {v | ∃ x, x ∈ P.graph.boundary ∧ h.column x = v}

/-- Interior column images are genuinely disjoint, not just disjoint after
assigning a different name to a shared quotient vertex. -/
theorem column_interiors_disjoint {P Q : Packed k} {ps : List (Packed k)}
    (h : Occurrence P ps) (h' : Occurrence Q ps) (hne : h.index ≠ h'.index) :
    Disjoint (columnInterior h) (columnInterior h') := by
  rw [Set.disjoint_left]
  rintro v ⟨x,hx,hxv⟩ ⟨y,hy,hyv⟩
  exact hx (column_overlap_boundary h h' hne x y (hxv.trans hyv.symm)).1

/-- Every global edge incident with a column interior is an edge of that same
factor. In particular its other endpoint remains in that actual column. -/
theorem edge_at_column_interior {P : Packed k} {ps : List (Packed k)}
    (h : Occurrence P ps) (x : P.Vertex) (hx : x ∉ P.graph.boundary)
    {w : (Packed.eval ps).Vertex} (he : (Packed.eval ps).graph.Adj (h.column x) w) :
    ∃ y : P.Vertex, P.graph.Adj x y ∧ h.column y = w := by
  obtain ⟨Q,h',a,b,hab,ha,hb⟩ := eval_edge_covered ps he
  have hi : h.index = h'.index := by
    by_contra hne
    exact hx (column_overlap_boundary h h' hne x a ha.symm).1
  have hPQ : P = Q := h.piece_eq_of_index_eq h' hi
  subst Q
  have hh : h = h' := h.eq_of_index_eq h' hi
  subst h'
  have hax : a = x := h.column_injective ha
  subst a
  exact ⟨b,hab,hb⟩

/-- Distinct column interiors have no edge between them in the actual graph. -/
theorem no_edge_between_column_interiors {P Q : Packed k} {ps : List (Packed k)}
    (h : Occurrence P ps) (h' : Occurrence Q ps) (hne : h.index ≠ h'.index)
    {v w : (Packed.eval ps).Vertex} (hv : v ∈ columnInterior h) (hw : w ∈ columnInterior h') :
    ¬ (Packed.eval ps).graph.Adj v w := by
  rintro he
  obtain ⟨x,hx,rfl⟩ := hv
  obtain ⟨y,hy,hyw⟩ := hw
  obtain ⟨z,_,hzw⟩ := edge_at_column_interior h x hx he
  exact hy (column_overlap_boundary h h' hne z y (hzw.trans hyw.symm)).2

/-- A neighbor of a column interior that is outside that interior is one of
this very column's named boundary vertices. -/
theorem column_interior_frontier {P : Packed k} {ps : List (Packed k)}
    (h : Occurrence P ps) {v w : (Packed.eval ps).Vertex}
    (hv : v ∈ columnInterior h) (hw : w ∉ columnInterior h)
    (he : (Packed.eval ps).graph.Adj v w) : w ∈ columnBoundary h := by
  classical
  obtain ⟨x,hx,rfl⟩ := hv
  obtain ⟨y,_,hyw⟩ := edge_at_column_interior h x hx he
  refine ⟨y,?_,hyw⟩
  by_contra hn
  exact hw ⟨y,hn,hyw⟩

#print axioms eval_vertex_covered
#print axioms eval_edge_covered
#print axioms column_overlap_boundary
#print axioms no_edge_between_column_interiors
#print axioms column_interior_frontier
end StackSorting.BiInterface.RepeatedColumn
