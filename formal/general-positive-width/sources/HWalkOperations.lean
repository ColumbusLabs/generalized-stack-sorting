import HypergraphPaths

/-!
# Edge-identifier-preserving operations on hypergraph walks

All constructions retain the original edge type. In particular, two parallel
edge identifiers are never identified merely because their incidences agree.
-/
namespace FiniteFlow.Hypergraph.HWalk

universe u v
variable {V : Type u} {E : Type v} {inc inc' : V → E → Prop}

/-- Concatenate actual hypergraph walks at their common endpoint. -/
def append {s m t : V} : HWalk inc s m → HWalk inc m t → HWalk inc s t
  | .nil _, q => q
  | .cons e hx hy p, q => .cons e hx hy (p.append q)

@[simp] theorem edges_append {s m t : V}
    (p : HWalk inc s m) (q : HWalk inc m t) :
    (p.append q).edges = p.edges ++ q.edges := by
  induction p with
  | nil => rfl
  | cons e hx hy p ih =>
    simp only [append, edges, ih, List.cons_append]

/-- Reverse a hypergraph walk, using the symmetric incidence step. -/
def reverse {s t : V} : HWalk inc s t → HWalk inc t s
  | .nil s => .nil s
  | .cons (x := s) e hx hy p =>
      p.reverse.append (.cons e hy hx (.nil s))

@[simp] theorem edges_reverse {s t : V} (p : HWalk inc s t) :
    p.reverse.edges = p.edges.reverse := by
  induction p with
  | nil => rfl
  | cons e hx hy p ih =>
    simp only [reverse, edges_append, edges, ih, List.reverse_cons]

/-- Enlarge the incidence relation without changing any edge identifier. -/
def mono (h : ∀ x e, inc x e → inc' x e) {s t : V} :
    HWalk inc s t → HWalk inc' s t
  | .nil s => .nil s
  | .cons e hx hy p => .cons e (h _ _ hx) (h _ _ hy) (p.mono h)

@[simp] theorem edges_mono (h : ∀ x e, inc x e → inc' x e)
    {s t : V} (p : HWalk inc s t) : (p.mono h).edges = p.edges := by
  induction p with
  | nil => rfl
  | cons e hx hy p ih => exact congrArg (List.cons e) ih

@[simp] theorem vertices_mono (h : ∀ x e, inc x e → inc' x e)
    {s t : V} (p : HWalk inc s t) : (p.mono h).vertices = p.vertices := by
  induction p with
  | nil => rfl
  | cons e hx hy p ih => exact congrArg (List.cons _) ih

/-- Restrict incidence to a predicate known for every traversed edge. -/
def restrictEdges (P : E → Prop) {s t : V} :
    (p : HWalk inc s t) → (∀ e ∈ p.edges, P e) →
      HWalk (fun x e => inc x e ∧ P e) s t
  | .nil s, _ => .nil s
  | .cons e hx hy p, h =>
      .cons e ⟨hx, h e (List.mem_cons_self)⟩
        ⟨hy, h e (List.mem_cons_self)⟩
        (p.restrictEdges P (fun f hf => h f (List.mem_cons_of_mem e hf)))

@[simp] theorem edges_restrictEdges (P : E → Prop) {s t : V}
    (p : HWalk inc s t) (h : ∀ e ∈ p.edges, P e) :
    (p.restrictEdges P h).edges = p.edges := by
  induction p with
  | nil => rfl
  | cons e hx hy p ih =>
    exact congrArg (List.cons e) (ih _)

@[simp] theorem vertices_restrictEdges (P : E → Prop) {s t : V}
    (p : HWalk inc s t) (h : ∀ e ∈ p.edges, P e) :
    (p.restrictEdges P h).vertices = p.vertices := by
  induction p with
  | nil => rfl
  | cons e hx hy p ih =>
    exact congrArg (List.cons _) (ih _)

/-- Split at an occurrence of an actual edge identifier. -/
theorem split_at_edge {s t : V} (w : HWalk inc s t) {e : E}
    (he : e ∈ w.edges) :
    ∃ (u v : V) (pre : HWalk inc s u) (suffix : HWalk inc v t),
      inc u e ∧ inc v e ∧
      w.edges = pre.edges ++ e :: suffix.edges := by
  induction w with
  | nil => simp only [edges, List.not_mem_nil] at he
  | @cons s a t f hx hy p ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨s, a, .nil s, p, hx, hy, rfl⟩
    · obtain ⟨u, v, pre, suffix, hu, hv, hs⟩ := ih he
      refine ⟨u, v, .cons f hx hy pre, suffix, hu, hv, ?_⟩
      simpa only [edges, List.cons_append] using congrArg (List.cons f) hs

/-- In an edge-simple walk, neither side of a split repeats the split edge.
Both remaining edge lists are themselves duplicate-free. -/
theorem split_at_edge_nodup {s t : V} (w : HWalk inc s t)
    (hw : w.edges.Nodup) {e : E} (he : e ∈ w.edges) :
    ∃ (u v : V) (pre : HWalk inc s u) (suffix : HWalk inc v t),
      inc u e ∧ inc v e ∧
      w.edges = pre.edges ++ e :: suffix.edges ∧
      e ∉ pre.edges ∧ e ∉ suffix.edges ∧
      pre.edges.Nodup ∧ suffix.edges.Nodup := by
  obtain ⟨u, v, pre, suffix, hu, hv, hs⟩ := w.split_at_edge he
  have hall : (pre.edges ++ e :: suffix.edges).Nodup := hs ▸ hw
  have hmiddle : (e :: (pre.edges ++ suffix.edges)).Nodup :=
    List.nodup_middle.mp hall
  have hnot := (List.nodup_cons.mp hmiddle).1
  refine ⟨u, v, pre, suffix, hu, hv, hs, ?_, ?_,
    hall.of_append_left, (List.nodup_cons.mp hall.of_append_right).2⟩
  · intro he
    exact hnot (List.mem_append_left _ he)
  · intro he
    exact hnot (List.mem_append_right _ he)

end FiniteFlow.Hypergraph.HWalk
