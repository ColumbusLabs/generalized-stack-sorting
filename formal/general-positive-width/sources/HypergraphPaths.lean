import FiniteDirectedPath
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sum

/-! Hypergraph paths retain actual edge identifiers, including parallel edges. -/
namespace FiniteFlow.Hypergraph

universe u v
variable {V : Type u} {E : Type v}

inductive Node (V : Type u) (E : Type v)
  | vertex : V → Node V E
  | enter : E → Node V E
  | leave : E → Node V E
  deriving DecidableEq, Fintype

inductive Step (inc : V → E → Prop) : Node V E → Node V E → Prop
  | enter {x e} : inc x e → Step inc (.vertex x) (.enter e)
  | cross (e) : Step inc (.enter e) (.leave e)
  | leave {x e} : inc x e → Step inc (.leave e) (.vertex x)

inductive HWalk (inc : V → E → Prop) : V → V → Type (max u v)
  | nil (x) : HWalk inc x x
  | cons {x y t} (e : E) (hx : inc x e) (hy : inc y e)
      (tail : HWalk inc y t) : HWalk inc x t

namespace HWalk
variable {inc : V → E → Prop}

def vertices {s t} : HWalk inc s t → List V
  | .nil s => [s]
  | .cons (x := s) _ _ _ p => s :: p.vertices

def edges {s t} : HWalk inc s t → List E
  | .nil _ => []
  | .cons e _ _ p => e :: p.edges

def split {s t} : HWalk inc s t → DWalk (Step inc) (Node.vertex s) (Node.vertex t)
  | .nil s => .nil (Node.vertex s)
  | .cons e hx hy p => .cons (.enter hx) (.cons (.cross e) (.cons (.leave hy) p.split))

end HWalk

/-- An actual alternating path: neither vertices nor edge identifiers repeat. -/
structure Path (inc : V → E → Prop) (s t : V) where
  walk : HWalk inc s t
  vertices_nodup : walk.vertices.Nodup
  edges_nodup : walk.edges.Nodup

end FiniteFlow.Hypergraph

namespace FiniteFlow.DWalk
open Hypergraph
variable {V : Type*} {E : Type*} {inc : V → E → Prop}

/-- The split-incidence shape groups directed arcs into actual hyperedge steps.
The existence proof eliminates the propositional incidence relation only into Prop. -/
theorem exists_collapse {s t : V}
    (p : DWalk (Step inc) (Node.vertex s) (Node.vertex t)) :
    ∃ q : HWalk inc s t,
      (q.vertices.map Node.vertex).Sublist p.vertices ∧
      (q.edges.map Node.enter).Sublist p.vertices ∧
      ∀ e, e ∈ q.edges ↔ p.Uses (Node.enter e) (Node.leave e) := by
  suffices h : ∀ n, ∀ {s t : V}
      (p : DWalk (Step inc) (Node.vertex s) (Node.vertex t)),
      p.vertices.length ≤ n →
      ∃ q : HWalk inc s t,
        (q.vertices.map Node.vertex).Sublist p.vertices ∧
        (q.edges.map Node.enter).Sublist p.vertices ∧
        ∀ e, e ∈ q.edges ↔ p.Uses (Node.enter e) (Node.leave e) by
    exact h _ p le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s t p hn
    cases p with
    | nil =>
      refine ⟨.nil _, .refl _, .cons _ .slnil, ?_⟩
      intro e
      simp [HWalk.edges, Uses]
    | cons h₁ p₁ =>
      cases h₁ with
      | enter hx =>
        cases p₁ with
        | cons h₂ p₂ =>
          cases h₂ with
          | cross e =>
            cases p₂ with
            | cons h₃ p₃ =>
              cases h₃ with
              | leave hy =>
                have hlt : p₃.vertices.length < n := by
                  simp only [vertices, List.length_cons] at hn
                  omega
                obtain ⟨q, hv, he, huse⟩ := ih _ hlt p₃ le_rfl
                refine ⟨.cons _ hx hy q, ?_, ?_, ?_⟩
                · exact .cons_cons _ (.cons _ (.cons _ hv))
                · exact .cons _ (.cons_cons _ (.cons _ he))
                · intro f
                  simp [HWalk.edges, Uses, huse]

/-- Project a split-incidence walk to a hypergraph walk with actual edge IDs. -/
noncomputable def collapse {s t : V}
    (p : DWalk (Step inc) (Node.vertex s) (Node.vertex t)) : HWalk inc s t :=
  Classical.choose p.exists_collapse

/-- Original vertices survive projection as a subsequence of split vertices. -/
theorem collapse_vertices_sublist {s t : V}
    (p : DWalk (Step inc) (Node.vertex s) (Node.vertex t)) :
    (p.collapse.vertices.map Node.vertex).Sublist p.vertices :=
  (Classical.choose_spec p.exists_collapse).1

/-- Every edge identifier is represented by its unique entry node. -/
theorem collapse_edges_sublist {s t : V}
    (p : DWalk (Step inc) (Node.vertex s) (Node.vertex t)) :
    (p.collapse.edges.map Node.enter).Sublist p.vertices :=
  (Classical.choose_spec p.exists_collapse).2.1

theorem collapse_simple {s t : V}
    (p : DWalk (Step inc) (Node.vertex s) (Node.vertex t))
    (hp : p.vertices.Nodup) :
    p.collapse.vertices.Nodup ∧ p.collapse.edges.Nodup := by
  exact ⟨List.Nodup.of_map Node.vertex (hp.sublist p.collapse_vertices_sublist),
    List.Nodup.of_map Node.enter (hp.sublist p.collapse_edges_sublist)⟩

/-- A projected edge occurs exactly when its capacity-controlling cross arc occurs. -/
theorem collapse_edge_iff {s t : V}
    (p : DWalk (Step inc) (Node.vertex s) (Node.vertex t)) (e : E) :
    e ∈ p.collapse.edges ↔ p.Uses (Node.enter e) (Node.leave e) :=
  (Classical.choose_spec p.exists_collapse).2.2 e

end FiniteFlow.DWalk

namespace FiniteFlow.Hypergraph.HWalk
variable {V : Type*} {E : Type*} {inc : V → E → Prop}

theorem split_uses_cross_iff {s t} (p : HWalk inc s t) (e : E) :
    p.split.Uses (.enter e) (.leave e) ↔ e ∈ p.edges := by
  induction p with
  | nil => simp [split, FiniteFlow.DWalk.Uses, edges]
  | cons f hx hy p ih => simp [split, FiniteFlow.DWalk.Uses, edges, ih]

/-- Every hypergraph walk yields an actual vertex- and edge-simple path.
Its edge IDs are a subset of the original walk's edge IDs. -/
theorem exists_path {s t} (p : HWalk inc s t) :
    ∃ q : Path inc s t, ∀ e ∈ q.walk.edges, e ∈ p.edges := by
  obtain ⟨z, hz, hsub⟩ := p.split.erase_loops
  have hsimple := DWalk.collapse_simple z hz
  refine ⟨⟨z.collapse, hsimple.1, hsimple.2⟩, ?_⟩
  intro e he
  exact (p.split_uses_cross_iff e).mp
    (hsub _ _ ((DWalk.collapse_edge_iff z e).mp he))

end FiniteFlow.Hypergraph.HWalk
