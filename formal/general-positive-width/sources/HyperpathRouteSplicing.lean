import HypergraphPathEmbedding
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

namespace FiniteFlow.Hypergraph
variable {V E : Type} {inc : V → E → Prop}
namespace HWalk

/-- The actual ordered traversal demands of a hyperwalk, retaining each
hyperedge identifier and both incident endpoints. -/
def traversals {s t : V} : HWalk inc s t → List (V × E × V)
  | .nil _ => []
  | .cons (x := a) (y := b) e _ _ tail => (a,e,b) :: tail.traversals

theorem start_mem_vertices {s t : V} (w : HWalk inc s t) : s ∈ w.vertices := by
  cases w <;> simp [vertices]

theorem traversal_incident {s t : V} (w : HWalk inc s t) {a b : V} {e : E}
    (h : (a,e,b) ∈ w.traversals) : inc a e ∧ inc b e := by
  induction w with
  | nil => simp [traversals] at h
  | @cons s u t f hs hu tail ih =>
    rcases List.mem_cons.mp h with he | he
    · have he' : a = s ∧ e = f ∧ b = u := by simpa using he
      rcases he' with ⟨rfl,rfl,rfl⟩
      exact ⟨hs,hu⟩
    · exact ih he

theorem traversal_edges {s t : V} (w : HWalk inc s t) :
    w.traversals.map (fun z => z.2.1) = w.edges := by
  induction w with
  | nil => rfl
  | @cons _ _ _ e _ _ _ ih => simpa [traversals,edges] using congrArg (List.cons e) ih

/-- Replace every actual traversal with an original-edge walk. The output
support is contained in the old hyperwalk vertices together with the supports
assigned to the hyperedges it actually uses. -/
theorem splice_original_walk {s t : V} (w : HWalk inc s t)
    (adj : V → V → Prop) (inside : E → V → Prop)
    (segments : ∀ a e b, (a,e,b) ∈ w.traversals →
      StackSorting.GraphWidth.Walk adj (fun x => x = a ∨ x = b ∨ inside e x) a b) :
    StackSorting.GraphWidth.Walk adj
      (fun x => x ∈ w.vertices ∨ ∃ e ∈ w.edges, inside e x) s t := by
  induction w with
  | nil s => exact .refl (Or.inl (by simp [vertices]))
  | @cons s u t e hs hu tail ih =>
    have hseg := segments s e u (List.mem_cons_self)
    have htail := ih (fun a f b h => segments a f b (List.mem_cons_of_mem _ h))
    apply StackSorting.GraphWidth.Walk.trans (hseg.mono (fun x hx => ?_))
      (htail.mono (fun x hx => ?_))
    · rcases hx with rfl | rfl | hx
      · exact Or.inl (List.mem_cons_self)
      · exact Or.inl (List.mem_cons_of_mem _ tail.start_mem_vertices)
      · exact Or.inr ⟨e,List.mem_cons_self,hx⟩
    · rcases hx with hx | ⟨f,hf,hx⟩
      · exact Or.inl (List.mem_cons_of_mem _ hx)
      · exact Or.inr ⟨f,List.mem_cons_of_mem _ hf,hx⟩
end HWalk
end FiniteFlow.Hypergraph

namespace StackSorting.LowPathwidthParts
/-- Turn a support-restricted propositional original-edge walk into an actual
SimpleGraph walk without weakening its support restriction. -/
theorem exists_simple_walk {V : Type} (G : SimpleGraph V) {P : V → Prop} {s t : V}
    (h : GraphWidth.Walk G.Adj P s t) :
    ∃ p : G.Walk s t, ∀ x ∈ p.support, P x := by
  induction h with
  | refl hs => exact ⟨.nil,by simpa using hs⟩
  | @step s u t hs hsu tail ih =>
    obtain ⟨p,hp⟩ := ih
    refine ⟨.cons hsu p,?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hs
    · exact hp x hx
end StackSorting.LowPathwidthParts
