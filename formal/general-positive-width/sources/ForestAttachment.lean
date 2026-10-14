import ForestIsolatedVertex
import DecompositionRestriction

namespace StackSorting.GuidedPathwidth
universe u
variable {N : Type u}

/-- Candidate edges attach one new node to the selected old forest components. -/
def attachmentGraph (T : SimpleGraph N) (M : Set N) : SimpleGraph (Option N) where
  Adj x y := match x,y with
    | none,none => False
    | none,some b => b ∈ M
    | some a,none => a ∈ M
    | some a,some b => T.Adj a b
  symm := ⟨by intro x y h; cases x <;> cases y <;> simp_all [SimpleGraph.adj_comm]⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

def attachmentSupport (M : Set N) : Set (Option N) :=
  {x | match x with | none => True | some a => a ∈ M}

theorem isolated_le_attachment (T : SimpleGraph N) (M : Set N) :
    withIsolated T ≤ attachmentGraph T M := by
  intro x y h
  cases x <;> cases y <;> simp_all [withIsolated,attachmentGraph]

theorem attachment_closed {T : SimpleGraph N} {M : Set N}
    (hM : ∀ {a b}, T.Adj a b → a ∈ M → b ∈ M)
    {x y : Option N} (h : (attachmentGraph T M).Adj x y)
    (hx : x ∈ attachmentSupport M) : y ∈ attachmentSupport M := by
  cases x <;> cases y <;> simp_all [attachmentGraph,attachmentSupport]
  all_goals exact hM h hx

/-- A real finite-index forest is obtained while retaining every old edge.
The new node connects all selected components without introducing a cycle. -/
structure AttachedForest (T : SimpleGraph N) (M : Set N) where
  graph : SimpleGraph (Option N)
  acyclic : graph.IsAcyclic
  oldEdges : withIsolated T ≤ graph
  allowedEdges : graph ≤ attachmentGraph T M
  markedConnected : ∀ a ∈ M,
    ReachIn graph (attachmentSupport M) none (some a)

theorem exists_attached_forest {T : SimpleGraph N} {M : Set N}
    (hT : T.IsAcyclic) (hM : ∀ {a b}, T.Adj a b → a ∈ M → b ∈ M) :
    Nonempty (AttachedForest T M) := by
  obtain ⟨F,hOld,hNew,ha,heq⟩ :=
    (attachmentGraph T M).exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic
      (isolated_le_attachment T M) (withIsolated_acyclic hT)
  refine ⟨⟨F,ha,hOld,hNew,?_⟩⟩
  intro a haM
  have hr : F.Reachable none (some a) := by
    rw [heq]
    exact (show (attachmentGraph T M).Adj none (some a) from haM).reachable
  obtain ⟨p⟩ := hr
  have hs : ∀ x ∈ p.support, x ∈ attachmentSupport M := by
    suffices ∀ {x y : Option N} (q : F.Walk x y),
        x ∈ attachmentSupport M → ∀ z ∈ q.support, z ∈ attachmentSupport M by
      exact this p trivial
    intro x y q
    induction q with
    | @nil x =>
      intro hx z hz
      have he : z = x := by simpa using hz
      exact he.symm ▸ hx
    | @cons x y z hxy q ih =>
      intro hx w hw
      simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact hx
      · exact ih (attachment_closed hM (hNew hxy) hx) w hw
  exact reachIn_of_induced ⟨p.induce (attachmentSupport M) hs⟩

#print axioms exists_attached_forest
end StackSorting.GuidedPathwidth
