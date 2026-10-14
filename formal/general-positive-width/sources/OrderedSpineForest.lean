import DecompositionForests
import Mathlib.Combinatorics.SimpleGraph.Hasse

namespace StackSorting.GuidedPathwidth

/-- Every spanning subgraph preserving path-graph reachability contains each
consecutive edge: a finite walk must cross the corresponding ordered cut. -/
theorem pathGraph_le_of_reachable {n : Nat} {F : SimpleGraph (Fin n)}
    (hF : F ≤ SimpleGraph.pathGraph n)
    (hR : F.Reachable = (SimpleGraph.pathGraph n).Reachable) :
    SimpleGraph.pathGraph n ≤ F := by
  have step : ∀ (i j : Fin n), i.val+1 = j.val → F.Adj i j := by
    intro i j hij
    by_contra hne
    have closed : ∀ {a b : Fin n}, F.Adj a b → a.val ≤ i.val → b.val ≤ i.val := by
      intro a b hab ha
      have hp := SimpleGraph.pathGraph_adj.mp (hF hab)
      by_contra hb
      have hai : a = i := by apply Fin.ext; omega
      have hbj : b = j := by apply Fin.ext; omega
      exact hne (hai ▸ hbj ▸ hab)
    have reach : F.Reachable i j := by
      rw [hR]
      exact (SimpleGraph.pathGraph_adj.mpr (Or.inl hij)).reachable
    obtain ⟨p⟩ := reach
    have stay : ∀ {a b : Fin n} (q : F.Walk a b), a.val ≤ i.val → b.val ≤ i.val := by
      intro a b q
      induction q with
      | nil => exact id
      | cons h q ih => exact fun ha => ih (closed h ha)
    have hh := stay p (le_refl _)
    omega
  intro i j hij
  rcases SimpleGraph.pathGraph_adj.mp hij with h | h
  · exact step i j h
  · exact (step j i h).symm

/-- The finite ordered spine is an actual acyclic graph. -/
theorem pathGraph_acyclic (n : Nat) : (SimpleGraph.pathGraph n).IsAcyclic := by
  obtain ⟨F,hF,hA,hR⟩ := (SimpleGraph.pathGraph n).exists_isAcyclic_reachable_eq_le
  have heq : F = SimpleGraph.pathGraph n := le_antisymm hF (pathGraph_le_of_reachable hF hR)
  exact heq ▸ hA

#print axioms pathGraph_acyclic
end StackSorting.GuidedPathwidth
