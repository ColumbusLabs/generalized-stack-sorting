import GuidedFactorizationInduction
import DecompositionUniverseTransport
import DecompositionTreeCompletion

namespace StackSorting.BiInterface.PathWord
open GuidedPathwidth RepeatedColumn
universe u
variable {V : Type u} {k : Nat}

def Original.simple (G : Original V) : SimpleGraph V where
  Adj := G.Adj
  symm := ⟨fun _ _ h => G.symm h⟩
  loopless := ⟨G.loopless⟩

/-- A coarse parameter-only palette budget. Arity k means bags of cardinality
at most k, or conventional pathwidth at most k-1 when k is positive. -/
noncomputable def pathwidthPalette (k : Nat) : Nat :=
  paletteBound k (Simon.monoidForestBound (Fintype.card (Abstract k)+1))

/-- Genuine bounded guidance from a supplied finite ordered path decomposition.
The small-piece word, quotient reconstruction, factorization tree, final bags
and actual rooted guides are all constructed; no guidance witness is assumed. -/
theorem exists_guided_path_decomposition [DecidableEq V]
    (G : Original V) (D : Decomposition G k) :
    Nonempty (GuidedDecomposition G.simple Set.univ (pathwidthPalette k)) := by
  obtain ⟨ws,hne,hsmall,hlen,hrecon,t,ht,hv,hh⟩ := exists_path_decomposition_factorization G D
  obtain ⟨E⟩ := exists_guided_factorization t hv (by simpa only [ht] using hsmall)
  have E' : GuidedDecomposition (Packed.eval ws).graph.simple Set.univ (pathwidthPalette k) := by
    rw [← ht]
    exact E.pad (paletteBound_mono k hh)
  obtain ⟨R⟩ := hrecon
  let F := E'.liftMapRegion (H := G.simple) R.vertex.toEmbedding
    (fun {a b} h => (R.adj a b).mp h)
    (fun {a b} _ _ h => (R.adj a b).mpr h)
  have he : R.vertex.toEmbedding '' Set.univ = Set.univ := by
    ext y
    constructor
    · intro h; trivial
    · intro h
      obtain ⟨x,rfl⟩ := R.vertex.surjective y
      exact ⟨x,trivial,rfl⟩
  exact ⟨he ▸ F⟩

/-- A single actual index tree can be obtained with the same palette and bag
bound, including for an empty original graph. The new root bag is empty. -/
theorem exists_tree_guided_path_decomposition [DecidableEq V]
    (G : Original V) (D : Decomposition G k) :
    ∃ E : GuidedDecomposition G.simple Set.univ (pathwidthPalette k),
      E.decomposition.forest.IsTree := by
  obtain ⟨E⟩ := exists_guided_path_decomposition G D
  exact E.exists_treeCompletion

#print axioms exists_guided_path_decomposition
#print axioms exists_tree_guided_path_decomposition
end StackSorting.BiInterface.PathWord
