import MarginalEdgeCodes
import PathwidthForestGuidance
import GuidedSetBagAdapter

/-!
The A.2 family application consumes the exact ordered path certificates that
5.9 still has to construct. It does not claim their existence from treewidth.
The local graph is literally `Nested.marginalGraph`, and `2*k+2` is bag
cardinality, corresponding to conventional pathwidth at most `2*k+1`.
-/
namespace StackSorting.GraphWidth.MarginalA2.Local
open FinitePort Nested GuidedPathwidth IndexTreeAdapter
variable {n t k : Nat} {G : Graph n} {T : RootedTree t}

/-- Pure graph-record conversion; adjacency is unchanged. -/
def graphOriginal {q : Nat} (H : Graph q) : BiInterface.PathWord.Original (Fin q) where
  Adj := H.Adj
  symm := H.symm
  loopless := H.loopless

@[simp] theorem graphOriginal_adj {q : Nat} (H : Graph q) (u v : Fin q) :
    (graphOriginal H).Adj u v ↔ H.Adj u v := Iff.rfl

@[simp] theorem finiteGraph_graphOriginal {q : Nat} (H : Graph q) :
    finiteGraph (graphOriginal H).simple = H := by
  cases H
  rfl

/-- Required local certificates. This is an input family, not the 5.9
existence theorem. Each actual finite ordered list covers the exact marginal
vertices and edges and has convex vertex occurrences. -/
structure PathFamily (D : Decomposition G T) (k : Nat) where
  vertices : Fin t → Nat
  names : ∀ x, Fin (vertices x) ≃ {v : Fin n // introductionNode D v=x}
  path : ∀ x, BiInterface.PathWord.Decomposition
    (graphOriginal (marginalGraph D x (names x))) (2*k+2)

namespace PathFamily
variable {D : Decomposition G T} (F : PathFamily D k)

abbrev graph (x : Fin t) := marginalGraph D x (F.names x)
abbrev original (x : Fin t) := graphOriginal (F.graph x)
noncomputable abbrev palette := BiInterface.PathWord.pathwidthPalette (2*k+2)

/-- The accepted theorem is applied separately to every actual marginal. -/
theorem exists_guidance (x : Fin t) :
    ∃ E : ForestGuidedDecomposition (F.original x).simple Set.univ
      (BiInterface.PathWord.pathwidthPalette (2*k+2)),
      E.decomposition.forest.IsTree ∧
      ∀ a, Nat.card (E.decomposition.bag a) ≤ BiInterface.PathWord.pathwidthPalette (2*k+2) :=
  BiInterface.PathWord.exists_bounded_forest_guidance_of_path_decomposition (F.original x) (F.path x)

noncomputable def guidance (x : Fin t) :
    ForestGuidedDecomposition (F.original x).simple Set.univ
      (BiInterface.PathWord.pathwidthPalette (2*k+2)) := Classical.choose (F.exists_guidance x)

theorem guidance_tree (x : Fin t) : (F.guidance x).decomposition.forest.IsTree :=
  (Classical.choose_spec (F.exists_guidance x)).1

theorem guidance_bound (x : Fin t) (a : (F.guidance x).decomposition.Node) :
    Nat.card ((F.guidance x).decomposition.bag a) ≤ BiInterface.PathWord.pathwidthPalette (2*k+2) :=
  (Classical.choose_spec (F.exists_guidance x)).2 a

/-- Orientation and numbering are constructed from the actual guided tree. -/
noncomputable def numbering (x : Fin t) :
    NamedNumberedTree (F.guidance x).decomposition.forest :=
  guidedNumbering (F.guidance x) (F.guidance_tree x)

/-- An actual finite rooted-tree decomposition of the same marginal graph.
No decomposition extraction or reindexing witness is supplied as a premise. -/
noncomputable def localDecomposition (x : Fin t) :
    Decomposition (F.graph x) (F.numbering x).tree := by
  have E := reindexDecomposition (F.numbering x) (namedGuidedDecomposition (F.guidance x))
  simpa only [original,finiteGraph_graphOriginal] using E

theorem localDecomposition_bound (x : Fin t) :
    (F.localDecomposition x).BagBound (BiInterface.PathWord.pathwidthPalette (2*k+2)) := by
  exact reindexDecomposition_bound (F.numbering x)
    (namedGuidedDecomposition (F.guidance x)) (namedGuidedDecomposition_bound (F.guidance x))

/-- The original-vertex normalized forest is also constructed. Its nodes are
exactly the marginal vertices, a fact needed by fixed-copy local syntax. -/
noncomputable def normalized (x : Fin t) :
    ConnectedConeNormalization.ForestDecomposition (F.graph x) :=
  ConnectedConeNormalization.normalizeSupplied (F.localDecomposition x)

theorem normalized_bound (x : Fin t) (v : Fin (F.vertices x)) :
    ((F.normalized x).bag v).card ≤ BiInterface.PathWord.pathwidthPalette (2*k+2) :=
  ConnectedConeNormalization.normalizeSupplied_bound (F.localDecomposition x)
    (F.localDecomposition_bound x) v

/-- Normalization preserves capture of these actual local bags. This says
nothing about capture of outer bags or guidance on the whole original graph. -/
theorem normalized_capture (x : Fin t) (v : Fin (F.vertices x)) :
    ForestCaptures (F.guidance x).colors {u | u ∈ (F.normalized x).bag v} := by
  exact normalized_guided_capture (F.guidance x) (F.numbering x) v

/-- Combinatorial input for the independently authored flattening stage.
Its remaining geometric inputs concern the actual outer decomposition only. -/
noncomputable def nestedInput (outerNonempty : 0<t)
    (marginNonempty : ∀ x, ∃ v, introductionNode D v=x)
    (connector : ∀ x, x.val≠0 →
      ∃ v, introductionNode D v=T.parent x ∧ outerAdhesion D x v) : NestedInput D where
  outerNonempty := outerNonempty
  vertices := F.vertices
  names := F.names
  marginNonempty := marginNonempty
  nodes x := (F.numbering x).size
  localTree x := (F.numbering x).tree
  localDecomp := F.localDecomposition
  connector := connector

theorem nestedInput_bound (outerNonempty : 0<t)
    (marginNonempty : ∀ x, ∃ v, introductionNode D v=x)
    (connector : ∀ x, x.val≠0 →
      ∃ v, introductionNode D v=T.parent x ∧ outerAdhesion D x v) (x : Fin t) :
    ((F.nestedInput outerNonempty marginNonempty connector).localDecomp x).BagBound
      (BiInterface.PathWord.pathwidthPalette (2*k+2)) := F.localDecomposition_bound x

end PathFamily
#print axioms PathFamily.exists_guidance
#print axioms PathFamily.localDecomposition
#print axioms PathFamily.normalized_capture
#print axioms PathFamily.nestedInput
end StackSorting.GraphWidth.MarginalA2.Local
