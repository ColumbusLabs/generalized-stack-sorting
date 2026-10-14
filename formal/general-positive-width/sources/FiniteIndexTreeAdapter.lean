import SaneSingletonNormalization
import FiniteSpanningTree
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Exact orientation and topological numbering of an actual finite index
TREE. The acyclicity hypothesis is used to prove that no old edge is lost.
This is not an arbitrary connected-graph-to-decomposition shortcut. -/
namespace StackSorting.IndexTreeAdapter
open GraphWidth FinitePort
variable {n : Nat}

/-- Transport ordinary graph walks to the accepted guarded-walk interface. -/
theorem simple_to_guarded {α : Type} {H : SimpleGraph α} {x y : α}
    (p : H.Walk x y) : Walk H.Adj (fun _ => True) x y := by
  induction p with
  | nil => exact .refl trivial
  | cons h p ih => exact .step trivial h ih

/-- Transport the accepted guarded walk back to ordinary graph reachability. -/
theorem guarded_to_simple {α : Type} {H : SimpleGraph α} {P : α → Prop} {x y : α}
    (p : Walk H.Adj P x y) : H.Reachable x y := by
  induction p with
  | refl => exact ⟨.nil⟩
  | step _ h _ ih => obtain ⟨q⟩ := ih; exact ⟨.cons h q⟩

theorem treeAdj_irrefl (T : RootedTree n) (v : Fin n) : ¬ TreeAdj T v v := by
  intro h
  rcases h with ⟨hv,hp⟩ | ⟨hv,hp⟩ <;>
    have hh := T.parent_lt v hv <;> rw [hp] at hh <;> exact Nat.lt_irrefl _ hh

/-- The numbered tree reaches every node from its genuine index-zero root. -/
theorem zero_walk (T : RootedTree n) (z : Fin n) (hz : z.val = 0) (v : Fin n) :
    Walk (TreeAdj T) (fun _ => True) z v := by
  by_cases hv : v.val = 0
  · have he : z = v := Fin.ext (hz.trans hv.symm)
    subst v
    exact .refl trivial
  · exact (zero_walk T z hz (T.parent v)).trans
      (.step trivial (Or.inr ⟨hv,rfl⟩) (.refl trivial))
termination_by v.val
decreasing_by exact T.parent_lt v hv

/-- Map guarded walks while preserving every visited occurrence predicate. -/
theorem map_guarded {α β : Type} {A : α → α → Prop} {B : β → β → Prop}
    {P : α → Prop} {Q : β → Prop} (f : α → β)
    (ha : ∀ x y, A x y → B (f x) (f y)) (hp : ∀ x, P x → Q (f x))
    {x y} (p : Walk A P x y) : Walk B Q (f x) (f y) := by
  induction p with
  | refl h => exact .refl (hp _ h)
  | step h hab _ ih => exact .step (hp _ h) (ha _ _ hab) ih

def selectedGraph {H : SimpleGraph (Fin n)} {root : Fin n}
    (S : RelabeledSpanningTree H.Adj root) : SimpleGraph (Fin n) where
  Adj u v := TreeAdj S.tree (S.index u) (S.index v)
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun v => treeAdj_irrefl S.tree (S.index v)⟩

/-- For an actual tree, the selected spanning-tree edges are all original
edges, not merely a subset. -/
theorem selectedGraph_exact {H : SimpleGraph (Fin n)} (hH : H.IsTree)
    {root : Fin n} (S : RelabeledSpanningTree H.Adj root) : selectedGraph S = H := by
  have hle : selectedGraph S ≤ H := by
    intro u v huv
    have h := S.edge (fun h => H.adj_symm h) huv
    simpa only [S.label_index] using h
  have hc : (selectedGraph S).Connected := by
    let : Nonempty (Fin n) := ⟨root⟩
    refine ⟨?_⟩
    intro u v
    have walk_to (x : Fin n) : (selectedGraph S).Reachable root x := by
      have p := zero_walk S.tree (S.index root) S.index_root_val (S.index x)
      have q : Walk (selectedGraph S).Adj (fun _ => True) root x := by
        have pp := map_guarded (B := (selectedGraph S).Adj)
          (Q := fun _ => True) S.label
          (fun a b hab => by simpa only [selectedGraph,S.index_label] using hab)
          (fun _ _ => trivial) p
        simpa only [S.label_index] using pp
      exact guarded_to_simple q
    exact (walk_to u).symm.trans (walk_to v)
  exact le_antisymm hle ((SimpleGraph.isTree_iff_minimal_connected.mp hH).2 hc hle)

structure NumberedIndexTree (H : SimpleGraph (Fin n)) where
  tree : RootedTree n
  names : Fin n ≃ Fin n
  edge_iff : ∀ i j, TreeAdj tree i j ↔ H.Adj (names i) (names j)

noncomputable def numberTree {H : SimpleGraph (Fin n)} (hH : H.IsTree) : NumberedIndexTree H := by
  let root : Fin n := Classical.choice hH.connected.nonempty
  have hc : ∀ u v, Walk H.Adj (fun _ => True) u v := by
    intro u v
    obtain ⟨p⟩ := hH.connected.preconnected u v
    exact simple_to_guarded p
  let S := relabeledSpanningTree H.Adj hc root
  refine ⟨S.tree,⟨S.label,S.index,S.index_label,S.label_index⟩,?_⟩
  intro i j
  change TreeAdj S.tree i j ↔ H.Adj (S.label i) (S.label j)
  have hh := congrArg (fun K : SimpleGraph (Fin n) => K.Adj (S.label i) (S.label j))
    (selectedGraph_exact hH S)
  simpa only [selectedGraph,S.index_label] using Iff.of_eq hh

#print axioms selectedGraph_exact
#print axioms numberTree
end StackSorting.IndexTreeAdapter
