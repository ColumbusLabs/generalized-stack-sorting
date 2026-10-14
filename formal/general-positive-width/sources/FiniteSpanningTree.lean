import ConnectedFiberDecomposition

/-!
A finite connected graph has an actual parent-numbered spanning tree after a
bijective relabeling. The construction grows a connected enumeration, retaining
any existing connected prefix, and chooses an earlier graph neighbor as parent.
Only Lean Core/Std and the existing graph/tree interfaces are used.
-/
namespace StackSorting.GraphWidth
open FinitePort

/-- Every noninitial entry has a graph neighbor earlier in the enumeration. -/
def EarlierNeighbors {α : Type} (adj : α → α → Prop) (xs : List α) : Prop :=
  ∀ (i : Nat) (hi : i < xs.length), i ≠ 0 →
    ∃ (j : Nat) (hj : j < xs.length), j < i ∧ adj xs[j] xs[i]

/-- A walk from a listed vertex to an unlisted one has an actual crossing edge. -/
theorem Walk.exists_crossing {α : Type} {adj : α → α → Prop} {P}
    {a b : α} (w : Walk adj P a b) (S : α → Prop)
    (ha : S a) (hb : ¬ S b) : ∃ u v, S u ∧ ¬ S v ∧ adj u v := by
  classical
  induction w with
  | refl => exact False.elim (hb ha)
  | @step a c b _ hac _ ih =>
    by_cases hc : S c
    · exact ih hc hb
    · exact ⟨a, c, ha, hc, hac⟩

theorem EarlierNeighbors.append_one {α : Type} {adj : α → α → Prop}
    {xs : List α} (h : EarlierNeighbors adj xs) {u v : α}
    (hu : u ∈ xs) (huv : adj u v) : EarlierNeighbors adj (xs ++ [v]) := by
  intro i hi hn
  by_cases hil : i < xs.length
  · obtain ⟨j, hj, hji, he⟩ := h i hil hn
    refine ⟨j, by simp; omega, hji, ?_⟩
    simpa only [List.getElem_append_left hil, List.getElem_append_left hj] using he
  · have heq : i = xs.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hi
      omega
    subst i
    obtain ⟨j, hj, hju⟩ := List.mem_iff_getElem.mp hu
    refine ⟨j, by simp; omega, hj, ?_⟩
    simpa only [List.getElem_append_left hj, List.getElem_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem_cons_zero, hju] using huv

theorem fin_list_length_le {n} {xs : List (Fin n)} (h : xs.Nodup) : xs.length ≤ n := by
  have := h.length_le_of_subset (l₂ := List.finRange n) (by
    intro v _; exact List.mem_finRange v)
  simpa using this

theorem fin_list_length_lt_of_missing {n} {xs : List (Fin n)}
    (h : xs.Nodup) {v : Fin n} (hv : v ∉ xs) : xs.length < n := by
  have h' : (v :: xs).Nodup := List.nodup_cons.mpr ⟨hv, h⟩
  have := fin_list_length_le h'
  simp only [List.length_cons] at this
  omega

/-- Extend any nonempty connected prefix to an exhaustive connected enumeration.
The original entries retain their order, with new vertices appended only. -/
theorem extend_connected_enumeration {n} (adj : Fin n → Fin n → Prop)
    (connected : ∀ u v, Walk adj (fun _ => True) u v)
    (xs : List (Fin n)) (hn : xs.Nodup) (he : EarlierNeighbors adj xs)
    (hne : xs ≠ []) :
    ∃ ys, (xs ++ ys).Nodup ∧ EarlierNeighbors adj (xs ++ ys) ∧
      ∀ v, v ∈ xs ++ ys := by
  classical
  by_cases hc : ∀ v, v ∈ xs
  · exact ⟨[], by simpa using hn, by simpa using he, by simpa using hc⟩
  · obtain ⟨v, hv⟩ := Classical.not_forall.mp hc
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil xs hne
    obtain ⟨u, w, hu, hw, huw⟩ := (connected r v).exists_crossing
      (fun q => q ∈ xs) hr hv
    have hn' : (xs ++ [w]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hn, by simp, ?_⟩
      intro x hx y hy
      have hyw : y = w := by simpa using hy
      subst y
      intro h
      subst x
      exact hw hx
    have hne' : xs ++ [w] ≠ [] := by simp
    obtain ⟨ys, hyn, hye, hyc⟩ := extend_connected_enumeration adj connected
      (xs ++ [w]) hn' (he.append_one hu huw) hne'
    refine ⟨w :: ys, ?_, ?_, ?_⟩
    · simpa [List.append_assoc] using hyn
    · simpa [List.append_assoc] using hye
    · simpa [List.append_assoc] using hyc
termination_by n - xs.length
decreasing_by
  have hlt := fin_list_length_lt_of_missing hn hw
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- A complete, duplicate-free vertex order with a specified first vertex. -/
structure RootedEnumeration {n} (adj : Fin n → Fin n → Prop) (root : Fin n) where
  vertices : List (Fin n)
  nodup : vertices.Nodup
  complete : ∀ v, v ∈ vertices
  earlier : EarlierNeighbors adj vertices
  first : vertices[0]? = some root

namespace RootedEnumeration

theorem length_eq {n adj root} (E : @RootedEnumeration n adj root) :
    E.vertices.length = n := by
  have hle := fin_list_length_le E.nodup
  have hge := (List.nodup_finRange n).length_le_of_subset (l₂ := E.vertices)
    (by intro v _; exact E.complete v)
  simp only [List.length_finRange] at hge
  omega

def label {n adj root} (E : @RootedEnumeration n adj root) (i : Fin n) : Fin n :=
  E.vertices[i.val]'(by rw [E.length_eq]; exact i.isLt)

def index {n adj root} (E : @RootedEnumeration n adj root) (v : Fin n) : Fin n :=
  ⟨E.vertices.idxOf v, by
    have h := List.idxOf_lt_length_of_mem (E.complete v)
    simpa only [E.length_eq] using h⟩

@[simp] theorem label_index {n adj root} (E : @RootedEnumeration n adj root) (v : Fin n) :
    E.label (E.index v) = v := by
  exact List.getElem_idxOf _

@[simp] theorem index_label {n adj root} (E : @RootedEnumeration n adj root) (i : Fin n) :
    E.index (E.label i) = i := by
  apply Fin.ext
  exact E.nodup.idxOf_getElem _ _

theorem label_root {n adj root} (E : @RootedEnumeration n adj root) (i : Fin n)
    (hi : i.val = 0) : E.label i = root := by
  have hget := List.getElem?_eq_getElem (show i.val < E.vertices.length by
    rw [E.length_eq]; exact i.isLt)
  have hroot : E.vertices[i.val]? = some root := by simpa only [hi] using E.first
  exact Option.some.inj (hget.symm.trans hroot)

theorem predecessor {n adj root} (E : @RootedEnumeration n adj root) (i : Fin n)
    (hi : i.val ≠ 0) : ∃ j : Fin n, j.val < i.val ∧ adj (E.label j) (E.label i) := by
  obtain ⟨j, hj, hji, he⟩ := E.earlier i.val (by rw [E.length_eq]; exact i.isLt) hi
  exact ⟨⟨j, by rw [← E.length_eq]; exact hj⟩, hji, he⟩

noncomputable def parent {n adj root} (E : @RootedEnumeration n adj root) (i : Fin n) :
    Fin n :=
  if hi : i.val = 0 then i else Classical.choose (E.predecessor i hi)

noncomputable def tree {n adj root} (E : @RootedEnumeration n adj root) : RootedTree n where
  parent := E.parent
  parent_lt := by
    intro i hi
    simp only [parent, dite_eq_right hi]
    exact (Classical.choose_spec (E.predecessor i hi)).1

theorem parent_edge {n adj root} (E : @RootedEnumeration n adj root) (i : Fin n)
    (hi : i.val ≠ 0) : adj (E.label (E.tree.parent i)) (E.label i) := by
  simp only [tree, parent, dite_eq_right hi]
  exact (Classical.choose_spec (E.predecessor i hi)).2

@[simp] theorem parent_root {n adj root} (E : @RootedEnumeration n adj root) (i : Fin n)
    (hi : i.val = 0) : E.tree.parent i = i := by simp [tree, parent, hi]

end RootedEnumeration

/-- All data of a spanning tree, including the two-sided vertex relabeling.
The labels send parent-tree edges to actual edges of the original graph. -/
structure RelabeledSpanningTree {n} (adj : Fin n → Fin n → Prop) (root : Fin n) where
  tree : RootedTree n
  label : Fin n → Fin n
  index : Fin n → Fin n
  label_index : ∀ v, label (index v) = v
  index_label : ∀ i, index (label i) = i
  label_root : ∀ i, i.val = 0 → label i = root
  parent_root : ∀ i, i.val = 0 → tree.parent i = i
  parent_edge : ∀ i, i.val ≠ 0 → adj (label (tree.parent i)) (label i)

noncomputable def RootedEnumeration.toSpanningTree {n adj root}
    (E : @RootedEnumeration n adj root) : RelabeledSpanningTree adj root where
  tree := E.tree
  label := E.label
  index := E.index
  label_index := E.label_index
  index_label := E.index_label
  label_root := E.label_root
  parent_root := E.parent_root
  parent_edge := E.parent_edge

/-- Connectedness alone constructs a complete rooted enumeration. -/
theorem exists_rooted_enumeration {n} (adj : Fin n → Fin n → Prop)
    (connected : ∀ u v, Walk adj (fun _ => True) u v) (root : Fin n) :
    Nonempty (RootedEnumeration adj root) := by
  have he : EarlierNeighbors adj [root] := by
    intro i hi hn
    simp only [List.length_cons, List.length_nil] at hi
    omega
  obtain ⟨ys, hn, he, hc⟩ := extend_connected_enumeration adj connected [root]
    (by simp) he (by simp)
  exact ⟨⟨root :: ys, by simpa using hn, by simpa using hc,
    by simpa using he, by simp⟩⟩

/-- Every connected finite graph has an actual spanning tree after relabeling.
A root vertex supplies nonemptiness; symmetry is only needed for undirected
edge containment, proved separately below. -/
theorem exists_relabeled_spanning_tree {n} (adj : Fin n → Fin n → Prop)
    (connected : ∀ u v, Walk adj (fun _ => True) u v) (root : Fin n) :
    Nonempty (RelabeledSpanningTree adj root) := by
  obtain ⟨E⟩ := exists_rooted_enumeration adj connected root
  exact ⟨E.toSpanningTree⟩

noncomputable def relabeledSpanningTree {n} (adj : Fin n → Fin n → Prop)
    (connected : ∀ u v, Walk adj (fun _ => True) u v) (root : Fin n) :
    RelabeledSpanningTree adj root :=
  Classical.choice (exists_relabeled_spanning_tree adj connected root)

namespace RelabeledSpanningTree

theorem label_injective {n adj root} (S : @RelabeledSpanningTree n adj root)
    {i j} (h : S.label i = S.label j) : i = j := by
  have := congrArg S.index h
  simpa only [S.index_label] using this

theorem label_surjective {n adj root} (S : @RelabeledSpanningTree n adj root) (v) :
    ∃ i, S.label i = v := ⟨S.index v, S.label_index v⟩

theorem edge {n adj root} (S : @RelabeledSpanningTree n adj root)
    (symm : ∀ {u v}, adj u v → adj v u) {i j} (h : TreeAdj S.tree i j) :
    adj (S.label i) (S.label j) := by
  obtain ⟨hi, hp⟩ | ⟨hj, hp⟩ := h
  · rw [← hp]
    exact symm (S.parent_edge i hi)
  · rw [← hp]
    exact S.parent_edge j hj

/-- The original root receives index zero. -/
theorem index_root_val {n adj root} (S : @RelabeledSpanningTree n adj root) :
    (S.index root).val = 0 := by
  let z : Fin n := ⟨0, by have := root.isLt; omega⟩
  have hz := S.label_root z rfl
  have hh : S.index root = z := (congrArg S.index hz).symm.trans (S.index_label z)
  exact congrArg Fin.val hh

/-- Distinct nonroot vertices select distinct undirected parent edges.
This is the edge-injectivity fact used by finite primal/dual edge counts. -/
theorem parent_edge_injective {n adj root} (S : @RelabeledSpanningTree n adj root)
    {i j : Fin n} (hi : i.val ≠ 0) (hj : j.val ≠ 0)
    (he : (S.label i = S.label j ∧
      S.label (S.tree.parent i) = S.label (S.tree.parent j)) ∨
      (S.label i = S.label (S.tree.parent j) ∧
      S.label (S.tree.parent i) = S.label j)) : i = j := by
  obtain h | h := he
  · exact S.label_injective h.1
  · have hij := S.label_injective h.1
    have hji := S.label_injective h.2
    have hli := S.tree.parent_lt i hi
    have hlj := S.tree.parent_lt j hj
    rw [hji] at hli
    rw [← hij] at hlj
    omega

end RelabeledSpanningTree

/-- Ready-to-use constructor for the existing finite undirected graph API. -/
noncomputable def Graph.spanningTree {n} (G : Graph n)
    (connected : ∀ u v, Walk G.Adj (fun _ => True) u v) (hpos : 0 < n) :
    RelabeledSpanningTree G.Adj ⟨0, hpos⟩ :=
  relabeledSpanningTree G.Adj connected ⟨0, hpos⟩

end StackSorting.GraphWidth
