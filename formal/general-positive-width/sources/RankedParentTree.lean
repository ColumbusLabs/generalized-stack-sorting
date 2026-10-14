import FiniteSpanningTree

/-! A parent map with a strictly decreasing natural rank has an exact,
parent-numbered finite-tree representation. No spanning tree or encoding is
assumed: the enumeration is constructed from directed root reachability. -/
namespace StackSorting.GraphWidth
open FinitePort

/-- Extend a connected prefix using only directed paths from its fixed root. -/
theorem extend_root_reachable_enumeration {n} (adj : Fin n → Fin n → Prop)
    (root : Fin n) (reachable : ∀ v, Walk adj (fun _ => True) root v)
    (xs : List (Fin n)) (hn : xs.Nodup) (he : EarlierNeighbors adj xs)
    (hr : root ∈ xs) :
    ∃ ys, (xs ++ ys).Nodup ∧ EarlierNeighbors adj (xs ++ ys) ∧
      ∀ v, v ∈ xs ++ ys := by
  classical
  by_cases hc : ∀ v, v ∈ xs
  · exact ⟨[], by simpa using hn, by simpa using he, by simpa using hc⟩
  · obtain ⟨v, hv⟩ := Classical.not_forall.mp hc
    obtain ⟨u, w, hu, hw, huw⟩ := (reachable v).exists_crossing
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
    obtain ⟨ys, hyn, hye, hyc⟩ := extend_root_reachable_enumeration adj root reachable
      (xs ++ [w]) hn' (he.append_one hu huw) (List.mem_append_left _ hr)
    refine ⟨w :: ys, ?_, ?_, ?_⟩
    · simpa [List.append_assoc] using hyn
    · simpa [List.append_assoc] using hye
    · simpa [List.append_assoc] using hyc
termination_by n - xs.length
decreasing_by
  have hlt := fin_list_length_lt_of_missing hn hw
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

theorem exists_root_reachable_enumeration {n} (adj : Fin n → Fin n → Prop)
    (root : Fin n) (reachable : ∀ v, Walk adj (fun _ => True) root v) :
    Nonempty (RootedEnumeration adj root) := by
  have he : EarlierNeighbors adj [root] := by
    intro i hi hn
    simp only [List.length_cons, List.length_nil] at hi
    omega
  obtain ⟨ys, hn, he, hc⟩ := extend_root_reachable_enumeration adj root reachable [root]
    (by simp) he (by simp)
  exact ⟨⟨root :: ys, by simpa using hn, by simpa using hc,
    by simpa using he, by simp⟩⟩

/-- The concrete input is only a parent function with a terminating rank. -/
structure RankedParent (n : Nat) where
  root : Fin n
  parent : Fin n → Fin n
  rank : Fin n → Nat
  parent_root : parent root = root
  rank_lt : ∀ v, v ≠ root → rank (parent v) < rank v

namespace RankedParent

def Arc {n} (P : RankedParent n) (u v : Fin n) : Prop :=
  v ≠ P.root ∧ P.parent v = u

theorem reachable {n} (P : RankedParent n) (v : Fin n) :
    Walk P.Arc (fun _ => True) P.root v := by
  by_cases hv : v = P.root
  · subst v; exact .refl trivial
  · exact (P.reachable (P.parent v)).trans (.step trivial ⟨hv, rfl⟩ (.refl trivial))
termination_by P.rank v
decreasing_by exact P.rank_lt v hv

/-- A genuine numbered tree with a two-sided code preserving every parent. -/
structure Numbered {n} (P : RankedParent n) where
  tree : RootedTree n
  label : Fin n → Fin n
  index : Fin n → Fin n
  label_index : ∀ v, label (index v) = v
  index_label : ∀ i, index (label i) = i
  label_root : ∀ i, i.val = 0 → label i = P.root
  parent_exact : ∀ i, label (tree.parent i) = P.parent (label i)

theorem exists_numbered {n} (P : RankedParent n) : Nonempty P.Numbered := by
  obtain ⟨E⟩ := exists_root_reachable_enumeration P.Arc P.root P.reachable
  refine ⟨⟨E.tree, E.label, E.index, E.label_index, E.index_label, E.label_root, ?_⟩⟩
  intro i
  by_cases hi : i.val = 0
  · rw [E.parent_root i hi, E.label_root i hi, P.parent_root]
  · exact (E.parent_edge i hi).2.symm

noncomputable def numbered {n} (P : RankedParent n) : P.Numbered :=
  Classical.choice P.exists_numbered

namespace Numbered

theorem label_injective {n} {P : RankedParent n} (N : P.Numbered)
    {i j} (h : N.label i = N.label j) : i = j := by
  have := congrArg N.index h
  simpa only [N.index_label] using this

theorem index_root_val {n} {P : RankedParent n} (N : P.Numbered) :
    (N.index P.root).val = 0 := by
  let z : Fin n := ⟨0, by have := P.root.isLt; omega⟩
  have he : N.index P.root = z := by
    rw [← N.label_root z rfl, N.index_label]
  exact congrArg Fin.val he

theorem label_eq_root_iff {n} {P : RankedParent n} (N : P.Numbered) (i : Fin n) :
    N.label i = P.root ↔ i.val = 0 := by
  constructor
  · intro h
    have hi : i = N.index P.root := by rw [← h, N.index_label]
    rw [hi, N.index_root_val]
  · exact N.label_root i

theorem parent_index {n} {P : RankedParent n} (N : P.Numbered) (v : Fin n) :
    N.tree.parent (N.index v) = N.index (P.parent v) := by
  apply N.label_injective
  rw [N.parent_exact, N.label_index, N.label_index]

theorem parent_root {n} {P : RankedParent n} (N : P.Numbered) (i : Fin n)
    (hi : i.val = 0) : N.tree.parent i = i := by
  apply N.label_injective
  rw [N.parent_exact, N.label_root i hi, P.parent_root]

end Numbered
end RankedParent
end StackSorting.GraphWidth
