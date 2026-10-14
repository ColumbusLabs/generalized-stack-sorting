import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace StackSorting.Simon

/-- Finite ordered trees. Internal arities are checked by `Valid`. -/
inductive FactorizationTree (A : Type*) where
  | leaf : A → FactorizationTree A
  | node : List (FactorizationTree A) → FactorizationTree A

namespace FactorizationTree

variable {A M : Type*} [Monoid M]

def leaves : FactorizationTree A → List A
  | .leaf a => [a]
  | .node ts => ts.flatMap leaves

def height : FactorizationTree A → ℕ
  | .leaf _ => 0
  | .node ts => (ts.map height).foldr max 0 + 1

def value (φ : A → M) (t : FactorizationTree A) : M :=
  (t.leaves.map φ).prod

/-- Exactly Simon's branching condition: binary, or common idempotent value.
The condition also excludes empty and unary nodes. -/
inductive Valid (φ : A → M) : FactorizationTree A → Prop
  | leaf (a : A) : Valid φ (.leaf a)
  | node (ts : List (FactorizationTree A))
      (children : ∀ t ∈ ts, Valid φ t)
      (arity : 2 ≤ ts.length)
      (branching : ts.length = 2 ∨
        ∃ e : M, e * e = e ∧ ∀ t ∈ ts, value φ t = e) :
      Valid φ (.node ts)

def HasTree (φ : A → M) (w : List A) (h : ℕ) : Prop :=
  ∃ t : FactorizationTree A, t.leaves = w ∧ Valid φ t ∧ t.height ≤ h

theorem hasTree_singleton (φ : A → M) (a : A) (h : ℕ) :
    HasTree φ [a] h :=
  ⟨.leaf a, by simp [leaves], .leaf a, by simp [height]⟩

theorem hasTree_mono {φ : A → M} {w : List A} {h k : ℕ}
    (ht : HasTree φ w h) (hk : h ≤ k) : HasTree φ w k := by
  obtain ⟨t, hw, hv, hh⟩ := ht
  exact ⟨t, hw, hv, hh.trans hk⟩

theorem hasTree_binary {φ : A → M} {u v : List A} {h : ℕ}
    (hu : HasTree φ u h) (hv : HasTree φ v h) :
    HasTree φ (u ++ v) (h + 1) := by
  obtain ⟨s, hs, hsv, hsh⟩ := hu
  obtain ⟨t, ht, htv, hth⟩ := hv
  refine ⟨.node [s,t], ?_, ?_, ?_⟩
  · simp [leaves, hs, ht]
  · apply Valid.node
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hsv
      · exact htv
    · simp
    · exact Or.inl rfl
  · simp only [height, List.map_cons, List.map_nil, List.foldr_cons,
      List.foldr_nil, max_eq_left (Nat.zero_le _)]
    exact Nat.add_le_add_right (max_le hsh hth) 1

private theorem choose_trees (φ : A → M) (ws : List (List A)) (h : ℕ)
    (hall : ∀ w ∈ ws, HasTree φ w h) :
    ∃ ts : List (FactorizationTree A), ts.map leaves = ws ∧
      ∀ t ∈ ts, Valid φ t ∧ t.height ≤ h := by
  induction ws with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons w ws ih =>
    obtain ⟨t, htw, htv, hth⟩ := hall w (by simp)
    obtain ⟨ts, htsw, htsh⟩ := ih (by
      intro v hv
      exact hall v (by simp [hv]))
    refine ⟨t :: ts, by simp [htw, htsw], ?_⟩
    intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ⟨htv, hth⟩
    · exact htsh v hv

private theorem foldr_max_le (xs : List ℕ) (h : ℕ)
    (hall : ∀ x ∈ xs, x ≤ h) : xs.foldr max 0 ≤ h := by
  induction xs with
  | nil => exact Nat.zero_le h
  | cons x xs ih =>
    exact max_le (hall x (by simp)) (ih (by
      intro y hy
      exact hall y (by simp [hy])))

/-- A nonempty list of already constructed factors with common idempotent
value can be joined with at most one additional level. -/
theorem hasTree_idempotent_blocks (φ : A → M) (ws : List (List A))
    (h : ℕ) (hne : ws ≠ []) (hall : ∀ w ∈ ws, HasTree φ w h)
    (e : M) (he : e * e = e) (hvalues : ∀ w ∈ ws, (w.map φ).prod = e) :
    HasTree φ ws.flatten (h + 1) := by
  obtain ⟨ts, hwords, htrees⟩ := choose_trees φ ws h hall
  cases ts with
  | nil => simp at hwords; exact (hne hwords).elim
  | cons t ts =>
    cases ts with
    | nil =>
      have ht := htrees t (by simp)
      refine ⟨t, ?_, ht.1, ht.2.trans (Nat.le_succ h)⟩
      simp only [List.map_cons, List.map_nil] at hwords
      rw [← hwords]
      simp
    | cons u ts =>
      refine ⟨.node (t :: u :: ts), ?_, ?_, ?_⟩
      · simpa only [leaves, List.flatMap_def] using
          congrArg List.flatten hwords
      · apply Valid.node
        · intro r hr
          exact (htrees r hr).1
        · simp
        · right
          refine ⟨e, he, ?_⟩
          intro r hr
          apply hvalues
          rw [← hwords]
          exact List.mem_map.mpr ⟨r, hr, rfl⟩
      · rw [height]
        apply Nat.add_le_add_right
        apply foldr_max_le
        intro k hk
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
        exact (htrees r hr).2

/-- A genuine constant-height base case: any nonempty word whose letters all
map to a fixed idempotent has a valid tree of height at most one. -/
theorem exists_height_one_of_constant_idempotent
    (φ : A → M) (w : List A) (hw : w ≠ []) (e : M)
    (he : e * e = e) (hall : ∀ a ∈ w, φ a = e) : HasTree φ w 1 := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons a tail =>
    cases tail with
    | nil => exact hasTree_singleton φ a 1
    | cons b rest =>
      let ts := (a :: b :: rest).map FactorizationTree.leaf
      refine ⟨.node ts, ?_, ?_, ?_⟩
      · simp [leaves, ts, List.flatMap_map]
      · apply Valid.node
        · intro t ht
          obtain ⟨c, _, rfl⟩ := List.mem_map.mp ht
          exact Valid.leaf c
        · simp [ts]
        · right
          refine ⟨e, he, ?_⟩
          intro t ht
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
          simpa [value, leaves] using hall c hc
      · rw [height]
        change (ts.map height).foldr max 0 + 1 ≤ 0 + 1
        apply Nat.add_le_add_right
        apply foldr_max_le
        intro k hk
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hk
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp ht
        simp [height]

/-- The singleton-monoid base case is unconditional on the letter map. -/
theorem exists_height_one_of_subsingleton [Subsingleton M]
    (φ : A → M) (w : List A) (hw : w ≠ []) : HasTree φ w 1 := by
  apply exists_height_one_of_constant_idempotent φ w hw 1 (one_mul 1)
  intro a _
  exact Subsingleton.elim _ _

#print axioms exists_height_one_of_constant_idempotent
#print axioms exists_height_one_of_subsingleton

end FactorizationTree
end StackSorting.Simon
