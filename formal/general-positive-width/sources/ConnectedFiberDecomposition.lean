import FinitePortEncoding

/-!
Finite graph tree decompositions and their connected-fiber lifts.
The index tree is the checked topologically numbered RootedTree used by the
existing finite-port codec. Width is represented by a bound on bag size.
This file proves no planarization, outerplanarity or stack-width premise.
-/
namespace StackSorting.GraphWidth
open FinitePort

structure Graph (n : Nat) where
  Adj : Fin n → Fin n → Prop
  symm : ∀ {u v}, Adj u v → Adj v u
  loopless : ∀ v, ¬ Adj v v

/-- An actual finite path whose every vertex satisfies P. Repetitions are allowed. -/
inductive Walk {α : Type} (adj : α → α → Prop) (P : α → Prop) : α → α → Prop
  | refl {u} : P u → Walk adj P u u
  | step {u v w} : P u → adj u v → Walk adj P v w → Walk adj P u w

namespace Walk

theorem start {α} {adj : α → α → Prop} {P} {u v} (h : Walk adj P u v) : P u := by
  cases h with
  | refl hu => exact hu
  | step hu _ _ => exact hu

theorem finish {α} {adj : α → α → Prop} {P} {u v} (h : Walk adj P u v) : P v := by
  induction h with
  | refl hu => exact hu
  | step _ _ _ ih => exact ih

theorem trans {α} {adj : α → α → Prop} {P} {u v w}
    (h : Walk adj P u v) (k : Walk adj P v w) : Walk adj P u w := by
  induction h with
  | refl => exact k
  | step hu huv _ ih => exact .step hu huv (ih k)

theorem mono {α} {adj : α → α → Prop} {P Q} {u v}
    (h : Walk adj P u v) (hpq : ∀ x, P x → Q x) : Walk adj Q u v := by
  induction h with
  | refl hu => exact .refl (hpq _ hu)
  | step hu huv _ ih => exact .step (hpq _ hu) huv ih

theorem reverse {α} {adj : α → α → Prop} {P} {u v}
    (h : Walk adj P u v) (hs : ∀ {x y}, adj x y → adj y x) : Walk adj P v u := by
  induction h with
  | refl hu => exact .refl hu
  | step hu huv tail ih => exact ih.trans (.step tail.start (hs huv) (.refl hu))

end Walk

/-- The undirected edges of the actual parent tree, omitting the root self-parent. -/
def TreeAdj {t} (T : RootedTree t) (i j : Fin t) : Prop :=
  (i.val ≠ 0 ∧ T.parent i = j) ∨ (j.val ≠ 0 ∧ T.parent j = i)

theorem treeAdj_symm {t} (T : RootedTree t) {i j} : TreeAdj T i j → TreeAdj T j i :=
  Or.symm

theorem treeAdj_loopless {t} (T : RootedTree t) (i) : ¬ TreeAdj T i i := by
  intro h
  obtain ⟨hn, he⟩ | ⟨hn, he⟩ := h <;>
    have hl := T.parent_lt i hn <;> rw [he] at hl <;> exact (Nat.lt_irrefl _ hl)

/-- Parent descent supplies the actual path to the unique root. -/
theorem tree_walk_to_root {t} (T : RootedTree t) (r : Fin t) (hr : r.val = 0)
    (i : Fin t) : Walk (TreeAdj T) (fun _ => True) i r := by
  by_cases he : i = r
  · subst i; exact .refl trivial
  · have hn : i.val ≠ 0 := by
      intro hz
      exact he (Fin.ext (hz.trans hr.symm))
    exact .step trivial (Or.inl ⟨hn, rfl⟩) (tree_walk_to_root T r hr (T.parent i))
termination_by i.val
decreasing_by exact T.parent_lt i hn

theorem tree_connected {t} (T : RootedTree t) (i j : Fin t) :
    Walk (TreeAdj T) (fun _ => True) i j := by
  let r : Fin t := ⟨0, by have := i.isLt; omega⟩
  exact (tree_walk_to_root T r rfl i).trans
    ((tree_walk_to_root T r rfl j).reverse (treeAdj_symm T))

/-- Each vertex has exactly its one parent as a smaller tree neighbor. This
strict-decrease property excludes a cycle at its largest vertex. -/
theorem tree_smaller_neighbor_unique {t} (T : RootedTree t) {i j k : Fin t}
    (hij : TreeAdj T i j) (hik : TreeAdj T i k)
    (hj : j.val < i.val) (hk : k.val < i.val) : j = k := by
  have parent_eq : ∀ v : Fin t, TreeAdj T i v → v.val < i.val → T.parent i = v := by
    intro v h hv
    obtain h | h := h
    · exact h.2
    · have hl := T.parent_lt v h.1
      rw [h.2] at hl
      omega
  exact (parent_eq j hij hj).symm.trans (parent_eq k hik hk)

/-- Covers vertices and edges and has genuinely connected occurrence sets in T. -/
structure Decomposition {n t} (G : Graph n) (T : RootedTree t) where
  bag : Fin t → List (Fin n)
  nodup : ∀ i, (bag i).Nodup
  vertex : ∀ v, ∃ i, v ∈ bag i
  edge : ∀ {u v}, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i
  running : ∀ {v i j}, v ∈ bag i → v ∈ bag j →
    Walk (TreeAdj T) (fun k => v ∈ bag k) i j

/-- The convention `BagBound b` means treewidth at most b-1 for nonempty graphs. -/
def Decomposition.BagBound {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) (b : Nat) : Prop := ∀ i, (D.bag i).length ≤ b

/-- Source vertices contribute finite sets of target vertices. Each target's
source fiber is connected; target edges arise within one source vertex or
across one source edge. No target decomposition is assumed. -/
structure ConnectedLift {n m} (G : Graph n) (H : Graph m) where
  labels : Fin n → List (Fin m)
  vertex : ∀ v, ∃ q, v ∈ labels q
  edge : ∀ {u v}, H.Adj u v →
    (∃ q, u ∈ labels q ∧ v ∈ labels q) ∨
    (∃ q r, G.Adj q r ∧ u ∈ labels q ∧ v ∈ labels r)
  fiber : ∀ {v q r}, v ∈ labels q → v ∈ labels r →
    Walk G.Adj (fun x => v ∈ labels x) q r

/-- Duplicate removal with elementary, checked cardinality facts. -/
def uniqueList {α} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if x ∈ uniqueList xs then uniqueList xs else x :: uniqueList xs

@[simp] theorem mem_uniqueList {α} [DecidableEq α] (xs : List α) (x : α) :
    x ∈ uniqueList xs ↔ x ∈ xs := by
  induction xs generalizing x with
  | nil => simp [uniqueList]
  | cons y ys ih =>
    simp only [uniqueList]
    split
    · rename_i h
      have hy : y ∈ ys := (ih y).mp h
      simp only [ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | hx)
        · exact hy
        · exact hx
    · simp [ih]

theorem uniqueList_nodup {α} [DecidableEq α] (xs : List α) : (uniqueList xs).Nodup := by
  induction xs with
  | nil => simp [uniqueList]
  | cons x xs ih => simp only [uniqueList]; split <;> simp_all

theorem uniqueList_length_le {α} [DecidableEq α] (xs : List α) :
    (uniqueList xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [uniqueList]
  | cons x xs ih => simp only [uniqueList]; split <;> simp_all <;> omega

noncomputable def liftedBag {n m t} {G : Graph n} {H : Graph m}
    {T : RootedTree t} (D : Decomposition G T) (L : ConnectedLift G H) (i : Fin t) :
    List (Fin m) := uniqueList ((D.bag i).flatMap L.labels)

@[simp] theorem mem_liftedBag {n m t} {G : Graph n} {H : Graph m}
    {T : RootedTree t} (D : Decomposition G T) (L : ConnectedLift G H) (i v) :
    v ∈ liftedBag D L i ↔ ∃ q, q ∈ D.bag i ∧ v ∈ L.labels q := by
  simp [liftedBag]

/-- A path through a source fiber yields a path of bags containing the target.
At each source edge, its covering bag joins the two occurrence subtrees. -/
theorem lift_fiber_walk {n m t} {G : Graph n} {H : Graph m} {T : RootedTree t}
    (D : Decomposition G T) (L : ConnectedLift G H) {v q r}
    (h : Walk G.Adj (fun x => v ∈ L.labels x) q r) {i j}
    (hi : q ∈ D.bag i) (hj : r ∈ D.bag j) :
    Walk (TreeAdj T) (fun k => v ∈ liftedBag D L k) i j := by
  induction h generalizing i with
  | refl hv =>
    exact (D.running hi hj).mono (fun k hk => (mem_liftedBag D L k v).mpr ⟨_, hk, hv⟩)
  | @step q r s hv hqr hrs ih =>
    obtain ⟨k, hqk, hrk⟩ := D.edge hqr
    exact ((D.running hi hqk).mono
      (fun z hz => (mem_liftedBag D L z v).mpr ⟨q, hz, hv⟩)).trans (ih hrk hj)

noncomputable def Decomposition.lift {n m t} {G : Graph n} {H : Graph m}
    {T : RootedTree t} (D : Decomposition G T) (L : ConnectedLift G H) :
    Decomposition H T where
  bag := liftedBag D L
  nodup := fun i => uniqueList_nodup _
  vertex := by
    intro v
    obtain ⟨q, hvq⟩ := L.vertex v
    obtain ⟨i, hqi⟩ := D.vertex q
    exact ⟨i, (mem_liftedBag D L i v).mpr ⟨q, hqi, hvq⟩⟩
  edge := by
    intro u v huv
    obtain ⟨q, huq, hvq⟩ | ⟨q, r, hqr, huq, hvr⟩ := L.edge huv
    · obtain ⟨i, hqi⟩ := D.vertex q
      exact ⟨i, (mem_liftedBag D L i u).mpr ⟨q, hqi, huq⟩,
        (mem_liftedBag D L i v).mpr ⟨q, hqi, hvq⟩⟩
    · obtain ⟨i, hqi, hri⟩ := D.edge hqr
      exact ⟨i, (mem_liftedBag D L i u).mpr ⟨q, hqi, huq⟩,
        (mem_liftedBag D L i v).mpr ⟨r, hri, hvr⟩⟩
  running := by
    intro v i j hi hj
    obtain ⟨q, hqi, hvq⟩ := (mem_liftedBag D L i v).mp hi
    obtain ⟨r, hrj, hvr⟩ := (mem_liftedBag D L j v).mp hj
    exact lift_fiber_walk D L (L.fiber hvq hvr) hqi hrj

theorem length_flatMap_le {α β} (xs : List α) (f : α → List β) (c : Nat)
    (h : ∀ x ∈ xs, (f x).length ≤ c) : (xs.flatMap f).length ≤ xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [Nat.add_mul]
    omega

theorem Decomposition.lift_bagBound {n m t} {G : Graph n} {H : Graph m}
    {T : RootedTree t} (D : Decomposition G T) (L : ConnectedLift G H) {b c}
    (hb : D.BagBound b) (hc : ∀ q, (L.labels q).length ≤ c) :
    (D.lift L).BagBound (b*c) := by
  intro i
  apply Nat.le_trans (uniqueList_length_le _)
  exact Nat.le_trans (length_flatMap_le (D.bag i) L.labels c (fun q _ => hc q))
    (Nat.mul_le_mul_right c (hb i))

/-- The standard existential tree-decomposition upper bound. For the empty
graph this nonnegative upper-bound predicate is still meaningful. -/
def HasTreewidthAtMost {n} (G : Graph n) (w : Nat) : Prop :=
  ∃ t, ∃ T : RootedTree t, ∃ D : Decomposition G T, D.BagBound (w+1)

theorem Decomposition.treewidthAtMost {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) {b : Nat} (hb : D.BagBound b) (hpos : 0 < b) :
    HasTreewidthAtMost G (b-1) := by
  refine ⟨t, T, D, ?_⟩
  have he : b - 1 + 1 = b := by omega
  simpa [he] using hb

/-- Isomorphic finite graphs, with actual two-sided vertex maps. -/
structure GraphIsomorphism {n m} (G : Graph n) (H : Graph m) where
  toFun : Fin n → Fin m
  invFun : Fin m → Fin n
  left_inverse : ∀ q, invFun (toFun q) = q
  right_inverse : ∀ v, toFun (invFun v) = v
  edge_iff : ∀ q r, G.Adj q r ↔ H.Adj (toFun q) (toFun r)

def GraphIsomorphism.connectedLift {n m} {G : Graph n} {H : Graph m}
    (F : GraphIsomorphism G H) : ConnectedLift G H where
  labels := fun q => [F.toFun q]
  vertex := fun v => ⟨F.invFun v, by simp [F.right_inverse]⟩
  edge := by
    intro u v huv
    right
    refine ⟨F.invFun u, F.invFun v, ?_, by simp [F.right_inverse],
      by simp [F.right_inverse]⟩
    exact (F.edge_iff _ _).mpr (by simpa [F.right_inverse] using huv)
  fiber := by
    intro v q r hq hr
    have hq' : v = F.toFun q := by simpa using hq
    have hr' : v = F.toFun r := by simpa using hr
    have hqr : q = r := by
      have h := congrArg F.invFun (hq'.symm.trans hr')
      simpa [F.left_inverse] using h
    subst r
    exact .refl hq

theorem GraphIsomorphism.treewidthAtMost {n m} {G : Graph n} {H : Graph m}
    (F : GraphIsomorphism G H) {w} (h : HasTreewidthAtMost G w) :
    HasTreewidthAtMost H w := by
  obtain ⟨t, T, D, hb⟩ := h
  refine ⟨t, T, D.lift F.connectedLift, ?_⟩
  have h' := D.lift_bagBound F.connectedLift hb (show
    ∀ q, (F.connectedLift.labels q).length ≤ 1 by intro q; simp [GraphIsomorphism.connectedLift])
  simpa using h'

end StackSorting.GraphWidth
