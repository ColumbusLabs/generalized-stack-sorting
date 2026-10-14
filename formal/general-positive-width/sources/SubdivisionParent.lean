import RootPathBags

namespace StackSorting.GraphWidth.UCurve.SubdivisionTree
open FinitePort
open PlaneGrid

/-- The length data of actual positive source-edge subdivision routes. -/
structure RouteLengths {n} (G : Graph n) where
  length : OrderedEdge G → Nat
  positive : ∀ e, 0<length e

inductive Vertex {n} {G : Graph n} (S : RouteLengths G) where
  | original : Fin n → Vertex S
  | interior : (e : OrderedEdge G) → Fin (S.length e-1) → Vertex S

def IsTreeEdge {n} {G : Graph n} (T : RootedTree n) (e : OrderedEdge G) : Prop :=
  T.parent e.high=e.low

instance {n} {G : Graph n} (T : RootedTree n) (e : OrderedEdge G) : Decidable (IsTreeEdge T e) :=
  inferInstanceAs (Decidable (T.parent e.high=e.low))

def parentEdge {n} {G : Graph n} (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (v : Fin n) (hv : v.val≠0) :
    OrderedEdge G := ⟨T.parent v,v,T.parent_lt v hv,he v hv⟩

noncomputable def branch {n} {G : Graph n} (S : RouteLengths G) (T : RootedTree n) :
    Vertex S → Fin n
  | .original v => v
  | .interior e _ => if IsTreeEdge T e then e.low else e.high

/-- Expand tree routes, and attach each non-tree route's interiors backwards
from its high endpoint, omitting only the first unit segment. -/
noncomputable def parent {n} {G : Graph n} (S : RouteLengths G) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) : Vertex S → Vertex S
  | .original v => if hv : v.val=0 then .original v else
      let e := parentEdge T he v hv
      if hl : 1<S.length e then .interior e ⟨S.length e-2,by omega⟩ else .original (T.parent v)
  | .interior e a => if IsTreeEdge T e then
      if ha : a.val=0 then .original e.low else .interior e ⟨a.val-1,by have := a.isLt; omega⟩
    else if ha : a.val+1=S.length e-1 then .original e.high
      else .interior e ⟨a.val+1,by have := a.isLt; omega⟩

theorem branch_parent_original {n} {G : Graph n} (S : RouteLengths G) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (v : Fin n) (hv : v.val≠0) :
    branch S T (parent S T he (.original v))=T.parent v := by
  classical
  simp only [parent,dite_eq_right hv]
  split
  · simp [branch,IsTreeEdge,parentEdge]
  · rfl

theorem branch_parent_interior {n} {G : Graph n} (S : RouteLengths G) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (e : OrderedEdge G)
    (a : Fin (S.length e-1)) :
    branch S T (parent S T he (.interior e a))=branch S T (.interior e a) := by
  classical
  by_cases ht : IsTreeEdge T e
  · by_cases ha : a.val=0 <;> simp [parent,branch,ht,ha]
  · by_cases ha : a.val+1=S.length e-1 <;> simp [parent,branch,ht,ha]

/-- Every expanded parent step either keeps its source branch or moves to
its source parent; no extra source label is introduced by subdivision. -/
theorem branch_parent_ancestor {n} {G : Graph n} (S : RouteLengths G) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (x : Vertex S) :
    Ancestor T (branch S T (parent S T he x)) (branch S T x) := by
  classical
  cases x with
  | original v =>
    by_cases hv : v.val=0
    · simp only [parent,dite_eq_left hv,branch]
      exact .refl v
    · rw [branch_parent_original S T he v hv]
      exact .step hv (.refl _)
  | interior e a => rw [branch_parent_interior]; exact .refl _

/-- A finite numerical descent rank, with non-tree route tails placed after
all original vertices. Its bound is supplied by the actual finite target. -/
noncomputable def rank {n} {G : Graph n} (S : RouteLengths G) (T : RootedTree n)
    (B : Nat) : Vertex S → Nat
  | .original v => (v.val+1)*(B+1)
  | .interior e a => if IsTreeEdge T e then e.high.val*(B+1)+(a.val+1)
      else (n+1)*(B+1)+(S.length e-1-a.val)


theorem rank_parent_lt {n} {G : Graph n} (S : RouteLengths G) (T : RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (B : Nat)
    (hB : ∀ e, S.length e≤B) (root : Fin n) (hr : root.val=0)
    (x : Vertex S) (hx : x≠.original root) :
    rank S T B (parent S T he x)<rank S T B x := by
  classical
  cases x with
  | original v =>
    have hv : v.val≠0 := by
      intro hz
      exact hx (congrArg Vertex.original (Fin.ext (hz.trans hr.symm)))
    simp only [parent,dite_eq_right hv]
    split
    · rename_i hl
      simp only [rank,IsTreeEdge,parentEdge]
      simp only [ite_true]
      have hb := hB (parentEdge T he v hv)
      dsimp only [parentEdge] at hb hl
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    · have ht := T.parent_lt v hv
      have hm : ((T.parent v).val+1)*(B+1)≤v.val*(B+1) :=
        Nat.mul_le_mul_right (B+1) (by omega)
      simp only [rank,Nat.add_mul,Nat.one_mul] at hm ⊢
      omega
  | interior e a =>
    by_cases ht : IsTreeEdge T e
    · simp only [parent,ite_eq_left ht]
      split
      · rename_i ha
        simp only [rank,ite_eq_left ht]
        have hm : (e.low.val+1)*(B+1)≤e.high.val*(B+1) :=
          Nat.mul_le_mul_right (B+1) (by have := e.ordered; omega)
        omega
      · simp only [rank,ite_eq_left ht]
        rename_i ha
        omega
    · simp only [parent,ite_eq_right ht]
      split
      · simp only [rank,ite_eq_right ht]
        have hm : (e.high.val+1)*(B+1)≤n*(B+1) :=
          Nat.mul_le_mul_right (B+1) (by have := e.high.isLt; omega)
        simp only [Nat.add_mul,Nat.one_mul] at hm ⊢
        omega
      · simp only [rank,ite_eq_right ht]
        rename_i ha
        have hb := a.isLt
        omega

end StackSorting.GraphWidth.UCurve.SubdivisionTree
