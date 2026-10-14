import BinaryParentMSO
import BinarySiblingLinearOrder
import Mathlib.Data.List.Chain

set_option warningAsError true

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic
variable {α : Type}

/-- Adjacent positions in a literal forest-root list are exactly the binary
right edges whose source belongs to that root chain. -/
theorem positionRoots_isChain_iff (t : BinaryTree α) (R : Position t → Position t → Prop) :
    (positionRoots t).IsChain R ↔
      ∀ p q, RootSibling p → Child true p q → R p q := by
  induction t with
  | nil =>
    constructor
    · intro _ p; cases p
    · intro _; exact List.IsChain.nil
  | node a l r _ ihr =>
    cases r with
    | nil =>
      constructor
      · intro _ p q hp he
        cases hp with
        | root => cases he
        | right hp => cases hp
      · intro _; exact List.IsChain.singleton _
    | node b rl rr =>
      have tail : ((positionRoots (.node b rl rr)).map
          (Position.right (a:=a) (l:=l))).IsChain R ↔
          ∀ p q : Position (.node b rl rr), RootSibling p → Child true p q →
            R (.right p) (.right q) := by
        rw [List.isChain_map]
        exact ihr _
      change (Position.root :: (positionRoots (.node b rl rr)).map Position.right).IsChain R ↔ _
      have split : (Position.root :: (positionRoots (.node b rl rr)).map
          (Position.right (a:=a) (l:=l))).IsChain R ↔
          R .root (.right .root) ∧
            ((positionRoots (.node b rl rr)).map Position.right).IsChain R := by
        exact List.isChain_cons_cons
      rw [split, tail]
      constructor
      · rintro ⟨hroot, htail⟩ p q hp he
        cases hp with
        | root => cases he with | rootRight => exact hroot
        | right hp => cases he with | right he => exact htail _ _ hp he
      · intro h
        exact ⟨h _ _ .root .rootRight, fun p q hp he => h _ _ (.right hp) (.right he)⟩

/-- Adjacent members of each literal child list are precisely the right edges
with that original parent. No normalization or distinct-label premise is used. -/
theorem positionChildren_isChain_iff {t : BinaryTree α} (p : Position t)
    (R : Position t → Position t → Prop) :
    (positionChildren p).IsChain R ↔
      ∀ q z, ParentPosition p q → Child true q z → R q z := by
  induction p with
  | root =>
    rw [positionChildren, List.isChain_map, positionRoots_isChain_iff]
    constructor
    · intro h q z hp he
      cases hp with
      | root hq => cases he with | left he => exact h _ _ hq he
    · intro h q z hq he
      exact h _ _ (.root hq) (.left he)
  | left p ih =>
    rw [positionChildren, List.isChain_map, ih]
    constructor
    · intro h q z hp he
      cases hp with
      | left hp => cases he with | left he => exact h _ _ hp he
    · intro h q z hp he
      exact h _ _ (.left hp) (.left he)
  | right p ih =>
    rw [positionChildren, List.isChain_map, ih]
    constructor
    · intro h q z hp he
      cases hp with
      | right hp => cases he with | right he => exact h _ _ hp he
    · intro h q z hp he
      exact h _ _ (.right hp) (.right he)

/-- Transitivity upgrades adjacent sibling checks to every pair in every
literal child list. The map e need not be injective or surjective. -/
theorem siblingOrderStrict_iff_edges {n : Nat} (O : FixedOrder n)
    (t : BinaryTree α) (e : Position t → Fin n) :
    SiblingOrderStrict O t e ↔
      ∀ p q z, ParentPosition p q → Child true q z → OrderBefore O (e q) (e z) := by
  let R : Position t → Position t → Prop := fun q z => OrderBefore O (e q) (e z)
  let : IsTrans (Position t) R := ⟨fun _ _ _ h₁ h₂ => Nat.lt_trans h₁ h₂⟩
  unfold SiblingOrderStrict
  simp only [List.pairwise_map]
  change (∀ p, (positionChildren p).Pairwise R) ↔ _
  simp only [← List.isChain_iff_pairwise, positionChildren_isChain_iff]
  rfl

/-- Empty or exactly one represented root. -/
def NormalizedBinaryShape (t : BinaryTree α) : Prop :=
  t = .nil ∨ ∃ a l, t = .node a l .nil

/-- An incoming edge in the binary tree, distinct from the original FCNS parent. -/
def HasBinaryPredecessor {t : BinaryTree α} (p : Position t) : Prop :=
  ∃ q, Child false q p ∨ Child true q p

theorem rootPosition_no_predecessor {t : BinaryTree α} {p : Position t}
    (hp : RootPosition p) : ¬ HasBinaryPredecessor p := by
  cases hp
  rintro ⟨q,h | h⟩ <;> cases h

theorem position_root_or_predecessor {t : BinaryTree α} (p : Position t) :
    RootPosition p ∨ HasBinaryPredecessor p := by
  induction p with
  | root => exact Or.inl .root
  | left p ih =>
    right
    rcases ih with hp | ⟨q,hq | hq⟩
    · cases hp; exact ⟨.root,Or.inl .rootLeft⟩
    · exact ⟨.left q,Or.inl (.left hq)⟩
    · exact ⟨.left q,Or.inr (.left hq)⟩
  | right p ih =>
    right
    rcases ih with hp | ⟨q,hq | hq⟩
    · cases hp; exact ⟨.root,Or.inr .rootRight⟩
    · exact ⟨.right q,Or.inl (.right hq)⟩
    · exact ⟨.right q,Or.inr (.right hq)⟩

theorem hasBinaryPredecessor_iff {t : BinaryTree α} (p : Position t) :
    HasBinaryPredecessor p ↔ ¬ RootPosition p := by
  constructor
  · intro hp hr; exact rootPosition_no_predecessor hr hp
  · intro hn
    rcases position_root_or_predecessor p with hp | hp
    · exact False.elim (hn hp)
    · exact hp

/-- The shape check uses only literal binary edges: each right-edge source
must itself have an incoming binary edge. -/
theorem normalizedBinaryShape_iff_edges (t : BinaryTree α) :
    NormalizedBinaryShape t ↔
      ∀ p q : Position t, Child true p q → HasBinaryPredecessor p := by
  constructor
  · rintro (rfl | ⟨a,l,rfl⟩) p q he
    · cases p
    · apply (hasBinaryPredecessor_iff p).mpr
      intro hp
      cases hp
      cases he
  · intro h
    cases t with
    | nil => exact Or.inl rfl
    | node a l r =>
      cases r with
      | nil => exact Or.inr ⟨a,l,rfl⟩
      | node b rl rr =>
        exact False.elim (rootPosition_no_predecessor RootPosition.root
          (h .root (.right .root) .rootRight))

#print axioms positionRoots_isChain_iff
#print axioms positionChildren_isChain_iff
#print axioms siblingOrderStrict_iff_edges
#print axioms normalizedBinaryShape_iff_edges
end StackSorting.FinitePort.ChildSibling
