import BinaryForestStructure

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic
variable {α : Type}

/-- Every actual position has a distinct preorder rank, even when all labels
are equal. This will supply the reverse decoder's exact finite carrier. -/
theorem positionRank_injective (t : BinaryTree α) :
    Function.Injective (@positionRank α t) := by
  induction t with
  | nil => intro p; cases p
  | node a l r ihl ihr =>
    intro p q he
    cases p with
    | root =>
      cases q with
      | root => rfl
      | left q => simp only [positionRank] at he; omega
      | right q => simp only [positionRank] at he; omega
    | left p =>
      cases q with
      | root => simp only [positionRank] at he; omega
      | left q =>
        apply congrArg Position.left
        apply ihl
        simp only [positionRank] at he
        omega
      | right q =>
        have hp := positionRank_lt p
        simp only [positionRank] at he
        omega
    | right p =>
      cases q with
      | root => simp only [positionRank] at he; omega
      | left q =>
        have hq := positionRank_lt q
        simp only [positionRank] at he
        omega
      | right q =>
        apply congrArg Position.right
        apply ihr
        simp only [positionRank] at he
        omega

def positionIndex {t : BinaryTree α} (p : Position t) : Fin t.numNodes :=
  ⟨positionRank p,positionRank_lt p⟩

theorem positionIndex_surjective (t : BinaryTree α) :
    Function.Surjective (@positionIndex α t) := by
  induction t with
  | nil => intro i; exact Fin.elim0 i
  | node a l r ihl ihr =>
    intro i
    by_cases hz : i.val=0
    · refine ⟨.root,Fin.ext ?_⟩
      exact hz.symm
    · by_cases hl : i.val≤l.numNodes
      · let j : Fin l.numNodes := ⟨i.val-1,by omega⟩
        obtain ⟨p,hp⟩ := ihl j
        refine ⟨.left p,Fin.ext ?_⟩
        have he := congrArg Fin.val hp
        change positionRank p=i.val-1 at he
        change 1+positionRank p=i.val
        omega
      · let j : Fin r.numNodes := ⟨i.val-1-l.numNodes,by
          have hi := i.isLt
          simp only [BinaryTree.numNodes] at hi
          omega⟩
        obtain ⟨p,hp⟩ := ihr j
        refine ⟨.right p,Fin.ext ?_⟩
        have he := congrArg Fin.val hp
        change positionRank p=i.val-1-l.numNodes at he
        change 1+l.numNodes+positionRank p=i.val
        omega

noncomputable def positionIndexEquiv (t : BinaryTree α) : Position t ≃ Fin t.numNodes :=
  Equiv.ofBijective positionIndex
    ⟨fun _ _ h => positionRank_injective t (congrArg Fin.val h),positionIndex_surjective t⟩

theorem positionIndexEquiv_val {t : BinaryTree α} (p : Position t) :
    (positionIndexEquiv t p).val=positionRank p := rfl

theorem positionRank_zero_iff (a : α) (l r : BinaryTree α)
    (p : Position (.node a l r)) : positionRank p=0 ↔ p=.root := by
  constructor
  · intro h
    exact positionRank_injective _ h
  · rintro rfl
    rfl

#print axioms positionIndexEquiv
#print axioms positionRank_zero_iff
end StackSorting.FinitePort.ChildSibling
