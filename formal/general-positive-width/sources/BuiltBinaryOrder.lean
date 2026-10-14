import BinaryExactCodeSentence
import FiniteAlphabetBinaryCode

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic GraphWidth
variable {α β : Type}

theorem positionRoots_labels (t : BinaryTree α) :
    (positionRoots t).map Position.label=rootLabels t := by
  simpa only [positionRelabel_labels] using (rootLabels_positionRelabel t Position.label).symm

theorem positionRoots_unmap (f : α → β) (t : BinaryTree α) :
    (positionRoots (t.map f)).map (unmapPosition f t)=positionRoots t := by
  induction t with
  | nil => rfl
  | node a l r _ ih =>
    dsimp only [BinaryTree.map]
    simpa only [BinaryTree.map,positionRoots,List.map_cons,List.map_map,
      Function.comp_def,unmapPosition] using congrArg (List.cons Position.root)
        (congrArg (List.map Position.right) ih)

theorem positionChildren_unmap (f : α → β) (t : BinaryTree α)
    (p : Position (t.map f)) :
    (positionChildren p).map (unmapPosition f t)=
      positionChildren (unmapPosition f t p) := by
  induction t with
  | nil => cases p
  | node a l r hl hr =>
    change Position (.node (f a) (l.map f) (r.map f)) at p
    cases p with
    | root =>
      simpa only [positionChildren,List.map_map,Function.comp_def,unmapPosition] using
        congrArg (List.map Position.left) (positionRoots_unmap f l)
    | left p =>
      simpa only [positionChildren,List.map_map,Function.comp_def,unmapPosition] using
        congrArg (List.map Position.left) (hl p)
    | right p =>
      simpa only [positionChildren,List.map_map,Function.comp_def,unmapPosition] using
        congrArg (List.map Position.right) (hr p)

/-- Every constructed sibling list is literally the independently ordered
children list, including when finite node labels later coincide. -/
theorem build_positionChildren_labels {n : Nat} (T : RootedTree n) (O : FixedOrder n)
    (fuel : Nat) (xs : List (Fin n)) (hf : ∀ v ∈ xs, n-v.val ≤ fuel)
    (p : Position (build T O fuel xs)) :
    (positionChildren p).map Position.label=children T O p.label := by
  revert p
  induction fuel generalizing xs with
  | zero => rw [build]; intro p; cases p
  | succ fuel ih =>
    induction xs with
    | nil => rw [build]; intro p; cases p
    | cons v vs ht =>
      rw [build]
      intro p
      have hch : ∀ w ∈ children T O v, n-w.val ≤ fuel :=
        fun _ hw => child_fuel T O (hf v (by simp)) hw
      have hvs : ∀ w ∈ vs, n-w.val ≤ fuel+1 := fun w hw => hf w (by simp [hw])
      cases p with
      | root =>
        simpa only [positionChildren,List.map_map,Function.comp_def,Position.label,
          positionRoots_labels] using rootLabels_build T O fuel (children T O v) hch
      | left p =>
        simpa only [positionChildren,List.map_map,Function.comp_def,Position.label] using ih _ hch p
      | right p =>
        simpa only [positionChildren,List.map_map,Function.comp_def,Position.label] using ht hvs p

theorem binaryCode_sibling_order {n colors relations W} {G : Diagram n colors relations}
    (E : ExactNumberedCodec G W) (O : FixedOrder n) (hn : 0<n) :
    SiblingOrderCompatible O (binaryCode E O hn) (binaryCodeIndexEquiv E O hn) := by
  intro p
  let f := alphabetCode E.code E.bounded
  let t := build E.tree O n [⟨0,hn⟩]
  have he : (positionChildren p).map (binaryCodeIndexEquiv E O hn)=
      (positionChildren (unmapPosition f t p)).map Position.label := by
    change (positionChildren p).map (fun q => (unmapPosition f t q).label)=_
    have h := congrArg (List.map Position.label) (positionChildren_unmap f t p)
    simpa only [List.map_map,Function.comp_def] using h
  rw [he,build_positionChildren_labels E.tree O n _ (fun _ _ => Nat.sub_le _ _)]
  exact List.filter_sublist

theorem binaryCode_sibling_strict {n colors relations W} {G : Diagram n colors relations}
    (E : ExactNumberedCodec G W) (O : FixedOrder n) (hn : 0<n) :
    SiblingOrderStrict O (binaryCode E O hn) (binaryCodeIndexEquiv E O hn) :=
  (siblingOrder_iff_strict O _ _).mp (binaryCode_sibling_order E O hn)

theorem binaryCode_normalized {n colors relations W} {G : Diagram n colors relations}
    (E : ExactNumberedCodec G W) (O : FixedOrder n) (hn : 0<n) :
    NormalizedBinaryShape (binaryCode E O hn) := by
  cases n with
  | zero => omega
  | succ n =>
    unfold binaryCode
    simp only [build,BinaryTree.map]
    exact Or.inr ⟨_,_,rfl⟩

#print axioms binaryCode_sibling_strict
#print axioms binaryCode_normalized
end StackSorting.FinitePort.ChildSibling
