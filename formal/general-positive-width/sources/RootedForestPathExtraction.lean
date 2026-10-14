import SaneSingletonNormalization

namespace StackSorting.ConnectedConeNormalization
open GraphWidth SameVertexForest
variable {n : Nat}

/-- Entering a subtree of a concrete ranked parent forest crosses its root. -/
theorem parentWalk_subtree_entry (O : RankedOrder n) {P : Fin n → Prop} {a x y}
    (h : Walk (ParentAdj O) P x y) (hx : ¬ Cone O a x) (hy : Cone O a y) : P a := by
  induction h with
  | refl => exact False.elim (hx hy)
  | @step x z y hpx hxz tail ih =>
    by_cases hz : Cone O a z
    · rcases hxz with ⟨hn,he⟩ | ⟨hn,he⟩
      · have hp : O.rel z x := he ▸ O.parent_rel hn
        exact False.elim (hx (cone_trans O hz (Or.inl hp)))
      · by_cases heq : a = z
        · exact heq.symm ▸ tail.start
        · have hc := cone_parent O (hz.resolve_right heq)
          exact False.elim (hx (he ▸ hc))
    · exact ih hz hy

/-- Parent ancestry can be extracted from the undirected chosen forest and
its unary set of roots by deleting one displayed vertex. There is no binary
parent parameter in this characterization. -/
def RootSeparator (O : RankedOrder n) (x y : Fin n) : Prop :=
  ∀ r, O.parent r = r → Walk (ParentAdj O) (fun _ => True) y r →
    ¬ Walk (ParentAdj O) (fun z => z ≠ x) y r

theorem rootSeparator_iff (O : RankedOrder n) (x y) :
    RootSeparator O x y ↔ Cone O x y := by
  constructor
  · intro h
    by_contra hn
    have hroot : Cone O (O.root y) y := O.ancestor_iff.mp (O.root_ancestor y)
    have hp : Walk (ParentAdj O) (fun z => z ≠ x) (O.root y) y :=
      cone_walk O hroot (fun z _ hzy he => hn (he ▸ hzy))
    have hr := hp.reverse (parentAdj_symm O)
    exact h (O.root y) (O.root_fixed y) (hr.mono (fun _ _ => trivial)) hr
  · intro h r hr _ hp
    by_cases he : x = r
    · exact hp.finish he.symm
    · have hn : ¬ Cone O x r := by
        rintro (hx | hx)
        · exact O.fixed_no_predecessor hr x hx
        · exact he hx
      have bad : x ≠ x := parentWalk_subtree_entry O (P := fun z => z ≠ x) (hp.reverse (parentAdj_symm O)) hn h
      exact bad rfl

/-- The extracted relation has the exact introduction semantics of the
singleton normalized decomposition, on the original vertex names. -/
theorem normalized_rootSeparator (G : Graph n) (O : RankedOrder n) (x y) :
    RootSeparator (normalizedOrder G O) x y ↔ ReachCone G O x y :=
  (rootSeparator_iff _ x y).trans (normalized_cone G O x y)

#print axioms rootSeparator_iff
#print axioms normalized_rootSeparator
end StackSorting.ConnectedConeNormalization
