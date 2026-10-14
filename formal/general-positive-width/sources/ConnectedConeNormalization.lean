import EliminationForestFromDecomposition

/-!
Constructive connected-cone normalization of an actual finite elimination
order. The new parent is obtained by the existing finite ranked-cover
construction, not assumed. This component does not assert MSO definability
or uniform guidance existence.
-/
namespace StackSorting.ConnectedConeNormalization
open GraphWidth SameVertexForest
variable {n : Nat}

def Cone (O : RankedOrder n) (x y : Fin n) : Prop := O.rel x y ∨ x = y

theorem cone_refl (O : RankedOrder n) (x : Fin n) : Cone O x x := Or.inr rfl

theorem cone_trans (O : RankedOrder n) {x y z : Fin n}
    (h : Cone O x y) (k : Cone O y z) : Cone O x z := by
  rcases h with h | rfl
  · rcases k with k | rfl
    · exact Or.inl (O.trans h k)
    · exact Or.inl h
  · exact k

/-- Remove ancestry across disconnected pieces of every old cone. -/
def ReachCone (G : Graph n) (O : RankedOrder n) (x y : Fin n) : Prop :=
  Walk G.Adj (Cone O x) x y

theorem reachCone_old (G : Graph n) (O : RankedOrder n) {x y}
    (h : ReachCone G O x y) : Cone O x y := h.finish

theorem reachCone_refl (G : Graph n) (O : RankedOrder n) (x) :
    ReachCone G O x x := .refl (cone_refl O x)

theorem reachCone_trans (G : Graph n) (O : RankedOrder n) {x y z}
    (h : ReachCone G O x y) (k : ReachCone G O y z) : ReachCone G O x z :=
  h.trans (k.mono (fun _ hz => cone_trans O h.finish hz))

theorem reachCone_antisymm (G : Graph n) (O : RankedOrder n) {x y}
    (h : ReachCone G O x y) (k : ReachCone G O y x) : x = y := by
  rcases h.finish with h | h
  · rcases k.finish with k | k
    · exact False.elim (O.irrefl x (O.trans h k))
    · exact k.symm
  · exact h

/-- A path can be relabelled by actual reachability from its starting point. -/
theorem walk_reachable {P : Fin n → Prop} {G : Graph n} {x u v}
    (h : Walk G.Adj P u v) (p : Walk G.Adj P x u) :
    Walk G.Adj (fun z => Walk G.Adj P x z) u v := by
  induction h generalizing x with
  | refl => exact .refl p
  | @step u v w hu huv tail ih =>
    exact .step p huv (ih (p.trans (.step hu huv (.refl tail.start))))

/-- New cones really are connected in the original graph. -/
theorem reachCone_connected (G : Graph n) (O : RankedOrder n) {x y z}
    (hy : ReachCone G O x y) (hz : ReachCone G O x z) :
    Walk G.Adj (ReachCone G O x) y z :=
  ((walk_reachable hy (reachCone_refl G O x)).reverse G.symm).trans
    (walk_reachable hz (reachCone_refl G O x))

/-- Common descendants still have comparable ancestors: connect their two
paths inside the larger old cone. -/
theorem reachCone_predecessors (G : Graph n) (O : RankedOrder n) {x y z}
    (hx : ReachCone G O x z) (hy : ReachCone G O y z) :
    ReachCone G O x y ∨ ReachCone G O y x := by
  rcases hx.finish with hxz | rfl
  · rcases hy.finish with hyz | rfl
    · rcases O.predecessors hxz hyz with hxy | rfl | hyx
      · exact Or.inl (hx.trans ((hy.mono (fun _ h => cone_trans O (Or.inl hxy) h)).reverse G.symm))
      · exact Or.inl (reachCone_refl G O x)
      · exact Or.inr (hy.trans ((hx.mono (fun _ h => cone_trans O (Or.inl hyx) h)).reverse G.symm))
    · exact Or.inl hx
  · exact Or.inr hy

/-- Every original edge remains comparable without adding edges. -/
theorem reachCone_eliminates (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u) {x y}
    (hxy : G.Adj x y) : ReachCone G O x y ∨ ReachCone G O y x := by
  rcases helim hxy with h | h
  · exact Or.inl (.step (cone_refl O x) hxy (.refl (Or.inl h)))
  · exact Or.inr (.step (cone_refl O y) (G.symm hxy) (.refl (Or.inl h)))

noncomputable def normalizedOrder (G : Graph n) (O : RankedOrder n) : RankedOrder n where
  rel x y := ReachCone G O x y ∧ x ≠ y
  irrefl _ h := h.2 rfl
  trans h k := ⟨reachCone_trans G O h.1 k.1, by
    intro e
    exact h.2 (reachCone_antisymm G O h.1 (by simpa only [e] using k.1))⟩
  predecessors := by
    intro x y z hx hy
    by_cases he : x = y
    · exact Or.inr (Or.inl he)
    · rcases reachCone_predecessors G O hx.1 hy.1 with h | h
      · exact Or.inl ⟨h,he⟩
      · exact Or.inr (Or.inr ⟨h,Ne.symm he⟩)
  rank := O.rank
  increasing h := O.increasing (h.1.finish.resolve_right h.2)

@[simp] theorem normalized_ancestor (G : Graph n) (O : RankedOrder n) (x y) :
    Ancestor (normalizedOrder G O).forest x y ↔ ReachCone G O x y := by
  rw [(normalizedOrder G O).ancestor_iff]
  constructor
  · rintro (h | rfl)
    · exact h.1
    · exact reachCone_refl G O x
  · intro h
    by_cases he : x = y
    · exact Or.inr he
    · exact Or.inl ⟨h,he⟩

/-- Exact bags shrink, not merely their cardinalities. -/
theorem normalized_frontier_subset (G : Graph n) (O : RankedOrder n) {v u}
    (h : EliminationFrontier (normalizedOrder G O).forest G v u) :
    EliminationFrontier O.forest G v u := by
  rcases h with h | ⟨huv,hne,w,hvw,he⟩
  · exact Or.inl h
  · refine Or.inr ⟨O.ancestor_iff.mpr ?_,hne,w,O.ancestor_iff.mpr ?_,he⟩
    · exact ((normalized_ancestor G O u v).mp huv).finish
    · exact ((normalized_ancestor G O v w).mp hvw).finish

theorem normalized_frontier_card (G : Graph n) (O : RankedOrder n) (v) :
    (eliminationFrontierSet (normalizedOrder G O).forest G v).card ≤
      (eliminationFrontierSet O.forest G v).card := by
  classical
  apply Finset.card_le_card
  intro u hu
  simp only [eliminationFrontierSet,Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
  exact normalized_frontier_subset G O hu

/-- Normalization keeps every bag inside the original introduction bag.
The original node is retained as a concrete origin label for every new node. -/
theorem normalized_origin_bag {t} {G : Graph n} {T : FinitePort.RootedTree t}
    (D : Decomposition G T) {v u}
    (h : EliminationFrontier (normalizedOrder G (introductionOrder D)).forest G v u) :
    u ∈ D.bag (introductionNode D v) := by
  apply introductionFrontier_subset D
  apply (eliminationFrontier_iff D v u).mp
  exact normalized_frontier_subset G (introductionOrder D) h

#print axioms normalized_ancestor
#print axioms reachCone_connected
#print axioms normalized_origin_bag
end StackSorting.ConnectedConeNormalization
