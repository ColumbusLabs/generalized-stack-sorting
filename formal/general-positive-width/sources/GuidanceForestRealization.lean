import GuidanceComponents

namespace StackSorting.GuidedPathwidth
universe u
variable {V : Type u} {G : SimpleGraph V} {P : Set V}
namespace Color

/-- Actual original edges restricted to one of this color's disjoint supports. -/
def supportGraph (C : Color G P) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ∃ r, x ∈ C.support r ∧ y ∈ C.support r
  symm := ⟨by
    intro x y h
    obtain ⟨hxy,r,hx,hy⟩ := h
    exact ⟨hxy.symm,r,hy,hx⟩⟩
  loopless := ⟨fun x h => h.1.ne rfl⟩

theorem supportGraph_le (C : Color G P) : C.supportGraph ≤ G := fun _ _ h => h.1

theorem walk_stays (C : Color G P) {x y r : V}
    (w : C.supportGraph.Walk x y) (hx : x ∈ C.support r) : y ∈ C.support r := by
  revert hx
  induction w with
  | nil => exact fun hx => hx
  | @cons x y z hxy w ih =>
    intro hx
    obtain ⟨_,s,hsx,hsy⟩ := hxy
    have he := C.unique r s x hx hsx
    subst s
    exact ih hsy

theorem root_reachable (C : Color G P) {x r : V} (hx : x ∈ C.support r) :
    C.supportGraph.Reachable x r := by
  let f : G.induce (C.support r) →g C.supportGraph := {
    toFun := Subtype.val
    map_rel' := by intro a b hab; exact ⟨hab,r,a.property,b.property⟩ }
  exact SimpleGraph.Reachable.map f (C.reaches r x hx).induced

/-- A real acyclic original-edge graph realizing all the support/root relations
at once. Selecting a spanning forest changes no reachable root. -/
structure ForestWitness (C : Color G P) where
  graph : SimpleGraph V
  subgraph : graph ≤ G
  acyclic : graph.IsAcyclic
  endpoints : ∀ {x y}, graph.Adj x y →
    (∃ r, x ∈ C.support r) ∧ (∃ r, y ∈ C.support r)
  exactRoots : ∀ x r, (r ∈ C.support r ∧ graph.Reachable x r) ↔ x ∈ C.support r

/-- Existence follows from a genuine spanning-forest theorem, not an assumed
acyclicity or root-relation witness. -/
theorem exists_forest (C : Color G P) : Nonempty (ForestWitness C) := by
  obtain ⟨F,hF,ha,heq⟩ := C.supportGraph.exists_isAcyclic_reachable_eq_le
  refine ⟨{
    graph := F
    subgraph := hF.trans C.supportGraph_le
    acyclic := ha
    endpoints := ?_
    exactRoots := ?_ }⟩
  · intro x y hxy
    obtain ⟨_,r,hx,hy⟩ := hF hxy
    exact ⟨⟨r,hx⟩,⟨r,hy⟩⟩
  · intro x r
    rw [heq]
    constructor
    · rintro ⟨hr,⟨w⟩⟩
      exact C.walk_stays w.reverse hr
    · intro hx
      exact ⟨C.root_mem hx,C.root_reachable hx⟩

/-- Every selected vertex has exactly one root in the actual chosen forest. -/
theorem ForestWitness.unique_root {C : Color G P} (F : ForestWitness C)
    {x : V} (hx : ∃ r, x ∈ C.support r) :
    ∃! r, r ∈ C.support r ∧ F.graph.Reachable x r := by
  obtain ⟨r,hr⟩ := hx
  refine ⟨r,(F.exactRoots x r).mpr hr,?_⟩
  intro s hs
  exact C.unique s r x ((F.exactRoots x s).mp hs) hr
end Color

#print axioms Color.exists_forest
end StackSorting.GuidedPathwidth
