import FactorizationTree

namespace StackSorting.Simon.FactorizationTree

variable {A B M : Type*} [Monoid M]

def map (f : A → B) : FactorizationTree A → FactorizationTree B
  | .leaf a => .leaf (f a)
  | .node ts => .node (ts.map (map f))

theorem leaves_map (f : A → B) (t : FactorizationTree A) :
    (t.map f).leaves = t.leaves.map f := by
  cases t with
  | leaf a => simp [map, leaves]
  | node ts =>
    rw [map, leaves, leaves, List.flatMap_map, List.map_flatMap]
    simp only [List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro t ht
    exact leaves_map f t
termination_by sizeOf t

theorem height_map (f : A → B) (t : FactorizationTree A) :
    (t.map f).height = t.height := by
  cases t with
  | leaf a => simp [map, height]
  | node ts =>
    have hm : (ts.map (map f)).map height = ts.map height := by
      rw [List.map_map]
      apply List.map_congr_left
      intro t ht
      exact height_map f t
    rw [map, height, height, hm]
termination_by sizeOf t

theorem value_map (φ : A → M) (ψ : B → M) (f : A → B) (t : FactorizationTree A)
    (hlabels : ∀ a ∈ t.leaves, ψ (f a) = φ a) :
    value ψ (t.map f) = value φ t := by
  simp only [value, leaves_map, List.map_map]
  congr 1
  exact List.map_congr_left hlabels

theorem valid_map (φ : A → M) (ψ : B → M) (f : A → B) (t : FactorizationTree A)
    (hv : Valid φ t) (hlabels : ∀ a ∈ t.leaves, ψ (f a) = φ a) :
    Valid ψ (t.map f) := by
  induction hv with
  | leaf a => simpa only [map] using (Valid.leaf (φ := ψ) (f a))
  | node ts hchildren harity hbranch ih =>
    rw [map]
    apply Valid.node
    · intro u hu
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
      apply ih r hr
      intro a ha
      exact hlabels a (by simpa only [leaves] using (List.mem_flatMap.mpr ⟨r, hr, ha⟩))
    · simpa using harity
    · rcases hbranch with hbinary | ⟨e, he, hall⟩
      · left
        simpa using hbinary
      · right
        refine ⟨e, he, ?_⟩
        intro u hu
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
        rw [value_map φ ψ f r (by
          intro a ha
          exact hlabels a (by simpa only [leaves] using (List.mem_flatMap.mpr ⟨r, hr, ha⟩)))]
        exact hall r hr

theorem hasTree_map (φ : A → M) (ψ : B → M) (f : A → B)
    (w : List A) (h : ℕ) (ht : HasTree φ w h)
    (hlabels : ∀ a ∈ w, ψ (f a) = φ a) : HasTree ψ (w.map f) h := by
  obtain ⟨t, hw, hv, hh⟩ := ht
  refine ⟨t.map f, ?_, ?_, ?_⟩
  · rw [leaves_map, hw]
  · exact valid_map φ ψ f t hv (by simpa [hw] using hlabels)
  · simpa only [height_map] using hh

#print axioms hasTree_map
end StackSorting.Simon.FactorizationTree
