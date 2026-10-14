import GraftMarkedConnectivity

namespace StackSorting.GuidedPathwidth
universe u
variable {V J : Type u} {G : SimpleGraph V} {P I : Set V}

/-- Concrete bag data for replacing interior pieces by a boundary spine.
There is no output decomposition or guidance witness in this data. -/
structure BoundaryGraftData (D : Decomposition G I) (T : SimpleGraph J) where
  core : J → Set V
  extra : D.Node → Set V
  location : D.Node → J
  interiorInside : I ⊆ P
  coreInside : ∀ j, core j ⊆ P \ I
  extraInside : ∀ a, extra a ⊆ core (location a)
  locationStable : ∀ {a b}, D.forest.Adj a b → location a = location b
  extraStable : ∀ {a b}, D.forest.Adj a b → extra a ⊆ extra b
  boundaryCovered : ∀ x ∈ P \ I, ∃ j, x ∈ core j
  crossCovered : ∀ {x y}, x ∈ I → y ∈ P \ I → G.Adj x y →
    ∀ a, x ∈ D.bag a → y ∈ extra a
  boundaryEdges : ∀ {x y}, x ∈ P \ I → y ∈ P \ I → G.Adj x y →
    ∃ j, x ∈ core j ∧ y ∈ core j
  coreRunning : ∀ x a b, x ∈ core a → x ∈ core b →
    ReachIn T {a | x ∈ core a} a b

namespace BoundaryGraftData
variable {D : Decomposition G I} {T : SimpleGraph J}

def bags (B : BoundaryGraftData (P := P) D T) : J ⊕ D.Node → Set V :=
  Sum.elim B.core (fun a => D.bag a ∪ B.extra a)

theorem running (B : BoundaryGraftData (P := P) D T) (F : GraftedForest T D.forest B.location)
    (x : V) (a b : J ⊕ D.Node) (ha : x ∈ B.bags a) (hb : x ∈ B.bags b) :
    ReachIn F.graph {a | x ∈ B.bags a} a b := by
  by_cases hx : x ∈ I
  · have old : ∀ a, x ∈ B.bags a → ∃ n, a = Sum.inr n ∧ x ∈ D.bag n := by
      intro a ha
      cases a with
      | inl j => exact ((B.coreInside j ha).2 hx).elim
      | inr n =>
        rcases ha with ha | ha
        · exact ⟨n,rfl,ha⟩
        · exact ((B.coreInside _ (B.extraInside n ha)).2 hx).elim
    obtain ⟨n,rfl,hn⟩ := old a ha
    obtain ⟨m,rfl,hm⟩ := old b hb
    have h := D.running x n m hn hm
    refine ⟨ha,hb,?_⟩
    exact h.2.2.map Sum.inr (fun _ _ h => F.oldEdges h) (fun _ h => Or.inl h)
  · let loc : J ⊕ D.Node → J := Sum.elim id B.location
    have route : ∀ a, x ∈ B.bags a →
        x ∈ B.core (loc a) ∧ ReachIn F.graph {a | x ∈ B.bags a} a (.inl (loc a)) := by
      intro a ha
      cases a with
      | inl j => exact ⟨ha,ReachIn.refl ha⟩
      | inr n =>
        have hn : x ∈ B.extra n := by
          rcases ha with ha | ha
          · exact (hx (D.inside n ha)).elim
          · exact ha
        have hcore := B.extraInside n hn
        refine ⟨hcore,?_⟩
        have hpath := F.markedConnected B.locationStable
          (M := {m | x ∈ B.extra m}) (fun h hm => B.extraStable h hm) hn
        apply hpath.mono
        intro a ha
        cases a with
        | inl j =>
          have he : j = B.location n := ha
          exact he.symm ▸ hcore
        | inr m => exact Or.inr ha.2
    obtain ⟨hca,hra⟩ := route a ha
    obtain ⟨hcb,hrb⟩ := route b hb
    have hcore := B.coreRunning x (loc a) (loc b) hca hcb
    have hc : ReachIn F.graph {a | x ∈ B.bags a} (.inl (loc a)) (.inl (loc b)) := by
      refine ⟨hca,hcb,?_⟩
      exact hcore.2.2.map Sum.inl (fun _ _ h => F.oldEdges h) (fun _ h => h)
    exact (hra.trans hc).trans hrb.symm

/-- The boundary spine and interior bags give an actual finite forest-indexed
cover with connected occurrences, using the constructed graft forest. -/
noncomputable def decomposition [Finite J] (B : BoundaryGraftData (P := P) D T) (hT : T.IsAcyclic) :
    Decomposition G P := by
  let F := Classical.choice (exists_graftedForest hT D.acyclic B.locationStable)
  exact {
    Node := J ⊕ D.Node
    finiteNode := inferInstance
    forest := F.graph
    acyclic := F.acyclic
    bag := B.bags
    inside := by
      intro a x hx
      cases a with
      | inl j => exact (B.coreInside j hx).1
      | inr n =>
        rcases hx with hx | hx
        · exact B.interiorInside (D.inside n hx)
        · exact (B.coreInside _ (B.extraInside n hx)).1
    vertex := by
      intro x hx
      by_cases hi : x ∈ I
      · obtain ⟨a,ha⟩ := D.vertex x hi
        exact ⟨.inr a,Or.inl ha⟩
      · obtain ⟨j,hj⟩ := B.boundaryCovered x ⟨hx,hi⟩
        exact ⟨.inl j,hj⟩
    edge := by
      intro x y hxy hx hy
      by_cases hxi : x ∈ I <;> by_cases hyi : y ∈ I
      · obtain ⟨a,ha,hb⟩ := D.edge hxy hxi hyi
        exact ⟨.inr a,Or.inl ha,Or.inl hb⟩
      · obtain ⟨a,ha⟩ := D.vertex x hxi
        exact ⟨.inr a,Or.inl ha,Or.inr (B.crossCovered hxi ⟨hy,hyi⟩ hxy a ha)⟩
      · obtain ⟨a,ha⟩ := D.vertex y hyi
        exact ⟨.inr a,Or.inr (B.crossCovered hyi ⟨hx,hxi⟩ hxy.symm a ha),Or.inl ha⟩
      · obtain ⟨j,hj,hk⟩ := B.boundaryEdges ⟨hx,hxi⟩ ⟨hy,hyi⟩ hxy
        exact ⟨.inl j,hj,hk⟩
    running := B.running F }
end BoundaryGraftData

#print axioms BoundaryGraftData.decomposition
end StackSorting.GuidedPathwidth
