import DecompositionEmbedding

namespace StackSorting.GuidedPathwidth
universe u

/-- Transport a small finite source decomposition into an arbitrary vertex
universe. Only index names are lifted; bags and original graph vertices are
mapped literally, and the exact guidance palette is retained. -/
noncomputable def GuidedDecomposition.liftMapRegion
    {V : Type} {W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}
    {P : Set V} {c : Nat} (D : GuidedDecomposition G P c) (f : V ↪ W)
    (hf : ∀ {a b}, G.Adj a b → H.Adj (f a) (f b))
    (hback : ∀ {a b}, a ∈ P → b ∈ P → H.Adj (f a) (f b) → G.Adj a b) :
    GuidedDecomposition H (f '' P) c := by
  let T : SimpleGraph (ULift.{u} D.decomposition.Node) := D.decomposition.forest.comap ULift.down
  have hT : T.IsAcyclic := by
    let h : T →g D.decomposition.forest := ⟨ULift.down,fun h => h⟩
    intro x p hp
    exact D.decomposition.acyclic (p.map h) (hp.map ULift.down_injective)
  let E : Decomposition H (f '' P) := {
    Node := ULift.{u} D.decomposition.Node
    finiteNode := inferInstance
    forest := T
    acyclic := hT
    bag := fun a => f '' D.decomposition.bag a.down
    inside := by
      rintro a y ⟨x,hx,rfl⟩
      exact ⟨x,D.decomposition.inside a.down hx,rfl⟩
    vertex := by
      rintro y ⟨x,hx,rfl⟩
      obtain ⟨a,ha⟩ := D.decomposition.vertex x hx
      exact ⟨⟨a⟩,x,ha,rfl⟩
    edge := by
      rintro x y hxy ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
      obtain ⟨t,hta,htb⟩ := D.decomposition.edge (hback ha hb hxy) ha hb
      exact ⟨⟨t⟩,⟨a,hta,rfl⟩,⟨b,htb,rfl⟩⟩
    running := by
      rintro x a b ⟨y,hy,rfl⟩ ⟨z,hz,he⟩
      have hzy : z = y := f.injective he
      subst z
      have h := D.decomposition.running y a.down b.down hy hz
      refine ⟨⟨y,hy,rfl⟩,⟨y,hz,rfl⟩,?_⟩
      exact h.2.2.map ULift.up (by intro a b hab; exact hab)
        (fun a ha => ⟨y,ha,rfl⟩) }
  exact ⟨E,D.guides.map f hf,fun a => System.map_captures D.guides f hf (D.captured a.down)⟩

#print axioms GuidedDecomposition.liftMapRegion
end StackSorting.GuidedPathwidth
