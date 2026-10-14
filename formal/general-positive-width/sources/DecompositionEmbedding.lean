import GuidanceEmbedding

namespace StackSorting.GuidedPathwidth
universe u
variable {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}
    {P : Set V} {c : Nat}

namespace Decomposition
/-- Transport a supplied decomposition along an induced graph embedding.
The index forest is unchanged and bags are literal vertex images. -/
noncomputable def mapRegion (D : Decomposition G P) (f : V ↪ W)
    (hback : ∀ {a b}, a ∈ P → b ∈ P → H.Adj (f a) (f b) → G.Adj a b) :
    Decomposition H (f '' P) where
  Node := D.Node
  finiteNode := inferInstance
  forest := D.forest
  acyclic := D.acyclic
  bag := fun a => f '' D.bag a
  inside := by
    rintro a y ⟨x,hx,rfl⟩
    exact ⟨x,D.inside a hx,rfl⟩
  vertex := by
    rintro y ⟨x,hx,rfl⟩
    obtain ⟨a,ha⟩ := D.vertex x hx
    exact ⟨a,x,ha,rfl⟩
  edge := by
    rintro x y hxy ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
    obtain ⟨t,hta,htb⟩ := D.edge (hback ha hb hxy) ha hb
    exact ⟨t,⟨a,hta,rfl⟩,⟨b,htb,rfl⟩⟩
  running := by
    rintro x a b ⟨y,hy,rfl⟩ ⟨z,hz,he⟩
    have hzy : z = y := f.injective he
    subst z
    have h := D.running y a b hy hz
    exact h.mono (fun t ht => ⟨y,ht,rfl⟩)
end Decomposition

namespace GuidedDecomposition
noncomputable def mapRegion (D : GuidedDecomposition G P c) (f : V ↪ W)
    (hf : ∀ {a b}, G.Adj a b → H.Adj (f a) (f b))
    (hback : ∀ {a b}, a ∈ P → b ∈ P → H.Adj (f a) (f b) → G.Adj a b) :
    GuidedDecomposition H (f '' P) c where
  decomposition := D.decomposition.mapRegion f hback
  guides := D.guides.map f hf
  captured := fun a => System.map_captures D.guides f hf (D.captured a)

noncomputable def map (D : GuidedDecomposition G P c) (f : G ↪g H) :
    GuidedDecomposition H (f '' P) c :=
  D.mapRegion f.toEmbedding (fun h => f.map_rel_iff.mpr h)
    (fun _ _ h => f.map_rel_iff.mp h)
end GuidedDecomposition

#print axioms GuidedDecomposition.map
end StackSorting.GuidedPathwidth
