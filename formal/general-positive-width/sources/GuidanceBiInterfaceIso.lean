import GuidanceBiInterface
import DecompositionEmbedding
import GraphIso

namespace StackSorting.BiInterface
open GuidedPathwidth
universe u
variable {k c : Nat} {V W : Type u} {G : Graph k V} {H : Graph k W}

/-- Literal graph isomorphisms transport constructed bags and guides without
altering the palette or replacing the original vertex names by an oracle. -/
noncomputable def Iso.mapGuided (e : Iso G H)
    (D : GuidedDecomposition G.simple Set.univ c) : GuidedDecomposition H.simple Set.univ c := by
  let f : G.simple ↪g H.simple := {
    toFun := e.vertex
    inj' := e.vertex.injective
    map_rel_iff' := fun {a b} => e.adj a b }
  let E := D.map f
  have he : f '' Set.univ = Set.univ := by
    ext y
    constructor
    · intro h; trivial
    · intro h
      obtain ⟨x,rfl⟩ := e.vertex.surjective y
      exact ⟨x,trivial,rfl⟩
  exact he ▸ E
end StackSorting.BiInterface
