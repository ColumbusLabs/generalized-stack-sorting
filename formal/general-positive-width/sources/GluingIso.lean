import GraphIso

namespace StackSorting.BiInterface
variable {k : ℕ} {U V W X : Type*}
namespace Iso
variable {G : Graph k U} {G' : Graph k V} {H : Graph k W} {H' : Graph k X}

noncomputable def symm (e : Iso G G') : Iso G' G where
  vertex := e.vertex.symm
  adj := by intro v w; simpa using (e.adj (e.vertex.symm v) (e.vertex.symm w)).symm
  left := by
    intro i
    rw [← e.left i,Option.map_map]
    simp
  right := by
    intro i
    rw [← e.right i,Option.map_map]
    simp

def mapGlue (e : Iso G G') (f : Iso H H') : Glued G H → Glued G' H' :=
  glueLift G H (fun u => inLeft G' H' (e.vertex u))
    (fun w => inRight G' H' (f.vertex w)) (by
      intro u w h
      obtain ⟨i,hi,hj⟩ := h
      exact (inLeft_eq_inRight G' H' _ _).mpr
        ⟨i,(e.port_some (true,i) u).mpr hi,(f.port_some (false,i) w).mpr hj⟩)

@[simp] theorem mapGlue_left (e : Iso G G') (f : Iso H H') (u : U) :
    mapGlue e f (inLeft G H u) = inLeft G' H' (e.vertex u) := rfl
@[simp] theorem mapGlue_right (e : Iso G G') (f : Iso H H') (w : W) :
    mapGlue e f (inRight G H w) = inRight G' H' (f.vertex w) := rfl

private theorem mapGlue_inverse (e : Iso G G') (f : Iso H H') (q : Glued G H) :
    mapGlue e.symm f.symm (mapGlue e f q) = q := by
  induction q using Quotient.inductionOn with | h q =>
    cases q <;> simp [mapGlue,symm,inLeft,inRight,glueLift]

noncomputable def glueEquiv (e : Iso G G') (f : Iso H H') : Glued G H ≃ Glued G' H' where
  toFun := mapGlue e f
  invFun := mapGlue e.symm f.symm
  left_inv := mapGlue_inverse e f
  right_inv := by
    intro q
    have h := mapGlue_inverse e.symm f.symm q
    exact h

private theorem mapGlue_adj (e : Iso G G') (f : Iso H H') {a b}
    (h : (BiInterface.glue G H).Adj a b) :
    (BiInterface.glue G' H').Adj (mapGlue e f a) (mapGlue e f b) := by
  rcases h with ⟨x,y,hxy,rfl,rfl⟩ | ⟨x,y,hxy,rfl,rfl⟩
  · exact Or.inl ⟨e.vertex x,e.vertex y,(e.adj x y).mpr hxy,rfl,rfl⟩
  · exact Or.inr ⟨f.vertex x,f.vertex y,(f.adj x y).mpr hxy,rfl,rfl⟩

noncomputable def glue (e : Iso G G') (f : Iso H H') :
    Iso (BiInterface.glue G H) (BiInterface.glue G' H') where
  vertex := glueEquiv e f
  adj := by
    intro a b
    constructor
    · intro h
      have hh := mapGlue_adj e.symm f.symm h
      change (BiInterface.glue G H).Adj
        ((glueEquiv e f).symm (glueEquiv e f a))
        ((glueEquiv e f).symm (glueEquiv e f b)) at hh
      simpa using hh
    · exact mapGlue_adj e f
  left := by
    intro i
    change ((G.left i).map (inLeft G H)).map (mapGlue e f) = (G'.left i).map (inLeft G' H')
    simpa only [Option.map_map,Function.comp_def,mapGlue_left] using
      congrArg (Option.map (inLeft G' H')) (e.left i)
  right := by
    intro i
    change ((H.right i).map (inRight G H)).map (mapGlue e f) = (H'.right i).map (inRight G' H')
    simpa only [Option.map_map,Function.comp_def,mapGlue_right] using
      congrArg (Option.map (inRight G' H')) (f.right i)

end Iso
end StackSorting.BiInterface
