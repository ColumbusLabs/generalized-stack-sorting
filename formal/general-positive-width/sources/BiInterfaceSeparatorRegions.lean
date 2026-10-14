import GuidanceBiInterface

namespace StackSorting.BiInterface
universe u
variable {k : Nat} {V W : Type u} (G : Graph k V) (H : Graph k W)

/-- The actual vertices named on a partial interface. -/
def namedVertices (p : Fin k → Option V) : Set V := {v | ∃ i, p i = some v}

def leftInteriorImage : Set (Glued G H) :=
  inLeft G H '' (namedVertices G.right)ᶜ

def rightInteriorImage : Set (Glued G H) :=
  inRight G H '' (namedVertices H.left)ᶜ

def joinBoundary : Set (Glued G H) :=
  (inLeft G H '' namedVertices G.right) ∪ (inRight G H '' namedVertices H.left)

theorem leftInterior_ne_right {x : V} (hx : x ∉ namedVertices G.right) (y : W) :
    inLeft G H x ≠ inRight G H y := by
  intro he
  obtain ⟨i,hi,_⟩ := (inLeft_eq_inRight G H x y).mp he
  exact hx ⟨i,hi⟩

theorem rightInterior_ne_left {y : W} (hy : y ∉ namedVertices H.left) (x : V) :
    inRight G H y ≠ inLeft G H x := by
  intro he
  obtain ⟨i,_,hi⟩ := (inLeft_eq_inRight G H x y).mp he.symm
  exact hy ⟨i,hi⟩

theorem interiorImages_disjoint : Disjoint (leftInteriorImage G H) (rightInteriorImage G H) := by
  apply Set.disjoint_left.mpr
  rintro a ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
  exact leftInterior_ne_right G H hx y he.symm

theorem interiorImages_no_edge {a b : Glued G H}
    (ha : a ∈ leftInteriorImage G H) (hb : b ∈ rightInteriorImage G H) :
    ¬ (glue G H).Adj a b := by
  rcases ha with ⟨x,hx,rfl⟩
  rcases hb with ⟨y,hy,rfl⟩
  rintro (⟨r,s,_,hr,hs⟩ | ⟨r,s,_,hr,hs⟩)
  · exact rightInterior_ne_left G H hy s hs.symm
  · exact leftInterior_ne_right G H hx r hr.symm

theorem leftInterior_reflects_adj {x y : V}
    (hx : x ∉ namedVertices G.right)
    (h : (glue G H).Adj (inLeft G H x) (inLeft G H y)) : G.Adj x y := by
  rcases h with ⟨a,b,hab,ha,hb⟩ | ⟨a,b,_,ha,hb⟩
  · have hax := inLeft_injective G H ha
    have hby := inLeft_injective G H hb
    subst a; subst b
    exact hab
  · exact (leftInterior_ne_right G H hx a ha.symm).elim

theorem rightInterior_reflects_adj {x y : W}
    (hx : x ∉ namedVertices H.left)
    (h : (glue G H).Adj (inRight G H x) (inRight G H y)) : H.Adj x y := by
  rcases h with ⟨a,b,_,ha,hb⟩ | ⟨a,b,hab,ha,hb⟩
  · exact (rightInterior_ne_left G H hx a ha.symm).elim
  · have hax := inRight_injective G H ha
    have hby := inRight_injective G H hb
    subst a; subst b
    exact hab

theorem interiorImages_cover :
    leftInteriorImage G H ∪ rightInteriorImage G H = (joinBoundary G H)ᶜ := by
  classical
  ext a
  constructor
  · rintro (⟨x,hx,rfl⟩ | ⟨y,hy,rfl⟩)
    · rintro (⟨z,hz,he⟩ | ⟨z,hz,he⟩)
      · exact hx ((inLeft_injective G H he) ▸ hz)
      · exact leftInterior_ne_right G H hx z he.symm
    · rintro (⟨z,hz,he⟩ | ⟨z,hz,he⟩)
      · exact rightInterior_ne_left G H hy z he.symm
      · exact hy ((inRight_injective G H he) ▸ hz)
  · intro ha
    induction a using Quotient.inductionOn with
    | _ a =>
      cases a with
      | inl x =>
        exact Or.inl ⟨x,fun hx => ha (Or.inl ⟨x,hx,rfl⟩),rfl⟩
      | inr y =>
        exact Or.inr ⟨y,fun hy => ha (Or.inr ⟨y,hy,rfl⟩),rfl⟩
end StackSorting.BiInterface
