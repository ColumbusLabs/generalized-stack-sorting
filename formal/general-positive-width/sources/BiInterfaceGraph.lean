import TorsoPaths
import Mathlib.Data.Fintype.Quotient

namespace StackSorting.BiInterface

/-- Partial injective interfaces. The cross condition is essential: a vertex
shared by left and right interfaces has the same interface name. -/
structure Graph (k : ℕ) (V : Type*) where
  Adj : V → V → Prop
  symm : ∀ {x y}, Adj x y → Adj y x
  loopless : ∀ x, ¬ Adj x x
  left : Fin k → Option V
  right : Fin k → Option V
  left_inj : ∀ i j x, left i = some x → left j = some x → i = j
  right_inj : ∀ i j x, right i = some x → right j = some x → i = j
  cross : ∀ i j x, left i = some x → right j = some x → i = j

variable {k : ℕ} {V W X : Type*}

/-- The only identifications made while gluing two partial-interface graphs. -/
def Seam (G : Graph k V) (H : Graph k W) (v : V) (w : W) : Prop :=
  ∃ i, G.right i = some v ∧ H.left i = some w

def GlueRel (G : Graph k V) (H : Graph k W) : Sum V W → Sum V W → Prop
  | .inl v, .inl v' => v = v'
  | .inr w, .inr w' => w = w'
  | .inl v, .inr w => Seam G H v w
  | .inr w, .inl v => Seam G H v w

private theorem seam_left_unique (G : Graph k V) (H : Graph k W)
    {v v' : V} {w : W} (h : Seam G H v w) (h' : Seam G H v' w) : v = v' := by
  obtain ⟨i, hi, hj⟩ := h
  obtain ⟨i', hi', hj'⟩ := h'
  have he := H.left_inj i i' w hj hj'
  subst i'
  exact Option.some.inj (hi.symm.trans hi')

private theorem seam_right_unique (G : Graph k V) (H : Graph k W)
    {v : V} {w w' : W} (h : Seam G H v w) (h' : Seam G H v w') : w = w' := by
  obtain ⟨i, hi, hj⟩ := h
  obtain ⟨i', hi', hj'⟩ := h'
  have he := G.right_inj i i' v hi hi'
  subst i'
  exact Option.some.inj (hj.symm.trans hj')

def glueSetoid (G : Graph k V) (H : Graph k W) : Setoid (Sum V W) where
  r := GlueRel G H
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a; cases a <;> rfl
    · intro a b h; cases a <;> cases b <;> first | exact h | exact h.symm
    · intro a b c hab hbc
      cases a with
      | inl a =>
        cases b with
        | inl b => cases c <;> simp only [GlueRel] at * <;> subst b <;> assumption
        | inr b =>
          cases c with
          | inl c => exact seam_left_unique G H hab hbc
          | inr c => exact hbc ▸ hab
      | inr a =>
        cases b with
        | inl b =>
          cases c with
          | inl c => exact hbc ▸ hab
          | inr c => exact seam_right_unique G H hab hbc
        | inr b => cases c <;> simp only [GlueRel] at * <;> subst b <;> assumption

abbrev Glued (G : Graph k V) (H : Graph k W) := Quotient (glueSetoid G H)

def inLeft (G : Graph k V) (H : Graph k W) (v : V) : Glued G H :=
  Quotient.mk _ (.inl v)
def inRight (G : Graph k V) (H : Graph k W) (w : W) : Glued G H :=
  Quotient.mk _ (.inr w)

theorem inLeft_injective (G : Graph k V) (H : Graph k W) :
    Function.Injective (inLeft G H) := by
  intro v v' h
  exact Quotient.exact h

theorem inRight_injective (G : Graph k V) (H : Graph k W) :
    Function.Injective (inRight G H) := by
  intro v v' h
  exact Quotient.exact h

theorem inLeft_eq_inRight (G : Graph k V) (H : Graph k W) (v : V) (w : W) :
    inLeft G H v = inRight G H w ↔ Seam G H v w := Quotient.eq

/-- Universal map out of the genuine quotient gluing. -/
def glueLift (G : Graph k V) (H : Graph k W) (f : V → X) (g : W → X)
    (h : ∀ v w, Seam G H v w → f v = g w) : Glued G H → X :=
  Quotient.lift (Sum.elim f g) (by
    intro a b hab
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg f hab
      | inr b => exact h a b hab
    | inr a => cases b with
      | inl b => exact (h b a hab).symm
      | inr b => exact congrArg g hab)

@[simp] theorem glueLift_left (G : Graph k V) (H : Graph k W) (f : V → X) (g : W → X)
    (h) (v : V) : glueLift G H f g h (inLeft G H v) = f v := rfl
@[simp] theorem glueLift_right (G : Graph k V) (H : Graph k W) (f : V → X) (g : W → X)
    (h) (w : W) : glueLift G H f g h (inRight G H w) = g w := rfl

/-- No additional identifications are hidden in quotient gluing. This permits
literal original-vertex reconstruction from a supplied bag decomposition. -/
theorem glueLift_injective (G : Graph k V) (H : Graph k W) (f : V → X) (g : W → X)
    (h : ∀ v w, Seam G H v w → f v = g w)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hcross : ∀ v w, f v = g w → Seam G H v w) :
    Function.Injective (glueLift G H f g h) := by
  intro a b
  induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
      intro he
      apply Quotient.sound
      cases a with
      | inl a => cases b with
        | inl b => exact hf he
        | inr b => exact hcross a b he
      | inr a => cases b with
        | inl b => exact hcross b a he.symm
        | inr b => exact hg he

theorem glueLift_surjective (G : Graph k V) (H : Graph k W) (f : V → X) (g : W → X)
    (h : ∀ v w, Seam G H v w → f v = g w)
    (hcover : ∀ x, (∃ v, f v = x) ∨ (∃ w, g w = x)) :
    Function.Surjective (glueLift G H f g h) := by
  intro x
  rcases hcover x with ⟨v,hv⟩ | ⟨w,hw⟩
  · exact ⟨inLeft G H v,hv⟩
  · exact ⟨inRight G H w,hw⟩

/-- Gluing finite graphs remains finite, without assuming any identity object. -/
instance gluedFinite (G : Graph k V) (H : Graph k W) [Finite V] [Finite W] :
    Finite (Glued G H) := inferInstanceAs (Finite (Quotient (glueSetoid G H)))

/-- Edges are the images of original edges. This existential presentation
removes parallel duplicates automatically and never creates a loop. -/
def gluedAdj (G : Graph k V) (H : Graph k W) (a b : Glued G H) : Prop :=
  (∃ x y, G.Adj x y ∧ inLeft G H x = a ∧ inLeft G H y = b) ∨
  (∃ x y, H.Adj x y ∧ inRight G H x = a ∧ inRight G H y = b)

noncomputable def glue (G : Graph k V) (H : Graph k W) : Graph k (Glued G H) where
  Adj := gluedAdj G H
  symm := by
    rintro a b (⟨x,y,hxy,hx,hy⟩ | ⟨x,y,hxy,hx,hy⟩)
    · exact Or.inl ⟨y,x,G.symm hxy,hy,hx⟩
    · exact Or.inr ⟨y,x,H.symm hxy,hy,hx⟩
  loopless := by
    rintro a (⟨x,y,hxy,hx,hy⟩ | ⟨x,y,hxy,hx,hy⟩)
    · have he := inLeft_injective G H (hx.trans hy.symm)
      subst y
      exact G.loopless x hxy
    · have he := inRight_injective G H (hx.trans hy.symm)
      subst y
      exact H.loopless x hxy
  left := fun i => (G.left i).map (inLeft G H)
  right := fun i => (H.right i).map (inRight G H)
  left_inj := by
    intro i j a hi hj
    obtain ⟨x, hx, hxa⟩ := Option.map_eq_some_iff.mp hi
    obtain ⟨y, hy, hya⟩ := Option.map_eq_some_iff.mp hj
    have he := inLeft_injective G H (hxa.trans hya.symm)
    subst y
    exact G.left_inj i j x hx hy
  right_inj := by
    intro i j a hi hj
    obtain ⟨x, hx, hxa⟩ := Option.map_eq_some_iff.mp hi
    obtain ⟨y, hy, hya⟩ := Option.map_eq_some_iff.mp hj
    have he := inRight_injective G H (hxa.trans hya.symm)
    subst y
    exact H.right_inj i j x hx hy
  cross := by
    intro i j a hi hj
    obtain ⟨x, hx, hxa⟩ := Option.map_eq_some_iff.mp hi
    obtain ⟨y, hy, hya⟩ := Option.map_eq_some_iff.mp hj
    obtain ⟨m, hm, hn⟩ := (inLeft_eq_inRight G H x y).mp (hxa.trans hya.symm)
    exact (G.cross i m x hx hm).trans (H.cross m j y hn hy)

end StackSorting.BiInterface
