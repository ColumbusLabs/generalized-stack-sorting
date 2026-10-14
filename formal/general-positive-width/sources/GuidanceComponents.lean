import GuidanceRegions

namespace StackSorting.GuidedPathwidth
attribute [local instance] Classical.propDecidable
open BiInterface
universe u
variable {V : Type u} {G : SimpleGraph V}

/-- The actual reachable component inside a named allowed set. -/
def component (G : SimpleGraph V) (P : Set V) (r : V) : Set V :=
  {x | ReachIn G P x r}

theorem component_subset (P : Set V) (r : V) : component G P r ⊆ P :=
  fun _ h => h.1

private theorem through_component {P : Set V} {x y : V}
    (h : Through G.Adj P x y) {r : V} (hy : ReachIn G P y r) :
    Through G.Adj (component G P r) x y := by
  revert hy
  induction h with
  | refl x => intro hy; exact .refl x
  | edge h => intro hy; exact .edge h
  | @join x y z hxy hym hyz ihxy ihyz =>
    intro hy
    have hyr : ReachIn G P y r := ⟨hym,hy.2.1,.join hyz hy.1 hy.2.2⟩
    exact .join (ihxy hyr) hyr (ihyz hy)

theorem reachIn_component {P : Set V} {x r : V} (h : ReachIn G P x r) :
    ReachIn G (component G P r) x r :=
  ⟨h,ReachIn.refl h.2.1,through_component h.2.2 (ReachIn.refl h.2.1)⟩

/-- One concrete connected guide, rooted at r. It is empty if r is absent. -/
noncomputable def componentColor (P : Set V) (r : V) : Color G P where
  support := fun s => if s = r then component G P r else ∅
  inside := by
    intro s x hx
    split_ifs at hx with hs
    · exact hx.1
    · exact hx.elim
  reaches := by
    intro s x hx
    split_ifs at hx ⊢ with hs
    · subst s
      exact reachIn_component hx
    · exact hx.elim
  unique := by
    intro s t x hs ht
    have hsr : s = r := by by_contra h; simp [h] at hs
    have htr : t = r := by by_contra h; simp [h] at ht
    exact hsr.trans htr.symm

@[simp] theorem componentColor_self (P : Set V) (r : V) :
    (componentColor (G := G) P r).support r = component G P r := by
  simp [componentColor]

namespace System
variable {P : Set V} {c d : Nat}
noncomputable def append (C : System G P c) (D : System G P d) : System G P (c+d) :=
  fun i => Sum.elim C D (finSumFinEquiv.symm i)

@[simp] theorem append_left (C : System G P c) (D : System G P d) (i : Fin c) :
    append C D (finSumFinEquiv (.inl i)) = C i := by simp [append]
@[simp] theorem append_right (C : System G P c) (D : System G P d) (i : Fin d) :
    append C D (finSumFinEquiv (.inr i)) = D i := by simp [append]

theorem captures_append_left (C : System G P c) (D : System G P d)
    {B : Set V} (h : Captures G C B) : Captures G (append C D) B := by
  intro hb
  obtain ⟨x,hx⟩ := h hb
  refine ⟨x,?_⟩
  intro r hr
  obtain ⟨i,hi⟩ := hx r hr
  exact ⟨finSumFinEquiv (.inl i),by simpa only [append_left] using hi⟩
end System

end StackSorting.GuidedPathwidth
