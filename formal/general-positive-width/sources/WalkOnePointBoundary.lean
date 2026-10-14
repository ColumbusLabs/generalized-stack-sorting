import DecompositionRestriction

namespace StackSorting.GuidedPathwidth
universe u
variable {V : Type u} {G : SimpleGraph V}

/-- A finite walk to the unique possible exit can be stopped on its first
visit there. No interior vertex ever needs to leave the specified region. -/
theorem reachIn_of_onePointBoundary {S : Set V} {r x : V}
    (hx : x ∈ S) (hr : r ∈ S)
    (hclosed : ∀ {a b}, a ∈ S → a ≠ r → G.Adj a b → b ∈ S)
    (h : G.Reachable x r) : ReachIn G S x r := by
  obtain ⟨p⟩ := h
  suffices ∀ {a b : V} (q : G.Walk a b), b = r → a ∈ S → ReachIn G S a r by
    exact this p rfl hx
  intro a b q
  induction q with
  | @nil a =>
    intro he ha
    subst a
    exact ReachIn.refl hr
  | @cons a b z hab q ih =>
    intro he ha
    by_cases har : a = r
    · subst a
      exact ReachIn.refl hr
    · have hb := hclosed ha har hab
      have hbr := ih he hb
      exact ⟨ha,hr,.join (.edge hab) hb hbr.2.2⟩
end StackSorting.GuidedPathwidth
