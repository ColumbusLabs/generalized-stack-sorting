import GuidanceComponents

namespace StackSorting.GuidedPathwidth
attribute [local instance] Classical.propDecidable
open BiInterface
universe u
variable {V : Type u} {G : SimpleGraph V} {P : Set V}
namespace Color

/-- Keep precisely the old guides which avoid the deleted vertex. -/
noncomputable def avoiding (C : Color G P) (u : V) : Color G (P \ {u}) where
  support := fun r => if u ∈ C.support r then ∅ else C.support r
  inside := by
    intro r x hx
    split_ifs at hx with hu
    · exact hx.elim
    · refine ⟨C.inside r hx,?_⟩
      intro he
      exact hu (he ▸ hx)
  reaches := by
    intro r x hx
    split_ifs at hx ⊢ with hu
    · exact hx.elim
    · exact C.reaches r x hx
  unique := by
    intro r s x hr hs
    have hr' : x ∈ C.support r := by
      by_cases h : u ∈ C.support r
      · simp [h] at hr
      · simpa [h] using hr
    have hs' : x ∈ C.support s := by
      by_cases h : u ∈ C.support s
      · simp [h] at hs
      · simpa [h] using hs
    exact C.unique r s x hr' hs'

/-- In one color at most one old guide contains u. Replace that guide by the
entire surviving component of its root. This adds only one palette copy. -/
noncomputable def repairing (C : Color G P) (u : V) : Color G (P \ {u}) where
  support := fun r => if u ∈ C.support r ∧ r ≠ u then component G (P \ {u}) r else ∅
  inside := by
    intro r x hx
    split_ifs at hx
    · exact hx.1
    · exact hx.elim
  reaches := by
    intro r x hx
    split_ifs at hx ⊢
    · exact reachIn_component hx
    · exact hx.elim
  unique := by
    intro r s x hr hs
    have hr' : u ∈ C.support r := by
      by_cases h : u ∈ C.support r ∧ r ≠ u
      · exact h.1
      · simp [h] at hr
    have hs' : u ∈ C.support s := by
      by_cases h : u ∈ C.support s ∧ s ≠ u
      · exact h.1
      · simp [h] at hs
    exact C.unique r s u hr' hs'

@[simp] theorem avoiding_of_not_mem (C : Color G P) (u r : V)
    (h : u ∉ C.support r) : (C.avoiding u).support r = C.support r := by
  simp [avoiding,h]
@[simp] theorem repairing_of_mem (C : Color G P) (u r : V)
    (h : u ∈ C.support r) (hne : r ≠ u) :
    (C.repairing u).support r = component G (P \ {u}) r := by
  simp [repairing,h,hne]
end Color

namespace System
variable {c : Nat}
noncomputable def deleteVertex (C : System G P c) (u : V) : System G (P \ {u}) (c+c) :=
  append (fun i => (C i).avoiding u) (fun i => (C i).repairing u)

/-- Constructive deletion estimate. The bag must stay inside one surviving
component, as in B–P Lemma 3.5; no guidance witness after deletion is assumed. -/
theorem deleteVertex_captures (C : System G P c) (u : V) {B : Set V}
    (hB : B ⊆ P \ {u})
    (hconn : ∀ r ∈ B, ∀ s ∈ B, ReachIn G (P \ {u}) r s)
    (hc : Captures G C B) : Captures G (C.deleteVertex u) B := by
  intro hne
  obtain ⟨b,hb⟩ := hne
  obtain ⟨x,hx⟩ := hc ⟨b,hb⟩
  by_cases hxb : ReachIn G (P \ {u}) x b
  · refine ⟨x,?_⟩
    intro r hr
    obtain ⟨i,hi⟩ := hx r hr
    by_cases hu : u ∈ (C i).support r
    · refine ⟨finSumFinEquiv (.inr i),?_⟩
      simpa only [deleteVertex,append_right,Color.repairing_of_mem _ _ _ hu (hB hr).2,component,Set.mem_ofPred_eq]
        using hxb.trans (hconn b hb r hr)
    · refine ⟨finSumFinEquiv (.inl i),?_⟩
      simpa only [deleteVertex,append_left,Color.avoiding_of_not_mem _ _ _ hu] using hi
  · refine ⟨b,?_⟩
    intro r hr
    obtain ⟨i,hi⟩ := hx r hr
    have hu : u ∈ (C i).support r := by
      by_contra hu
      have hs : (C i).support r ⊆ P \ {u} := by
        intro z hz
        refine ⟨(C i).inside r hz,?_⟩
        intro he
        exact hu (he ▸ hz)
      exact hxb (((C i).reaches r x hi).mono hs |>.trans (hconn r hr b hb))
    refine ⟨finSumFinEquiv (.inr i),?_⟩
    simpa only [deleteVertex,append_right,
      Color.repairing_of_mem _ _ _ hu (hB hr).2,component,Set.mem_ofPred_eq] using hconn b hb r hr
end System

#print axioms System.deleteVertex_captures
end StackSorting.GuidedPathwidth
