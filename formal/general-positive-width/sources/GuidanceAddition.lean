import GuidanceComponents

namespace StackSorting.GuidedPathwidth
universe u
variable {V : Type u} {G : SimpleGraph V} {P : Set V} {c : Nat}
namespace System

noncomputable def addRoot (C : System G P c) (u : V) : System G P (c+1) :=
  append C (fun _ : Fin 1 => componentColor P u)

/-- One new spanning component guide captures the added vertex simultaneously
for every bag lying in a single component. Existing guides are unchanged. -/
theorem addRoot_captures (C : System G P c) (u : V) {B : Set V}
    (hconn : ∀ r ∈ B, ∀ s ∈ B, ReachIn G P r s)
    (hc : Captures G C (B \ {u})) : Captures G (C.addRoot u) B := by
  classical
  intro hne
  by_cases hminus : (B \ {u}).Nonempty
  · obtain ⟨b,hb⟩ := hminus
    obtain ⟨x,hx⟩ := hc ⟨b,hb⟩
    refine ⟨x,?_⟩
    intro r hr
    by_cases hru : r = u
    · subst r
      obtain ⟨i,hi⟩ := hx b hb
      have hxb : ReachIn G P x b := ((C i).reaches b x hi).mono ((C i).inside b)
      refine ⟨finSumFinEquiv (.inr (0 : Fin 1)),?_⟩
      simpa only [addRoot,append_right,componentColor_self,component,Set.mem_ofPred_eq] using
        hxb.trans (hconn b hb.1 u hr)
    · obtain ⟨i,hi⟩ := hx r ⟨hr,hru⟩
      exact ⟨finSumFinEquiv (.inl i),by simpa only [addRoot,append_left] using hi⟩
  · obtain ⟨b,hb⟩ := hne
    have heq : ∀ r ∈ B, r = u := by
      intro r hr
      by_contra hru
      exact hminus ⟨r,hr,hru⟩
    have hu : u ∈ B := heq b hb ▸ hb
    refine ⟨u,?_⟩
    intro r hr
    have hr' := heq r hr
    subst r
    refine ⟨finSumFinEquiv (.inr (0 : Fin 1)),?_⟩
    simpa only [addRoot,append_right,componentColor_self,component,Set.mem_ofPred_eq] using hconn u hu u hu

/-- Restoring a deleted vertex first embeds all old trees without changing
any edge, support or root, then adds the one new component tree. -/
noncomputable def restoreVertex (u : V) (C : System G (P \ {u}) c) : System G P (c+1) :=
  addRoot (fun i => (C i).enlarge Set.sdiff_subset) u
end System

#print axioms System.addRoot_captures
end StackSorting.GuidedPathwidth
