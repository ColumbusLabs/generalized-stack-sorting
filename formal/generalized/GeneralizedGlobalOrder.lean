import GeneralizedLazy

/-!
A single global token order for an exact executable generalized-stack history.
This module uses the established literal `RawOp`, `step`, and `run` definitions.
The proof works backward through the exact operation sequence. It does not use
interval graphs, and does not yet extract interval endpoints or prove peeling.
-/
namespace StackSorting.Generalized
open List

/-- Every actual intermediate stack of this exact executable operation sequence
is a sublist of `order`. Initial and final stacks are both included. -/
def OrderFits (order : List Nat) (r s : Nat) : List RawOp → List Nat → Prop
  | [], held => held <+ order
  | op :: ops, held => held <+ order ∧
      ∃ middle emitted, step r s op held = some (middle, emitted) ∧
        OrderFits order r s ops middle

theorem OrderFits.initial {order held : List Nat} {r s : Nat} {ops : List RawOp}
    (h : OrderFits order r s ops held) : held <+ order := by
  cases ops with
  | nil => exact h
  | cons _ _ => exact h.1

/-- Extending a master order preserves all already-ordered physical stacks. -/
theorem OrderFits.mono {order larger held : List Nat} {r s : Nat} {ops : List RawOp}
    (h : OrderFits order r s ops held) (hs : order <+ larger) :
    OrderFits larger r s ops held := by
  induction ops generalizing held with
  | nil => exact h.trans hs
  | cons op ops ih =>
    obtain ⟨middle, emitted, hstep, htail⟩ := h.2
    exact ⟨h.1.trans hs, middle, emitted, hstep, ih htail⟩

/-- Executing any prefix of the exact raw sequence reaches the suffix state
certified by `OrderFits`; determinism prevents choosing a different history. -/
theorem OrderFits.after_prefix {order held middle emitted : List Nat} {r s : Nat}
    {preOps suffix : List RawOp}
    (h : OrderFits order r s (preOps ++ suffix) held)
    (hp : run r s preOps held = some (middle, emitted)) :
    OrderFits order r s suffix middle := by
  induction preOps generalizing held emitted with
  | nil =>
    simp only [run, Option.some.injEq, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩
    exact h
  | cons op preOps ih =>
    obtain ⟨next, out, hs, ht⟩ := h.2
    obtain ⟨next', out', tail, hs', hr, _⟩ := split_run r s op preOps held middle emitted hp
    have heq : next = next' ∧ out = out' := by
      simpa only [Option.some.injEq, Prod.mk.injEq] using hs.symm.trans hs'
    rcases heq with ⟨rfl, rfl⟩
    exact ih ht hr

/-- A single physical step extends a master order for its successor stack to
one for its predecessor stack, without changing the relative order of any
already-present token. The master list contains exactly the step's total supply
plus an arbitrary remaining input list. -/
theorem Step.extend_global_order {r s : Nat}
    {held input output middle rest order : List Nat}
    (h : Step r s held input output middle)
    (hp : order.Perm (middle ++ rest)) (hm : middle <+ order) :
    ∃ larger, larger.Perm (held ++ input ++ rest) ∧
      held <+ larger ∧ order <+ larger := by
  cases h with
  | push pre post x allowed =>
    have hsupply := (Step.push (s := s) pre post x allowed).supply.append_right rest
    have hp' : order.Perm ((pre ++ post) ++ [x] ++ rest) := by
      exact hp.trans (by simpa using hsupply.symm)
    have hsub : pre ++ post <+ pre ++ x :: post :=
      (List.Sublist.refl pre).append ((List.Sublist.refl post).cons x)
    exact ⟨order, hp', hsub.trans hm, List.Sublist.refl order⟩
  | pop pre post x allowed =>
    obtain ⟨left, right, hsplit, hpre, hpost⟩ := List.append_sublist_iff.mp hm
    let larger := left ++ x :: right
    have hperm : larger.Perm (x :: order) := by
      simp [larger, hsplit, List.perm_middle]
    have hsupply := (Step.pop (r := r) pre post x allowed).supply.append_right rest
    have hperm' : larger.Perm ((pre ++ x :: post) ++ [] ++ rest) := by
      apply hperm.trans
      apply (List.Perm.cons x hp).trans
      simpa [List.append_assoc] using hsupply.symm
    have hheld : pre ++ x :: post <+ larger :=
      hpre.append (hpost.cons_cons x)
    have horder : order <+ larger := by
      rw [hsplit]
      exact (List.Sublist.refl left).append ((List.Sublist.refl right).cons x)
    exact ⟨larger, hperm', hheld, horder⟩

/-- Every successful exact raw-op history has a master list of exactly its
initial and introduced tokens, preserving every intermediate physical stack.
No uniqueness hypothesis is required for this list-supersequence statement. -/
theorem run_has_global_order {r s : Nat} {ops : List RawOp}
    {held final output : List Nat}
    (h : run r s ops held = some (final, output)) :
    ∃ order, order.Perm (held ++ inputs ops) ∧ OrderFits order r s ops held := by
  induction ops generalizing held final output with
  | nil =>
    exact ⟨held, by simp [inputs], List.Sublist.refl held⟩
  | cons op ops ih =>
    obtain ⟨middle, emitted, tail, hs, ht, _⟩ := split_run r s op ops held final output h
    obtain ⟨order, hp, hf⟩ := ih ht
    obtain ⟨larger, hperm, hheld, horder⟩ :=
      (step_relational r s op held middle emitted hs).extend_global_order hp hf.initial
    refine ⟨larger, ?_, hheld, middle, emitted, hs, hf.mono horder⟩
    simpa [inputs, List.append_assoc] using hperm

/-- With distinct token supply, the master list is a duplicate-free global
physical order on exactly those tokens, for the same raw operations and slots. -/
theorem run_has_distinct_global_order {r s : Nat} {ops : List RawOp}
    {held final output : List Nat}
    (h : run r s ops held = some (final, output))
    (hd : (held ++ inputs ops).Nodup) :
    ∃ order, order.Nodup ∧ order.Perm (held ++ inputs ops) ∧
      OrderFits order r s ops held := by
  obtain ⟨order, hp, hf⟩ := run_has_global_order h
  exact ⟨order, hp.nodup_iff.mpr hd, hp, hf⟩

/-- Public history-to-order bridge stated entirely in terms of the existing
executable machine: every physical stack reached by every prefix of this exact
successful history is a sublist of one duplicate-free order on its token supply. -/
theorem run_global_order_all_prefixes {r s : Nat} {ops : List RawOp}
    {held final output : List Nat}
    (h : run r s ops held = some (final, output))
    (hd : (held ++ inputs ops).Nodup) :
    ∃ order, order.Nodup ∧ order.Perm (held ++ inputs ops) ∧
      ∀ preOps suffix, ops = preOps ++ suffix →
        ∀ middle emitted, run r s preOps held = some (middle, emitted) →
          middle <+ order := by
  obtain ⟨order, hn, hp, hf⟩ := run_has_distinct_global_order h hd
  refine ⟨order, hn, hp, ?_⟩
  intro preOps suffix heq middle emitted hr
  rw [heq] at hf
  exact (hf.after_prefix hr).initial

#print axioms Step.extend_global_order
#print axioms run_has_global_order
#print axioms run_has_distinct_global_order
#print axioms run_global_order_all_prefixes
end StackSorting.Generalized
