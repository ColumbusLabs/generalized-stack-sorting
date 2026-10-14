import IntervalCritical
import GeneralizedRelational

/-! Endpoint peeling, a feasible global order, and exact literal endpoint steps.
This module does not concatenate the steps into a history or extract endpoints
from a history. Those are separate remaining bridges. -/
namespace StackSorting.IntervalCritical
open List

/-- Read a top-first order from left to right. Its `above` prefix gives the
physical depth at both endpoints of the next token. -/
def FeasibleAbove (e : Endpoints) (r s : Nat) (above : Tokens) : Tokens → Prop
  | [] => True
  | v :: below => Eligible e r s above v ∧ FeasibleAbove e r s (above ++ [v]) below

def FeasibleEndpointOrder (e : Endpoints) (r s : Nat) (order : Tokens) : Prop :=
  FeasibleAbove e r s [] order

theorem feasibleAbove_append (e : Endpoints) (r s : Nat) (above xs ys : Tokens) :
    FeasibleAbove e r s above (xs ++ ys) ↔
      FeasibleAbove e r s above xs ∧ FeasibleAbove e r s (above ++ xs) ys := by
  induction xs generalizing above with
  | nil => simp [FeasibleAbove]
  | cons v xs ih => simp [FeasibleAbove, ih, List.append_assoc, and_assoc]

theorem feasibleOrder_snoc (e : Endpoints) (r s : Nat) (order : Tokens) (v : Nat) :
    FeasibleEndpointOrder e r s (order ++ [v]) ↔
      FeasibleEndpointOrder e r s order ∧ Eligible e r s order v := by
  simp [FeasibleEndpointOrder, feasibleAbove_append, FeasibleAbove]

/-- The recursive predicate is exactly the pair of slot bounds at every prefix. -/
theorem feasibleOrder_iff_prefixes (e : Endpoints) (r s : Nat) (order : Tokens) :
    FeasibleEndpointOrder e r s order ↔
      ∀ above v below, order = above ++ v :: below → Eligible e r s above v := by
  have aux : ∀ xs above, FeasibleAbove e r s above xs ↔
      ∀ pre v post, xs = pre ++ v :: post → Eligible e r s (above ++ pre) v := by
    intro xs
    induction xs with
    | nil => intro above; simp [FeasibleAbove]
    | cons x xs ih =>
      intro above
      rw [FeasibleAbove, ih]
      constructor
      · rintro ⟨hx, ht⟩ pre v post heq
        cases pre with
        | nil => simp at heq; rcases heq with ⟨rfl, rfl⟩; simpa using hx
        | cons y pre =>
          simp only [List.cons_append, List.cons.injEq] at heq
          rcases heq with ⟨rfl, heq⟩
          simpa [List.append_assoc] using ht pre v post heq
      · intro h
        refine ⟨?_, ?_⟩
        · simpa using h [] x xs rfl
        · intro pre v post heq
          simpa [List.append_assoc] using h (x :: pre) v post (by simp [heq])
  simpa [FeasibleEndpointOrder] using aux order []

theorem Eligible.perm {e : Endpoints} {r s v : Nat} {U V : Tokens}
    (h : Eligible e r s U v) (hp : U.Perm V) : Eligible e r s V v := by
  unfold Eligible endpointCount at *
  simpa only [hp.countP_eq] using h

theorem Peelable.perm {e : Endpoints} {r s : Nat} {U V : Tokens}
    (h : Peelable e r s U) (hp : U.Perm V) : Peelable e r s V := by
  induction h generalizing V with
  | nil => have hv : V = [] := List.perm_nil.mp hp.symm; subst V; exact .nil
  | step v hv he _ ih =>
    exact .step v (hp.mem_iff.mp hv) (he.perm hp) (ih (hp.erase v))

theorem eligible_snoc_self (e : Endpoints) (r s : Nat) (U : Tokens) (v : Nat) :
    Eligible e r s (U ++ [v]) v ↔ Eligible e r s U v := by
  simp [Eligible, endpointCount, List.countP_append, Covers]

/-- Successful peeling constructs a feasible top-first order by restoring each
peeled token at the bottom. -/
theorem Peelable.feasible_order {e : Endpoints} {r s : Nat} {U : Tokens}
    (h : Peelable e r s U) (hn : U.Nodup) :
    ∃ order, order.Perm U ∧ FeasibleEndpointOrder e r s order := by
  revert hn
  induction h with
  | nil => intro _; exact ⟨[], .refl [], trivial⟩
  | @step U v hv he hrest ih =>
    intro hn
    obtain ⟨order, hp, hf⟩ := ih (List.Nodup.erase v hn)
    have he' : Eligible e r s (U.erase v) v := by
      unfold Eligible at *
      rw [endpointCount_erase_of_not_covered hn (own_left_not_covered e v),
        endpointCount_erase_of_not_covered hn (own_right_not_covered e v)]
      exact he
    have ho : Eligible e r s order v := he'.perm hp.symm
    refine ⟨order ++ [v], ?_, (feasibleOrder_snoc e r s order v).mpr ⟨hf, ho⟩⟩
    have hrotate : (order ++ [v]).Perm (v :: order) := by
      simp
    exact hrotate.trans ((List.Perm.cons v hp).trans (List.perm_cons_erase hv).symm)

/-- A feasible top-first order peels by deleting bottom tokens. -/
theorem feasible_order_peelable {e : Endpoints} {r s : Nat} {order : Tokens}
    (hn : order.Nodup) (hf : FeasibleEndpointOrder e r s order) :
    Peelable e r s order := by
  have aux : ∀ rev : Tokens, rev.reverse.Nodup →
      FeasibleEndpointOrder e r s rev.reverse → Peelable e r s rev.reverse := by
    intro rev
    induction rev with
    | nil => intro _ _; exact .nil
    | cons v rev ih =>
      intro hn hf
      simp only [List.reverse_cons] at hn hf ⊢
      have hn' := List.nodup_append.mp hn
      have hv : v ∉ rev.reverse := by
        intro hm
        exact hn'.2.2 v hm v (by simp) rfl
      obtain ⟨hf', he⟩ := (feasibleOrder_snoc e r s rev.reverse v).mp hf
      have ht := ih hn'.1 hf'
      apply Peelable.step v (by simp) ((eligible_snoc_self e r s rev.reverse v).mpr he)
      simpa [List.erase_append_right _ hv] using ht
  simpa using aux order.reverse (by simpa using hn) (by simpa using hf)

/-- Exact finite recognition by feasible global endpoint order. This theorem is
an equivalence about intervals, not yet an equivalence with complete histories. -/
theorem peelable_iff_feasible_endpoint_order {e : Endpoints} {r s : Nat} {U : Tokens}
    (hn : U.Nodup) :
    Peelable e r s U ↔
      ∃ order, order.Perm U ∧ FeasibleEndpointOrder e r s order := by
  constructor
  · exact fun h => h.feasible_order hn
  · rintro ⟨order, hp, hf⟩
    exact (feasible_order_peelable (hp.nodup_iff.mpr hn) hf).perm hp

/-- Reordering the finite token list preserves its exact endpoint hypotheses. -/
theorem WellFormed.perm {e : Endpoints} {U V : Tokens}
    (wf : WellFormed e U) (hp : U.Perm V) : WellFormed e V := by
  have hm : ∀ v ∈ V, v ∈ U := fun _ hv => hp.mem_iff.mpr hv
  exact ⟨hp.nodup_iff.mp wf.nodup,
    fun v hv => wf.proper v (hm v hv),
    fun u hu v hv => wf.left_unique u (hm u hu) v (hm v hv),
    fun u hu v hv => wf.right_unique u (hm u hu) v (hm v hv),
    fun u hu v hv => wf.cross_distinct u (hm u hu) v (hm v hv)⟩

/-- The order supplied by successful peeling satisfies exactly the endpoint
hypotheses needed by the literal-event bridge below. -/
theorem Peelable.wellFormed_feasible_order {e : Endpoints} {r s : Nat} {U : Tokens}
    (h : Peelable e r s U) (wf : WellFormed e U) :
    ∃ order, order.Perm U ∧ WellFormed e order ∧ FeasibleEndpointOrder e r s order := by
  obtain ⟨order, hp, hf⟩ := h.feasible_order wf.nodup
  exact ⟨order, hp, wf.perm hp.symm, hf⟩

/-- Physical stack immediately before event time `t`. -/
def beforeStack (e : Endpoints) (order : Tokens) (t : Nat) : Tokens :=
  order.filter (fun u => decide (e.left u < t ∧ t ≤ e.right u))

/-- Physical stack immediately after event time `t`, including a just-inserted
record with consecutive endpoints. -/
def afterStack (e : Endpoints) (order : Tokens) (t : Nat) : Tokens :=
  order.filter (fun u => decide (e.left u ≤ t ∧ t < e.right u))

def coveringList (e : Endpoints) (order : Tokens) (t : Nat) : Tokens :=
  order.filter (fun u => decide (Covers e u t))

theorem beforeStack_eq_covering {e : Endpoints} {W : Tokens} {t : Nat}
    (h : ∀ u ∈ W, t ≠ e.right u) :
    beforeStack e W t = coveringList e W t := by
  apply List.filter_congr
  intro u hu
  have hh := h u hu
  have heq : (e.left u < t ∧ t ≤ e.right u) ↔ Covers e u t := by
    unfold Covers
    omega
  simp only [heq]

theorem afterStack_eq_covering {e : Endpoints} {W : Tokens} {t : Nat}
    (h : ∀ u ∈ W, e.left u ≠ t) :
    afterStack e W t = coveringList e W t := by
  apply List.filter_congr
  intro u hu
  have hh := h u hu
  have heq : (e.left u ≤ t ∧ t < e.right u) ↔ Covers e u t := by
    unfold Covers
    omega
  simp only [heq]

/-- Distinct endpoints ensure that at an insertion/removal event exactly the
endpoint owner changes membership in the globally ordered physical stack. -/
theorem endpoint_stack_splits {e : Endpoints} {order above below : Tokens} {v : Nat}
    (wf : WellFormed e order) (split : order = above ++ v :: below) :
    beforeStack e order (e.left v) =
        coveringList e above (e.left v) ++ coveringList e below (e.left v) ∧
    afterStack e order (e.left v) =
        coveringList e above (e.left v) ++ v :: coveringList e below (e.left v) ∧
    beforeStack e order (e.right v) =
        coveringList e above (e.right v) ++ v :: coveringList e below (e.right v) ∧
    afterStack e order (e.right v) =
        coveringList e above (e.right v) ++ coveringList e below (e.right v) := by
  have hv : v ∈ order := by simp [split]
  have ha : above ⊆ order := by intro u hu; simp [split, hu]
  have hb : below ⊆ order := by intro u hu; simp [split, hu]
  have hn := List.nodup_append.mp (show (above ++ v :: below).Nodup by rw [← split]; exact wf.nodup)
  have hva : v ∉ above := by
    intro hu
    exact hn.2.2 v hu v (by simp) rfl
  have hvb : v ∉ below := (List.nodup_cons.mp hn.2.1).1
  have hproper := wf.proper v hv
  have hleft {W : Tokens} (hW : W ⊆ order) (hnot : v ∉ W) :
      ∀ u ∈ W, e.left u ≠ e.left v := by
    intro u hu heq
    have he := wf.left_unique u (hW hu) v hv heq
    exact hnot (he ▸ hu)
  have hright {W : Tokens} (hW : W ⊆ order) (hnot : v ∉ W) :
      ∀ u ∈ W, e.right v ≠ e.right u := by
    intro u hu heq
    have he := wf.right_unique v hv u (hW hu) heq
    exact hnot (he.symm ▸ hu)
  have hbeforeLeft : beforeStack e order (e.left v) = coveringList e order (e.left v) :=
    beforeStack_eq_covering (fun u hu => wf.cross_distinct v hv u hu)
  have hafterRight : afterStack e order (e.right v) = coveringList e order (e.right v) :=
    afterStack_eq_covering (fun u hu => wf.cross_distinct u hu v hv)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hbeforeLeft]
    simp [coveringList, split, List.filter_append, Covers]
  · calc
      afterStack e order (e.left v) =
          afterStack e above (e.left v) ++ v :: afterStack e below (e.left v) := by
        simp [afterStack, split, List.filter_append, hproper]
      _ = _ := by rw [afterStack_eq_covering (hleft ha hva), afterStack_eq_covering (hleft hb hvb)]
  · calc
      beforeStack e order (e.right v) =
          beforeStack e above (e.right v) ++ v :: beforeStack e below (e.right v) := by
        simp [beforeStack, split, List.filter_append, hproper]
      _ = _ := by rw [beforeStack_eq_covering (hright ha hva), beforeStack_eq_covering (hright hb hvb)]
  · rw [hafterRight]
    simp [coveringList, split, List.filter_append, Covers]

/-- A feasible endpoint order gives the actual literal push/pop at each event,
using exactly the strict covering-prefix count as its zero-based slot index.
This is a statement about the existing executable `Generalized.step`. -/
theorem feasible_endpoint_raw_steps {e : Endpoints} {r s v : Nat}
    {order above below : Tokens} (wf : WellFormed e order)
    (hf : FeasibleEndpointOrder e r s order) (split : order = above ++ v :: below) :
    Generalized.step r s (.push (endpointCount e above (e.left v)) v)
        (beforeStack e order (e.left v)) = some (afterStack e order (e.left v), []) ∧
    Generalized.step r s (.pop (endpointCount e above (e.right v)))
        (beforeStack e order (e.right v)) = some (afterStack e order (e.right v), [v]) := by
  have he := (feasibleOrder_iff_prefixes e r s order).mp hf above v below split
  obtain ⟨hbl, hal, hbr, har⟩ := endpoint_stack_splits wf split
  have hl : endpointCount e above (e.left v) = (coveringList e above (e.left v)).length :=
    List.countP_eq_length_filter
  have hr : endpointCount e above (e.right v) = (coveringList e above (e.right v)).length :=
    List.countP_eq_length_filter
  have hpush := Generalized.insertAt_prefix
    (coveringList e above (e.left v)) (coveringList e below (e.left v)) v
  have hpop := Generalized.removeAt_prefix
    (coveringList e above (e.right v)) (coveringList e below (e.right v)) v
  have hallowL : (coveringList e above (e.left v)).length < r := by rw [← hl]; exact he.1
  have hallowR : (coveringList e above (e.right v)).length < s := by rw [← hr]; exact he.2
  constructor
  · simp [Generalized.step, hbl, hal, hl, hpush, hallowL]
  · simp [Generalized.step, hbr, har, hr, hpop, hallowR]

/-- The same concrete event bridge in the established relational `Step` API. -/
theorem feasible_endpoint_steps {e : Endpoints} {r s v : Nat}
    {order above below : Tokens} (wf : WellFormed e order)
    (hf : FeasibleEndpointOrder e r s order) (split : order = above ++ v :: below) :
    Generalized.Step r s (beforeStack e order (e.left v)) [v] []
        (afterStack e order (e.left v)) ∧
    Generalized.Step r s (beforeStack e order (e.right v)) [] [v]
        (afterStack e order (e.right v)) := by
  obtain ⟨hi, ho⟩ := feasible_endpoint_raw_steps wf hf split
  exact ⟨Generalized.step_relational r s _ _ _ _ hi,
    Generalized.step_relational r s _ _ _ _ ho⟩

#print axioms feasibleOrder_iff_prefixes
#print axioms peelable_iff_feasible_endpoint_order
#print axioms Peelable.wellFormed_feasible_order
#print axioms endpoint_stack_splits
#print axioms feasible_endpoint_raw_steps
#print axioms feasible_endpoint_steps
end StackSorting.IntervalCritical
