import GeneralizedDeletion

/-!
# Exact interval description of no-pop top-two push orders

Ranks here are zero-based. `IntervalOrder` is an explicit interval-partition
language; `PushOrder` is the actual sequential top-two insertion language.
Their equivalence is proved below, together with legal generalized histories.
This is the one-block foundation, not yet the restricted-pop image theorem.
-/
namespace StackSorting.Generalized

/-- No-pop insertion of successive maxima 0,...,n-1 in the first two slots. -/
inductive PushOrder : Nat → List Nat → Prop where
  | nil : PushOrder 0 []
  | top {n : Nat} {xs : List Nat} (h : PushOrder n xs) :
      PushOrder (n+1) (n :: xs)
  | second {n x : Nat} {xs : List Nat} (h : PushOrder n (x :: xs)) :
      PushOrder (n+1) (x :: n :: xs)

/-- Consecutive intervals, highest first; the highest interval starts with its
minimum `lo`, then has a descending tail `lo+t,...,lo+1`. -/
inductive IntervalOrder : Nat → List Nat → Prop where
  | nil : IntervalOrder 0 []
  | block (lo t : Nat) (xs : List Nat) (lower : IntervalOrder lo xs) :
      IntervalOrder (lo+t+1) ((lo :: (List.range' (lo+1) t).reverse) ++ xs)

theorem interval_tail_succ (lo t : Nat) :
    (List.range' (lo+1) (t+1)).reverse =
      (lo+t+1) :: (List.range' (lo+1) t).reverse := by
  rw [List.range'_concat, List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
  congr 1 <;> omega

theorem IntervalOrder.length {n : Nat} {xs : List Nat} (h : IntervalOrder n xs) :
    xs.length = n := by
  induction h with
  | nil => rfl
  | block lo t xs lower ih => simp [ih]; omega

theorem PushOrder.length {n : Nat} {xs : List Nat} (h : PushOrder n xs) :
    xs.length = n := by
  induction h with
  | nil => rfl
  | top h ih => simp [ih]
  | second h ih => simp_all

theorem PushOrder.interval {n : Nat} {xs : List Nat} (h : PushOrder n xs) :
    IntervalOrder n xs := by
  induction h with
  | nil => exact .nil
  | @top n xs h ih =>
      simpa using IntervalOrder.block n 0 xs ih
  | @second n x xs h ih =>
      cases ih with
      | block lo t lower ih =>
          have hz := IntervalOrder.block x (t+1) lower ih
          simpa [interval_tail_succ, Nat.add_assoc] using hz

theorem PushOrder.add_interval {lo : Nat} {xs : List Nat}
    (h : PushOrder lo xs) (t : Nat) :
    PushOrder (lo+t+1) ((lo :: (List.range' (lo+1) t).reverse) ++ xs) := by
  induction t with
  | zero => simpa using h.top
  | succ t ih =>
      have hz := ih.second
      simpa [interval_tail_succ, Nat.add_assoc] using hz

theorem IntervalOrder.push {n : Nat} {xs : List Nat} (h : IntervalOrder n xs) :
    PushOrder n xs := by
  induction h with
  | nil => exact .nil
  | block lo t xs lower ih => exact ih.add_interval t

theorem pushOrder_iff_intervalOrder (n : Nat) (xs : List Nat) :
    PushOrder n xs ↔ IntervalOrder n xs := ⟨PushOrder.interval, IntervalOrder.push⟩

/-- Every interval-partition order has a no-pop original generalized history.
The pop width is arbitrary because this history emits nothing. -/
theorem PushOrder.history {n : Nat} {xs : List Nat} (h : PushOrder n xs) (s : Nat) :
    Run 2 s [] (List.range n) [] xs := by
  induction h with
  | nil => simpa using Run.nil ([] : List Nat)
  | @top n xs h ih =>
      have ht := Run.single (Step.push (r := 2) (s := s) [] xs n (by decide))
      simpa [List.range_succ] using ih.append ht
  | @second n x xs h ih =>
      have ht := Run.single (Step.push (r := 2) (s := s) [x] xs n (by simp))
      simpa [List.range_succ] using ih.append ht

theorem IntervalOrder.history {n : Nat} {xs : List Nat}
    (h : IntervalOrder n xs) (s : Nat) : Run 2 s [] (List.range n) [] xs :=
  h.push.history s

/-- Completeness for actual no-pop histories, including an existing block. -/
theorem Run.continuePushOrder {s : Nat} {held input output final : List Nat}
    (h : Run 2 s held input output final) {n k : Nat}
    (emptyOutput : output = []) (start : PushOrder n held)
    (increasingInput : input = List.range' n k) : PushOrder (n+k) final := by
  induction h generalizing n k with
  | nil held =>
      have hk : k = 0 := by
        have hz := congrArg List.length increasingInput
        simpa using hz.symm
      subst k
      simpa using start
  | @cons held middle final input output inputs outputs head tail ih =>
      cases head with
      | push pre post x allowed =>
          have ht : outputs = [] := by simpa using emptyOutput
          cases k with
          | zero => simp at increasingInput
          | succ k =>
              have he : x = n ∧ inputs = List.range' (n+1) k := by
                simpa [List.range'_succ] using increasingInput
              rcases he with ⟨rfl, hi⟩
              have next : PushOrder (x+1) (pre ++ x :: post) := by
                cases pre with
                | nil => simpa using start.top
                | cons a pre =>
                    cases pre with
                    | nil => simpa using start.second
                    | cons b pre => simp at allowed; omega
              have hz := ih ht next hi
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz
      | pop pre post x allowed => simp at emptyOutput

/-- The interval denotation is exactly original top-two no-pop reachability. -/
theorem intervalOrder_iff_history (n s : Nat) (xs : List Nat) :
    IntervalOrder n xs ↔ Run 2 s [] (List.range n) [] xs := by
  constructor
  · intro h; exact h.history s
  · intro h
    have hp := h.continuePushOrder (n := 0) (k := n) rfl PushOrder.nil (by simp [List.range_eq_range'])
    simpa using hp.interval

#print axioms pushOrder_iff_intervalOrder
#print axioms IntervalOrder.history
#print axioms intervalOrder_iff_history
end StackSorting.Generalized
