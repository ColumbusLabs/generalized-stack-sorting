import GeneralizedLazy

/-! Exact record-batch segmentation for generation from increasing input. -/
namespace StackSorting.Generalized

theorem range_prefix_endpoint (pre rest : List Nat) (a k n : Nat)
    (h : pre ++ a :: rest = List.range' k n) :
    a = k + pre.length ∧ pre = List.range' k pre.length ∧
      rest = List.range' (a+1) rest.length ∧ n = pre.length + 1 + rest.length := by
  have hlen : n = pre.length + 1 + rest.length := by
    have hz := congrArg List.length h
    simp at hz
    omega
  have hdrop := congrArg (List.drop pre.length) h
  have hminus : n - pre.length = rest.length + 1 := by omega
  simp only [List.drop_left, List.drop_range', Nat.mul_one, hminus, List.range'_succ,
    List.cons.injEq] at hdrop
  obtain ⟨ha, hr⟩ := hdrop
  refine ⟨ha, ?_, by simpa [ha] using hr, hlen⟩
  have hsplit : List.range' k pre.length ++ List.range' (k+pre.length) (rest.length+1) =
      List.range' k n := by
    simp [hlen, Nat.add_comm, Nat.add_left_comm]
  have he := h.trans hsplit.symm
  exact List.append_inj_left he (by simp)

/-- `next` is the first unread input value and `limit` the exclusive final
input bound. Each record segment reads exactly `next,...,a` and pops `a`.
Thus there are no extra reads before a held output or after the final output. -/
inductive RangeLazyRun (r s limit : Nat) : Nat → List Nat → List Nat → Prop where
  | nil : RangeLazyRun r s limit limit [] []
  | held {next a : Nat} {held after out : List Nat}
      (pop : Step r s held [] [a] after)
      (tail : RangeLazyRun r s limit next after out) :
      RangeLazyRun r s limit next held (a :: out)
  | record {next a : Nat} {held before after out : List Nat}
      (lower : next ≤ a) (upper : a < limit) (fresh : a ∉ held)
      (read : Run r s held (List.range' next (a+1-next)) [] before)
      (pop : Step r s before [] [a] after)
      (tail : RangeLazyRun r s limit (a+1) after out) :
      RangeLazyRun r s limit next held (a :: out)

theorem LazyRun.range {r s : Nat} {held input output : List Nat}
    (h : LazyRun r s held input output) (k n : Nat)
    (hi : input = List.range' k n) : RangeLazyRun r s (k+n) k held output := by
  induction h generalizing k n with
  | nil =>
    have hn : n = 0 := by simpa using (congrArg List.length hi).symm
    subst n
    exact RangeLazyRun.nil
  | held pop tail ih => exact RangeLazyRun.held pop (ih k n hi)
  | @record held before after pre rest out a fresh first read pop tail ih =>
    obtain ⟨ha, hp, hr, hn⟩ := range_prefix_endpoint pre rest a k n hi
    have hlo : k ≤ a := by omega
    have hup : a < k+n := by omega
    have hcount : a+1-k = pre.length+1 := by omega
    have hread : Run r s held (List.range' k (a+1-k)) [] before := by
      have he : pre ++ [a] = List.range' k (pre.length+1) := by
        rw [hp, List.range'_concat]
        simp [ha]
      simpa [he, hcount] using read
    have ht := ih (a+1) rest.length hr
    have hend : a+1+rest.length = k+n := by omega
    rw [hend] at ht
    exact RangeLazyRun.record hlo hup fresh hread pop ht

/-- Every actual complete increasing-input computation has exact lazy record
segments; no composition transition hypothesis is assumed. -/
theorem Run.rangeLazy {r s k n : Nat} {held output : List Nat}
    (h : Run r s held (List.range' k n) output [])
    (hd : (held ++ List.range' k n).Nodup) :
    RangeLazyRun r s (k+n) k held output := (h.lazy output hd).range k n rfl

theorem generated_rangeLazy {r s n : Nat} {output : List Nat}
    (h : Run r s [] (List.range n) output []) : RangeLazyRun r s n 0 [] output := by
  have hr : Run r s [] (List.range' 0 n) output [] := by
    simpa [List.range_eq_range'] using h
  have hz := hr.rangeLazy (by simpa using (List.nodup_range' (s := 0) (n := n)))
  simpa using hz

theorem RangeLazyRun.bound {r s limit next : Nat} {held output : List Nat}
    (h : RangeLazyRun r s limit next held output) : next ≤ limit := by
  induction h with
  | nil => exact Nat.le_refl _
  | held pop tail ih => exact ih
  | record lower upper fresh read pop tail ih => omega

theorem RangeLazyRun.history {r s limit next : Nat} {held output : List Nat}
    (h : RangeLazyRun r s limit next held output) :
    Run r s held (List.range' next (limit-next)) output [] := by
  induction h with
  | nil => simpa using Run.nil ([] : List Nat)
  | held pop tail ih => simpa using Run.cons pop ih
  | @record next a held before after out lower upper fresh read pop tail ih =>
    have he : List.range' next (a+1-next) ++ List.range' (a+1) (limit-(a+1)) =
        List.range' next (limit-next) := by
      have hstart : next + 1 * (a+1-next) = a+1 := by omega
      have hcount : a+1-next + (limit-(a+1)) = limit-next := by omega
      have hz := List.range'_append (s := next) (m := a+1-next)
        (n := limit-(a+1)) (step := 1)
      simpa only [hstart, hcount] using hz
    simpa [he] using read.append (Run.cons pop ih)

theorem generated_rangeLazy_iff (r s n : Nat) (output : List Nat) :
    RangeLazyRun r s n 0 [] output ↔ Run r s [] (List.range n) output [] := by
  constructor
  · intro h
    simpa [List.range_eq_range'] using h.history
  · exact generated_rangeLazy

#print axioms RangeLazyRun.history
#print axioms generated_rangeLazy_iff

#print axioms Run.rangeLazy
#print axioms generated_rangeLazy
end StackSorting.Generalized
