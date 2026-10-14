import Std

/-! Slot-indexed single-token stack machine. Stacks are top first and slots
are zero based. There is no bypass operation and no hidden pop-priority rule. -/
namespace StackSorting.Generalized

inductive RawOp where
  | push (slot token : Nat)
  | pop (slot : Nat)
  deriving DecidableEq, Repr

def insertAt? : Nat → Nat → List Nat → Option (List Nat)
  | 0, a, xs => some (a :: xs)
  | _ + 1, _, [] => none
  | k + 1, a, x :: xs => (insertAt? k a xs).map (x :: ·)

def removeAt? : Nat → List Nat → Option (List Nat × Nat)
  | _, [] => none
  | 0, x :: xs => some (xs, x)
  | k + 1, x :: xs => (removeAt? k xs).map (fun (ys, y) => (x :: ys, y))

def step (r s : Nat) : RawOp → List Nat → Option (List Nat × List Nat)
  | .push k a, xs => if k < r then (insertAt? k a xs).map (fun ys => (ys, [])) else none
  | .pop k, xs => if k < s then (removeAt? k xs).map (fun (ys, a) => (ys, [a])) else none

def run (r s : Nat) : List RawOp → List Nat → Option (List Nat × List Nat)
  | [], xs => some (xs, [])
  | op :: ops, xs => do
      let (ys, out) ← step r s op xs
      let (zs, outs) ← run r s ops ys
      pure (zs, out ++ outs)

def introduced : RawOp → List Nat
  | .push _ a => [a]
  | .pop _ => []

def inputs (ops : List RawOp) : List Nat := ops.flatMap introduced

def CanTransform (r s : Nat) (held input output : List Nat) : Prop :=
  ∃ ops, run r s ops held = some ([], output) ∧ inputs ops = input

def CanSort (r s : Nat) (input : List Nat) : Prop :=
  CanTransform r s [] input (List.range' 1 input.length)

/-- Physical capacity counts every intermediate stack, including a push
immediately followed by removal of that same token. -/
def Fits (r s H : Nat) : List RawOp → List Nat → Prop
  | [], xs => xs.length ≤ H
  | op :: ops, xs => xs.length ≤ H ∧
      ∃ ys out, step r s op xs = some (ys, out) ∧ Fits r s H ops ys

theorem run_append (r s : Nat) (as bs : List RawOp) (held : List Nat) :
    run r s (as ++ bs) held = (do
      let (t, out) ← run r s as held
      let (u, outs) ← run r s bs t
      pure (u, out ++ outs)) := by
  induction as generalizing held with
  | nil => simp [run, Prod.eta]
  | cons op ops ih => simp [run, ih, Option.bind_assoc, List.append_assoc]

theorem split_run (r s : Nat) (op : RawOp) (ops : List RawOp)
    (held after output : List Nat)
    (h : run r s (op :: ops) held = some (after, output)) :
    ∃ middle emitted tail, step r s op held = some (middle, emitted) ∧
      run r s ops middle = some (after, tail) ∧ emitted ++ tail = output := by
  cases hs : step r s op held with
  | none => simp [run, hs] at h
  | some p =>
    rcases p with ⟨middle, emitted⟩
    cases ht : run r s ops middle with
    | none => simp [run, hs, ht] at h
    | some p =>
      rcases p with ⟨last, tail⟩
      simp [run, hs, ht] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨middle, emitted, tail, rfl, ht, rfl⟩

theorem insertAt_length (k a : Nat) (xs ys : List Nat)
    (h : insertAt? k a xs = some ys) : ys.length = xs.length + 1 := by
  induction k generalizing xs ys with
  | zero => simp [insertAt?] at h; subst ys; rfl
  | succ k ih =>
    cases xs with
    | nil => simp [insertAt?] at h
    | cons x xs =>
      cases ht : insertAt? k a xs with
      | none => simp [insertAt?, ht] at h
      | some zs =>
        simp [insertAt?, ht] at h
        subst ys
        simpa using (ih xs zs ht)

theorem removeAt_length (k : Nat) (xs ys : List Nat) (a : Nat)
    (h : removeAt? k xs = some (ys, a)) : ys.length + 1 = xs.length := by
  induction k generalizing xs ys with
  | zero =>
    cases xs with
    | nil => simp [removeAt?] at h
    | cons x xs => simp [removeAt?] at h; rcases h with ⟨rfl, rfl⟩; rfl
  | succ k ih =>
    cases xs with
    | nil => simp [removeAt?] at h
    | cons x xs =>
      cases ht : removeAt? k xs with
      | none => simp [removeAt?, ht] at h
      | some p =>
        rcases p with ⟨zs, b⟩
        simp [removeAt?, ht] at h
        rcases h with ⟨rfl, rfl⟩
        simpa using (ih xs zs ht)

/-- Local lazy-normalization swap. A push followed by removal of another
value may be swapped. Both new slot indices weakly decrease. -/
theorem insert_remove_commute (i j x y : Nat) (xs middle after : List Nat)
    (hi : insertAt? i x xs = some middle)
    (hj : removeAt? j middle = some (after, y)) (hne : y ≠ x) :
    ∃ xs' i' j', removeAt? j' xs = some (xs', y) ∧
      insertAt? i' x xs' = some after ∧ i' ≤ i ∧ j' ≤ j := by
  induction i generalizing j xs middle after with
  | zero =>
    simp [insertAt?] at hi
    subst middle
    cases j with
    | zero => simp [removeAt?] at hj; exact (hne hj.2.symm).elim
    | succ j =>
      cases h : removeAt? j xs with
      | none => simp [removeAt?, h] at hj
      | some p =>
        rcases p with ⟨zs, z⟩
        simp [removeAt?, h] at hj
        rcases hj with ⟨rfl, rfl⟩
        exact ⟨zs, 0, j, h, rfl, Nat.le_refl 0, Nat.le_succ j⟩
  | succ i ih =>
    cases xs with
    | nil => simp [insertAt?] at hi
    | cons a xs =>
      cases h : insertAt? i x xs with
      | none => simp [insertAt?, h] at hi
      | some zs =>
        simp [insertAt?, h] at hi
        subst middle
        cases j with
        | zero =>
          simp [removeAt?] at hj
          rcases hj with ⟨rfl, rfl⟩
          exact ⟨xs, i, 0, rfl, h, Nat.le_succ i, Nat.le_refl 0⟩
        | succ j =>
          cases hp : removeAt? j zs with
          | none => simp [removeAt?, hp] at hj
          | some p =>
            rcases p with ⟨ws, w⟩
            simp [removeAt?, hp] at hj
            rcases hj with ⟨rfl, rfl⟩
            obtain ⟨us, i', j', hd, hu, hile, hjle⟩ := ih j xs zs ws h hp
            exact ⟨a :: us, i' + 1, j' + 1, by simp [removeAt?, hd],
              by simp [insertAt?, hu], Nat.succ_le_succ hile, Nat.succ_le_succ hjle⟩

theorem legal_push_pop_commute (r s i j x y : Nat) (xs middle after : List Nat)
    (hir : i < r) (hjs : j < s)
    (hi : insertAt? i x xs = some middle)
    (hj : removeAt? j middle = some (after, y)) (hne : y ≠ x) :
    ∃ xs' i' j', i' < r ∧ j' < s ∧
      step r s (.pop j') xs = some (xs', [y]) ∧
      step r s (.push i' x) xs' = some (after, []) ∧
      run r s [.pop j', .push i' x] xs = some (after, [y]) ∧
      xs'.length + 1 = xs.length := by
  obtain ⟨xs', i', j', hd, hu, hi', hj'⟩ :=
    insert_remove_commute i j x y xs middle after hi hj hne
  have bir := Nat.lt_of_le_of_lt hi' hir
  have bjs := Nat.lt_of_le_of_lt hj' hjs
  have hs₁ : step r s (.pop j') xs = some (xs', [y]) := by simp [step, bjs, hd]
  have hs₂ : step r s (.push i' x) xs' = some (after, []) := by simp [step, bir, hu]
  exact ⟨xs', i', j', bir, bjs, hs₁, hs₂, by simp [run, hs₁, hs₂],
    removeAt_length j' xs xs' y hd⟩

#print axioms legal_push_pop_commute

#print axioms insert_remove_commute

end StackSorting.Generalized
