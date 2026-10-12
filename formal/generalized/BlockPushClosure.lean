import RelabelledBlocks

/-! Exact highest-block enlargement under actual top-two pushes. -/
namespace StackSorting.Generalized

theorem SegmentOrder.push_top {base top : Nat} {xs : List Nat}
    (h : SegmentOrder base top xs) : SegmentOrder base (top+1) (top :: xs) := by
  simpa using SegmentOrder.block top 0 xs h

theorem SegmentOrder.push_second {base top x : Nat} {xs : List Nat}
    (h : SegmentOrder base top (x :: xs)) :
    SegmentOrder base (top+1) (x :: top :: xs) := by
  cases h with
  | block lo t lower ih =>
      have hz := SegmentOrder.block x (t+1) lower ih
      simpa [interval_tail_succ, Nat.add_assoc] using hz

theorem SegmentOrder.push_step {base top s : Nat} {xs ys : List Nat}
    (h : SegmentOrder base top xs) (hp : Step 2 s xs [top] [] ys) :
    SegmentOrder base (top+1) ys := by
  cases hp with
  | push pre post top allowed =>
      cases pre with
      | nil => simpa using h.push_top
      | cons a pre =>
          cases pre with
          | nil => simpa using h.push_second
          | cons b pre => simp at allowed; omega

/-- Any enlarged interval block has an actual predecessor under its last push. -/
theorem SegmentOrder.unpush {base top : Nat} {ys : List Nat}
    (h : SegmentOrder base (top+1) ys) (hb : base ≤ top) (s : Nat) :
    ∃ xs, SegmentOrder base top xs ∧ Step 2 s xs [top] [] ys := by
  cases h with
  | nil => omega
  | block lo t xs lower =>
      cases t with
      | zero =>
          refine ⟨xs, lower, ?_⟩
          simpa using Step.push (r := 2) (s := s) [] xs lo (by simp)
      | succ t =>
          have hp := SegmentOrder.block lo t xs lower
          refine ⟨(lo :: (List.range' (lo+1) t).reverse) ++ xs, hp, ?_⟩
          have hs := Step.push (r := 2) (s := s) [lo]
            ((List.range' (lo+1) t).reverse ++ xs) (lo+t+1) (by simp)
          simpa [interval_tail_succ, Nat.add_assoc] using hs

/-- Exact one-push image, not merely closure of an overapproximation. -/
theorem SegmentOrder.push_image {base top s : Nat} {ys : List Nat}
    (hb : base ≤ top) :
    (∃ xs, SegmentOrder base top xs ∧ Step 2 s xs [top] [] ys) ↔
      SegmentOrder base (top+1) ys :=
  ⟨fun ⟨_, h, hp⟩ => h.push_step hp, fun h => h.unpush hb s⟩

/-- A nonempty highest block shields every lower suffix from top-two pushes. -/
theorem Step.push_suffix {α : Type} {s : Nat} {xs tail final : List α} {x : α}
    (h : Step 2 s (xs ++ tail) [x] [] final) (hne : xs ≠ []) :
    ∃ ys, Step 2 s xs [x] [] ys ∧ final = ys ++ tail := by
  generalize he : xs ++ tail = held at h
  cases h with
  | push pre post x allowed =>
      cases pre with
      | nil =>
          refine ⟨x :: xs, ?_, ?_⟩
          · simpa using Step.push (r := 2) (s := s) [] xs x (by simp)
          · simpa using congrArg (List.cons x) he.symm
      | cons a pre =>
          cases pre with
          | nil =>
              cases xs with
              | nil => contradiction
              | cons b xs =>
                  simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
                  rcases he with ⟨rfl, rfl⟩
                  exact ⟨b :: x :: xs, by simpa using
                    (Step.push (r := 2) (s := s) [b] xs x (by simp)), rfl⟩
          | cons b pre => simp at allowed; omega

theorem Step.append_suffix {α : Type} {r s : Nat} {xs ins outs ys : List α}
    (h : Step r s xs ins outs ys) (tail : List α) :
    Step r s (xs ++ tail) ins outs (ys ++ tail) := by
  cases h with
  | push pre post x allowed => simpa [List.append_assoc] using
      (Step.push pre (post ++ tail) x allowed)
  | pop pre post x allowed => simpa [List.append_assoc] using
      (Step.pop pre (post ++ tail) x allowed)

theorem Run.append_suffix {α : Type} {r s : Nat} {xs ins outs ys : List α}
    (h : Run r s xs ins outs ys) (tail : List α) :
    Run r s (xs ++ tail) ins outs (ys ++ tail) := by
  induction h with
  | nil => exact Run.nil _
  | cons head rest ih => exact Run.cons (head.append_suffix tail) ih

/-- Actual no-pop runs enlarge one interval block. -/
theorem Run.continueSegment {s : Nat} {held input output final : List Nat}
    (h : Run 2 s held input output final) {base top k : Nat}
    (emptyOutput : output = []) (start : SegmentOrder base top held)
    (increasingInput : input = List.range' top k) :
    SegmentOrder base (top+k) final := by
  induction h generalizing base top k with
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
              have he : x = top ∧ inputs = List.range' (top+1) k := by
                simpa [List.range'_succ] using increasingInput
              rcases he with ⟨rfl, hi⟩
              have next := start.push_step (Step.push (s := s) pre post x allowed)
              have hz := ih ht next hi
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz
      | pop pre post x allowed => simp at emptyOutput

/-- Surjective batched enlargement of the same top block. -/
theorem SegmentOrder.read_image {base top s : Nat} (k : Nat) (final : List Nat)
    (hb : base ≤ top) :
    (∃ held, SegmentOrder base top held ∧
      Run 2 s held (List.range' top k) [] final) ↔
      SegmentOrder base (top+k) final := by
  constructor
  · rintro ⟨held, hh, hr⟩
    exact hr.continueSegment rfl hh rfl
  · intro hf
    induction k generalizing final with
    | zero => exact ⟨final, by simpa using hf, by simpa using Run.nil final⟩
    | succ k ih =>
        obtain ⟨before, hh, hp⟩ := hf.unpush (by omega : base ≤ top+k) s
        obtain ⟨held, hs, hr⟩ := ih before hh
        refine ⟨held, hs, ?_⟩
        have hz := hr.append (Run.single hp)
        simpa [List.range'_concat] using hz

/-- A push-only run cannot reach into a frozen suffix below a nonempty block. -/
theorem Run.strip_push_suffix {α : Type} {s : Nat} {held input output final : List α}
    (h : Run 2 s held input output final) (emptyOutput : output = [])
    (xs tail : List α) (split : held = xs ++ tail) (hne : xs ≠ []) :
    ∃ ys, Run 2 s xs input [] ys ∧ final = ys ++ tail := by
  induction h generalizing xs with
  | nil held => exact ⟨xs, Run.nil xs, split⟩
  | @cons held middle final input output inputs outputs head rest ih =>
      cases head with
      | push pre post x allowed =>
          have ht : outputs = [] := by simpa using emptyOutput
          have hp : Step 2 s (xs ++ tail) [x] [] (pre ++ x :: post) := by
            simpa [← split] using Step.push (r := 2) (s := s) pre post x allowed
          obtain ⟨middle, hm, he⟩ := hp.push_suffix hne
          have hnonempty : middle ≠ [] := by
            cases hm with
            | push pre post x allowed => simp
          obtain ⟨ys, hr, hf⟩ := ih ht middle he hnonempty
          exact ⟨ys, by simpa using Run.cons hm hr, hf⟩
      | pop pre post x allowed => simp at emptyOutput

/-- Exact batched push image above any fixed lower stack, with a nonempty
initial top block. This is the shield required by composition states. -/
theorem SegmentOrder.read_image_suffix {base top s : Nat} (k : Nat)
    (tail final : List Nat) (hb : base < top) :
    (∃ held, SegmentOrder base top held ∧
      Run 2 s (held ++ tail) (List.range' top k) [] final) ↔
      ∃ high, SegmentOrder base (top+k) high ∧ final = high ++ tail := by
  constructor
  · rintro ⟨held, hh, hr⟩
    have hne : held ≠ [] := by
      have hlen := hh.length
      intro he; simp [he] at hlen; omega
    obtain ⟨high, hs, rfl⟩ := hr.strip_push_suffix rfl held tail rfl hne
    exact ⟨high, hs.continueSegment rfl hh rfl, rfl⟩
  · rintro ⟨high, hh, rfl⟩
    obtain ⟨held, hs, hr⟩ := (SegmentOrder.read_image k high (Nat.le_of_lt hb)).mpr hh
    exact ⟨held, hs, hr.append_suffix tail⟩

#print axioms SegmentOrder.push_image
#print axioms Step.push_suffix
#print axioms Step.append_suffix
#print axioms SegmentOrder.read_image
#print axioms SegmentOrder.read_image_suffix
end StackSorting.Generalized
