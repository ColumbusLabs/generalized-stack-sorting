import GeneralizedDecoratedClauseImages

/-! Exact exceptional-suffix language identities derived from the literal
physical-coordinate scanner. No decorated closure or counting identity is
assumed. All statements concern sets of coordinate words. -/
namespace StackSorting.Generalized.Decorated
namespace ExceptionalSuffix
open Coordinates
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

@[simp] theorem denotes_nil (digits : List Nat) : denotes [] digits ↔ digits = [] := Iff.rfl

@[simp] theorem denotes_Z (state : State) (digits : List Nat) :
    denotes (.Z :: state) digits ↔ ∃ tail, denotes state tail ∧ digits = 0 :: tail := by
  simp [denotes, Factor.denotes]

@[simp] theorem denotes_O (state : State) (digits : List Nat) :
    denotes (.O :: state) digits ↔ ∃ tail, denotes state tail ∧ digits = 1 :: tail := by
  simp [denotes, Factor.denotes]

@[simp] theorem denotes_B (state : State) (digits : List Nat) :
    denotes (.B :: state) digits ↔ ∃ digit tail,
      (digit = 0 ∨ digit = 1) ∧ denotes state tail ∧ digits = digit :: tail := by
  constructor
  · rintro ⟨left, right, hl, hr, rfl⟩
    rcases hl with rfl | rfl
    · exact ⟨0, right, Or.inl rfl, hr, rfl⟩
    · exact ⟨1, right, Or.inr rfl, hr, rfl⟩
  · rintro ⟨digit, tail, hd, ht, rfl⟩
    rcases hd with rfl | rfl
    · exact ⟨[0], tail, Or.inl rfl, ht, rfl⟩
    · exact ⟨[1], tail, Or.inr rfl, ht, rfl⟩

@[simp] theorem denotes_T (state : State) (digits : List Nat) :
    denotes (.T :: state) digits ↔ ∃ digit tail,
      (digit = 0 ∨ digit = 1 ∨ digit = 2) ∧ denotes state tail ∧ digits = digit :: tail := by
  constructor
  · rintro ⟨left, right, hl, hr, rfl⟩
    rcases hl with rfl | rfl | rfl
    · exact ⟨0, right, Or.inl rfl, hr, rfl⟩
    · exact ⟨1, right, Or.inr (Or.inl rfl), hr, rfl⟩
    · exact ⟨2, right, Or.inr (Or.inr rfl), hr, rfl⟩
  · rintro ⟨digit, tail, hd, ht, rfl⟩
    rcases hd with rfl | rfl | rfl
    · exact ⟨[0], tail, Or.inl rfl, ht, rfl⟩
    · exact ⟨[1], tail, Or.inr (Or.inl rfl), ht, rfl⟩
    · exact ⟨[2], tail, Or.inr (Or.inr rfl), ht, rfl⟩

@[simp] theorem denotes_single (factor : Factor) (digits : List Nat) :
    denotes [factor] digits ↔ factor.denotes digits := by
  simp [denotes]

@[simp] theorem denotes_B_replicate (n : Nat) (digits : List Nat) :
    denotes (List.replicate n .B) digits ↔
      digits.length = n ∧ ∀ digit ∈ digits, digit ≤ 1 := by
  induction n generalizing digits with
  | zero => cases digits <;> simp
  | succ n ih =>
    cases digits with
    | nil => simp [List.replicate_succ]
    | cons digit digits =>
      simp only [List.replicate_succ, denotes_B, List.cons.injEq]
      constructor
      · rintro ⟨a, tail, ha, ht, rfl, rfl⟩
        obtain ⟨hlen, hb⟩ := (ih digits).mp ht
        refine ⟨by simp [hlen], ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rcases ha with rfl | rfl <;> omega
        · exact hb x hx
      · rintro ⟨hlen, hb⟩
        have ha := hb digit (by simp)
        exact ⟨digit, digits, by omega, (ih digits).mpr ⟨by simpa using hlen, fun x hx => hb x (by simp [hx])⟩, rfl, rfl⟩

@[simp] theorem denotes_O_replicate (n : Nat) (digits : List Nat) :
    denotes (List.replicate n .O) digits ↔ digits = List.replicate n 1 := by
  induction n generalizing digits with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

theorem binary_or_ones (n : Nat) (digits : List Nat) :
    (Factor.C n).denotes digits ∨ digits = List.replicate n 1 ↔
      denotes (List.replicate n .B) digits := by
  rw [denotes_B_replicate]
  constructor
  · rintro (⟨hl, hb, _⟩ | rfl)
    · exact ⟨hl, hb⟩
    · simp
  · rintro ⟨hl, hb⟩
    by_cases hz : 0 ∈ digits
    · exact Or.inl ⟨hl, hb, hz⟩
    · right
      have allones : ∀ (word : List Nat), (∀ a ∈ word, a ≤ 1) → 0 ∉ word →
          word = List.replicate word.length 1 := by
        intro word hbin hzero
        induction word with
        | nil => rfl
        | cons digit rest ih =>
          have hd := hbin digit (by simp)
          have hn : digit ≠ 0 := by
            intro he
            exact hzero (by simp [he])
          have hd' : digit = 1 := by omega
          have hr := ih (fun x hx => hbin x (by simp [hx]))
            (by intro hx; exact hzero (by simp [hx]))
          simpa [List.replicate_succ, hd'] using congrArg (1 :: ·) hr
      simpa [hl] using allones digits hb hz

@[simp] theorem scanImage_nil (p : Nat) (output : List Nat) :
    ScanImage p [] output ↔ p < 3 ∧ output = [] := by
  simp [ScanImage, denotes, scan]

@[simp] theorem scanImage_T_zero_nil (state : State) :
    ¬ ScanImage 0 (.T :: state) [] := by
  rintro ⟨digits, hd, hs⟩
  obtain ⟨digit, tail, hchoices, ht, rfl⟩ := (denotes_T state digits).mp hd
  rcases hchoices with rfl | rfl | rfl <;>
    simp [scan_three_zero_zero, scan_three_zero_one, scan_three_zero_two,
      Option.map_eq_some_iff] at hs

theorem scanImage_T_zero_cons (state : State) (digit : Nat) (output : List Nat) :
    ScanImage 0 (.T :: state) (digit :: output) ↔
      (digit = 0 ∧ ScanImage 1 state output) ∨
      (digit = 0 ∧ ScanImage 0 state output) ∨
      (digit = 1 ∧ ScanImage 0 state output) := by
  constructor
  · rintro ⟨digits, hd, hs⟩
    obtain ⟨a, tail, ha, ht, rfl⟩ := (denotes_T state digits).mp hd
    rcases ha with rfl | rfl | rfl
    · rw [scan_three_zero_zero, Option.map_eq_some_iff] at hs
      obtain ⟨out, hs, he⟩ := hs
      obtain ⟨rfl, rfl⟩ := List.cons.inj he
      exact Or.inl ⟨rfl, tail, ht, hs⟩
    · rw [scan_three_zero_one, Option.map_eq_some_iff] at hs
      obtain ⟨out, hs, he⟩ := hs
      obtain ⟨rfl, rfl⟩ := List.cons.inj he
      exact Or.inr (Or.inl ⟨rfl, tail, ht, hs⟩)
    · rw [scan_three_zero_two, Option.map_eq_some_iff] at hs
      obtain ⟨out, hs, he⟩ := hs
      obtain ⟨rfl, rfl⟩ := List.cons.inj he
      exact Or.inr (Or.inr ⟨rfl, tail, ht, hs⟩)
  · rintro (⟨rfl, tail, ht, hs⟩ | ⟨rfl, tail, ht, hs⟩ | ⟨rfl, tail, ht, hs⟩)
    · exact ⟨0 :: tail, (denotes_T state _).mpr ⟨0, tail, Or.inl rfl, ht, rfl⟩, by rw [scan_three_zero_zero, hs]; rfl⟩
    · exact ⟨1 :: tail, (denotes_T state _).mpr ⟨1, tail, Or.inr (Or.inl rfl), ht, rfl⟩, by rw [scan_three_zero_one, hs]; rfl⟩
    · exact ⟨2 :: tail, (denotes_T state _).mpr ⟨2, tail, Or.inr (Or.inr rfl), ht, rfl⟩, by rw [scan_three_zero_two, hs]; rfl⟩

/-- Exactly the four singleton alphabets in the written normal form. -/
def Unary (factor : Factor) : Prop :=
  factor = .Z ∨ factor = .O ∨ factor = .B ∨ factor = .T

/-- The literal terminal map f(Z)=Z, f(O)=O, f(B)=f(T)=B. -/
def terminal : Factor → Factor
  | .Z => .Z
  | .O => .O
  | _ => .B

theorem exceptional_nonempty (q : Nat) {factor : Factor} (hu : Unary factor)
    {digits : List Nat} (hd : denotes (List.replicate q .T ++ [factor]) digits) :
    digits ≠ [] := by
  obtain ⟨left, right, _, hr, rfl⟩ := (denotes_append _ _ _).mp hd
  have hf : factor.height = 1 := by rcases hu with rfl | rfl | rfl | rfl <;> rfl
  have hl : right.length = 1 := by
    have h := Factor.denotes_length ((denotes_single factor right).mp hr)
    exact h.trans hf
  intro he
  have hz := congrArg List.length he
  simp only [List.length_append, List.length_nil] at hz
  omega

@[simp] theorem scanImage_one_single {factor : Factor} (hu : Unary factor) (output : List Nat) :
    ScanImage 1 [factor] output ↔ denotes [terminal factor] output := by
  rcases hu with rfl | rfl | rfl | rfl <;>
    simp [ScanImage, denotes, Factor.denotes, scan, advance, retained, terminal,
      exists_or, and_or_left, or_and_right, eq_comm]

theorem scanImage_one_T {state : State}
    (hn : ∀ digits, denotes state digits → digits ≠ []) (output : List Nat) :
    ScanImage 1 (.T :: state) output ↔
      ∃ tail, ScanImage 1 state tail ∧ output = 1 :: tail := by
  constructor
  · rintro ⟨digits, hd, hs⟩
    obtain ⟨a, input, ha, ht, rfl⟩ := (denotes_T state digits).mp hd
    have htwo : scan 3 2 input = none := scan_two_nonempty (hn input ht) (denotes_bounded ht)
    rcases ha with rfl | rfl | rfl
    · simp [scan_three_one_zero, htwo] at hs
    · simp [scan_three_one_one, htwo] at hs
    · rw [scan_three_one_two, Option.map_eq_some_iff] at hs
      obtain ⟨tail, hs, rfl⟩ := hs
      exact ⟨tail, ⟨input, ht, hs⟩, rfl⟩
  · rintro ⟨tail, ⟨input, hi, hs⟩, rfl⟩
    exact ⟨2 :: input,
      (denotes_T state _).mpr ⟨2, input, Or.inr (Or.inr rfl), hi, rfl⟩,
      by rw [scan_three_one_two, hs]; rfl⟩

/-- F₁(T^q A)=O^q f(A), uniformly over the four unary terminals. -/
theorem scanImage_one_exceptional (q : Nat) {factor : Factor} (hu : Unary factor)
    (output : List Nat) :
    ScanImage 1 (List.replicate q .T ++ [factor]) output ↔
      denotes (List.replicate q .O ++ [terminal factor]) output := by
  induction q generalizing output with
  | zero => simpa using scanImage_one_single hu output
  | succ q ih =>
    simp only [List.replicate_succ, List.cons_append]
    rw [scanImage_one_T (fun digits hd => exceptional_nonempty q hu hd), denotes_O]
    exact exists_congr (fun tail => and_congr_left (fun _ => ih tail))

/-- A fixed one in a prefix may be relaxed to a free binary coordinate. -/
theorem ones_prefix_sub_binary (q : Nat) (suffix : State) {output : List Nat}
    (h : denotes (List.replicate q .O ++ suffix) output) :
    denotes (List.replicate q .B ++ suffix) output := by
  induction q generalizing output with
  | zero => exact h
  | succ q ih =>
    simp only [List.replicate_succ, List.cons_append, denotes_O] at h
    obtain ⟨tail, ht, rfl⟩ := h
    exact (denotes_B _ _).mpr ⟨1, tail, Or.inr rfl, ih ht, rfl⟩

theorem unary_binary (factor : Factor) (h : factor = .O ∨ factor = .B)
    {output : List Nat} (hd : denotes [factor] output) :
    denotes [.B] output := by
  rcases h with rfl | rfl
  · have he : output = [1] := (denotes_single _ _).mp hd
    subst output
    exact ⟨[1], [], Or.inr rfl, rfl, rfl⟩
  · exact hd

theorem ones_terminal_sub_binary (q : Nat) {factor : Factor}
    (hf : factor = .O ∨ factor = .B) {output : List Nat}
    (hd : denotes (List.replicate q .O ++ [factor]) output) :
    denotes (List.replicate (q+1) .B) output := by
  obtain ⟨left, right, hl, hr, rfl⟩ := (denotes_append _ _ _).mp hd
  have hleft : denotes (List.replicate q .B) left := by
    have he := (denotes_O_replicate q left).mp hl
    subst left
    simp
  have hright := unary_binary factor hf hr
  have hcat := (denotes_append (List.replicate q .B) [.B] (left ++ right)).mpr
    ⟨left, right, hleft, hright, rfl⟩
  simpa only [List.replicate_succ'] using hcat

theorem ones_terminal_allones (q : Nat) {factor : Factor}
    (hf : factor = .O ∨ factor = .B) :
    denotes (List.replicate q .O ++ [factor]) (List.replicate (q+1) 1) := by
  have hr : denotes [factor] [1] := by
    rcases hf with rfl | rfl <;> simp [Factor.denotes]
  rw [List.replicate_succ']
  exact (denotes_append _ _ _).mpr ⟨List.replicate q 1, [1], by simp, hr, rfl⟩

/-- The only missing point of a clause is supplied by either O^q O or O^q B. -/
theorem clause_union_ones_terminal (q : Nat) {factor : Factor}
    (hf : factor = .O ∨ factor = .B) (output : List Nat) :
    (Factor.C (q+1)).denotes output ∨
      denotes (List.replicate q .O ++ [factor]) output ↔
        denotes (List.replicate (q+1) .B) output := by
  constructor
  · rintro (hc | ho)
    · exact (binary_or_ones (q+1) output).mp (Or.inl hc)
    · exact ones_terminal_sub_binary q hf ho
  · intro hb
    rcases (binary_or_ones (q+1) output).mpr hb with hc | rfl
    · exact Or.inl hc
    · exact Or.inr (ones_terminal_allones q hf)

@[simp] theorem scanImage_zero_single_Z (output : List Nat) :
    ScanImage 0 [.Z] output ↔ denotes [.Z] output := by
  simp [ScanImage, denotes, Factor.denotes, scan, advance, retained, eq_comm]

@[simp] theorem scanImage_zero_single_O (output : List Nat) :
    ScanImage 0 [.O] output ↔ (Factor.C 1).denotes output := by
  have hc : (Factor.C 1).denotes output ↔ output = [0] := by
    constructor
    · rintro ⟨hl, hb, hz⟩
      cases output with
      | nil => simp at hl
      | cons digit rest =>
        have hr : rest = [] := List.length_eq_zero_iff.mp (Nat.succ.inj hl)
        subst rest
        simpa [eq_comm] using hz
    · rintro rfl
      simp [Factor.denotes]
  rw [hc]
  simp [ScanImage, denotes, Factor.denotes, scan, advance, retained, eq_comm]

@[simp] theorem scanImage_zero_single_B (output : List Nat) :
    ScanImage 0 [.B] output ↔ (Factor.C 1).denotes output := by
  rw [← scanImage_zero_single_O]
  simp [ScanImage, denotes, Factor.denotes, scan, advance, retained, exists_or, or_and_right]

@[simp] theorem scanImage_zero_single_T (output : List Nat) :
    ScanImage 0 [.T] output ↔ denotes [.B] output := by
  simp [ScanImage, denotes, Factor.denotes, scan, advance, retained, exists_or,
    or_and_right, eq_comm]

/-- F₀(T^q Z)=B^q Z. -/
theorem scanImage_zero_Z (q : Nat) (output : List Nat) :
    ScanImage 0 (List.replicate q .T ++ [.Z]) output ↔
      denotes (List.replicate q .B ++ [.Z]) output := by
  induction q generalizing output with
  | zero => simpa using scanImage_zero_single_Z output
  | succ q ih =>
    cases output with
    | nil => simp [List.replicate_succ]
    | cons digit output =>
      simp only [List.replicate_succ, List.cons_append, scanImage_T_zero_cons,
        scanImage_one_exceptional q (Or.inl rfl), terminal, ih, denotes_B, List.cons.injEq]
      constructor
      · rintro (⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩)
        · exact ⟨0, output, Or.inl rfl, ones_prefix_sub_binary q [.Z] ht, rfl, rfl⟩
        · exact ⟨0, output, Or.inl rfl, ht, rfl, rfl⟩
        · exact ⟨1, output, Or.inr rfl, ht, rfl, rfl⟩
      · rintro ⟨a, tail, ha, ht, rfl, rfl⟩
        rcases ha with rfl | rfl
        · exact Or.inr (Or.inl ⟨rfl, ht⟩)
        · exact Or.inr (Or.inr ⟨rfl, ht⟩)

/-- F₀(T^(q+1))=B^(q+1). -/
theorem scanImage_zero_T (q : Nat) (output : List Nat) :
    ScanImage 0 (List.replicate q .T ++ [.T]) output ↔
      denotes (List.replicate (q+1) .B) output := by
  induction q generalizing output with
  | zero => simpa using scanImage_zero_single_T output
  | succ q ih =>
    cases output with
    | nil => simp [List.replicate_succ]
    | cons digit output =>
      change ScanImage 0 (.T :: (List.replicate q .T ++ [.T])) (digit :: output) ↔
        denotes (.B :: List.replicate (q+1) .B) (digit :: output)
      rw [scanImage_T_zero_cons,
        scanImage_one_exceptional q (Or.inr (Or.inr (Or.inr rfl))), ih, denotes_B]
      simp only [terminal, List.cons.injEq]
      constructor
      · rintro (⟨rfl, ht⟩ | ⟨rfl, ht⟩ | ⟨rfl, ht⟩)
        · exact ⟨0, output, Or.inl rfl, ones_terminal_sub_binary q (Or.inr rfl) ht, rfl, rfl⟩
        · exact ⟨0, output, Or.inl rfl, ht, rfl, rfl⟩
        · exact ⟨1, output, Or.inr rfl, ht, rfl, rfl⟩
      · rintro ⟨a, tail, ha, ht, rfl, rfl⟩
        rcases ha with rfl | rfl
        · exact Or.inr (Or.inl ⟨rfl, ht⟩)
        · exact Or.inr (Or.inr ⟨rfl, ht⟩)

/-- A binary clause has a zero immediately, or starts with one and retains a
zero somewhere in its remaining tail. -/
theorem clause_cons (n digit : Nat) (output : List Nat) :
    (Factor.C (n+1)).denotes (digit :: output) ↔
      (digit = 0 ∧ denotes (List.replicate n .B) output) ∨
      (digit = 1 ∧ (Factor.C n).denotes output) := by
  rw [denotes_B_replicate]
  constructor
  · rintro ⟨hl, hb, hz⟩
    have hd := hb digit (by simp)
    have hlen : output.length = n := by simpa using hl
    have hbin : ∀ a ∈ output, a ≤ 1 := fun a ha => hb a (by simp [ha])
    by_cases he : digit = 0
    · exact Or.inl ⟨he, hlen, hbin⟩
    · have he' : digit = 1 := by omega
      exact Or.inr ⟨he', hlen, hbin, by simpa [he'] using hz⟩
  · rintro (⟨rfl, hl, hb⟩ | ⟨rfl, hl, hb, hz⟩)
    · exact ⟨by simp [hl], by simpa using hb, by simp⟩
    · exact ⟨by simp [hl], by simpa using hb, by simp [hz]⟩

/-- F₀(T^q O)=F₀(T^q B)=C_(q+1). -/
theorem scanImage_zero_O_or_B (q : Nat) {factor : Factor}
    (hf : factor = .O ∨ factor = .B) (output : List Nat) :
    ScanImage 0 (List.replicate q .T ++ [factor]) output ↔
      (Factor.C (q+1)).denotes output := by
  have hu : Unary factor := by rcases hf with rfl | rfl; exact Or.inr (Or.inl rfl); exact Or.inr (Or.inr (Or.inl rfl))
  have he : terminal factor = factor := by rcases hf with rfl | rfl <;> rfl
  induction q generalizing output with
  | zero => rcases hf with rfl | rfl <;> simp
  | succ q ih =>
    cases output with
    | nil => simp [List.replicate_succ, Factor.denotes]
    | cons digit output =>
      rw [List.replicate_succ, List.cons_append, scanImage_T_zero_cons,
        scanImage_one_exceptional q hu]
      simp only [he, ih]
      rw [clause_cons]
      constructor
      · rintro (⟨rfl, ho⟩ | ⟨rfl, hc⟩ | ⟨rfl, hc⟩)
        · exact Or.inl ⟨rfl, (clause_union_ones_terminal q hf output).mp (Or.inr ho)⟩
        · exact Or.inl ⟨rfl, (clause_union_ones_terminal q hf output).mp (Or.inl hc)⟩
        · exact Or.inr ⟨rfl, hc⟩
      · rintro (⟨rfl, hb⟩ | ⟨rfl, hc⟩)
        · rcases (clause_union_ones_terminal q hf output).mpr hb with hc | ho
          · exact Or.inr (Or.inl ⟨rfl, hc⟩)
          · exact Or.inl ⟨rfl, ho⟩
        · exact Or.inr (Or.inr ⟨rfl, hc⟩)

/-- U(T^q Z)=B^q Z as an ordinary union of exact image sets. -/
theorem scanImage_union_Z (q : Nat) (output : List Nat) :
    ScanImage 0 (List.replicate q .T ++ [.Z]) output ∨
      ScanImage 1 (List.replicate q .T ++ [.Z]) output ↔
        denotes (List.replicate q .B ++ [.Z]) output := by
  rw [scanImage_zero_Z, scanImage_one_exceptional q (Or.inl rfl)]
  constructor
  · rintro (hb | ho)
    · exact hb
    · exact ones_prefix_sub_binary q [.Z] ho
  · exact Or.inl

/-- U(T^q O)=U(T^q B)=B^(q+1); the union is not a sum of witnesses. -/
theorem scanImage_union_O_or_B (q : Nat) {factor : Factor}
    (hf : factor = .O ∨ factor = .B) (output : List Nat) :
    ScanImage 0 (List.replicate q .T ++ [factor]) output ∨
      ScanImage 1 (List.replicate q .T ++ [factor]) output ↔
        denotes (List.replicate (q+1) .B) output := by
  have hu : Unary factor := by rcases hf with rfl | rfl; exact Or.inr (Or.inl rfl); exact Or.inr (Or.inr (Or.inl rfl))
  have he : terminal factor = factor := by rcases hf with rfl | rfl <;> rfl
  rw [scanImage_zero_O_or_B q hf, scanImage_one_exceptional q hu, he]
  exact clause_union_ones_terminal q hf output

/-- U(T^(q+1))=B^(q+1). -/
theorem scanImage_union_T (q : Nat) (output : List Nat) :
    ScanImage 0 (List.replicate q .T ++ [.T]) output ∨
      ScanImage 1 (List.replicate q .T ++ [.T]) output ↔
        denotes (List.replicate (q+1) .B) output := by
  rw [scanImage_zero_T,
    scanImage_one_exceptional q (Or.inr (Or.inr (Or.inr rfl)))]
  constructor
  · rintro (hb | ho)
    · exact hb
    · exact ones_terminal_sub_binary q (Or.inr rfl) ho
  · exact Or.inl

#print axioms scanImage_one_exceptional
#print axioms scanImage_zero_Z
#print axioms scanImage_zero_O_or_B
#print axioms scanImage_zero_T
#print axioms scanImage_union_Z
#print axioms scanImage_union_O_or_B
#print axioms scanImage_union_T

end ExceptionalSuffix
end StackSorting.Generalized.Decorated
