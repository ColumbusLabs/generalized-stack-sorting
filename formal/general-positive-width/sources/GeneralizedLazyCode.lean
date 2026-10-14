import GeneralizedGeneratedDisplacement

/-! Literal lazy output codes. N b reads b labels INCLUDING the immediately
emitted new record, so b-1 remain held. H k emits the one-based kth held label.
Held labels are maintained in strictly increasing order, not physical stack order.
This file does not identify the code language with any finite-state recognizer. -/
namespace StackSorting.Generalized
namespace LazyCode
open List

inductive Letter where
  | N (batch : Nat)
  | H (rank : Nat)
  deriving DecidableEq, Repr

/-- Complete literal decoding. `next` is the first unread zero-based label;
`limit` is the first label after the complete increasing input. -/
inductive Decodes (limit : Nat) : Nat → List Nat → List Letter → List Nat → Prop where
  | nil : Decodes limit limit [] [] []
  | held {next a : Nat} {pre post : List Nat} {code : List Letter} {output : List Nat}
      (old : a < next)
      (tail : Decodes limit next (pre ++ post) code output) :
      Decodes limit next (pre ++ a :: post) (.H (pre.length+1) :: code) (a :: output)
  | record {next a : Nat} {held : List Nat} {code : List Letter} {output : List Nat}
      (new : next ≤ a)
      (tail : Decodes limit (a+1) (held ++ List.range' next (a-next)) code output) :
      Decodes limit next held (.N (a+1-next) :: code) (a :: output)

/-- The bounded code language, with literal transient push height `h+b`, not
just the post-output held height `h+b-1`. Ranks in H are one-based. -/
inductive Bounded (H : Nat) : Nat → List Letter → Prop where
  | nil : Bounded H 0 []
  | held {h k : Nat} {code : List Letter}
      (positive : 0 < k) (valid : k ≤ h) (tail : Bounded H (h-1) code) :
      Bounded H h (.H k :: code)
  | record {h b : Nat} {code : List Letter}
      (positive : 0 < b) (physical : h+b ≤ H) (tail : Bounded H (h+b-1) code) :
      Bounded H h (.N b :: code)

/-- Executable membership in the literal height-bounded code language. -/
def boundedCheck (H h : Nat) : List Letter → Bool
  | [] => h == 0
  | .H k :: code => decide (0 < k ∧ k ≤ h) && boundedCheck H (h-1) code
  | .N b :: code => decide (0 < b ∧ h+b ≤ H) && boundedCheck H (h+b-1) code

theorem boundedCheck_iff (H h : Nat) (code : List Letter) :
    boundedCheck H h code = true ↔ Bounded H h code := by
  induction code generalizing h with
  | nil =>
    constructor
    · intro hcheck
      have hz : h = 0 := by simpa [boundedCheck] using hcheck
      subst h
      exact .nil
    · intro hb
      cases hb
      rfl
  | cons letter code ih =>
    cases letter with
    | H k =>
      simp only [boundedCheck, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ⟨⟨hp, hv⟩, ht⟩; exact .held hp hv ht
      · intro hb; cases hb with | held hp hv ht => exact ⟨⟨hp, hv⟩, ht⟩
    | N b =>
      simp only [boundedCheck, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ⟨⟨hp, hv⟩, ht⟩; exact .record hp hv ht
      · intro hb; cases hb with | record hp hv ht => exact ⟨⟨hp, hv⟩, ht⟩

/-- Total encoder; malformed output words can produce invalid H ranks, which
are excluded by the proved Decodes relation below. -/
def encode (next : Nat) (held : List Nat) : List Nat → List Letter
  | [] => []
  | a :: output =>
    if a < next then .H (held.idxOf a+1) :: encode next (held.erase a) output
    else .N (a+1-next) :: encode (a+1) (held ++ List.range' next (a-next)) output

/-- Executable decoder; a complete word must finish with an empty held list. -/
def decode (next : Nat) (held : List Nat) : List Letter → Option (Nat × List Nat)
  | [] => if held = [] then some (next, []) else none
  | .N b :: code =>
    if 0 < b then do
      let (limit, output) ← decode (next+b) (held ++ List.range' next (b-1)) code
      pure (limit, (next+b-1) :: output)
    else none
  | .H k :: code =>
    if 0 < k then do
      let (after, a) ← removeAt? (k-1) held
      let (limit, output) ← decode next after code
      pure (limit, a :: output)
    else none

/-- The strict increasing-order invariant establishes that H is value rank,
not a physical stack position. -/
def HeldInvariant (next : Nat) (held : List Nat) : Prop :=
  held.Pairwise (· < ·) ∧ ∀ a ∈ held, a < next

theorem HeldInvariant.nodup {next : Nat} {held : List Nat} (h : HeldInvariant next held) :
    held.Nodup := h.1.imp Nat.ne_of_lt

theorem HeldInvariant.remove {next a : Nat} {pre post : List Nat}
    (h : HeldInvariant next (pre ++ a :: post)) : HeldInvariant next (pre ++ post) := by
  have hsub : pre ++ post <+ pre ++ a :: post := (List.Sublist.cons a (List.Sublist.refl post)).append_left pre
  exact ⟨h.1.sublist hsub, fun v hv => h.2 v (hsub.subset hv)⟩

theorem HeldInvariant.record {next a : Nat} {held : List Nat}
    (h : HeldInvariant next held) (ha : next ≤ a) :
    HeldInvariant (a+1) (held ++ List.range' next (a-next)) := by
  constructor
  · apply List.pairwise_append.mpr
    refine ⟨h.1, List.pairwise_lt_range', ?_⟩
    intro x hx y hy
    have := h.2 x hx
    have := (List.mem_range'_1.mp hy).1
    omega
  · intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · have := h.2 v hv; omega
    · have := List.mem_range'.mp hv; omega

theorem Decodes.length {limit next : Nat} {held output : List Nat} {code : List Letter}
    (h : Decodes limit next held code output) : code.length = output.length := by
  induction h <;> simp_all

theorem Decodes.decode_eq {limit next : Nat} {held output : List Nat} {code : List Letter}
    (h : Decodes limit next held code output) : decode next held code = some (limit, output) := by
  induction h with
  | nil => simp [decode]
  | @held next a pre post code output old tail ih =>
    simp [decode, removeAt_prefix, ih]
  | @record next a held code output new tail ih =>
    have hpos : 0 < a+1-next := by omega
    have hnext : next+(a+1-next) = a+1 := by omega
    have hsize : a+1-next-1 = a-next := by omega
    have hout : next+(a+1-next)-1 = a := by omega
    simp [decode, hpos, hnext, hsize, ih]

theorem Decodes.encode_eq {limit next : Nat} {held output : List Nat} {code : List Letter}
    (h : Decodes limit next held code output) (inv : HeldInvariant next held) :
    encode next held output = code := by
  induction h with
  | nil => rfl
  | @held next a pre post code output old tail ih =>
    have hn : a ∉ pre := by
      intro ha
      have hp := (List.nodup_append.mp inv.nodup).2.2
      exact hp a ha a (by simp) rfl
    have ht := ih inv.remove
    simp [encode, old, List.idxOf_append, hn, List.erase_append_right, ht]
  | @record next a held code output new tail ih =>
    simpa [encode, Nat.not_lt.mpr new] using ih (inv.record new)

theorem Decodes.unique_code {limit limit' next : Nat} {held output : List Nat} {a b : List Letter}
    (ha : Decodes limit next held a output) (hb : Decodes limit' next held b output)
    (inv : HeldInvariant next held) : a = b :=
  (ha.encode_eq inv).symm.trans (hb.encode_eq inv)

/-- An exact range split at the newly emitted record. -/
theorem range_split_at {next a limit : Nat} (hlo : next ≤ a) (hhi : a < limit) :
    List.range' next (limit-next) =
      List.range' next (a-next) ++ a :: List.range' (a+1) (limit-(a+1)) := by
  have hs : next + 1 * (a-next) = a := by omega
  have hc : a-next + (limit-a) = limit-next := by omega
  have hl : limit-a = (limit-(a+1))+1 := by omega
  have he := List.range'_append (s := next) (m := a-next) (n := limit-a) (step := 1)
  rw [hs, hc, hl, List.range'_succ] at he
  simpa using he.symm

/-- Literal decoding conserves exactly the unused increasing labels. In
particular, a complete code starting empty always yields a real permutation. -/
theorem Decodes.supply {limit next : Nat} {held output : List Nat} {code : List Letter}
    (h : Decodes limit next held code output) :
    next ≤ limit ∧ output.Perm (held ++ List.range' next (limit-next)) := by
  induction h with
  | nil => simp
  | @held next a pre post code output old tail ih =>
    refine ⟨ih.1, ?_⟩
    have hc := ih.2.cons a
    apply hc.trans
    simpa [List.append_assoc] using (List.perm_middle (l₁ := pre) (l₂ := post ++ List.range' next (limit-next)) (a := a)).symm
  | @record next a held code output new tail ih =>
    refine ⟨by omega, ?_⟩
    rw [range_split_at new (by omega : a < limit), ← List.append_assoc]
    exact (ih.2.cons a).trans List.perm_middle.symm

/-- A complete bounded word admits literal decoding. Bounds are checked from
its finite alphabet rules; no permutation or machine run is supplied. -/
theorem Bounded.decodes {H h next : Nat} {code : List Letter} {held : List Nat}
    (hb : Bounded H h code) (hlen : held.length = h) (inv : HeldInvariant next held) :
    ∃ limit output, Decodes limit next held code output := by
  induction hb generalizing next held with
  | nil =>
    have hh : held = [] := List.length_eq_zero_iff.mp hlen
    subst held
    exact ⟨next, [], .nil⟩
  | @held h k code positive valid tail ih =>
    have hidx : k-1 < held.length := by omega
    have he : held = held.take (k-1) ++ held[k-1] :: held.drop k := by
      have hk : k-1+1 = k := by omega
      have hs : held[k-1] :: held.drop k = held.drop (k-1) := by
        simpa only [hk] using List.getElem_cons_drop hidx
      rw [hs, List.take_append_drop]
    let pre := held.take (k-1)
    let post := held.drop k
    let a := held[k-1]
    have hex : held = pre ++ a :: post := he
    have hp : pre.length+1 = k := by
      simp only [pre, List.length_take, Nat.min_eq_left (Nat.le_of_lt hidx)]
      omega
    have ha : a < next := inv.2 a (List.getElem_mem hidx)
    have hl : (pre ++ post).length = h-1 := by
      rw [hex] at hlen
      simp only [List.length_append, List.length_cons] at hlen ⊢
      omega
    have hi : HeldInvariant next (pre ++ post) := by
      rw [hex] at inv
      exact inv.remove
    obtain ⟨limit, output, hd⟩ := ih hl hi
    refine ⟨limit, a :: output, ?_⟩
    rw [hex, ← hp]
    exact .held ha hd
  | @record h b code positive physical tail ih =>
    let a := next+b-1
    have new : next ≤ a := by dsimp [a]; omega
    have hl : (held ++ List.range' next (a-next)).length = h+b-1 := by
      simp only [List.length_append, List.length_range', hlen]
      dsimp [a]
      omega
    obtain ⟨limit, output, hd⟩ := ih hl (inv.record new)
    have hb : a+1-next = b := by dsimp [a]; omega
    exact ⟨limit, a :: output, by simpa only [hb] using Decodes.record new hd⟩

/-- All bounded words from height zero decode to distinct-entry permutations
of their own length, and the executable decoder agrees. -/
theorem bounded_word_permutation {H : Nat} {code : List Letter} (hb : Bounded H 0 code) :
    ∃ output, Decodes code.length 0 [] code output ∧
      output.Perm (List.range code.length) ∧
      decode 0 [] code = some (code.length, output) := by
  obtain ⟨limit, output, hd⟩ := hb.decodes (held := []) (next := 0) rfl (by simp [HeldInvariant])
  have hp : output.Perm (List.range limit) := by
    simpa [List.range_eq_range'] using hd.supply.2
  have hl : code.length = limit := by
    have := hp.length_eq
    have := hd.length
    simp_all
  subst limit
  exact ⟨output, hd, hp, hd.decode_eq⟩

theorem Bounded.held_tail {H h k : Nat} {code : List Letter}
    (hb : Bounded H h (.H k :: code)) : Bounded H (h-1) code := by
  cases hb with
  | held _ _ tail => exact tail

theorem Bounded.record_info {H h b : Nat} {code : List Letter}
    (hb : Bounded H h (.N b :: code)) : h+b ≤ H ∧ Bounded H (h+b-1) code := by
  cases hb with
  | record _ physical tail => exact ⟨physical, tail⟩

/-- Read the bound back from a literal decoding. This proves the physical
code convention enforces the displacement inequality on actual output values. -/
theorem Decodes.output_bound {H limit next consumed : Nat} {held output : List Nat}
    {code : List Letter} (hd : Decodes limit next held code output)
    (hb : Bounded H held.length code) (inv : HeldInvariant next held)
    (balance : consumed+held.length = next) (height : held.length ≤ H) :
    ∀ pre a post, output = pre ++ a :: post → a+1 ≤ consumed+pre.length+H := by
  induction hd generalizing consumed with
  | nil => intro pre a post he; simp at he
  | @held next a pre post code output old tail ih =>
    have hb' : Bounded H (pre ++ post).length code := by
      simpa [List.length_append, List.length_cons, Nat.add_assoc] using hb.held_tail
    have bal' : consumed+1+(pre ++ post).length = next := by
      simp only [List.length_append, List.length_cons] at balance ⊢
      omega
    have height' : (pre ++ post).length ≤ H := by
      simp only [List.length_append, List.length_cons] at height ⊢
      omega
    have ht := ih hb' inv.remove bal' height'
    intro pref v suffix he
    cases pref with
    | nil =>
      have hv : a = v := (List.cons.inj he).1
      simp only [List.length_nil, Nat.add_zero]
      omega
    | cons x pref =>
      have hh : output = pref ++ v :: suffix := (List.cons.inj he).2
      have hh' := ht pref v suffix hh
      simp only [List.length_cons]
      omega
  | @record next a held code output new tail ih =>
    obtain ⟨physical, htail⟩ := hb.record_info
    have hsize : held.length+(a+1-next)-1 = (held ++ List.range' next (a-next)).length := by
      simp only [List.length_append, List.length_range']
      omega
    have hb' : Bounded H (held ++ List.range' next (a-next)).length code := by
      simpa only [hsize] using htail
    have bal' : consumed+1+(held ++ List.range' next (a-next)).length = a+1 := by
      simp only [List.length_append, List.length_range']
      omega
    have height' : (held ++ List.range' next (a-next)).length ≤ H := by omega
    have ht := ih hb' (inv.record new) bal' height'
    intro pref v suffix he
    cases pref with
    | nil =>
      have hv : a = v := (List.cons.inj he).1
      simp only [List.length_nil, Nat.add_zero]
      omega
    | cons x pref =>
      have hh : output = pref ++ v :: suffix := (List.cons.inj he).2
      have hh' := ht pref v suffix hh
      simp only [List.length_cons]
      omega

/-- Construct the unique lazy code from actual pending labels. The only width
premise is the literal output-value/position inequality. -/
theorem exists_bounded_code {H limit next consumed : Nat} {held output : List Nat}
    (hp : output.Perm (held ++ List.range' next (limit-next)))
    (hn : next ≤ limit) (inv : HeldInvariant next held)
    (balance : consumed + held.length = next)
    (bound : ∀ pre a post, output = pre ++ a :: post → a+1 ≤ consumed+pre.length+H) :
    ∃ code, Decodes limit next held code output ∧ Bounded H held.length code := by
  induction output generalizing next consumed held with
  | nil =>
    have he : held ++ List.range' next (limit-next) = [] := List.nil_perm.mp hp
    have hl := congrArg List.length he
    simp only [List.length_append, List.length_range', List.length_nil] at hl
    have hh : held = [] := List.length_eq_zero_iff.mp (by omega)
    have hn' : next = limit := by omega
    subst held; subst next
    exact ⟨[], .nil, .nil⟩
  | cons a output ih =>
    have ha : a ∈ held ++ List.range' next (limit-next) := hp.mem_iff.mp (by simp)
    have bound' : ∀ pre v post, output = pre ++ v :: post →
        v+1 ≤ (consumed+1)+pre.length+H := by
      intro pre v post he
      have hb := bound (a :: pre) v post (by simp [he])
      simp only [List.length_cons] at hb
      omega
    by_cases old : a < next
    · have hm : a ∈ held := by
        rcases List.mem_append.mp ha with hm | hm
        · exact hm
        · have := List.mem_range'_1.mp hm; omega
      obtain ⟨pre, post, rfl⟩ := List.append_of_mem hm
      have hp' : output.Perm ((pre ++ post) ++ List.range' next (limit-next)) := by
        apply List.Perm.cons_inv (a := a)
        apply hp.trans
        simp [List.append_assoc]
      have bal' : consumed+1+(pre ++ post).length = next := by
        simp only [List.length_append, List.length_cons] at balance ⊢
        omega
      obtain ⟨code, hd, hb⟩ := ih hp' hn inv.remove bal' bound'
      refine ⟨.H (pre.length+1) :: code, .held old hd, ?_⟩
      apply Bounded.held (by omega) (by simp)
      simpa [List.length_append, List.length_cons, Nat.add_assoc] using hb
    · have new : next ≤ a := Nat.le_of_not_gt old
      have upper : a < limit := by
        rcases List.mem_append.mp ha with hm | hm
        · have := inv.2 a hm; omega
        · have := List.mem_range'_1.mp hm; omega
      have split := range_split_at new upper
      have hp' : output.Perm
          ((held ++ List.range' next (a-next)) ++ List.range' (a+1) (limit-(a+1))) := by
        apply List.Perm.cons_inv (a := a)
        rw [split, ← List.append_assoc] at hp
        exact hp.trans List.perm_middle
      have bal' : consumed+1+(held ++ List.range' next (a-next)).length = a+1 := by
        simp only [List.length_append, List.length_range']
        omega
      obtain ⟨code, hd, hb⟩ := ih hp' (by omega) (inv.record new) bal' bound'
      refine ⟨.N (a+1-next) :: code, .record new hd, ?_⟩
      have hfirst := bound [] a output (by simp)
      simp only [List.length_nil, Nat.add_zero] at hfirst
      apply Bounded.record (by omega) (by omega)
      have he : held.length + (a+1-next) - 1 = (held ++ List.range' next (a-next)).length := by
        simp only [List.length_append, List.length_range']
        omega
      simpa only [he] using hb

/-- Every actual permutation satisfying the displacement bound has a unique
complete bounded lazy code. No automaton-recognition equivalence is assumed. -/
theorem permutation_unique_bounded_code {H n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n))
    (bound : ∀ pre a post, output = pre ++ a :: post → a+1 ≤ pre.length+H) :
    ∃ code, Decodes n 0 [] code output ∧ Bounded H 0 code ∧
      (∀ other, Decodes n 0 [] other output → other = code) ∧
      decode 0 [] code = some (n, output) ∧ code.length = output.length := by
  have hp' : output.Perm ([] ++ List.range' 0 (n-0)) := by
    simpa [List.range_eq_range'] using hp
  have inv : HeldInvariant 0 [] := by simp [HeldInvariant]
  obtain ⟨code, hd, hb⟩ := exists_bounded_code (consumed := 0) hp' (by omega) inv (by simp)
    (by simpa using bound)
  exact ⟨code, hd, hb, fun other ho => ho.unique_code hd inv, hd.decode_eq, hd.length⟩

/-- Exact bounded-code characterization of actual permutations. This is the
input-language bridge only, not recognition of machine membership or basis. -/
theorem permutation_bounded_code_iff {H n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) :
    (∃ code, Decodes n 0 [] code output ∧ Bounded H 0 code) ↔
      ∀ pre a post, output = pre ++ a :: post → a+1 ≤ pre.length+H := by
  constructor
  · rintro ⟨code, hd, hb⟩
    simpa using hd.output_bound (consumed := 0) hb (by simp [HeldInvariant])
      (by simp) (by simp)
  · intro h
    obtain ⟨code, hd, hb, _⟩ := permutation_unique_bounded_code hp h
    exact ⟨code, hd, hb⟩

/-- All ordinary generated-output minimal obstructions enter the bounded lazy
code language. For N_b, the b includes the transient record token. -/
theorem oneDeletionMinimal_unique_bounded_code {r s n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hr : 0 < r) (hs : 0 < s)
    (hreject : ¬ Run r s [] (List.range n) output [])
    (hdelete : ∀ v ∈ List.range n,
      Run r s [] (List.range (n-1)) (deleteWord v output) []) :
    ∃ code, Decodes n 0 [] code output ∧ Bounded (2*max r s+1) 0 code ∧
      (∀ other, Decodes n 0 [] other output → other = code) ∧
      decode 0 [] code = some (n, output) ∧ code.length = output.length := by
  apply permutation_unique_bounded_code hp
  intro pre a post he
  have hd := oneDeletionMinimal_output_displacement hp hr hs hreject hdelete he
  omega

theorem three_three_minimal_unique_width_seven_code {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n))
    (hreject : ¬ Run 3 3 [] (List.range n) output [])
    (hdelete : ∀ v ∈ List.range n,
      Run 3 3 [] (List.range (n-1)) (deleteWord v output) []) :
    ∃ code, Decodes n 0 [] code output ∧ Bounded 7 0 code ∧
      (∀ other, Decodes n 0 [] other output → other = code) ∧
      decode 0 [] code = some (n, output) ∧ code.length = output.length := by
  simpa using oneDeletionMinimal_unique_bounded_code hp (by decide : 0 < 3)
    (by decide : 0 < 3) hreject hdelete

#print axioms boundedCheck_iff
#print axioms Decodes.decode_eq
#print axioms Decodes.encode_eq
#print axioms Decodes.unique_code
#print axioms Decodes.supply
#print axioms Bounded.decodes
#print axioms bounded_word_permutation
#print axioms Decodes.output_bound
#print axioms permutation_bounded_code_iff
#print axioms exists_bounded_code
#print axioms permutation_unique_bounded_code
#print axioms oneDeletionMinimal_unique_bounded_code
#print axioms three_three_minimal_unique_width_seven_code
end LazyCode
end StackSorting.Generalized
