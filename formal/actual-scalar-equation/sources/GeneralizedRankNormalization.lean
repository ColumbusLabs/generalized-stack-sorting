import GeneralizedCodeRecognition

/-! Exact one-based physical-order quotient of the labelled code recognizer.
The normalization uses positions in the increasing held-label list. Pushes
insert the new largest rank and pops delete a rank and close its gap.
This does not certify annotation shadows, reachable DFA IDs, or minimization. -/
namespace StackSorting.Generalized
namespace LazyCode
open List

/-- One-based value rank. Only members of `held` are semantically used. -/
def valueRank (held : List Nat) (a : Nat) : Nat := held.idxOf a + 1

/-- Physical order is retained; only the names of its tokens change. -/
def normalize (held physical : List Nat) : List Nat := physical.map (valueRank held)

/-- Close the gap left after deleting the one-based value rank `k`. -/
def closeRank (k v : Nat) : Nat := if k < v then v-1 else v

/-- The normalized held transition used by the Python order-subset recognizer. -/
def rankPopOrders (s k : Nat) (physical : List Nat) : List (List Nat) :=
  (popOrders s k physical).map (List.map (closeRank k))

/-- Repeated pushes always introduce the next largest currently held rank. -/
def rankReadOrders (r : Nat) : Nat → Nat → List Nat → List (List Nat)
  | _, 0, physical => [physical]
  | h, n+1, physical => (pushOrders r (h+1) physical).flatMap (rankReadOrders r (h+1) n)

theorem valueRank_inj {held : List Nat} {a b : Nat}
    (ha : a ∈ held) (hb : b ∈ held) (he : valueRank held a = valueRank held b) : a = b := by
  have hi : held.idxOf a = held.idxOf b := by simpa [valueRank] using he
  have hia := List.idxOf_lt_length_of_mem ha
  have hib := List.idxOf_lt_length_of_mem hb
  calc
    a = held[held.idxOf a] := (List.getElem_idxOf hia).symm
    _ = held[held.idxOf b] := by simp only [hi]
    _ = b := List.getElem_idxOf hib

theorem valueRank_append_old {held extra : List Nat} {a : Nat} (ha : a ∈ held) :
    valueRank (held ++ extra) a = valueRank held a := by
  simp [valueRank, List.idxOf_append, ha]

theorem valueRank_append_new {held : List Nat} {a : Nat} (ha : a ∉ held) :
    valueRank (held ++ [a]) a = held.length+1 := by
  simp [valueRank, List.idxOf_append, ha]

theorem normalize_append_old {held extra physical : List Nat} (hp : physical ⊆ held) :
    normalize (held ++ extra) physical = normalize held physical := by
  apply List.map_congr_left
  intro a ha
  exact valueRank_append_old (hp ha)

/-- Normalizing the sorted duplicate-free label dictionary yields exactly
1, ..., h, rather than merely some list of bounded integers. -/
theorem normalize_self {held : List Nat} (hn : held.Nodup) :
    normalize held held = List.range' 1 held.length := by
  induction held with
  | nil => rfl
  | cons a held ih =>
    have hn' := List.nodup_cons.mp hn
    have hm : held.map (valueRank (a :: held)) = (normalize held held).map (· + 1) := by
      simp only [normalize, List.map_map]
      apply List.map_congr_left
      intro x hx
      have hax : a ≠ x := by intro he; subst x; exact hn'.1 hx
      simp [valueRank, List.idxOf_cons, hax]
    simp only [normalize, List.map_cons, valueRank, List.idxOf_cons_self]
    change 1 :: held.map (valueRank (a :: held)) = List.range' 1 (held.length+1)
    rw [hm, ih hn'.2, ← List.range'_succ_left]
    rfl

/-- Every valid physical order is mapped to a permutation of exactly 1..h.
Thus at bounded held height the label quotient has a finite order universe. -/
theorem normalize_perm {held physical : List Nat}
    (hn : held.Nodup) (hp : physical.Perm held) :
    (normalize held physical).Perm (List.range' 1 held.length) := by
  have hh := hp.map (valueRank held)
  rw [← normalize_self hn]
  exact hh

/-- Within a fixed label dictionary no two different physical orders collapse.
The quotient forgets absolute labels but does not forget stack order. -/
theorem normalize_inj {held xs ys : List Nat} (hx : xs ⊆ held) (hy : ys ⊆ held)
    (he : normalize held xs = normalize held ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => simpa [normalize] using he.symm
  | cons a xs ih =>
    cases ys with
    | nil => simp [normalize] at he
    | cons b ys =>
      have hh := List.cons.inj (show valueRank held a :: normalize held xs =
          valueRank held b :: normalize held ys from he)
      have hab := valueRank_inj (hx (by simp)) (hy (by simp)) hh.1
      subst b
      exact congrArg (a :: ·) (ih (fun x h => hx (by simp [h]))
        (fun x h => hy (by simp [h])) hh.2)

/-- Arbitrary relabelling transports every push and reflects every possible
physical insertion, even if the relabelling is not globally injective. -/
theorem pushOrders_map_iff {r a : Nat} {physical target : List Nat} (f : Nat → Nat) :
    target ∈ pushOrders r (f a) (physical.map f) ↔
      ∃ after, after ∈ pushOrders r a physical ∧ target = after.map f := by
  simp only [mem_pushOrders_iff (s := 0)]
  constructor
  · intro h
    generalize he : physical.map f = held at h
    cases h with
    | push pre post x allowed =>
      obtain ⟨as, bs, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp he
      exact ⟨as ++ a :: bs, Step.push as bs a (by simpa using allowed), by simp⟩
  · rintro ⟨after, h, rfl⟩
    simpa using h.map f

/-- Pop reflection needs injectivity only on the actual held-label support. -/
theorem popOrders_map_iff {s a : Nat} {physical target : List Nat} (f : Nat → Nat)
    (faithful : ∀ x ∈ physical, f x = f a → x = a) :
    target ∈ popOrders s (f a) (physical.map f) ↔
      ∃ after, after ∈ popOrders s a physical ∧ target = after.map f := by
  simp only [mem_popOrders_iff (r := 0)]
  constructor
  · intro h
    generalize he : physical.map f = held at h
    cases h with
    | pop pre post x allowed =>
      obtain ⟨as, bs, hx, hpre, hpost⟩ := List.map_eq_append_iff.mp he
      obtain ⟨x, xs, hbs, hxa, hxs⟩ := List.map_eq_cons_iff.mp hpost
      have hxa' : x = a := faithful x (by simp [hx, hbs]) hxa
      subst x
      subst bs
      subst physical
      subst pre
      subst post
      exact ⟨as ++ xs, Step.pop as xs a (by simpa using allowed), by simp⟩
  · rintro ⟨after, h, rfl⟩
    simpa using h.map f

/-- One push is exactly insertion of h+1 after normalization, for arbitrary
labels and every push width. The physical insertion slot is unchanged. -/
theorem normalize_push_iff {r a : Nat} {held physical target : List Nat}
    (hp : physical.Perm held) (fresh : a ∉ held) :
    target ∈ pushOrders r (held.length+1) (normalize held physical) ↔
      ∃ after, after ∈ pushOrders r a physical ∧ target = normalize (held ++ [a]) after := by
  rw [← valueRank_append_new fresh, ← normalize_append_old (extra := [a]) hp.subset]
  exact pushOrders_map_iff (valueRank (held ++ [a]))

/-- Deleting the kth held label leaves lower ranks unchanged and subtracts
one from every higher rank. This is derived from list positions. -/
theorem valueRank_remove {pre post : List Nat} {a x : Nat}
    (hn : (pre ++ a :: post).Nodup) (hx : x ∈ pre ++ post) :
    valueRank (pre ++ post) x = closeRank (pre.length+1) (valueRank (pre ++ a :: post) x) := by
  have hna : a ∉ pre := by
    intro ha
    exact (List.nodup_append.mp hn).2.2 a ha a (by simp) rfl
  by_cases hp : x ∈ pre
  · have hi := List.idxOf_lt_length_of_mem hp
    simp only [valueRank, List.idxOf_append, hp, ite_true, closeRank]
    split <;> omega
  · have hpost : x ∈ post := (List.mem_append.mp hx).resolve_left hp
    have hax : a ≠ x := by
      intro he
      subst x
      exact (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1 hpost
    simp only [valueRank, List.idxOf_append, hp, ite_false, List.idxOf_cons,
      beq_eq_false_iff_ne.mpr hax, Bool.false_eq_true, ite_false, closeRank]
    split <;> omega

/-- H_k quotient transition: every normalized successor comes from a literal
labelled pop, and every literal pop has exactly the stated normalized order. -/
theorem normalize_pop_iff {s a : Nat} {pre post physical target : List Nat}
    (hn : (pre ++ a :: post).Nodup) (hp : physical.Perm (pre ++ a :: post)) :
    target ∈ rankPopOrders s (pre.length+1) (normalize (pre ++ a :: post) physical) ↔
      ∃ after, after ∈ popOrders s a physical ∧ target = normalize (pre ++ post) after := by
  have hna : a ∉ pre := by
    intro ha
    exact (List.nodup_append.mp hn).2.2 a ha a (by simp) rfl
  have ha : valueRank (pre ++ a :: post) a = pre.length+1 := by
    simp [valueRank, List.idxOf_append, hna]
  have faithful : ∀ x ∈ physical,
      valueRank (pre ++ a :: post) x = valueRank (pre ++ a :: post) a → x = a := by
    intro x hx he
    exact valueRank_inj (hp.mem_iff.mp hx) (by simp) he
  simp only [rankPopOrders, List.mem_map]
  constructor
  · rintro ⟨middle, hm, rfl⟩
    rw [← ha] at hm
    obtain ⟨after, hafter, rfl⟩ := (popOrders_map_iff _ faithful).mp hm
    refine ⟨after, hafter, ?_⟩
    have hs := (pop_remaining_perm hp ((mem_popOrders_iff (r := 0)).mp hafter)).subset
    simp only [normalize, List.map_map]
    apply List.map_congr_left
    intro x hx
    exact (valueRank_remove hn (hs hx)).symm
  · rintro ⟨after, hafter, rfl⟩
    refine ⟨normalize (pre ++ a :: post) after, ?_, ?_⟩
    · rw [← ha]
      exact (popOrders_map_iff _ faithful).mpr ⟨after, hafter, rfl⟩
    · have hs := (pop_remaining_perm hp ((mem_popOrders_iff (r := 0)).mp hafter)).subset
      simp only [normalize, List.map_map]
      apply List.map_congr_left
      intro x hx
      exact (valueRank_remove hn (hs hx)).symm

/-- The N_b shortcut uses b-1 largest-rank pushes. This theorem handles
arbitrary fresh input words; it is not restricted to one batch size or height. -/
theorem normalize_read_iff {r : Nat} {held input physical target : List Nat}
    (hp : physical.Perm held) (hn : (held ++ input).Nodup) :
    target ∈ rankReadOrders r held.length input.length (normalize held physical) ↔
      ∃ after, after ∈ readOrders r input physical ∧ target = normalize (held ++ input) after := by
  induction input generalizing held physical with
  | nil => simp [rankReadOrders, readOrders]
  | cons a input ih =>
    have fresh : a ∉ held := by
      intro ha
      exact (List.nodup_append.mp hn).2.2 a ha a (by simp) rfl
    have hn' : ((held ++ [a]) ++ input).Nodup := by simpa using hn
    have afterPerm {middle : List Nat} (hm : middle ∈ pushOrders r a physical) :
        middle.Perm (held ++ [a]) := by
      have hs := ((mem_pushOrders_iff (s := 0)).mp hm).supply
      simpa using hs.symm.trans (hp.append_right [a])
    simp only [List.length_cons, rankReadOrders, List.mem_flatMap]
    constructor
    · rintro ⟨middleRank, hm, ht⟩
      obtain ⟨middle, hmiddle, rfl⟩ := (normalize_push_iff hp fresh).mp hm
      have ht' : target ∈ rankReadOrders r (held ++ [a]).length input.length
          (normalize (held ++ [a]) middle) := by simpa using ht
      obtain ⟨after, haf, he⟩ := (ih (afterPerm hmiddle) hn').mp ht'
      exact ⟨after, List.mem_flatMap.mpr ⟨middle, hmiddle, haf⟩, by simpa using he⟩
    · rintro ⟨after, haf, he⟩
      obtain ⟨middle, hmiddle, haf⟩ := List.mem_flatMap.mp haf
      refine ⟨normalize (held ++ [a]) middle, (normalize_push_iff hp fresh).mpr ⟨middle, hmiddle, rfl⟩, ?_⟩
      have ht := (ih (afterPerm hmiddle) hn').mpr ⟨after, haf, by simpa using he⟩
      simpa using ht

/-- Label-free executable physical-order recognizer. Its local transitions
are exactly largest-rank insertion and rank deletion with gap closure. The
finite list represents a set by membership; duplicate entries do not matter. -/
def rankCodeOrders (r s : Nat) : Nat → List Letter → List Nat → List (List Nat)
  | _, [], physical => [physical]
  | h, .N b :: code, physical =>
    if 0 < b then
      (rankReadOrders r h (b-1) physical).flatMap (rankCodeOrders r s (h+b-1) code)
    else []
  | h, .H k :: code, physical =>
    if 0 < k then
      (rankPopOrders s k physical).flatMap (rankCodeOrders r s (h-1) code)
    else []

/-- Full all-length quotient theorem for every complete valid lazy code.
The original labels are eliminated by proved transport, not a presumed equality
between the labelled recognizer and a serialized automaton. -/
theorem Decodes.rankCodeOrders_iff {r s limit next : Nat}
    {held output physical : List Nat} {code : List Letter}
    (hd : Decodes limit next held code output)
    (inv : HeldInvariant next held) (hp : physical.Perm held) :
    [] ∈ rankCodeOrders r s held.length code (normalize held physical) ↔
      [] ∈ codeOrders r s next held code physical := by
  induction hd generalizing physical with
  | nil =>
    have he : physical = [] := List.perm_nil.mp hp
    subst physical
    simp [rankCodeOrders, codeOrders, normalize]
  | @held next a pre post code output old tail ih =>
    have hlen : (pre ++ a :: post).length-1 = (pre ++ post).length := by simp_all <;> omega
    simp only [rankCodeOrders, Nat.zero_lt_succ, ite_true, hlen, List.mem_flatMap]
    rw [held_code_step]
    constructor
    · rintro ⟨middleRank, hm, ht⟩
      obtain ⟨middle, hmiddle, rfl⟩ := (normalize_pop_iff inv.nodup hp).mp hm
      have pop := (mem_popOrders_iff (r := r)).mp hmiddle
      exact ⟨middle, pop, (ih inv.remove (pop_remaining_perm hp pop)).mp ht⟩
    · rintro ⟨middle, pop, ht⟩
      refine ⟨normalize (pre ++ post) middle, ?_, (ih inv.remove (pop_remaining_perm hp pop)).mpr ht⟩
      exact (normalize_pop_iff inv.nodup hp).mpr ⟨middle, mem_popOrders_iff.mpr pop, rfl⟩
  | @record next a held code output new tail ih =>
    have positive : 0 < a+1-next := by omega
    have hnext : next+(a+1-next) = a+1 := by omega
    have hcount : a+1-next-1 = a-next := by omega
    have hlen : held.length+(a+1-next)-1 = (held ++ List.range' next (a-next)).length := by simp_all <;> omega
    have inv' := inv.record new
    have afterPerm {middle : List Nat}
        (hm : middle ∈ readOrders r (List.range' next (a-next)) physical) :
        middle.Perm (held ++ List.range' next (a-next)) := by
      have hs := ((mem_readOrders_iff (s := s)).mp hm).supply
      simpa using hs.symm.trans (hp.append_right _)
    simp only [rankCodeOrders, codeOrders, positive, ite_true, hcount, hnext, hlen, List.mem_flatMap]
    constructor
    · rintro ⟨middleRank, hm, ht⟩
      have hm' : middleRank ∈ rankReadOrders r held.length (List.range' next (a-next)).length
          (normalize held physical) := by simpa using hm
      obtain ⟨middle, hmiddle, rfl⟩ := (normalize_read_iff hp inv'.nodup).mp hm'
      exact ⟨middle, hmiddle, (ih inv' (afterPerm hmiddle)).mp ht⟩
    · rintro ⟨middle, hmiddle, ht⟩
      refine ⟨normalize (held ++ List.range' next (a-next)) middle, ?_, (ih inv' (afterPerm hmiddle)).mpr ht⟩
      have hm := (normalize_read_iff hp inv'.nodup).mpr ⟨middle, hmiddle, rfl⟩
      simpa using hm

/-- The normalized physical-order recognizer accepts exactly actual machine
generation, at every length and every positive pair of push/pop widths. -/
theorem Decodes.rankCodeOrders_iff_generated {r s n : Nat}
    {output : List Nat} {code : List Letter}
    (hd : Decodes n 0 [] code output) (hr : 0 < r) (hs : 0 < s) :
    [] ∈ rankCodeOrders r s 0 code [] ↔ Run r s [] (List.range n) output [] :=
  (hd.rankCodeOrders_iff (r := r) (s := s) (by simp [HeldInvariant]) (List.Perm.refl [])).trans
    (hd.codeOrders_iff_generated hr hs)

/-- Executable acceptance from the empty one-based rank order. -/
def rankRecognizes (r s : Nat) (code : List Letter) : Bool :=
  (rankCodeOrders r s 0 code []).contains []

theorem Decodes.rankRecognizes_iff {r s n : Nat}
    {output : List Nat} {code : List Letter}
    (hd : Decodes n 0 [] code output) (hr : 0 < r) (hs : 0 < s) :
    rankRecognizes r s code = true ↔ Run r s [] (List.range n) output [] := by
  simpa only [rankRecognizes, List.contains_iff_mem] using hd.rankCodeOrders_iff_generated hr hs

/-- Canonical encoding of every actual permutation is recognized exactly by
the label-free recognizer. No caller-supplied machine acceptance premise. -/
theorem permutation_rankRecognizes_iff {r s n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hr : 0 < r) (hs : 0 < s) :
    rankRecognizes r s (encode 0 [] output) = true ↔ Run r s [] (List.range n) output [] := by
  have bound : ∀ pre a post, output = pre ++ a :: post → a+1 ≤ pre.length+n := by
    intro pre a post he
    have ha : a ∈ output := by simp [he]
    have hlt := List.mem_range.mp (hp.mem_iff.mp ha)
    omega
  obtain ⟨code, hd, _, _⟩ := permutation_unique_bounded_code hp bound
  rw [hd.encode_eq (by simp [HeldInvariant])]
  exact hd.rankRecognizes_iff hr hs

#print axioms valueRank_inj
#print axioms normalize_self
#print axioms normalize_perm
#print axioms normalize_inj
#print axioms pushOrders_map_iff
#print axioms popOrders_map_iff
#print axioms normalize_push_iff
#print axioms valueRank_remove
#print axioms normalize_pop_iff
#print axioms normalize_read_iff
#print axioms Decodes.rankCodeOrders_iff
#print axioms Decodes.rankCodeOrders_iff_generated
#print axioms Decodes.rankRecognizes_iff
#print axioms permutation_rankRecognizes_iff

end LazyCode
end StackSorting.Generalized
