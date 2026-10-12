import GeneralizedShadowMerging
import GeneralizedRankNormalization
import GeneralizedShadowPrefix

/-! Per-deletion-ID recognizer-state composition. The table is explicit;
no serialized table coverage, pruning, or finite-closure claim is made. -/
namespace StackSorting.Generalized
namespace LazyCode
namespace Shadow
namespace Merging
namespace Recognition
open List

/-- Literal deterministic recognizer execution, with an absorbing rejection. -/
def recognizeFrom (δ : Table) : Option Nat → List Letter → Option Nat
  | q, [] => q
  | q, l :: ls => recognizeFrom δ (q.bind (fun x => δ x l)) ls

theorem recognizeFrom_append (δ : Table) (q : Option Nat) (xs ys : List Letter) :
    recognizeFrom δ q (xs ++ ys) = recognizeFrom δ (recognizeFrom δ q xs) ys := by
  induction xs generalizing q with
  | nil => rfl
  | cons x xs ih => exact ih _

structure Fixed where
  next : Nat
  cells : List Nat
  q : Option Nat
  deriving DecidableEq, Repr

def advance (δ : Table) (q : Option Nat) (emitted : Option Letter) : Option Nat :=
  match emitted with
  | none => q
  | some l => q.bind (fun x => δ x l)

def fixedUpdate (δ : Table) (next index : Nat) (cells : List Nat) (q : Option Nat) : Option Fixed := do
  let (emitted, after) ← updateAt cells index
  pure ⟨next, after, advance δ q emitted⟩

/-- Full fixed-value stream, including its virtual pre-birth segment. Unlike
updatePair this records a rejecting q instead of aborting, and has no height
assertion. Successful actual builder copies are proved to agree with it. -/
def fixedStep (δ : Table) (v : Nat) (st : Fixed) : Letter → Option Fixed
  | .H k => if 0 < k then fixedUpdate δ st.next (k-1) st.cells st.q else none
  | .N b => if 0 < b then fixedUpdate δ (st.next+b) (st.cells.length+b-1)
      (st.cells ++ arrivalTags v st.next b) st.q else none

def fixedRun (δ : Table) (v : Nat) : Fixed → List Letter → Option Fixed
  | st, [] => some st
  | st, l :: ls => (fixedStep δ v st l).bind (fun after => fixedRun δ v after ls)

theorem fixedRun_append (δ : Table) (v : Nat) (st : Fixed) (xs ys : List Letter) :
    fixedRun δ v st (xs ++ ys) =
      (fixedRun δ v st xs).bind (fun mid => fixedRun δ v mid ys) := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, fixedRun]
    cases h : fixedStep δ v st x <;> simp [ih]

/-- A fixed stream's final q is exactly execution on its emitted word. -/
theorem fixedRun_semantics (δ : Table) (v : Nat) {st after : Fixed} {code : List Letter}
    (h : fixedRun δ v st code = some after) :
    ∃ emitted, transduceTags v st.next st.cells code = some emitted ∧
      recognizeFrom δ st.q emitted = after.q := by
  induction code generalizing st with
  | nil => cases h; exact ⟨[], rfl, rfl⟩
  | cons l code ih =>
    cases hs : fixedStep δ v st l with
    | none => simp [fixedRun, hs] at h
    | some mid =>
      have ht : fixedRun δ v mid code = some after := by simpa [fixedRun, hs] using h
      obtain ⟨emitted, he, hq⟩ := ih ht
      cases l with
      | H k =>
        simp only [fixedStep] at hs
        split at hs
        next positive =>
          unfold fixedUpdate at hs
          cases hu : updateAt st.cells (k-1) with
          | none => simp [hu] at hs
          | some p =>
            simp [hu] at hs
            subst mid
            refine ⟨p.1.toList ++ emitted, ?_, ?_⟩
            · simp [transduceTags, positive, hu, he]
            · rw [recognizeFrom_append]
              cases hp : p.1 <;> simpa [advance, recognizeFrom, hp] using hq
        next => contradiction
      | N b =>
        simp only [fixedStep] at hs
        split at hs
        next positive =>
          unfold fixedUpdate at hs
          cases hu : updateAt (st.cells ++ arrivalTags v st.next b) (st.cells.length+b-1) with
          | none => simp [hu] at hs
          | some p =>
            simp [hu] at hs
            subst mid
            refine ⟨p.1.toList ++ emitted, ?_, ?_⟩
            · simp [transduceTags, positive, hu, he]
            · rw [recognizeFrom_append]
              cases hp : p.1 <;> simpa [advance, recognizeFrom, hp] using hq
        next => contradiction

theorem updateAt_length {cells after : List Nat} {index : Nat} {emitted : Option Letter}
    (h : updateAt cells index = some (emitted, after)) : after.length = cells.length-1 := by
  unfold updateAt at h
  cases hs : cells[index]? with
  | none => simp [hs] at h
  | some selected =>
    have hi : index < cells.length := List.getElem?_eq_some_iff.mp hs |>.1
    simp [hs] at h
    have he := congrArg (fun p : Option Letter × List Nat => p.2.length) h
    simp only [updateTags] at he
    split at he <;> (try split at he) <;>
      simp only [List.length_append, List.length_take, List.length_drop, List.length_map] at he <;>
      omega

theorem updatePair_fixed (δ : Table) (height : Nat → Nat) (next index : Nat)
    {sh out : Pair} (h : updatePair δ height index sh = some out) :
    fixedUpdate δ next index sh.1 (some sh.2) = some ⟨next, out.1, some out.2⟩ ∧
      out.1.length = sh.1.length-1 := by
  unfold updatePair at h
  cases hu : updateAt sh.1 index with
  | none => simp [hu] at h
  | some p =>
    rcases p with ⟨emitted, cells⟩
    simp [hu] at h
    have hl := updateAt_length hu
    cases emitted with
    | none =>
      change (if _ then some _ else none) = some out at h
      split at h
      · cases h; exact ⟨by simp [fixedUpdate, hu, advance], hl⟩
      · contradiction
    | some l =>
      cases hq : δ sh.2 l with
      | none => simp [hq] at h
      | some q =>
        simp [hq] at h
        obtain ⟨_, rfl⟩ := h
        exact ⟨by simp [fixedUpdate, hu, advance, hq], hl⟩

theorem collect_output (f : α → Option β) {xs : List α} {ys : List β}
    (h : collect f xs = some ys) {y : β} (hy : y ∈ ys) :
    ∃ x ∈ xs, f x = some y := by
  unfold collect at h
  split at h
  · cases h; exact List.mem_filterMap.mp hy
  · contradiction

theorem collect_input (f : α → Option β) {xs : List α} {ys : List β}
    (h : collect f xs = some ys) {x : α} (hx : x ∈ xs) :
    ∃ y ∈ ys, f x = some y := by
  unfold collect at h
  split at h
  next ha =>
    have hf := List.all_eq_true.mp ha x hx
    cases he : f x with
    | none => simp [he] at hf
    | some y =>
      cases h
      exact ⟨y, List.mem_filterMap.mpr ⟨x, hx, he⟩, rfl⟩
  next => contradiction

def Lengths (st : IndexedState) : Prop :=
  ∀ entry ∈ st.shadows, entry.2.1.length = st.original.height

/-- A full fixed-value stream agrees with its unique born copy, or with the
shared original pre-step state while its deleted value has not yet arrived. -/
def Aligned (v : Nat) (st : IndexedState) (fixed : Fixed) : Prop :=
  fixed.next = st.original.next ∧
  ((v < st.original.next ∧ ∃ q, fixed.q = some q ∧ (v, (fixed.cells, q)) ∈ st.shadows) ∨
    (st.original.next ≤ v ∧ fixed.cells = List.replicate st.original.height 1 ∧
      fixed.q = st.original.q))


theorem collected_copy (δ : Table) (height : Nat → Nat) (index : Nat)
    {xs ys : List Indexed} {v : Nat} {sh : Pair}
    (hc : collect (updateIndexed (updatePair δ height index)) xs = some ys)
    (hm : (v, sh) ∈ xs) :
    ∃ out, (v, out) ∈ ys ∧ updatePair δ height index sh = some out := by
  obtain ⟨entry, he, hu⟩ := collect_input _ hc hm
  unfold updateIndexed at hu
  cases hp : updatePair δ height index sh with
  | none => simp [hp] at hu
  | some out =>
    simp only [hp, Option.map_some, Option.some.injEq] at hu
    subst entry
    exact ⟨out, he, rfl⟩

theorem recipe_input_length (δ : Table) (bound : Nat)
    {st : IndexedState} {l : Letter} {r : Recipe}
    (hl : Lengths st) (hr : recipe δ bound st.original l = some r) :
    ∀ entry ∈ indexedInputs r st.shadows, entry.2.1.length = r.after.height+1 := by
  cases l with
  | H k =>
    simp only [recipe] at hr
    split at hr
    next guard =>
      cases hr
      intro entry he
      have hm : entry ∈ st.shadows := by simpa [indexedInputs, extendIndexed] using he
      have hh := hl entry hm
      simp only
      omega
    next => contradiction
  | N b =>
    simp only [recipe] at hr
    cases hq : st.original.q with
    | none => simp [hq] at hr
    | some q =>
      simp [hq] at hr
      obtain ⟨guard, rfl⟩ := hr
      intro entry he
      simp only [indexedInputs, List.mem_append, List.mem_map, births] at he
      rcases he with ⟨old, hm, rfl⟩ | ⟨d, _, rfl⟩
      · have hh := hl old hm
        simp only [extendIndexed, List.length_append, List.length_replicate]
        omega
      · simp only [birthVector, List.length_append, List.length_replicate, List.length_map,
          List.length_range]
        omega

theorem step_lengths (δ : Table) (height : Nat → Nat) (bound : Nat)
    {st after : IndexedState} {l : Letter} (hl : Lengths st)
    (hs : indexedStep δ height bound st l = some after) : Lengths after := by
  unfold indexedStep at hs
  cases hr : recipe δ bound st.original l with
  | none => simp [hr] at hs
  | some r =>
    cases hc : collect (updateIndexed (updatePair δ height r.index)) (indexedInputs r st.shadows) with
    | none => simp [hr, hc] at hs
    | some ys =>
      simp [hr, hc] at hs
      subst after
      intro entry he
      obtain ⟨old, hm, hu⟩ := collect_output _ hc he
      have hlen := recipe_input_length δ bound hl hr old hm
      unfold updateIndexed at hu
      cases hp : updatePair δ height r.index old.2 with
      | none => simp [hp] at hu
      | some out =>
        simp only [hp, Option.map_some, Option.some.injEq] at hu
        subst entry
        have hh := (updatePair_fixed δ height st.original.next r.index hp).2
        simp only
        omega

theorem arrivalTags_past {v start count : Nat} (h : v < start) :
    arrivalTags v start count = List.replicate count 0 := by
  apply arrivalTags_absent
  intro hm
  have hh := List.mem_range'.mp hm
  omega

theorem birthVector_arrival (h start b d : Nat) :
    birthVector h b d = List.replicate h 1 ++ arrivalTags (start+d) start b := by
  simp [birthVector, arrivalTags, List.range'_eq_map_range, List.map_map, Function.comp_def]

theorem update_ones_H (h k : Nat) (hp : 0 < k) (hv : k ≤ h) :
    updateAt (List.replicate h 1) (k-1) =
      some (some (.H k), List.replicate (h-1) 1) := by
  have he : h = (k-1)+1+(h-k) := by omega
  have hn : (k-1)+(h-k) = h-1 := by omega
  have hk : k-1+1 = k := by omega
  have hx := before_birth_held (k-1) (h-k)
  rw [hn, hk] at hx
  have hr : List.replicate h 1 = List.replicate (k-1) 1 ++ 1 :: List.replicate (h-k) 1 := by
    calc
      _ = List.replicate ((k-1)+(1+(h-k))) 1 := by congr 1; omega
      _ = _ := by rw [← List.replicate_succ, List.replicate_append_replicate]; congr 1; omega
  rw [hr]
  exact hx

theorem update_ones_N (h b : Nat) (hp : 0 < b) :
    updateAt (List.replicate h 1 ++ List.replicate b 0) (h+b-1) =
      some (some (.N b), List.replicate (h+b-1) 1) := by
  have hb : b = (b-1)+1 := by omega
  have hh : h+b-1 = h+(b-1) := by omega
  have hx := before_birth_record h (b-1)
  rw [← hb, ← hh] at hx
  have hr : List.replicate b 0 = List.replicate (b-1) 0 ++ [0] := by
    calc
      _ = List.replicate ((b-1)+1) 0 := by rw [← hb]
      _ = _ := by rw [← List.replicate_one, List.replicate_append_replicate]
  simpa only [hr, List.append_assoc] using hx

theorem aligned_step_H (δ : Table) (height : Nat → Nat)
    {st : IndexedState} {fixed : Fixed} {ys : List Indexed} {v k : Nat}
    (_hl : Lengths st) (ha : Aligned v st fixed) (hp : 0 < k) (hv : k ≤ st.original.height)
    (hc : collect (updateIndexed (updatePair δ height (k-1))) st.shadows = some ys) :
    ∃ out, fixedStep δ v fixed (.H k) = some out ∧
      Aligned v ⟨⟨st.original.height-1, st.original.next,
        st.original.q.bind (fun q => δ q (.H k))⟩, ys⟩ out := by
  obtain ⟨hn, born | unborn⟩ := ha
  · obtain ⟨hborn, q, hq, hm⟩ := born
    obtain ⟨pair, hmem, hu⟩ := collected_copy δ height (k-1) hc hm
    have hf := (updatePair_fixed δ height fixed.next (k-1) hu).1
    refine ⟨⟨fixed.next, pair.1, some pair.2⟩, ?_, ?_⟩
    · simpa [fixedStep, hp, hq] using hf
    · exact ⟨hn, Or.inl ⟨hborn, pair.2, rfl, hmem⟩⟩
  · obtain ⟨hfuture, hcells, hq⟩ := unborn
    refine ⟨⟨fixed.next, List.replicate (st.original.height-1) 1,
      st.original.q.bind (fun q => δ q (.H k))⟩, ?_, ?_⟩
    · simp [fixedStep, hp, fixedUpdate, hcells, hq, update_ones_H _ _ hp hv, advance]
    · exact ⟨hn, Or.inr ⟨hfuture, rfl, rfl⟩⟩

theorem aligned_step_N (δ : Table) (height : Nat → Nat)
    {st : IndexedState} {fixed : Fixed} {ys : List Indexed} {v b q : Nat}
    (hl : Lengths st) (ha : Aligned v st fixed) (hp : 0 < b) (hq : st.original.q = some q)
    (hc : collect (updateIndexed (updatePair δ height (st.original.height+b-1)))
      (st.shadows.map (fun sh => (sh.1, (sh.2.1 ++ List.replicate b 0, sh.2.2))) ++
        births st.original.height st.original.next b q) = some ys) :
    ∃ out, fixedStep δ v fixed (.N b) = some out ∧
      Aligned v ⟨⟨st.original.height+b-1, st.original.next+b, δ q (.N b)⟩, ys⟩ out := by
  obtain ⟨hn, born | unborn⟩ := ha
  · obtain ⟨hborn, oldq, holdq, hm⟩ := born
    have hlen : fixed.cells.length = st.original.height := hl _ hm
    have hin : (v, (fixed.cells ++ List.replicate b 0, oldq)) ∈
        st.shadows.map (fun sh => (sh.1, (sh.2.1 ++ List.replicate b 0, sh.2.2))) ++
          births st.original.height st.original.next b q :=
      List.mem_append_left _ (List.mem_map.mpr ⟨_, hm, rfl⟩)
    obtain ⟨pair, hmem, hu⟩ := collected_copy δ height _ hc hin
    have hf := (updatePair_fixed δ height (fixed.next+b) _ hu).1
    refine ⟨⟨fixed.next+b, pair.1, some pair.2⟩, ?_, ?_⟩
    · simpa [fixedStep, hp, hlen, holdq, hn, arrivalTags_past hborn] using hf
    · exact ⟨by simpa using congrArg (· + b) hn, Or.inl ⟨by dsimp; omega, pair.2, rfl, hmem⟩⟩
  · obtain ⟨hfuture, hcells, hfixedq⟩ := unborn
    by_cases hborn : v < st.original.next+b
    · let d := v-st.original.next
      have hd : d < b := by dsimp [d]; omega
      have hv : st.original.next+d = v := by dsimp [d]; omega
      have hin : (v, (birthVector st.original.height b d, q)) ∈
          st.shadows.map (fun sh => (sh.1, (sh.2.1 ++ List.replicate b 0, sh.2.2))) ++
            births st.original.height st.original.next b q := by
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨d, List.mem_range.mpr hd, by simp [hv]⟩
      obtain ⟨pair, hmem, hu⟩ := collected_copy δ height _ hc hin
      have hf := (updatePair_fixed δ height (fixed.next+b) _ hu).1
      refine ⟨⟨fixed.next+b, pair.1, some pair.2⟩, ?_, ?_⟩
      · simpa [fixedStep, hp, hcells, hfixedq, hq, hn, birthVector_arrival st.original.height st.original.next b d, hv] using hf
      · exact ⟨by simpa using congrArg (· + b) hn, Or.inl ⟨hborn, pair.2, rfl, hmem⟩⟩
    · have hstill : st.original.next+b ≤ v := by omega
      refine ⟨⟨fixed.next+b, List.replicate (st.original.height+b-1) 1, δ q (.N b)⟩, ?_, ?_⟩
      · simp [fixedStep, hp, fixedUpdate, hcells, hfixedq, hq, hn,
          arrivalTags_before hstill, update_ones_N _ _ hp, advance]
      · exact ⟨by simpa using congrArg (· + b) hn, Or.inr ⟨hstill, rfl, rfl⟩⟩


theorem step_aligned (δ : Table) (height : Nat → Nat) (bound : Nat)
    {st after : IndexedState} {fixed : Fixed} {v : Nat} {l : Letter}
    (hl : Lengths st) (ha : Aligned v st fixed)
    (hs : indexedStep δ height bound st l = some after) :
    ∃ out, fixedStep δ v fixed l = some out ∧ Aligned v after out := by
  unfold indexedStep at hs
  cases hr : recipe δ bound st.original l with
  | none => simp [hr] at hs
  | some r =>
    cases hc : collect (updateIndexed (updatePair δ height r.index)) (indexedInputs r st.shadows) with
    | none => simp [hr, hc] at hs
    | some ys =>
      simp [hr, hc] at hs
      subst after
      cases l with
      | H k =>
        simp only [recipe] at hr
        split at hr
        next guard =>
          cases hr
          have hc' : collect (updateIndexed (updatePair δ height (k-1))) st.shadows = some ys := by
            change collect (updateIndexed (updatePair δ height (k-1)))
              (st.shadows.map (fun x => x) ++ []) = some ys at hc
            simpa using hc
          exact aligned_step_H δ height hl ha guard.1 guard.2 hc'
        next => contradiction
      | N b =>
        simp only [recipe] at hr
        cases hq : st.original.q with
        | none => simp [hq] at hr
        | some q =>
          simp [hq] at hr
          obtain ⟨guard, rfl⟩ := hr
          have hc' := hc
          simp only [indexedInputs] at hc'
          exact aligned_step_N δ height hl ha guard.1 hq hc'

theorem run_aligned (δ : Table) (height : Nat → Nat) (bound : Nat)
    {st after : IndexedState} {fixed : Fixed} {v : Nat} {code : List Letter}
    (hl : Lengths st) (ha : Aligned v st fixed)
    (hs : run (indexedStep δ height bound) st code = some after) :
    ∃ out, fixedRun δ v fixed code = some out ∧ Aligned v after out := by
  induction code generalizing st fixed with
  | nil => cases hs; exact ⟨fixed, rfl, ha⟩
  | cons l code ih =>
    cases ht : indexedStep δ height bound st l with
    | none => simp [run, ht] at hs
    | some mid =>
      obtain ⟨next, hn, hna⟩ := step_aligned δ height bound hl ha ht
      have htail : run (indexedStep δ height bound) mid code = some after := by
        simpa [run, ht] using hs
      obtain ⟨out, ho, hao⟩ := ih (step_lengths δ height bound hl ht) hna htail
      exact ⟨out, by simp [fixedRun, hn, ho], hao⟩

theorem same_id_unique {xs : List Indexed} (h : (xs.map Prod.fst).Nodup)
    {v : Nat} {a b : Pair} (ha : (v,a) ∈ xs) (hb : (v,b) ∈ xs) : a = b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    have hh := List.nodup_cons.mp h
    simp only [List.mem_cons] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Prod.mk.inj (ha.trans hb.symm) |>.2
    · have he : x.1 = v := by rw [← ha]
      exact False.elim (hh.1 (he ▸ List.mem_map.mpr ⟨(v,b), hb, rfl⟩))
    · have he : x.1 = v := by rw [← hb]
      exact False.elim (hh.1 (he ▸ List.mem_map.mpr ⟨(v,a), ha, rfl⟩))
    · exact ih hh.2 ha hb

/-- Main table-fold correspondence. Every actually retained deletion ID has
exactly the q obtained by running the SAME table from its initial state on the
full fixed-value emitted prefix. No correspondence is an input hypothesis. -/
theorem initial_indexed_q (δ : Table) (height : Nat → Nat) (bound q0 : Nat)
    {code : List Letter} {after : IndexedState} {v : Nat} {pair : Pair}
    (hs : run (indexedStep δ height bound) (initialIndexed q0) code = some after)
    (hm : (v,pair) ∈ after.shadows) :
    ∃ emitted, transduceTags v 0 [] code = some emitted ∧
      recognizeFrom δ (some q0) emitted = some pair.2 := by
  have hb := initial_run_allBorn δ height bound q0 hs
  have hv : v < after.original.next := by
    have hm' : v ∈ after.shadows.map Prod.fst := List.mem_map.mpr ⟨(v,pair), hm, rfl⟩
    rw [hb] at hm'
    exact List.mem_range.mp hm'
  have hl : Lengths (initialIndexed q0) := by intro entry he; simp [initialIndexed] at he
  have ha : Aligned v (initialIndexed q0) ⟨0, [], some q0⟩ :=
    ⟨rfl, Or.inr ⟨Nat.zero_le v, rfl, rfl⟩⟩
  obtain ⟨fixed, hf, halign⟩ := run_aligned δ height bound hl ha hs
  obtain ⟨emitted, he, hq⟩ := fixedRun_semantics δ v hf
  refine ⟨emitted, he, ?_⟩
  rcases halign.2 with ⟨_, q, hfixedq, hmem⟩ | ⟨hfuture, _, _⟩
  · have hn : (after.shadows.map Prod.fst).Nodup := by rw [hb]; exact List.nodup_range
    have hp := same_id_unique hn hmem hm
    have hp' : q = pair.2 := congrArg Prod.snd hp
    simpa [hq, hfixedq] using congrArg some hp'
  · omega

/-- Exact q for the actual standardized deletion of an actual output prefix.
Reachability is successful execution plus literal partial decoding; neither
premise assumes anything about a deletion code or its recognizer state. -/
theorem initial_indexed_q_encode (δ : Table) (height : Nat → Nat) (bound q0 : Nat)
    {code : List Letter} {output : List Nat} {after : IndexedState} {v : Nat} {pair : Pair}
    (hd : PartialDecodes 0 [] code output)
    (hs : run (indexedStep δ height bound) (initialIndexed q0) code = some after)
    (hm : (v,pair) ∈ after.shadows) :
    recognizeFrom δ (some q0) (encode 0 [] (deleteWord v output)) = some pair.2 := by
  obtain ⟨emitted, he, hq⟩ := initial_indexed_q δ height bound q0 hs hm
  have ht := transduceTags_partial_initial_eq_encode (v := v) hd
  have heq : emitted = encode 0 [] (deleteWord v output) := Option.some.inj (he.symm.trans ht)
  simpa only [heq] using hq

/-- Direct prefix corollary of complete literal decoding, at every cut length. -/
theorem initial_indexed_q_take (δ : Table) (height : Nat → Nat) (bound q0 : Nat)
    {n : Nat} {code : List Letter} {output : List Nat} {after : IndexedState}
    {v t : Nat} {pair : Pair} (hd : Decodes n 0 [] code output)
    (hs : run (indexedStep δ height bound) (initialIndexed q0) (code.take t) = some after)
    (hm : (v,pair) ∈ after.shadows) :
    recognizeFrom δ (some q0) (encode 0 [] (deleteWord v (output.take t))) = some pair.2 :=
  initial_indexed_q_encode δ height bound q0 (hd.partial_take t) hs hm

/-- The reviewed quotient now transfers actual deletion-prefix q semantics to
all merged members and covers every deletion ID already born at that prefix. -/
theorem initial_merged_q_encode (δ : Table) (height : Nat → Nat) (bound q0 : Nat)
    {code : List Letter} {output : List Nat} {after : MergedState}
    (hd : PartialDecodes 0 [] code output)
    (hs : run (mergedStep δ height bound) (initialMerged q0) code = some after) :
    (∀ pair ∈ after.shadows, ∃ v, v < after.original.next ∧
      recognizeFrom δ (some q0) (encode 0 [] (deleteWord v output)) = some pair.2) ∧
    (∀ v, v < after.original.next → ∃ pair ∈ after.shadows,
      recognizeFrom δ (some q0) (encode 0 [] (deleteWord v output)) = some pair.2) := by
  obtain ⟨indexed, hi, hb, ho, hmembers⟩ := initial_success_members δ height bound q0 hs
  constructor
  · intro pair hm
    obtain ⟨v, hv⟩ := (hmembers pair).mp hm
    refine ⟨v, ?_, initial_indexed_q_encode δ height bound q0 hd hi hv⟩
    have he : v ∈ indexed.shadows.map Prod.fst := List.mem_map.mpr ⟨(v,pair), hv, rfl⟩
    rw [hb] at he
    rw [ho]
    exact List.mem_range.mp he
  · intro v hv
    have hm : v ∈ indexed.shadows.map Prod.fst := by rw [hb]; exact List.mem_range.mpr (ho ▸ hv)
    obtain ⟨entry, he, hev⟩ := List.mem_map.mp hm
    rcases entry with ⟨id, pair⟩
    simp only at hev
    subst id
    exact ⟨pair, (hmembers pair).mpr ⟨v, he⟩,
      initial_indexed_q_encode δ height bound q0 hd hi he⟩


/-- Primitive table reachability, independent of deletion words. -/
inductive TableReachable (δ : Table) (q0 : Nat) : Nat → Prop where
  | initial : TableReachable δ q0 q0
  | step {q q' : Nat} {l : Letter} : TableReachable δ q0 q →
      δ q l = some q' → TableReachable δ q0 q'

def rankHeight (h : Nat) : Letter → Nat
  | .N b => h+b-1
  | .H _ => h-1

/-- Existing normalized recognizer's literal one-letter transition. -/
def rankTransition (r s h : Nat) : Letter → List Nat → List (List Nat)
  | .N b, physical => if 0 < b then rankReadOrders r h (b-1) physical else []
  | .H k, physical => if 0 < k then rankPopOrders s k physical else []

theorem rankCodeOrders_cons (r s h : Nat) (l : Letter) (code : List Letter) (physical : List Nat) :
    rankCodeOrders r s h (l :: code) physical =
      (rankTransition r s h l physical).flatMap (rankCodeOrders r s (rankHeight h l) code) := by
  cases l <;> simp only [rankCodeOrders, rankTransition, rankHeight] <;> split <;> rfl

theorem same_trans {xs ys zs : List α} (h : SameMembers xs ys) (k : SameMembers ys zs) :
    SameMembers xs zs := fun x => (h x).trans (k x)

theorem same_flatMap (f : α → List β) {xs ys : List α} (h : SameMembers xs ys) :
    SameMembers (xs.flatMap f) (ys.flatMap f) := by
  intro y
  simp only [List.mem_flatMap]
  constructor <;> rintro ⟨x, hx, hy⟩
  · exact ⟨x, (h x).mp hx, hy⟩
  · exact ⟨x, (h x).mpr hx, hy⟩

/-- Explicit LOCAL interpretation contract for live reachable table entries.
It does not assume any global code/shadow correspondence. It also does not
assert rejected transitions are complete; that stronger table-certification
obligation is outside the per-live-deletion result. -/
structure LiveRankTable (δ : Table) (height : Nat → Nat) (orders : Nat → List (List Nat))
    (q0 r s : Nat) : Prop where
  initial_height : height q0 = 0
  initial_orders : SameMembers (orders q0) [[]]
  transition : ∀ q l q', TableReachable δ q0 q → δ q l = some q' →
    height q' = rankHeight (height q) l ∧
      SameMembers (orders q') ((orders q).flatMap (rankTransition r s (height q) l))

@[simp] theorem recognizeFrom_none (δ : Table) (code : List Letter) :
    recognizeFrom δ none code = none := by
  induction code with
  | nil => rfl
  | cons l code ih => exact ih

theorem live_rank_run (δ : Table) (height : Nat → Nat) (orders : Nat → List (List Nat))
    (q0 r s : Nat) (spec : LiveRankTable δ height orders q0 r s)
    {q final : Nat} {code : List Letter} (reach : TableReachable δ q0 q)
    (hr : recognizeFrom δ (some q) code = some final) :
    SameMembers (orders final) ((orders q).flatMap (rankCodeOrders r s (height q) code)) := by
  induction code generalizing q with
  | nil => cases hr; simpa [rankCodeOrders] using same_refl (orders final)
  | cons l code ih =>
    cases ht : δ q l with
    | none => simp [recognizeFrom, ht] at hr
    | some mid =>
      have htail : recognizeFrom δ (some mid) code = some final := by
        simpa [recognizeFrom, ht] using hr
      have hspec := spec.transition q l mid reach ht
      have hrec := ih (.step reach ht) htail
      rw [hspec.1] at hrec
      have hmap := same_flatMap (rankCodeOrders r s (rankHeight (height q) l) code) hspec.2
      have he := same_trans hrec hmap
      have hf : rankCodeOrders r s (height q) (l :: code) =
          fun physical => (rankTransition r s (height q) l physical).flatMap
            (rankCodeOrders r s (rankHeight (height q) l) code) := by
        funext physical
        exact rankCodeOrders_cons r s (height q) l code physical
      rw [hf]
      simpa only [List.flatMap_assoc] using he

theorem live_rank_initial (δ : Table) (height : Nat → Nat) (orders : Nat → List (List Nat))
    (q0 r s : Nat) (spec : LiveRankTable δ height orders q0 r s)
    {q : Nat} {code : List Letter} (hr : recognizeFrom δ (some q0) code = some q) :
    SameMembers (orders q) (rankCodeOrders r s 0 code []) := by
  have h := live_rank_run δ height orders q0 r s spec .initial hr
  rw [spec.initial_height] at h
  have hm := same_flatMap (rankCodeOrders r s 0 code) spec.initial_orders
  simpa using same_trans h hm

/-- Conditional semantic interpretation of the ACTUAL stored q, using only
initial and one-step live reachable table obligations. The recognizer on the
right is the existing rank-normalized physical-order recognizer. -/
theorem initial_indexed_rank_orders (δ : Table) (height : Nat → Nat)
    (orders : Nat → List (List Nat)) (bound q0 r s : Nat)
    (spec : LiveRankTable δ height orders q0 r s)
    {code : List Letter} {output : List Nat} {after : IndexedState} {v : Nat} {pair : Pair}
    (hd : PartialDecodes 0 [] code output)
    (hs : run (indexedStep δ height bound) (initialIndexed q0) code = some after)
    (hm : (v,pair) ∈ after.shadows) :
    SameMembers (orders pair.2) (rankCodeOrders r s 0 (encode 0 [] (deleteWord v output)) []) :=
  live_rank_initial δ height orders q0 r s spec
    (initial_indexed_q_encode δ height bound q0 hd hs hm)

theorem initial_indexed_rank_accepts (δ : Table) (height : Nat → Nat)
    (orders : Nat → List (List Nat)) (bound q0 r s : Nat)
    (spec : LiveRankTable δ height orders q0 r s)
    {code : List Letter} {output : List Nat} {after : IndexedState} {v : Nat} {pair : Pair}
    (hd : PartialDecodes 0 [] code output)
    (hs : run (indexedStep δ height bound) (initialIndexed q0) code = some after)
    (hm : (v,pair) ∈ after.shadows) :
    [] ∈ orders pair.2 ↔ rankRecognizes r s (encode 0 [] (deleteWord v output)) = true := by
  simpa only [rankRecognizes, List.contains_iff_mem] using
    initial_indexed_rank_orders δ height orders bound q0 r s spec hd hs hm []

def birthCount : List Letter → Nat
  | [] => 0
  | .N b :: code => b + birthCount code
  | .H _ :: code => birthCount code

theorem recipe_next (δ : Table) (bound : Nat) {o : Original} {l : Letter} {rec : Recipe}
    (hr : recipe δ bound o l = some rec) : rec.after.next = o.next + birthCount [l] := by
  cases l with
  | H k =>
    simp only [recipe] at hr
    split at hr
    · cases hr; simp [birthCount]
    · contradiction
  | N b =>
    simp only [recipe] at hr
    cases hq : o.q with
    | none => simp [hq] at hr
    | some q => simp [hq] at hr; obtain ⟨_, rfl⟩ := hr; simp [birthCount]

theorem step_next (δ : Table) (height : Nat → Nat) (bound : Nat)
    {st after : IndexedState} {l : Letter}
    (hs : indexedStep δ height bound st l = some after) :
    after.original.next = st.original.next + birthCount [l] := by
  unfold indexedStep at hs
  cases hr : recipe δ bound st.original l with
  | none => simp [hr] at hs
  | some rec =>
    cases hc : collect (updateIndexed (updatePair δ height rec.index)) (indexedInputs rec st.shadows) with
    | none => simp [hr, hc] at hs
    | some ys =>
      simp [hr, hc] at hs
      subst after
      exact recipe_next δ bound hr

theorem run_next (δ : Table) (height : Nat → Nat) (bound : Nat)
    {st after : IndexedState} {code : List Letter}
    (hs : run (indexedStep δ height bound) st code = some after) :
    after.original.next = st.original.next + birthCount code := by
  induction code generalizing st with
  | nil => cases hs; simp [birthCount]
  | cons l code ih =>
    cases ht : indexedStep δ height bound st l with
    | none => simp [run, ht] at hs
    | some mid =>
      have hh := step_next δ height bound ht
      have htail : run (indexedStep δ height bound) mid code = some after := by
        simpa [run, ht] using hs
      have hi := ih htail
      cases l <;> simp_all [birthCount] <;> omega

theorem decodes_birthCount {n next : Nat} {held output : List Nat} {code : List Letter}
    (hd : Decodes n next held code output) : next + birthCount code = n := by
  induction hd with
  | nil => simp [birthCount]
  | held _ _ ih => exact ih
  | record hn _ ih => simp only [birthCount]; omega

/-- At a complete decoding, every actual stored deletion q has the ordinary
machine-generation semantics from GeneralizedRankNormalization/CodeRecognition.
The only additional assumption is the explicit local live-table contract. -/
theorem initial_indexed_generated (δ : Table) (height : Nat → Nat)
    (orders : Nat → List (List Nat)) (bound q0 r s : Nat)
    (spec : LiveRankTable δ height orders q0 r s)
    {n : Nat} {code : List Letter} {output : List Nat} {after : IndexedState}
    {v : Nat} {pair : Pair} (hd : Decodes n 0 [] code output)
    (hs : run (indexedStep δ height bound) (initialIndexed q0) code = some after)
    (hm : (v,pair) ∈ after.shadows) (hr : 0 < r) (hpop : 0 < s) :
    [] ∈ orders pair.2 ↔ Run r s [] (List.range (n-1)) (deleteWord v output) [] := by
  have hb := initial_run_allBorn δ height bound q0 hs
  have hn : after.original.next = n := by
    have hh := run_next δ height bound hs
    have hcount := decodes_birthCount hd
    simpa [initialIndexed, hcount] using hh
  have hv : v < n := by
    have hm' : v ∈ after.shadows.map Prod.fst := List.mem_map.mpr ⟨(v,pair), hm, rfl⟩
    rw [hb, hn] at hm'
    exact List.mem_range.mp hm'
  have hp : output.Perm (List.range n) := by simpa [List.range_eq_range'] using hd.supply.2
  exact (initial_indexed_rank_accepts δ height orders bound q0 r s spec hd.partial hs hm).trans
    (permutation_rankRecognizes_iff (deleteWord_permutation hp hv) hr hpop)

#print axioms initial_indexed_q
#print axioms initial_indexed_q_encode
#print axioms initial_indexed_q_take
#print axioms initial_merged_q_encode
#print axioms live_rank_initial
#print axioms initial_indexed_rank_orders
#print axioms initial_indexed_rank_accepts
#print axioms initial_indexed_generated

end Recognition
end Merging
end Shadow
end LazyCode
end StackSorting.Generalized
