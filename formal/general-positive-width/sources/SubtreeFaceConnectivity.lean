import SubtreeSupportedCuts

namespace StackSorting.GraphWidth.UCurve.PlaneGrid
open FinitePort

/-- Exactly the face occurrences of a vertex in the union-of-root-paths bag. -/
def SubtreeFace {α V F} (I : IncidenceMap α V F) (T : RootedTree V)
    (v : Fin V) (f : Fin F) : Prop := ∃ d, I.face d=f ∧ Ancestor T v (I.tail d)

theorem rotation_walk_color {α V F} (I : IncidenceMap α V F) (T : RootedTree V)
    (v : Fin V) (rot : α → α) (ht : ∀ d, I.tail (rot d)=I.tail d)
    (hf : ∀ d, I.face (rot d)=I.face (I.reverse d)) (color : Fin F → Bool)
    (hall : ∀ d, Ancestor T v (I.tail d) → color (I.face d)=color (I.face (I.reverse d)))
    {d e} (hd : Ancestor T v (I.tail d))
    (h : Walk (OrbitStep rot) (fun _ => True) d e) : color (I.face d)=color (I.face e) := by
  induction h with
  | refl => rfl
  | @step a b c _ hs _ ih =>
    have ht' : I.tail b=I.tail a := by
      obtain hs | hs := hs
      · rw [← hs,ht]
      · rw [← hs,ht]
    have hb : Ancestor T v (I.tail b) := ht' ▸ hd
    have hc : color (I.face a)=color (I.face b) := by
      obtain hs | hs := hs
      · rw [← hs,hf]
        exact hall a hd
      · rw [← hs,hf]
        exact (hall b hb).symm
    exact hc.trans (ih hb)

theorem descendant_dart_color {α V F} (I : IncidenceMap α V F) (T : RootedTree V)
    (v : Fin V) (rot : α → α) (ht : ∀ d, I.tail (rot d)=I.tail d)
    (hf : ∀ d, I.face (rot d)=I.face (I.reverse d))
    (hv : ∀ d e, I.tail d=I.tail e → Walk (OrbitStep rot) (fun _ => True) d e)
    (hedge : ∀ x, x.val≠0 → ∃ d, I.tail d=x ∧ I.tail (I.reverse d)=T.parent x)
    (color : Fin F → Bool)
    (hall : ∀ d, Ancestor T v (I.tail d) → color (I.face d)=color (I.face (I.reverse d)))
    (base : α) (hbase : I.tail base=v) {x : Fin V} (hx : Ancestor T v x)
    (d : α) (hd : I.tail d=x) : color (I.face d)=color (I.face base) := by
  induction hx generalizing d with
  | refl =>
    exact rotation_walk_color I T v rot ht hf color hall (by rw [hd]; exact Ancestor.refl v)
      (hv d base (hd.trans hbase.symm))
  | @step x hn hp ih =>
    obtain ⟨e,he,her⟩ := hedge x hn
    have ha : Ancestor T v (I.tail d) := hd ▸ Ancestor.step hn hp
    have hb : Ancestor T v (I.tail e) := he ▸ Ancestor.step hn hp
    exact (rotation_walk_color I T v rot ht hf color hall ha (hv d e (hd.trans he.symm))).trans
      ((hall e hb).trans (ih (I.reverse e) her))

/-- The root-path occurrence set of any vertex is connected in the actual
complementary dual adjacency. This supplies running intersection before the
separate Euler/counting step identifies that dual with a tree. -/
theorem subtree_faces_cotree_connected {α V F} (I : IncidenceMap α V F) (T : RootedTree V)
    (hc : CutContinues I) (rot : α → α) (ht : ∀ d, I.tail (rot d)=I.tail d)
    (hf : ∀ d, I.face (rot d)=I.face (I.reverse d))
    (hv : ∀ d e, I.tail d=I.tail e → Walk (OrbitStep rot) (fun _ => True) d e)
    (hsurj : ∀ x, ∃ d, I.tail d=x)
    (hedge : ∀ x, x.val≠0 → ∃ d, I.tail d=x ∧ I.tail (I.reverse d)=T.parent x)
    (v : Fin V) {a b : Fin F} (ha : SubtreeFace I T v a) (hb : SubtreeFace I T v b) :
    Walk (CotreeAdj I T) (SubtreeFace I T v) a b := by
  classical
  let P : Fin F → Prop := fun x => Walk (CotreeAdj I T) (SubtreeFace I T v) a x
  let color : Fin F → Bool := fun x => decide (P x)
  have hs : ∀ d, Ancestor T v (I.tail d) → FaceCut I color d →
      TreeAdj T (I.tail d) (I.tail (I.reverse d)) := by
    intro d hd hcut
    apply Classical.byContradiction
    intro hn
    have hstart : SubtreeFace I T v (I.face d) := ⟨d,rfl,hd⟩
    have hend : SubtreeFace I T v (I.face (I.reverse d)) :=
      ⟨rot d,hf d,by rw [ht]; exact hd⟩
    have he : Walk (CotreeAdj I T) (SubtreeFace I T v)
        (I.face d) (I.face (I.reverse d)) :=
      .step hstart ⟨d,rfl,rfl,hn⟩ (.refl hend)
    have hp : P (I.face d) ↔ P (I.face (I.reverse d)) :=
      ⟨fun h => h.trans he,fun h => h.trans (he.reverse (cotreeAdj_symm I T))⟩
    apply hcut
    change decide (P (I.face d))=decide (P (I.face (I.reverse d)))
    rw [propext hp]
  have hall : ∀ d, Ancestor T v (I.tail d) → color (I.face d)=color (I.face (I.reverse d)) := by
    intro d hd
    apply Classical.byContradiction
    exact subtree_supported_cut_false I T hc v color hs d hd
  obtain ⟨d,hda,hd⟩ := ha
  obtain ⟨e,heb,he⟩ := hb
  obtain ⟨base,hbase⟩ := hsurj v
  have hd' := descendant_dart_color I T v rot ht hf hv hedge color hall base hbase hd d rfl
  have he' := descendant_dart_color I T v rot ht hf hv hedge color hall base hbase he e rfl
  have hab : color a=color b := by rw [← hda,← heb]; exact hd'.trans he'.symm
  have htrue : color a=true := decide_eq_true (.refl ⟨d,hda,hd⟩)
  exact of_decide_eq_true (hab.symm.trans htrue)

end StackSorting.GraphWidth.UCurve.PlaneGrid
