import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.List.Chain
import Mathlib.Tactic

namespace StackSorting.BiInterface
variable {V : Type*} [DecidableEq V] {k : ℕ}

/-- A bag has an injective assignment of interface names. -/
abbrev BagName (B : Finset V) (k : ℕ) := B ↪ Fin k

/-- Names on an overlap extend to a new bag without increasing the interface
arity. The proof extends a finite partial permutation of the name set. -/
theorem extend_bag_names (B C : Finset V) (hC : C.card ≤ k) (f : BagName B k) :
    ∃ g : BagName C k, ∀ v (hB : v ∈ B) (hC : v ∈ C),
      g ⟨v,hC⟩ = f ⟨v,hB⟩ := by
  classical
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le
    (by simpa using hC : Fintype.card C ≤ Fintype.card (Fin k))
  let shared := B ∩ C
  let a : shared → Fin k := fun v => g ⟨v.val, (Finset.mem_inter.mp v.property).2⟩
  let b : shared → Fin k := fun v => f ⟨v.val, (Finset.mem_inter.mp v.property).1⟩
  have ha : Function.Injective a := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : C => z.val) (g.injective h)
  have hb : Function.Injective b := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : B => z.val) (f.injective h)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair a b ha hb
  refine ⟨g.trans σ.toEmbedding, ?_⟩
  intro v hvB hvC
  exact hσ ⟨v,Finset.mem_inter.mpr ⟨hvB,hvC⟩⟩

structure NamedBag (V : Type*) (k : ℕ) where
  bag : Finset V
  name : BagName bag k

def NamedBag.Compatible (B C : NamedBag V k) : Prop :=
  ∀ v (hB : v ∈ B.bag) (hC : v ∈ C.bag), B.name ⟨v,hB⟩ = C.name ⟨v,hC⟩

/-- Every bounded ordered bag list admits compatible adjacent interface names.
No coloring or compatible-naming witness is assumed. -/
theorem name_bag_list (bs : List (Finset V)) (hbound : ∀ B ∈ bs, B.card ≤ k) :
    ∃ ns : List (NamedBag V k), ns.map NamedBag.bag = bs ∧
      ns.IsChain NamedBag.Compatible := by
  induction bs with
  | nil => exact ⟨[],rfl,.nil⟩
  | cons B bs ih =>
    obtain ⟨ns, hns, hc⟩ := ih (by intro C hC; exact hbound C (List.mem_cons_of_mem _ hC))
    cases ns with
    | nil =>
      have hbs : bs = [] := hns.symm
      obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
        (by simpa using hbound B (by simp) : Fintype.card B ≤ Fintype.card (Fin k))
      refine ⟨[⟨B,f⟩], ?_, .singleton _⟩
      simp [hbs]
    | cons C ns =>
      obtain ⟨f,hf⟩ := extend_bag_names C.bag B (hbound B (by simp)) C.name
      refine ⟨⟨B,f⟩ :: C :: ns, ?_, ?_⟩
      · simpa using congrArg (List.cons B) hns
      · apply (List.isChain_cons_iff _ _ _).mpr
        refine Or.inr ⟨C,ns,?_,hc,rfl⟩
        intro v hvB hvC
        exact hf v hvC hvB

#print axioms name_bag_list
end StackSorting.BiInterface
