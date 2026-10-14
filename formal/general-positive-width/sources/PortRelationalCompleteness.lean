import PortRelationalNormalForm

namespace StackSorting.FinitePort

theorem PortNormalForm.to_relational {n colors relations} {T : RootedTree n}
    {O : FixedOrder n} {G : Diagram n colors relations} {C : Code n colors relations}
    (h : PortNormalForm T O G C) : RelationalPortNormalForm T O G C := by
  classical
  refine ⟨h.color,?_,?_,?_,h.bits⟩
  · intro v i hi
    have hj : i < (inherited T O G v).length := by rw [←h.length]; exact hi
    exact ⟨(inherited T O G v)[i],h.resolved v i hi hj⟩
  · intro v u
    constructor
    · intro hu
      have hm := (mem_inherited T O G v u).mpr hu
      let i := (inherited T O G v).idxOf u
      have he : (inherited T O G v)[i]?=some u := getElem?_idxOf_of_mem hm
      obtain ⟨hj,hval⟩ := List.getElem?_eq_some_iff.mp he
      have hi : i < (C v).ports.length := by rw [h.length]; exact hj
      refine ⟨i,hi,?_⟩
      simpa only [hval] using h.resolved v i hi hj
    · rintro ⟨i,hi,hr⟩
      have hj : i < (inherited T O G v).length := by rw [←h.length]; exact hi
      have he := Option.some.inj ((h.resolved v i hi hj).symm.trans hr)
      apply (mem_inherited T O G v u).mp
      rw [←he]
      exact List.getElem_mem hj
  · intro v i j hij hj u w hu hw
    have hi : i < (C v).ports.length := by omega
    have hiI : i < (inherited T O G v).length := by rw [←h.length]; exact hi
    have hjI : j < (inherited T O G v).length := by rw [←h.length]; exact hj
    have heU := Option.some.inj ((h.resolved v i hi hiI).symm.trans hu)
    have heW := Option.some.inj ((h.resolved v j hj hjI).symm.trans hw)
    have hsO : O.vertices.Pairwise (fun a b => O.vertices.idxOf a < O.vertices.idxOf b) := by
      rw [List.pairwise_iff_getElem]
      intro a b ha hb hab
      simpa only [O.nodup.idxOf_getElem a ha,O.nodup.idxOf_getElem b hb] using hab
    have hsI : (inherited T O G v).Pairwise
        (fun a b => O.vertices.idxOf a < O.vertices.idxOf b) := hsO.filter _
    have hh := (List.pairwise_iff_getElem.mp hsI) i j hiI hjI hij
    simpa only [heU,heW] using hh

theorem encode_relationalNormalForm {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations) :
    RelationalPortNormalForm T O G (encode T O G) := (encode_normalForm T O G).to_relational

#print axioms PortNormalForm.to_relational
#print axioms encode_relationalNormalForm
end StackSorting.FinitePort
