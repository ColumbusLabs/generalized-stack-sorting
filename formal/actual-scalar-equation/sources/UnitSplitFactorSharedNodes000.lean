import RingReflection
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

def usfn0E : RingExpr := (.int 0)
def usfn0P : Lean.Grind.CommRing.Poly := (.num (0))
theorem usfn0_norm : (reflectRing usfn0E).toPoly=usfn0P := by
  exact eq_of_beq (by decide : (reflectRing usfn0E).toPoly == usfn0P)

def usfn1E : RingExpr := (.var 7)
def usfn1P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨7,1⟩ .unit) (.num (0)))
theorem usfn1_norm : (reflectRing usfn1E).toPoly=usfn1P := by
  exact eq_of_beq (by decide : (reflectRing usfn1E).toPoly == usfn1P)

def usfn2E : RingExpr := (.var 10)
def usfn2P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨10,1⟩ .unit) (.num (0)))
theorem usfn2_norm : (reflectRing usfn2E).toPoly=usfn2P := by
  exact eq_of_beq (by decide : (reflectRing usfn2E).toPoly == usfn2P)

def usfn3E : RingExpr := (.var 9)
def usfn3P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨9,1⟩ .unit) (.num (0)))
theorem usfn3_norm : (reflectRing usfn3E).toPoly=usfn3P := by
  exact eq_of_beq (by decide : (reflectRing usfn3E).toPoly == usfn3P)

def usfn4E : RingExpr := (.pow (.var 8) 2)
def usfn4P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨8,2⟩ .unit) (.num (0)))
theorem usfn4_norm : (reflectRing usfn4E).toPoly=usfn4P := by
  exact eq_of_beq (by decide : (reflectRing usfn4E).toPoly == usfn4P)

def usfn5E : RingExpr := (.mul (.var 11) (.var 2))
def usfn5P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨2,1⟩ (.mult ⟨11,1⟩ .unit)) (.num (0)))
theorem usfn5_norm : (reflectRing usfn5E).toPoly=usfn5P := by
  exact eq_of_beq (by decide : (reflectRing usfn5E).toPoly == usfn5P)

def usfn6E : RingExpr := (.mul (.var 11) (.mul (.var 1) (.var 3)))
def usfn6P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨11,1⟩ .unit))) (.num (0)))
theorem usfn6_norm : (reflectRing usfn6E).toPoly=usfn6P := by
  exact eq_of_beq (by decide : (reflectRing usfn6E).toPoly == usfn6P)

def usfn7E : RingExpr := (.mul (.int 2) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2))))
def usfn7P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.num (0)))
theorem usfn7_norm : (reflectRing usfn7E).toPoly=usfn7P := by
  exact eq_of_beq (by decide : (reflectRing usfn7E).toPoly == usfn7P)

def usfn8E : RingExpr := (.mul (.int 2) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))))
def usfn8P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.num (0)))
theorem usfn8_norm : (reflectRing usfn8E).toPoly=usfn8P := by
  exact eq_of_beq (by decide : (reflectRing usfn8E).toPoly == usfn8P)

def usfn9E : RingExpr := (.mul (.int 2) (.mul (.var 12) (.mul (.var 2) (.mul (.var 3) (.var 4)))))
def usfn9P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.num (0)))
theorem usfn9_norm : (reflectRing usfn9E).toPoly=usfn9P := by
  exact eq_of_beq (by decide : (reflectRing usfn9E).toPoly == usfn9P)

def usfn10E : RingExpr := (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))
def usfn10P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.num (0)))
theorem usfn10_norm : (reflectRing usfn10E).toPoly=usfn10P := by
  exact eq_of_beq (by decide : (reflectRing usfn10E).toPoly == usfn10P)

def usfn11E : RingExpr := (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.mul (.int 4) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))
def usfn11P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit)))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.num (0))))))))
theorem usfn11_norm : (reflectRing usfn11E).toPoly=usfn11P := by
  exact eq_of_beq (by decide : (reflectRing usfn11E).toPoly == usfn11P)

def usfn12E : RingExpr := (.add usfn10E usfn11E)
def usfn12P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit)))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.num (0)))))))))
theorem usfn12_norm : (reflectRing usfn12E).toPoly=usfn12P := by
  change (reflectRing usfn10E).toPoly.combine (reflectRing usfn11E).toPoly=usfn12P
  rw [usfn10_norm, usfn11_norm]
  exact eq_of_beq (by decide : usfn10P.combine usfn11P == usfn12P)

def usfn13E : RingExpr := (.add usfn9E usfn12E)
def usfn13P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit)))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (2) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.num (0))))))))))
theorem usfn13_norm : (reflectRing usfn13E).toPoly=usfn13P := by
  change (reflectRing usfn9E).toPoly.combine (reflectRing usfn12E).toPoly=usfn13P
  rw [usfn9_norm, usfn12_norm]
  exact eq_of_beq (by decide : usfn9P.combine usfn12P == usfn13P)

def usfn14E : RingExpr := (.add usfn8E usfn13E)
def usfn14P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit)))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (2) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.num (0)))))))))))
theorem usfn14_norm : (reflectRing usfn14E).toPoly=usfn14P := by
  change (reflectRing usfn8E).toPoly.combine (reflectRing usfn13E).toPoly=usfn14P
  rw [usfn8_norm, usfn13_norm]
  exact eq_of_beq (by decide : usfn8P.combine usfn13P == usfn14P)

def usfn15E : RingExpr := (.add usfn7E usfn14E)
def usfn15P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit)))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (2) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.num (0))))))))))))
theorem usfn15_norm : (reflectRing usfn15E).toPoly=usfn15P := by
  change (reflectRing usfn7E).toPoly.combine (reflectRing usfn14E).toPoly=usfn15P
  rw [usfn7_norm, usfn14_norm]
  exact eq_of_beq (by decide : usfn7P.combine usfn14P == usfn15P)

def usfn16E : RingExpr := (.add usfn6E usfn15E)
def usfn16P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit)))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (2) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨11,1⟩ .unit))) (.num (0)))))))))))))
theorem usfn16_norm : (reflectRing usfn16E).toPoly=usfn16P := by
  change (reflectRing usfn6E).toPoly.combine (reflectRing usfn15E).toPoly=usfn16P
  rw [usfn6_norm, usfn15_norm]
  exact eq_of_beq (by decide : usfn6P.combine usfn15P == usfn16P)

def usfn17E : RingExpr := (.add usfn5E usfn16E)
def usfn17P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit)))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (2) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (1) (.mult ⟨2,1⟩ (.mult ⟨11,1⟩ .unit)) (.num (0))))))))))))))
theorem usfn17_norm : (reflectRing usfn17E).toPoly=usfn17P := by
  change (reflectRing usfn5E).toPoly.combine (reflectRing usfn16E).toPoly=usfn17P
  rw [usfn5_norm, usfn16_norm]
  exact eq_of_beq (by decide : usfn5P.combine usfn16P == usfn17P)

def usfn18E : RingExpr := (.mul usfn4E usfn17E)
def usfn18P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨12,1⟩ .unit)))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨15,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨15,1⟩ .unit))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (2) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (1) (.mult ⟨2,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))) (.num (0))))))))))))))
theorem usfn18_norm : (reflectRing usfn18E).toPoly=usfn18P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn17E).toPoly=usfn18P
  rw [usfn4_norm, usfn17_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn17P == usfn18P)

def usfn19E : RingExpr := (.mul usfn3E usfn18E)
def usfn19P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨12,1⟩ .unit))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨15,1⟩ .unit)))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨12,1⟩ .unit)))))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨15,1⟩ .unit)))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨12,1⟩ .unit)))))) (.add (2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨12,1⟩ .unit)))))) (.add (1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (1) (.mult ⟨2,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨11,1⟩ .unit)))) (.num (0))))))))))))))
theorem usfn19_norm : (reflectRing usfn19E).toPoly=usfn19P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn18E).toPoly=usfn19P
  rw [usfn3_norm, usfn18_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn18P == usfn19P)

def usfn20E : RingExpr := (.mul usfn2E usfn19E)
def usfn20P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))) (.add (2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (2) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))) (.add (1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (1) (.mult ⟨2,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))) (.num (0))))))))))))))
theorem usfn20_norm : (reflectRing usfn20E).toPoly=usfn20P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn19E).toPoly=usfn20P
  rw [usfn2_norm, usfn19_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn19P == usfn20P)

def usfn21E : RingExpr := (.mul usfn1E usfn20E)
def usfn21P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (2) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (1) (.mult ⟨2,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.num (0))))))))))))))
theorem usfn21_norm : (reflectRing usfn21E).toPoly=usfn21P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn20E).toPoly=usfn21P
  rw [usfn1_norm, usfn20_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn20P == usfn21P)

def usfn22E : RingExpr := (.mul usfn0E usfn21E)
def usfn22P : Lean.Grind.CommRing.Poly := (.num (0))
theorem usfn22_norm : (reflectRing usfn22E).toPoly=usfn22P := by
  change (reflectRing usfn0E).toPoly.mul (reflectRing usfn21E).toPoly=usfn22P
  rw [usfn0_norm, usfn21_norm]
  exact eq_of_beq (by decide : usfn0P.mul usfn21P == usfn22P)

def usfn23E : RingExpr := (.add usfn0E usfn22E)
def usfn23P : Lean.Grind.CommRing.Poly := (.num (0))
theorem usfn23_norm : (reflectRing usfn23E).toPoly=usfn23P := by
  change (reflectRing usfn0E).toPoly.combine (reflectRing usfn22E).toPoly=usfn23P
  rw [usfn0_norm, usfn22_norm]
  exact eq_of_beq (by decide : usfn0P.combine usfn22P == usfn23P)

def usfn24E : RingExpr := (.mul (.int (-1)) (.mul (.var 11) (.var 2)))
def usfn24P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨2,1⟩ (.mult ⟨11,1⟩ .unit)) (.num (0)))
theorem usfn24_norm : (reflectRing usfn24E).toPoly=usfn24P := by
  exact eq_of_beq (by decide : (reflectRing usfn24E).toPoly == usfn24P)

def usfn25E : RingExpr := (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 0) (.pow (.var 3) 2))))
def usfn25P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨11,1⟩ .unit))) (.num (0)))
theorem usfn25_norm : (reflectRing usfn25E).toPoly=usfn25P := by
  exact eq_of_beq (by decide : (reflectRing usfn25E).toPoly == usfn25P)

def usfn26E : RingExpr := (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))
def usfn26P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨15,1⟩ .unit))) (.add (-1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.num (0))))))))))
theorem usfn26_norm : (reflectRing usfn26E).toPoly=usfn26P := by
  exact eq_of_beq (by decide : (reflectRing usfn26E).toPoly == usfn26P)

def usfn27E : RingExpr := (.add usfn25E usfn26E)
def usfn27P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨11,1⟩ .unit))) (.add (-2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨15,1⟩ .unit))) (.add (-1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.num (0)))))))))))
theorem usfn27_norm : (reflectRing usfn27E).toPoly=usfn27P := by
  change (reflectRing usfn25E).toPoly.combine (reflectRing usfn26E).toPoly=usfn27P
  rw [usfn25_norm, usfn26_norm]
  exact eq_of_beq (by decide : usfn25P.combine usfn26P == usfn27P)

def usfn28E : RingExpr := (.add usfn24E usfn27E)
def usfn28P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨11,1⟩ .unit))) (.add (-2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨15,1⟩ .unit))) (.add (-1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (-1) (.mult ⟨2,1⟩ (.mult ⟨11,1⟩ .unit)) (.num (0))))))))))))
theorem usfn28_norm : (reflectRing usfn28E).toPoly=usfn28P := by
  change (reflectRing usfn24E).toPoly.combine (reflectRing usfn27E).toPoly=usfn28P
  rw [usfn24_norm, usfn27_norm]
  exact eq_of_beq (by decide : usfn24P.combine usfn27P == usfn28P)

def usfn29E : RingExpr := (.mul usfn4E usfn28E)
def usfn29P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (-2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (-1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (-1) (.mult ⟨2,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))) (.num (0))))))))))))
theorem usfn29_norm : (reflectRing usfn29E).toPoly=usfn29P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn28E).toPoly=usfn29P
  rw [usfn4_norm, usfn28_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn28P == usfn29P)

def usfn30E : RingExpr := (.mul usfn1E usfn29E)
def usfn30P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨12,1⟩ .unit)))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨12,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨15,1⟩ .unit))))) (.add (-1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-1) (.mult ⟨2,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))) (.num (0))))))))))))
theorem usfn30_norm : (reflectRing usfn30E).toPoly=usfn30P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn29E).toPoly=usfn30P
  rw [usfn1_norm, usfn29_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn29P == usfn30P)

def usfn31E : RingExpr := (.mul usfn0E usfn30E)
def usfn31P : Lean.Grind.CommRing.Poly := (.num (0))
theorem usfn31_norm : (reflectRing usfn31E).toPoly=usfn31P := by
  change (reflectRing usfn0E).toPoly.mul (reflectRing usfn30E).toPoly=usfn31P
  rw [usfn0_norm, usfn30_norm]
  exact eq_of_beq (by decide : usfn0P.mul usfn30P == usfn31P)

def usfn32E : RingExpr := (.add usfn23E usfn31E)
def usfn32P : Lean.Grind.CommRing.Poly := (.num (0))
theorem usfn32_norm : (reflectRing usfn32E).toPoly=usfn32P := by
  change (reflectRing usfn23E).toPoly.combine (reflectRing usfn31E).toPoly=usfn32P
  rw [usfn23_norm, usfn31_norm]
  exact eq_of_beq (by decide : usfn23P.combine usfn31P == usfn32P)

def usfn33E : RingExpr := (.mul (.int 0) (.int 0))
def usfn33P : Lean.Grind.CommRing.Poly := (.num (0))
theorem usfn33_norm : (reflectRing usfn33E).toPoly=usfn33P := by
  exact eq_of_beq (by decide : (reflectRing usfn33E).toPoly == usfn33P)

def usfn34E : RingExpr := (.add usfn32E usfn33E)
def usfn34P : Lean.Grind.CommRing.Poly := (.num (0))
theorem usfn34_norm : (reflectRing usfn34E).toPoly=usfn34P := by
  change (reflectRing usfn32E).toPoly.combine (reflectRing usfn33E).toPoly=usfn34P
  rw [usfn32_norm, usfn33_norm]
  exact eq_of_beq (by decide : usfn32P.combine usfn33P == usfn34P)

def usfn35E : RingExpr := (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 1) (.var 3))))
def usfn35P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨11,1⟩ .unit))) (.num (0)))
theorem usfn35_norm : (reflectRing usfn35E).toPoly=usfn35P := by
  exact eq_of_beq (by decide : (reflectRing usfn35E).toPoly == usfn35P)

def usfn36E : RingExpr := (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2))))
def usfn36P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.num (0)))
theorem usfn36_norm : (reflectRing usfn36E).toPoly=usfn36P := by
  exact eq_of_beq (by decide : (reflectRing usfn36E).toPoly == usfn36P)

def usfn37E : RingExpr := (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 0) (.pow (.var 3) 3))))
def usfn37P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨15,1⟩ .unit))) (.num (0)))
theorem usfn37_norm : (reflectRing usfn37E).toPoly=usfn37P := by
  exact eq_of_beq (by decide : (reflectRing usfn37E).toPoly == usfn37P)

def usfn38E : RingExpr := (.mul (.int 2) (.mul (.var 11) (.mul (.var 3) (.var 4))))
def usfn38P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.num (0)))
theorem usfn38_norm : (reflectRing usfn38E).toPoly=usfn38P := by
  exact eq_of_beq (by decide : (reflectRing usfn38E).toPoly == usfn38P)

def usfn39E : RingExpr := (.mul (.int 2) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2))))
def usfn39P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨15,1⟩ .unit))) (.num (0)))
theorem usfn39_norm : (reflectRing usfn39E).toPoly=usfn39P := by
  exact eq_of_beq (by decide : (reflectRing usfn39E).toPoly == usfn39P)

def usfn40E : RingExpr := (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 0) (.pow (.var 3) 3)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))))))))
def usfn40P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨14,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨16,1⟩ .unit))) (.num (0)))))))))
theorem usfn40_norm : (reflectRing usfn40E).toPoly=usfn40P := by
  exact eq_of_beq (by decide : (reflectRing usfn40E).toPoly == usfn40P)

def usfn41E : RingExpr := (.add usfn39E usfn40E)
def usfn41P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨14,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨16,1⟩ .unit))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨15,1⟩ .unit))) (.num (0))))))))))
theorem usfn41_norm : (reflectRing usfn41E).toPoly=usfn41P := by
  change (reflectRing usfn39E).toPoly.combine (reflectRing usfn40E).toPoly=usfn41P
  rw [usfn39_norm, usfn40_norm]
  exact eq_of_beq (by decide : usfn39P.combine usfn40P == usfn41P)

def usfn42E : RingExpr := (.add usfn38E usfn41E)
def usfn42P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨14,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨16,1⟩ .unit))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨15,1⟩ .unit))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.num (0)))))))))))
theorem usfn42_norm : (reflectRing usfn42E).toPoly=usfn42P := by
  change (reflectRing usfn38E).toPoly.combine (reflectRing usfn41E).toPoly=usfn42P
  rw [usfn38_norm, usfn41_norm]
  exact eq_of_beq (by decide : usfn38P.combine usfn41P == usfn42P)

def usfn43E : RingExpr := (.add usfn37E usfn42E)
def usfn43P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨14,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨15,1⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨16,1⟩ .unit))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨15,1⟩ .unit))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.num (0))))))))))))
theorem usfn43_norm : (reflectRing usfn43E).toPoly=usfn43P := by
  change (reflectRing usfn37E).toPoly.combine (reflectRing usfn42E).toPoly=usfn43P
  rw [usfn37_norm, usfn42_norm]
  exact eq_of_beq (by decide : usfn37P.combine usfn42P == usfn43P)

def usfn44E : RingExpr := (.add usfn36E usfn43E)
def usfn44P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨14,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨15,1⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨16,1⟩ .unit))) (.add (-2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨15,1⟩ .unit))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.num (0)))))))))))))
theorem usfn44_norm : (reflectRing usfn44E).toPoly=usfn44P := by
  change (reflectRing usfn36E).toPoly.combine (reflectRing usfn43E).toPoly=usfn44P
  rw [usfn36_norm, usfn43_norm]
  exact eq_of_beq (by decide : usfn36P.combine usfn43P == usfn44P)

def usfn45E : RingExpr := (.add usfn35E usfn44E)
def usfn45P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨14,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨15,1⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨16,1⟩ .unit))) (.add (-2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨15,1⟩ .unit))) (.add (-1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.num (0))))))))))))))
theorem usfn45_norm : (reflectRing usfn45E).toPoly=usfn45P := by
  change (reflectRing usfn35E).toPoly.combine (reflectRing usfn44E).toPoly=usfn45P
  rw [usfn35_norm, usfn44_norm]
  exact eq_of_beq (by decide : usfn35P.combine usfn44P == usfn45P)

def usfn46E : RingExpr := (.add usfn25E usfn45E)
def usfn46P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨14,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨15,1⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨16,1⟩ .unit))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨11,1⟩ .unit))) (.add (-2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨15,1⟩ .unit))) (.add (-1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.num (0)))))))))))))))
theorem usfn46_norm : (reflectRing usfn46E).toPoly=usfn46P := by
  change (reflectRing usfn25E).toPoly.combine (reflectRing usfn45E).toPoly=usfn46P
  rw [usfn25_norm, usfn45_norm]
  exact eq_of_beq (by decide : usfn25P.combine usfn45P == usfn46P)

def usfn47E : RingExpr := (.add usfn24E usfn46E)
def usfn47P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨14,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨15,1⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨16,1⟩ .unit))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨11,1⟩ .unit))) (.add (-2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨15,1⟩ .unit))) (.add (-1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (-1) (.mult ⟨2,1⟩ (.mult ⟨11,1⟩ .unit)) (.num (0))))))))))))))))
theorem usfn47_norm : (reflectRing usfn47E).toPoly=usfn47P := by
  change (reflectRing usfn24E).toPoly.combine (reflectRing usfn46E).toPoly=usfn47P
  rw [usfn24_norm, usfn46_norm]
  exact eq_of_beq (by decide : usfn24P.combine usfn46P == usfn47P)

def usfn48E : RingExpr := (.mul usfn4E usfn47E)
def usfn48P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨14,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨16,1⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (-2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (-1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (-1) (.mult ⟨2,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))) (.num (0))))))))))))))))
theorem usfn48_norm : (reflectRing usfn48E).toPoly=usfn48P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn47E).toPoly=usfn48P
  rw [usfn4_norm, usfn47_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn47P == usfn48P)

def usfn49E : RingExpr := (.mul usfn1E usfn48E)
def usfn49P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨12,1⟩ .unit)))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨12,1⟩ .unit)))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨12,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨14,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨15,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨16,1⟩ .unit))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨15,1⟩ .unit))))) (.add (-1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-1) (.mult ⟨2,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))) (.num (0))))))))))))))))
theorem usfn49_norm : (reflectRing usfn49E).toPoly=usfn49P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn48E).toPoly=usfn49P
  rw [usfn1_norm, usfn48_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn48P == usfn49P)

def usfn50E : RingExpr := (.mul usfn0E usfn49E)
def usfn50P : Lean.Grind.CommRing.Poly := (.num (0))
theorem usfn50_norm : (reflectRing usfn50E).toPoly=usfn50P := by
  change (reflectRing usfn0E).toPoly.mul (reflectRing usfn49E).toPoly=usfn50P
  rw [usfn0_norm, usfn49_norm]
  exact eq_of_beq (by decide : usfn0P.mul usfn49P == usfn50P)

def usfn51E : RingExpr := (.add usfn34E usfn50E)
def usfn51P : Lean.Grind.CommRing.Poly := (.num (0))
theorem usfn51_norm : (reflectRing usfn51E).toPoly=usfn51P := by
  change (reflectRing usfn34E).toPoly.combine (reflectRing usfn50E).toPoly=usfn51P
  rw [usfn34_norm, usfn50_norm]
  exact eq_of_beq (by decide : usfn34P.combine usfn50P == usfn51P)

def usfn52E : RingExpr := (.pow (.var 8) 3)
def usfn52P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨8,3⟩ .unit) (.num (0)))
theorem usfn52_norm : (reflectRing usfn52E).toPoly=usfn52P := by
  exact eq_of_beq (by decide : (reflectRing usfn52E).toPoly == usfn52P)

def usfn53E : RingExpr := (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 3) (.var 4))))
def usfn53P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.num (0)))
theorem usfn53_norm : (reflectRing usfn53E).toPoly=usfn53P := by
  exact eq_of_beq (by decide : (reflectRing usfn53E).toPoly == usfn53P)

def usfn54E : RingExpr := (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2))))
def usfn54P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨15,1⟩ .unit))) (.num (0)))
theorem usfn54_norm : (reflectRing usfn54E).toPoly=usfn54P := by
  exact eq_of_beq (by decide : (reflectRing usfn54E).toPoly == usfn54P)

def usfn55E : RingExpr := (.mul (.int 4) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2))))
def usfn55P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.num (0)))
theorem usfn55_norm : (reflectRing usfn55E).toPoly=usfn55P := by
  exact eq_of_beq (by decide : (reflectRing usfn55E).toPoly == usfn55P)

def usfn56E : RingExpr := (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))
def usfn56P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨2,3⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))) (.num (0)))
theorem usfn56_norm : (reflectRing usfn56E).toPoly=usfn56P := by
  exact eq_of_beq (by decide : (reflectRing usfn56E).toPoly == usfn56P)

def usfn57E : RingExpr := (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))
def usfn57P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.num (0)))
theorem usfn57_norm : (reflectRing usfn57E).toPoly=usfn57P := by
  exact eq_of_beq (by decide : (reflectRing usfn57E).toPoly == usfn57P)

def usfn58E : RingExpr := (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))))
def usfn58P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.num (0)))
theorem usfn58_norm : (reflectRing usfn58E).toPoly=usfn58P := by
  exact eq_of_beq (by decide : (reflectRing usfn58E).toPoly == usfn58P)

def usfn59E : RingExpr := (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3)))))
def usfn59P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.num (0)))
theorem usfn59_norm : (reflectRing usfn59E).toPoly=usfn59P := by
  exact eq_of_beq (by decide : (reflectRing usfn59E).toPoly == usfn59P)

def usfn60E : RingExpr := (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))
def usfn60P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.num (0)))
theorem usfn60_norm : (reflectRing usfn60E).toPoly=usfn60P := by
  exact eq_of_beq (by decide : (reflectRing usfn60E).toPoly == usfn60P)

def usfn61E : RingExpr := (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))
def usfn61P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.num (0)))
theorem usfn61_norm : (reflectRing usfn61E).toPoly=usfn61P := by
  exact eq_of_beq (by decide : (reflectRing usfn61E).toPoly == usfn61P)

def usfn62E : RingExpr := (.mul (.int (-8)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))
def usfn62P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.num (0)))
theorem usfn62_norm : (reflectRing usfn62E).toPoly=usfn62P := by
  exact eq_of_beq (by decide : (reflectRing usfn62E).toPoly == usfn62P)

def usfn63E : RingExpr := (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))
def usfn63P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.num (0)))))))
theorem usfn63_norm : (reflectRing usfn63E).toPoly=usfn63P := by
  exact eq_of_beq (by decide : (reflectRing usfn63E).toPoly == usfn63P)

def usfn64E : RingExpr := (.add usfn62E usfn63E)
def usfn64P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.num (0))))))))
theorem usfn64_norm : (reflectRing usfn64E).toPoly=usfn64P := by
  change (reflectRing usfn62E).toPoly.combine (reflectRing usfn63E).toPoly=usfn64P
  rw [usfn62_norm, usfn63_norm]
  exact eq_of_beq (by decide : usfn62P.combine usfn63P == usfn64P)

def usfn65E : RingExpr := (.add usfn8E usfn64E)
def usfn65P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.num (0)))))))))
theorem usfn65_norm : (reflectRing usfn65E).toPoly=usfn65P := by
  change (reflectRing usfn8E).toPoly.combine (reflectRing usfn64E).toPoly=usfn65P
  rw [usfn8_norm, usfn64_norm]
  exact eq_of_beq (by decide : usfn8P.combine usfn64P == usfn65P)

def usfn66E : RingExpr := (.add usfn61E usfn65E)
def usfn66P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.num (0))))))))))
theorem usfn66_norm : (reflectRing usfn66E).toPoly=usfn66P := by
  change (reflectRing usfn61E).toPoly.combine (reflectRing usfn65E).toPoly=usfn66P
  rw [usfn61_norm, usfn65_norm]
  exact eq_of_beq (by decide : usfn61P.combine usfn65P == usfn66P)

def usfn67E : RingExpr := (.add usfn60E usfn66E)
def usfn67P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.num (0)))))))))))
theorem usfn67_norm : (reflectRing usfn67E).toPoly=usfn67P := by
  change (reflectRing usfn60E).toPoly.combine (reflectRing usfn66E).toPoly=usfn67P
  rw [usfn60_norm, usfn66_norm]
  exact eq_of_beq (by decide : usfn60P.combine usfn66P == usfn67P)

def usfn68E : RingExpr := (.add usfn59E usfn67E)
def usfn68P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.num (0))))))))))))
theorem usfn68_norm : (reflectRing usfn68E).toPoly=usfn68P := by
  change (reflectRing usfn59E).toPoly.combine (reflectRing usfn67E).toPoly=usfn68P
  rw [usfn59_norm, usfn67_norm]
  exact eq_of_beq (by decide : usfn59P.combine usfn67P == usfn68P)

def usfn69E : RingExpr := (.add usfn58E usfn68E)
def usfn69P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.num (0)))))))))))))
theorem usfn69_norm : (reflectRing usfn69E).toPoly=usfn69P := by
  change (reflectRing usfn58E).toPoly.combine (reflectRing usfn68E).toPoly=usfn69P
  rw [usfn58_norm, usfn68_norm]
  exact eq_of_beq (by decide : usfn58P.combine usfn68P == usfn69P)

def usfn70E : RingExpr := (.add usfn57E usfn69E)
def usfn70P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.num (0))))))))))))))
theorem usfn70_norm : (reflectRing usfn70E).toPoly=usfn70P := by
  change (reflectRing usfn57E).toPoly.combine (reflectRing usfn69E).toPoly=usfn70P
  rw [usfn57_norm, usfn69_norm]
  exact eq_of_beq (by decide : usfn57P.combine usfn69P == usfn70P)

def usfn71E : RingExpr := (.add usfn56E usfn70E)
def usfn71P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨2,3⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.num (0)))))))))))))))
theorem usfn71_norm : (reflectRing usfn71E).toPoly=usfn71P := by
  change (reflectRing usfn56E).toPoly.combine (reflectRing usfn70E).toPoly=usfn71P
  rw [usfn56_norm, usfn70_norm]
  exact eq_of_beq (by decide : usfn56P.combine usfn70P == usfn71P)

def usfn72E : RingExpr := (.add usfn55E usfn71E)
def usfn72P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨2,3⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.num (0))))))))))))))))
theorem usfn72_norm : (reflectRing usfn72E).toPoly=usfn72P := by
  change (reflectRing usfn55E).toPoly.combine (reflectRing usfn71E).toPoly=usfn72P
  rw [usfn55_norm, usfn71_norm]
  exact eq_of_beq (by decide : usfn55P.combine usfn71P == usfn72P)

def usfn73E : RingExpr := (.add usfn54E usfn72E)
def usfn73P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨2,3⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨15,1⟩ .unit))) (.num (0)))))))))))))))))
theorem usfn73_norm : (reflectRing usfn73E).toPoly=usfn73P := by
  change (reflectRing usfn54E).toPoly.combine (reflectRing usfn72E).toPoly=usfn73P
  rw [usfn54_norm, usfn72_norm]
  exact eq_of_beq (by decide : usfn54P.combine usfn72P == usfn73P)

def usfn74E : RingExpr := (.add usfn53E usfn73E)
def usfn74P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨2,3⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨15,1⟩ .unit))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.num (0))))))))))))))))))
theorem usfn74_norm : (reflectRing usfn74E).toPoly=usfn74P := by
  change (reflectRing usfn53E).toPoly.combine (reflectRing usfn73E).toPoly=usfn74P
  rw [usfn53_norm, usfn73_norm]
  exact eq_of_beq (by decide : usfn53P.combine usfn73P == usfn74P)

def usfn75E : RingExpr := (.add usfn6E usfn74E)
def usfn75P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨2,3⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨15,1⟩ .unit))) (.add (1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.num (0)))))))))))))))))))
theorem usfn75_norm : (reflectRing usfn75E).toPoly=usfn75P := by
  change (reflectRing usfn6E).toPoly.combine (reflectRing usfn74E).toPoly=usfn75P
  rw [usfn6_norm, usfn74_norm]
  exact eq_of_beq (by decide : usfn6P.combine usfn74P == usfn75P)

def usfn76E : RingExpr := (.add usfn5E usfn75E)
def usfn76P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨2,3⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨15,1⟩ .unit)))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨11,1⟩ .unit)))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨12,1⟩ .unit)))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨15,1⟩ .unit))) (.add (1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨11,1⟩ .unit))) (.add (1) (.mult ⟨2,1⟩ (.mult ⟨11,1⟩ .unit)) (.num (0))))))))))))))))))))
theorem usfn76_norm : (reflectRing usfn76E).toPoly=usfn76P := by
  change (reflectRing usfn5E).toPoly.combine (reflectRing usfn75E).toPoly=usfn76P
  rw [usfn5_norm, usfn75_norm]
  exact eq_of_beq (by decide : usfn5P.combine usfn75P == usfn76P)

def usfn77E : RingExpr := (.mul usfn52E usfn76E)
def usfn77P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨12,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨15,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨11,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨12,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (4) (.mult ⟨2,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨11,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨12,1⟩ .unit))))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨15,1⟩ .unit))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨11,1⟩ .unit))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨12,1⟩ .unit))))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨11,1⟩ .unit)))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨15,1⟩ .unit)))) (.add (1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨8,3⟩ (.mult ⟨11,1⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨11,1⟩ .unit)))) (.add (1) (.mult ⟨2,1⟩ (.mult ⟨8,3⟩ (.mult ⟨11,1⟩ .unit))) (.num (0))))))))))))))))))))
theorem usfn77_norm : (reflectRing usfn77E).toPoly=usfn77P := by
  change (reflectRing usfn52E).toPoly.mul (reflectRing usfn76E).toPoly=usfn77P
  rw [usfn52_norm, usfn76_norm]
  exact eq_of_beq (by decide : usfn52P.mul usfn76P == usfn77P)

def usfn78E : RingExpr := (.mul usfn3E usfn77E)
def usfn78P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨12,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨15,1⟩ .unit)))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨12,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (4) (.mult ⟨2,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨12,1⟩ .unit)))))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨15,1⟩ .unit)))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨12,1⟩ .unit)))))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨15,1⟩ .unit))))) (.add (1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨11,1⟩ .unit))))) (.add (1) (.mult ⟨2,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨11,1⟩ .unit)))) (.num (0))))))))))))))))))))
theorem usfn78_norm : (reflectRing usfn78E).toPoly=usfn78P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn77E).toPoly=usfn78P
  rw [usfn3_norm, usfn77_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn77P == usfn78P)

def usfn79E : RingExpr := (.mul usfn2E usfn78E)
def usfn79P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (4) (.mult ⟨2,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))) (.add (1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (1) (.mult ⟨2,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))) (.num (0))))))))))))))))))))
theorem usfn79_norm : (reflectRing usfn79E).toPoly=usfn79P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn78E).toPoly=usfn79P
  rw [usfn2_norm, usfn78_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn78P == usfn79P)

#print axioms usfn79_norm
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
