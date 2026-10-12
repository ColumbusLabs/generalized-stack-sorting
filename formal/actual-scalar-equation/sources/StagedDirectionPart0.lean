import DirectionReflection
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

def dz2n0E : RingExpr := (.int (-9))
def dz2n0P : Lean.Grind.CommRing.Poly := (.num (-9))
theorem dz2n0_norm : (reflectRing dz2n0E).toPoly=dz2n0P := by
  exact eq_of_beq (by decide : (reflectRing dz2n0E).toPoly == dz2n0P)

def dz2n1E : RingExpr := (.var 17)
def dz2n1P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨17,1⟩ .unit) (.num (0)))
theorem dz2n1_norm : (reflectRing dz2n1E).toPoly=dz2n1P := by
  exact eq_of_beq (by decide : (reflectRing dz2n1E).toPoly == dz2n1P)

def dz2n2E : RingExpr := (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 4))))
def dz2n2P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ .unit))) (.num (0)))
theorem dz2n2_norm : (reflectRing dz2n2E).toPoly=dz2n2P := by
  exact eq_of_beq (by decide : (reflectRing dz2n2E).toPoly == dz2n2P)

def dz2n3E : RingExpr := (.mul (.int 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 3))))
def dz2n3P : Lean.Grind.CommRing.Poly := (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.num (0)))
theorem dz2n3_norm : (reflectRing dz2n3E).toPoly=dz2n3P := by
  exact eq_of_beq (by decide : (reflectRing dz2n3E).toPoly == dz2n3P)

def dz2n4E : RingExpr := (.mul (.int 12) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))
def dz2n4P : Lean.Grind.CommRing.Poly := (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.num (0)))
theorem dz2n4_norm : (reflectRing dz2n4E).toPoly=dz2n4P := by
  exact eq_of_beq (by decide : (reflectRing dz2n4E).toPoly == dz2n4P)

def dz2n5E : RingExpr := (.mul (.int 16) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 2))))
def dz2n5P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ .unit))) (.num (0)))
theorem dz2n5_norm : (reflectRing dz2n5E).toPoly=dz2n5P := by
  exact eq_of_beq (by decide : (reflectRing dz2n5E).toPoly == dz2n5P)

def dz2n6E : RingExpr := (.mul (.int 24) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))
def dz2n6P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.num (0)))
theorem dz2n6_norm : (reflectRing dz2n6E).toPoly=dz2n6P := by
  exact eq_of_beq (by decide : (reflectRing dz2n6E).toPoly == dz2n6P)

def dz2n7E : RingExpr := (.mul (.int 48) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))
def dz2n7P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.num (0)))
theorem dz2n7_norm : (reflectRing dz2n7E).toPoly=dz2n7P := by
  exact eq_of_beq (by decide : (reflectRing dz2n7E).toPoly == dz2n7P)

def dz2n8E : RingExpr := (.mul (.int 48) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))
def dz2n8P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit))) (.num (0)))
theorem dz2n8_norm : (reflectRing dz2n8E).toPoly=dz2n8P := by
  exact eq_of_beq (by decide : (reflectRing dz2n8E).toPoly == dz2n8P)

def dz2n9E : RingExpr := (.mul (.int (-96)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))
def dz2n9P : Lean.Grind.CommRing.Poly := (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.num (0)))
theorem dz2n9_norm : (reflectRing dz2n9E).toPoly=dz2n9P := by
  exact eq_of_beq (by decide : (reflectRing dz2n9E).toPoly == dz2n9P)

def dz2n10E : RingExpr := (.mul (.int (-64)) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))
def dz2n10P : Lean.Grind.CommRing.Poly := (.add (-64) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit)))) (.num (0)))
theorem dz2n10_norm : (reflectRing dz2n10E).toPoly=dz2n10P := by
  exact eq_of_beq (by decide : (reflectRing dz2n10E).toPoly == dz2n10P)

def dz2n11E : RingExpr := (.mul (.int (-40)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))))
def dz2n11P : Lean.Grind.CommRing.Poly := (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ .unit)))) (.num (0)))
theorem dz2n11_norm : (reflectRing dz2n11E).toPoly=dz2n11P := by
  exact eq_of_beq (by decide : (reflectRing dz2n11E).toPoly == dz2n11P)

def dz2n12E : RingExpr := (.mul (.int (-24)) (.mul (.var 0) (.mul (.var 6) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))))
def dz2n12P : Lean.Grind.CommRing.Poly := (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))
theorem dz2n12_norm : (reflectRing dz2n12E).toPoly=dz2n12P := by
  exact eq_of_beq (by decide : (reflectRing dz2n12E).toPoly == dz2n12P)

def dz2n13E : RingExpr := (.mul (.int 24) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))
def dz2n13P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))
theorem dz2n13_norm : (reflectRing dz2n13E).toPoly=dz2n13P := by
  exact eq_of_beq (by decide : (reflectRing dz2n13E).toPoly == dz2n13P)

def dz2n14E : RingExpr := (.mul (.int 24) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))
def dz2n14P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))
theorem dz2n14_norm : (reflectRing dz2n14E).toPoly=dz2n14P := by
  exact eq_of_beq (by decide : (reflectRing dz2n14E).toPoly == dz2n14P)

def dz2n15E : RingExpr := (.mul (.int 48) (.mul (.var 6) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 7) (.pow (.var 4) 3)))))
def dz2n15P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))
theorem dz2n15_norm : (reflectRing dz2n15E).toPoly=dz2n15P := by
  exact eq_of_beq (by decide : (reflectRing dz2n15E).toPoly == dz2n15P)

def dz2n16E : RingExpr := (.mul (.int 48) (.mul (.var 6) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))
def dz2n16P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))
theorem dz2n16_norm : (reflectRing dz2n16E).toPoly=dz2n16P := by
  exact eq_of_beq (by decide : (reflectRing dz2n16E).toPoly == dz2n16P)

def dz2n17E : RingExpr := (.mul (.int 48) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))
def dz2n17P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))
theorem dz2n17_norm : (reflectRing dz2n17E).toPoly=dz2n17P := by
  exact eq_of_beq (by decide : (reflectRing dz2n17E).toPoly == dz2n17P)

def dz2n18E : RingExpr := (.mul (.int 48) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3)))))
def dz2n18P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit)))) (.num (0)))
theorem dz2n18_norm : (reflectRing dz2n18E).toPoly=dz2n18P := by
  exact eq_of_beq (by decide : (reflectRing dz2n18E).toPoly == dz2n18P)

def dz2n19E : RingExpr := (.mul (.int 48) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))
def dz2n19P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.num (0)))
theorem dz2n19_norm : (reflectRing dz2n19E).toPoly=dz2n19P := by
  exact eq_of_beq (by decide : (reflectRing dz2n19E).toPoly == dz2n19P)

def dz2n20E : RingExpr := (.add (.mul (.int 72) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 96) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-96)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3)))))) (.add (.mul (.int (-96)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.add (.mul (.int (-96)) (.mul (.var 0) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.mul (.int 96) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))))))))
def dz2n20P : Lean.Grind.CommRing.Poly := (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.num (0))))))))
theorem dz2n20_norm : (reflectRing dz2n20E).toPoly=dz2n20P := by
  exact eq_of_beq (by decide : (reflectRing dz2n20E).toPoly == dz2n20P)

def dz2n21E : RingExpr := (.add dz2n19E dz2n20E)
def dz2n21P : Lean.Grind.CommRing.Poly := (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.num (0)))))))))
theorem dz2n21_norm : (reflectRing dz2n21E).toPoly=dz2n21P := by
  change (reflectRing dz2n19E).toPoly.combine (reflectRing dz2n20E).toPoly=dz2n21P
  rw [dz2n19_norm, dz2n20_norm]
  exact eq_of_beq (by decide : dz2n19P.combine dz2n20P == dz2n21P)

def dz2n22E : RingExpr := (.add dz2n18E dz2n21E)
def dz2n22P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.num (0))))))))))
theorem dz2n22_norm : (reflectRing dz2n22E).toPoly=dz2n22P := by
  change (reflectRing dz2n18E).toPoly.combine (reflectRing dz2n21E).toPoly=dz2n22P
  rw [dz2n18_norm, dz2n21_norm]
  exact eq_of_beq (by decide : dz2n18P.combine dz2n21P == dz2n22P)

def dz2n23E : RingExpr := (.add dz2n17E dz2n22E)
def dz2n23P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.num (0)))))))))))
theorem dz2n23_norm : (reflectRing dz2n23E).toPoly=dz2n23P := by
  change (reflectRing dz2n17E).toPoly.combine (reflectRing dz2n22E).toPoly=dz2n23P
  rw [dz2n17_norm, dz2n22_norm]
  exact eq_of_beq (by decide : dz2n17P.combine dz2n22P == dz2n23P)

def dz2n24E : RingExpr := (.add dz2n16E dz2n23E)
def dz2n24P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.num (0))))))))))))
theorem dz2n24_norm : (reflectRing dz2n24E).toPoly=dz2n24P := by
  change (reflectRing dz2n16E).toPoly.combine (reflectRing dz2n23E).toPoly=dz2n24P
  rw [dz2n16_norm, dz2n23_norm]
  exact eq_of_beq (by decide : dz2n16P.combine dz2n23P == dz2n24P)

def dz2n25E : RingExpr := (.add dz2n15E dz2n24E)
def dz2n25P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.num (0)))))))))))))
theorem dz2n25_norm : (reflectRing dz2n25E).toPoly=dz2n25P := by
  change (reflectRing dz2n15E).toPoly.combine (reflectRing dz2n24E).toPoly=dz2n25P
  rw [dz2n15_norm, dz2n24_norm]
  exact eq_of_beq (by decide : dz2n15P.combine dz2n24P == dz2n25P)

def dz2n26E : RingExpr := (.add dz2n14E dz2n25E)
def dz2n26P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (24) (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0))))))))))))))
theorem dz2n26_norm : (reflectRing dz2n26E).toPoly=dz2n26P := by
  change (reflectRing dz2n14E).toPoly.combine (reflectRing dz2n25E).toPoly=dz2n26P
  rw [dz2n14_norm, dz2n25_norm]
  exact eq_of_beq (by decide : dz2n14P.combine dz2n25P == dz2n26P)

def dz2n27E : RingExpr := (.add dz2n13E dz2n26E)
def dz2n27P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (24) (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))))))))))))))
theorem dz2n27_norm : (reflectRing dz2n27E).toPoly=dz2n27P := by
  change (reflectRing dz2n13E).toPoly.combine (reflectRing dz2n26E).toPoly=dz2n27P
  rw [dz2n13_norm, dz2n26_norm]
  exact eq_of_beq (by decide : dz2n13P.combine dz2n26P == dz2n27P)

def dz2n28E : RingExpr := (.add dz2n12E dz2n27E)
def dz2n28P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (24) (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0))))))))))))))))
theorem dz2n28_norm : (reflectRing dz2n28E).toPoly=dz2n28P := by
  change (reflectRing dz2n12E).toPoly.combine (reflectRing dz2n27E).toPoly=dz2n28P
  rw [dz2n12_norm, dz2n27_norm]
  exact eq_of_beq (by decide : dz2n12P.combine dz2n27P == dz2n28P)

def dz2n29E : RingExpr := (.add dz2n11E dz2n28E)
def dz2n29P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (24) (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))))))))))))))))
theorem dz2n29_norm : (reflectRing dz2n29E).toPoly=dz2n29P := by
  change (reflectRing dz2n11E).toPoly.combine (reflectRing dz2n28E).toPoly=dz2n29P
  rw [dz2n11_norm, dz2n28_norm]
  exact eq_of_beq (by decide : dz2n11P.combine dz2n28P == dz2n29P)

def dz2n30E : RingExpr := (.add dz2n10E dz2n29E)
def dz2n30P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-64) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit)))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (24) (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0))))))))))))))))))
theorem dz2n30_norm : (reflectRing dz2n30E).toPoly=dz2n30P := by
  change (reflectRing dz2n10E).toPoly.combine (reflectRing dz2n29E).toPoly=dz2n30P
  rw [dz2n10_norm, dz2n29_norm]
  exact eq_of_beq (by decide : dz2n10P.combine dz2n29P == dz2n30P)

def dz2n31E : RingExpr := (.add dz2n9E dz2n30E)
def dz2n31P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-64) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit)))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (24) (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))))))))))))))))))
theorem dz2n31_norm : (reflectRing dz2n31E).toPoly=dz2n31P := by
  change (reflectRing dz2n9E).toPoly.combine (reflectRing dz2n30E).toPoly=dz2n31P
  rw [dz2n9_norm, dz2n30_norm]
  exact eq_of_beq (by decide : dz2n9P.combine dz2n30P == dz2n31P)

def dz2n32E : RingExpr := (.add dz2n8E dz2n31E)
def dz2n32P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-64) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit)))) (.add (48) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (24) (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0))))))))))))))))))))
theorem dz2n32_norm : (reflectRing dz2n32E).toPoly=dz2n32P := by
  change (reflectRing dz2n8E).toPoly.combine (reflectRing dz2n31E).toPoly=dz2n32P
  rw [dz2n8_norm, dz2n31_norm]
  exact eq_of_beq (by decide : dz2n8P.combine dz2n31P == dz2n32P)

def dz2n33E : RingExpr := (.add dz2n7E dz2n32E)
def dz2n33P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-64) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit)))) (.add (48) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (24) (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.num (0)))))))))))))))))))))
theorem dz2n33_norm : (reflectRing dz2n33E).toPoly=dz2n33P := by
  change (reflectRing dz2n7E).toPoly.combine (reflectRing dz2n32E).toPoly=dz2n33P
  rw [dz2n7_norm, dz2n32_norm]
  exact eq_of_beq (by decide : dz2n7P.combine dz2n32P == dz2n33P)

def dz2n34E : RingExpr := (.add dz2n6E dz2n33E)
def dz2n34P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.add (-64) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit)))) (.add (48) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (24) (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.num (0))))))))))))))))))))))
theorem dz2n34_norm : (reflectRing dz2n34E).toPoly=dz2n34P := by
  change (reflectRing dz2n6E).toPoly.combine (reflectRing dz2n33E).toPoly=dz2n34P
  rw [dz2n6_norm, dz2n33_norm]
  exact eq_of_beq (by decide : dz2n6P.combine dz2n33P == dz2n34P)

def dz2n35E : RingExpr := (.add dz2n5E dz2n34E)
def dz2n35P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ .unit))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.add (-64) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit)))) (.add (48) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (24) (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.num (0)))))))))))))))))))))))
theorem dz2n35_norm : (reflectRing dz2n35E).toPoly=dz2n35P := by
  change (reflectRing dz2n5E).toPoly.combine (reflectRing dz2n34E).toPoly=dz2n35P
  rw [dz2n5_norm, dz2n34_norm]
  exact eq_of_beq (by decide : dz2n5P.combine dz2n34P == dz2n35P)

def dz2n36E : RingExpr := (.add dz2n4E dz2n35E)
def dz2n36P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ .unit))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.add (-64) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit)))) (.add (48) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (24) (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.num (0))))))))))))))))))))))))
theorem dz2n36_norm : (reflectRing dz2n36E).toPoly=dz2n36P := by
  change (reflectRing dz2n4E).toPoly.combine (reflectRing dz2n35E).toPoly=dz2n36P
  rw [dz2n4_norm, dz2n35_norm]
  exact eq_of_beq (by decide : dz2n4P.combine dz2n35P == dz2n36P)

def dz2n37E : RingExpr := (.add dz2n3E dz2n36E)
def dz2n37P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ .unit))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.add (-64) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit)))) (.add (48) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (24) (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.num (0)))))))))))))))))))))))))
theorem dz2n37_norm : (reflectRing dz2n37E).toPoly=dz2n37P := by
  change (reflectRing dz2n3E).toPoly.combine (reflectRing dz2n36E).toPoly=dz2n37P
  rw [dz2n3_norm, dz2n36_norm]
  exact eq_of_beq (by decide : dz2n3P.combine dz2n36P == dz2n37P)

def dz2n38E : RingExpr := (.add dz2n2E dz2n37E)
def dz2n38P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ .unit))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ .unit)))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.add (-64) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit)))) (.add (48) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (24) (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ .unit))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.num (0))))))))))))))))))))))))))
theorem dz2n38_norm : (reflectRing dz2n38E).toPoly=dz2n38P := by
  change (reflectRing dz2n2E).toPoly.combine (reflectRing dz2n37E).toPoly=dz2n38P
  rw [dz2n2_norm, dz2n37_norm]
  exact eq_of_beq (by decide : dz2n2P.combine dz2n37P == dz2n38P)

def dz2n39E : RingExpr := (.mul dz2n1E dz2n38E)
def dz2n39P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit)))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit))))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit)))) (.add (-64) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit))))) (.add (48) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit)))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit))))) (.add (24) (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨17,1⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit)))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨17,1⟩ .unit)))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨17,1⟩ .unit)))) (.num (0))))))))))))))))))))))))))
theorem dz2n39_norm : (reflectRing dz2n39E).toPoly=dz2n39P := by
  change (reflectRing dz2n1E).toPoly.mul (reflectRing dz2n38E).toPoly=dz2n39P
  rw [dz2n1_norm, dz2n38_norm]
  exact eq_of_beq (by decide : dz2n1P.mul dz2n38P == dz2n39P)

def dz2n40E : RingExpr := (.var 2)
def dz2n40P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨2,1⟩ .unit) (.num (0)))
theorem dz2n40_norm : (reflectRing dz2n40E).toPoly=dz2n40P := by
  exact eq_of_beq (by decide : (reflectRing dz2n40E).toPoly == dz2n40P)

def dz2n41E : RingExpr := (.mul dz2n39E dz2n40E)
def dz2n41P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (48) (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-64) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit))))) (.add (48) (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit)))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (48) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit)))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (12) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨17,1⟩ .unit)))) (.num (0))))))))))))))))))))))))))
theorem dz2n41_norm : (reflectRing dz2n41E).toPoly=dz2n41P := by
  change (reflectRing dz2n39E).toPoly.mul (reflectRing dz2n40E).toPoly=dz2n41P
  rw [dz2n39_norm, dz2n40_norm]
  exact eq_of_beq (by decide : dz2n39P.mul dz2n40P == dz2n41P)

def dz2n42E : RingExpr := (.mul dz2n0E dz2n41E)
def dz2n42P : Lean.Grind.CommRing.Poly := (.add (-432) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-432) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (864) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (864) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-432) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (864) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-144) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-432) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (864) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-864) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (360) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-864) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (216) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-432) (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-216) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit))))) (.add (576) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-432) (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit)))) (.add (-216) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-648) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-216) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (72) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-432) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit)))) (.add (-108) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-108) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨17,1⟩ .unit)))) (.num (0))))))))))))))))))))))))))
theorem dz2n42_norm : (reflectRing dz2n42E).toPoly=dz2n42P := by
  change (reflectRing dz2n0E).toPoly.mul (reflectRing dz2n41E).toPoly=dz2n42P
  rw [dz2n0_norm, dz2n41_norm]
  exact eq_of_beq (by decide : dz2n0P.mul dz2n41P == dz2n42P)

def dz2n43E : RingExpr := (.mul (.var 1) (.var 3))
def dz2n43P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨1,1⟩ (.mult ⟨3,1⟩ .unit)) (.num (0)))
theorem dz2n43_norm : (reflectRing dz2n43E).toPoly=dz2n43P := by
  exact eq_of_beq (by decide : (reflectRing dz2n43E).toPoly == dz2n43P)

def dz2n44E : RingExpr := (.mul dz2n39E dz2n43E)
def dz2n44P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,8⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (48) (.mult ⟨1,3⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit))))) (.add (48) (.mult ⟨1,3⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (96) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit))))) (.add (96) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (24) (.mult ⟨1,3⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit)))) (.add (-64) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (72) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit))))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit))))) (.add (12) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨17,1⟩ .unit)))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨17,1⟩ .unit))))) (.num (0))))))))))))))))))))))))))
theorem dz2n44_norm : (reflectRing dz2n44E).toPoly=dz2n44P := by
  change (reflectRing dz2n39E).toPoly.mul (reflectRing dz2n43E).toPoly=dz2n44P
  rw [dz2n39_norm, dz2n43_norm]
  exact eq_of_beq (by decide : dz2n39P.mul dz2n43P == dz2n44P)

def dz2n45E : RingExpr := (.mul dz2n0E dz2n44E)
def dz2n45P : Lean.Grind.CommRing.Poly := (.add (-432) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,8⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-432) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (864) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (864) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-432) (.mult ⟨1,3⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (864) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (-144) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-432) (.mult ⟨1,3⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (864) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-864) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (360) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-864) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (216) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-432) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-216) (.mult ⟨1,3⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit)))) (.add (576) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-432) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-216) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-648) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-216) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (72) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-432) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-108) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨17,1⟩ .unit)))) (.add (-108) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨17,1⟩ .unit))))) (.num (0))))))))))))))))))))))))))
theorem dz2n45_norm : (reflectRing dz2n45E).toPoly=dz2n45P := by
  change (reflectRing dz2n0E).toPoly.mul (reflectRing dz2n44E).toPoly=dz2n45P
  rw [dz2n0_norm, dz2n44_norm]
  exact eq_of_beq (by decide : dz2n0P.mul dz2n44P == dz2n45P)

def dz2n46E : RingExpr := (.int 6)
def dz2n46P : Lean.Grind.CommRing.Poly := (.num (6))
theorem dz2n46_norm : (reflectRing dz2n46E).toPoly=dz2n46P := by
  exact eq_of_beq (by decide : (reflectRing dz2n46E).toPoly == dz2n46P)

def dz2n47E : RingExpr := (.mul (.var 5) (.var 2))
def dz2n47P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨2,1⟩ (.mult ⟨5,1⟩ .unit)) (.num (0)))
theorem dz2n47_norm : (reflectRing dz2n47E).toPoly=dz2n47P := by
  exact eq_of_beq (by decide : (reflectRing dz2n47E).toPoly == dz2n47P)

def dz2n48E : RingExpr := (.mul dz2n39E dz2n47E)
def dz2n48P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (48) (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-64) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (48) (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (48) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (12) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit))))) (.num (0))))))))))))))))))))))))))
theorem dz2n48_norm : (reflectRing dz2n48E).toPoly=dz2n48P := by
  change (reflectRing dz2n39E).toPoly.mul (reflectRing dz2n47E).toPoly=dz2n48P
  rw [dz2n39_norm, dz2n47_norm]
  exact eq_of_beq (by decide : dz2n39P.mul dz2n47P == dz2n48P)

def dz2n49E : RingExpr := (.mul dz2n46E dz2n48E)
def dz2n49P : Lean.Grind.CommRing.Poly := (.add (288) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (288) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-576) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))))) (.add (-576) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (288) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (-576) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (96) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (288) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-576) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (576) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (-240) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (576) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (288) (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-384) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (288) (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (144) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))))) (.add (432) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (144) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (288) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (72) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨17,1⟩ .unit))))) (.num (0))))))))))))))))))))))))))
theorem dz2n49_norm : (reflectRing dz2n49E).toPoly=dz2n49P := by
  change (reflectRing dz2n46E).toPoly.mul (reflectRing dz2n48E).toPoly=dz2n49P
  rw [dz2n46_norm, dz2n48_norm]
  exact eq_of_beq (by decide : dz2n46P.mul dz2n48P == dz2n49P)

def dz2n50E : RingExpr := (.int 12)
def dz2n50P : Lean.Grind.CommRing.Poly := (.num (12))
theorem dz2n50_norm : (reflectRing dz2n50E).toPoly=dz2n50P := by
  exact eq_of_beq (by decide : (reflectRing dz2n50E).toPoly == dz2n50P)

def dz2n51E : RingExpr := (.mul (.var 3) (.var 4))
def dz2n51P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ .unit)) (.num (0)))
theorem dz2n51_norm : (reflectRing dz2n51E).toPoly=dz2n51P := by
  exact eq_of_beq (by decide : (reflectRing dz2n51E).toPoly == dz2n51P)

def dz2n52E : RingExpr := (.mul dz2n39E dz2n51E)
def dz2n52P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨3,8⟩ (.mult ⟨4,4⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit)))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨17,1⟩ .unit))))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit)))) (.add (-64) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (48) (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨17,1⟩ .unit)))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (24) (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit)))) (.add (48) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit)))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit)))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit)))) (.num (0))))))))))))))))))))))))))
theorem dz2n52_norm : (reflectRing dz2n52E).toPoly=dz2n52P := by
  change (reflectRing dz2n39E).toPoly.mul (reflectRing dz2n51E).toPoly=dz2n52P
  rw [dz2n39_norm, dz2n51_norm]
  exact eq_of_beq (by decide : dz2n39P.mul dz2n51P == dz2n52P)

def dz2n53E : RingExpr := (.mul dz2n50E dz2n52E)
def dz2n53P : Lean.Grind.CommRing.Poly := (.add (576) (.mult ⟨0,2⟩ (.mult ⟨3,8⟩ (.mult ⟨4,4⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (576) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-1152) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-1152) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (576) (.mult ⟨1,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-1152) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,4⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (192) (.mult ⟨0,2⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit)))) (.add (576) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-1152) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨17,1⟩ .unit))))) (.add (1152) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit)))))) (.add (-480) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (1152) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-288) (.mult ⟨0,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (576) (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (288) (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit)))) (.add (-768) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (576) (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨17,1⟩ .unit)))) (.add (288) (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (864) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit))))) (.add (288) (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨17,1⟩ .unit))))) (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit)))) (.add (576) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨17,1⟩ .unit)))) (.add (144) (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit)))) (.add (144) (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨17,1⟩ .unit)))) (.num (0))))))))))))))))))))))))))
theorem dz2n53_norm : (reflectRing dz2n53E).toPoly=dz2n53P := by
  change (reflectRing dz2n50E).toPoly.mul (reflectRing dz2n52E).toPoly=dz2n53P
  rw [dz2n50_norm, dz2n52_norm]
  exact eq_of_beq (by decide : dz2n50P.mul dz2n52P == dz2n53P)

def dz2n54E : RingExpr := (.mul (.int 6) (.pow (.var 2) 2))
def dz2n54P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨2,2⟩ .unit) (.num (0)))
theorem dz2n54_norm : (reflectRing dz2n54E).toPoly=dz2n54P := by
  exact eq_of_beq (by decide : (reflectRing dz2n54E).toPoly == dz2n54P)

def dz2n55E : RingExpr := (.mul (.int 36) (.mul (.var 4) (.pow (.var 2) 3)))
def dz2n55P : Lean.Grind.CommRing.Poly := (.add (36) (.mult ⟨2,3⟩ (.mult ⟨4,1⟩ .unit)) (.num (0)))
theorem dz2n55_norm : (reflectRing dz2n55E).toPoly=dz2n55P := by
  exact eq_of_beq (by decide : (reflectRing dz2n55E).toPoly == dz2n55P)

def dz2n56E : RingExpr := (.mul (.int 48) (.mul (.pow (.var 2) 5) (.pow (.var 4) 3)))
def dz2n56P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨2,5⟩ (.mult ⟨4,3⟩ .unit)) (.num (0)))
theorem dz2n56_norm : (reflectRing dz2n56E).toPoly=dz2n56P := by
  exact eq_of_beq (by decide : (reflectRing dz2n56E).toPoly == dz2n56P)

def dz2n57E : RingExpr := (.mul (.int 72) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2)))
def dz2n57P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨2,4⟩ (.mult ⟨4,2⟩ .unit)) (.num (0)))
theorem dz2n57_norm : (reflectRing dz2n57E).toPoly=dz2n57P := by
  exact eq_of_beq (by decide : (reflectRing dz2n57E).toPoly == dz2n57P)

def dz2n58E : RingExpr := (.mul (.int (-48)) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))
def dz2n58P : Lean.Grind.CommRing.Poly := (.add (-48) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit))) (.num (0)))
theorem dz2n58_norm : (reflectRing dz2n58E).toPoly=dz2n58P := by
  exact eq_of_beq (by decide : (reflectRing dz2n58E).toPoly == dz2n58P)

def dz2n59E : RingExpr := (.mul (.int (-48)) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 3))))
def dz2n59P : Lean.Grind.CommRing.Poly := (.add (-48) (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ .unit))) (.num (0)))
theorem dz2n59_norm : (reflectRing dz2n59E).toPoly=dz2n59P := by
  exact eq_of_beq (by decide : (reflectRing dz2n59E).toPoly == dz2n59P)

def dz2n60E : RingExpr := (.mul (.int (-24)) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))
def dz2n60P : Lean.Grind.CommRing.Poly := (.add (-24) (.mult ⟨1,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit))) (.num (0)))
theorem dz2n60_norm : (reflectRing dz2n60E).toPoly=dz2n60P := by
  exact eq_of_beq (by decide : (reflectRing dz2n60E).toPoly == dz2n60P)

def dz2n61E : RingExpr := (.mul (.int (-16)) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2))))
def dz2n61P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ .unit))) (.num (0)))
theorem dz2n61_norm : (reflectRing dz2n61E).toPoly=dz2n61P := by
  exact eq_of_beq (by decide : (reflectRing dz2n61E).toPoly == dz2n61P)

def dz2n62E : RingExpr := (.mul (.int (-12)) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))
def dz2n62P : Lean.Grind.CommRing.Poly := (.add (-12) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.num (0)))
theorem dz2n62_norm : (reflectRing dz2n62E).toPoly=dz2n62P := by
  exact eq_of_beq (by decide : (reflectRing dz2n62E).toPoly == dz2n62P)

def dz2n63E : RingExpr := (.mul (.int (-12)) (.mul (.var 2) (.mul (.var 3) (.var 4))))
def dz2n63P : Lean.Grind.CommRing.Poly := (.add (-12) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ .unit))) (.num (0)))
theorem dz2n63_norm : (reflectRing dz2n63E).toPoly=dz2n63P := by
  exact eq_of_beq (by decide : (reflectRing dz2n63E).toPoly == dz2n63P)

def dz2n64E : RingExpr := (.mul (.int 6) (.mul (.var 0) (.mul (.var 1) (.pow (.var 3) 3))))
def dz2n64P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ .unit))) (.num (0)))
theorem dz2n64_norm : (reflectRing dz2n64E).toPoly=dz2n64P := by
  exact eq_of_beq (by decide : (reflectRing dz2n64E).toPoly == dz2n64P)

def dz2n65E : RingExpr := (.mul (.int 6) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2))))
def dz2n65P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ .unit))) (.num (0)))
theorem dz2n65_norm : (reflectRing dz2n65E).toPoly=dz2n65P := by
  exact eq_of_beq (by decide : (reflectRing dz2n65E).toPoly == dz2n65P)

def dz2n66E : RingExpr := (.mul (.int 6) (.mul (.var 1) (.mul (.var 2) (.var 3))))
def dz2n66P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ .unit))) (.num (0)))
theorem dz2n66_norm : (reflectRing dz2n66E).toPoly=dz2n66P := by
  exact eq_of_beq (by decide : (reflectRing dz2n66E).toPoly == dz2n66P)

def dz2n67E : RingExpr := (.mul (.int 8) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))
def dz2n67P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.num (0)))
theorem dz2n67_norm : (reflectRing dz2n67E).toPoly=dz2n67P := by
  exact eq_of_beq (by decide : (reflectRing dz2n67E).toPoly == dz2n67P)

def dz2n68E : RingExpr := (.mul (.int (-96)) (.mul (.var 0) (.mul (.pow (.var 2) 4) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))
def dz2n68P : Lean.Grind.CommRing.Poly := (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit)))) (.num (0)))
theorem dz2n68_norm : (reflectRing dz2n68E).toPoly=dz2n68P := by
  exact eq_of_beq (by decide : (reflectRing dz2n68E).toPoly == dz2n68P)

def dz2n69E : RingExpr := (.mul (.int (-96)) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))
def dz2n69P : Lean.Grind.CommRing.Poly := (.add (-96) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit)))) (.num (0)))
theorem dz2n69_norm : (reflectRing dz2n69E).toPoly=dz2n69P := by
  exact eq_of_beq (by decide : (reflectRing dz2n69E).toPoly == dz2n69P)

def dz2n70E : RingExpr := (.mul (.int (-72)) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))
def dz2n70P : Lean.Grind.CommRing.Poly := (.add (-72) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit)))) (.num (0)))
theorem dz2n70_norm : (reflectRing dz2n70E).toPoly=dz2n70P := by
  exact eq_of_beq (by decide : (reflectRing dz2n70E).toPoly == dz2n70P)

def dz2n71E : RingExpr := (.mul (.int (-72)) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))
def dz2n71P : Lean.Grind.CommRing.Poly := (.add (-72) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit)))) (.num (0)))
theorem dz2n71_norm : (reflectRing dz2n71E).toPoly=dz2n71P := by
  exact eq_of_beq (by decide : (reflectRing dz2n71E).toPoly == dz2n71P)

def dz2n72E : RingExpr := (.mul (.int (-48)) (.mul (.var 6) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3)))))
def dz2n72P : Lean.Grind.CommRing.Poly := (.add (-48) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))
theorem dz2n72_norm : (reflectRing dz2n72E).toPoly=dz2n72P := by
  exact eq_of_beq (by decide : (reflectRing dz2n72E).toPoly == dz2n72P)

def dz2n73E : RingExpr := (.mul (.int (-48)) (.mul (.var 6) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))
def dz2n73P : Lean.Grind.CommRing.Poly := (.add (-48) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))
theorem dz2n73_norm : (reflectRing dz2n73E).toPoly=dz2n73P := by
  exact eq_of_beq (by decide : (reflectRing dz2n73E).toPoly == dz2n73P)

def dz2n74E : RingExpr := (.mul (.int (-48)) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))
def dz2n74P : Lean.Grind.CommRing.Poly := (.add (-48) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))
theorem dz2n74_norm : (reflectRing dz2n74E).toPoly=dz2n74P := by
  exact eq_of_beq (by decide : (reflectRing dz2n74E).toPoly == dz2n74P)

def dz2n75E : RingExpr := (.mul (.int (-48)) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))
def dz2n75P : Lean.Grind.CommRing.Poly := (.add (-48) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit)))) (.num (0)))
theorem dz2n75_norm : (reflectRing dz2n75E).toPoly=dz2n75P := by
  exact eq_of_beq (by decide : (reflectRing dz2n75E).toPoly == dz2n75P)

def dz2n76E : RingExpr := (.mul (.int (-48)) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))
def dz2n76P : Lean.Grind.CommRing.Poly := (.add (-48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.num (0)))
theorem dz2n76_norm : (reflectRing dz2n76E).toPoly=dz2n76P := by
  exact eq_of_beq (by decide : (reflectRing dz2n76E).toPoly == dz2n76P)

def dz2n77E : RingExpr := (.mul (.int (-24)) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))
def dz2n77P : Lean.Grind.CommRing.Poly := (.add (-24) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))
theorem dz2n77_norm : (reflectRing dz2n77E).toPoly=dz2n77P := by
  exact eq_of_beq (by decide : (reflectRing dz2n77E).toPoly == dz2n77P)

def dz2n78E : RingExpr := (.mul (.int (-24)) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))
def dz2n78P : Lean.Grind.CommRing.Poly := (.add (-24) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))
theorem dz2n78_norm : (reflectRing dz2n78E).toPoly=dz2n78P := by
  exact eq_of_beq (by decide : (reflectRing dz2n78E).toPoly == dz2n78P)

def dz2n79E : RingExpr := (.mul (.int (-12)) (.mul (.var 6) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.pow (.var 3) 5)))))
def dz2n79P : Lean.Grind.CommRing.Poly := (.add (-12) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))
theorem dz2n79_norm : (reflectRing dz2n79E).toPoly=dz2n79P := by
  exact eq_of_beq (by decide : (reflectRing dz2n79E).toPoly == dz2n79P)

end StackSorting.FiniteGraph
