import UnitSplitFactorSharedNodes095
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

def usfn4973E : RingExpr := (.mul usfn1944E usfn4972E)
def usfn4973P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-64) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (20) (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-12) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.num (0))))))))))
theorem usfn4973_norm : (reflectRing usfn4973E).toPoly=usfn4973P := by
  change (reflectRing usfn1944E).toPoly.mul (reflectRing usfn4972E).toPoly=usfn4973P
  rw [usfn1944_norm, usfn4972_norm]
  exact eq_of_beq (by decide : usfn1944P.mul usfn4972P == usfn4973P)

def usfn4974E : RingExpr := (.mul usfn4962E usfn4973E)
def usfn4974P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,2⟩ (.mult ⟨2,5⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))))) (.add (-64) (.mult ⟨0,1⟩ (.mult ⟨2,5⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨2,5⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨2,5⟩ (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨2,5⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨2,5⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (20) (.mult ⟨2,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-12) (.mult ⟨2,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.num (0))))))))))
theorem usfn4974_norm : (reflectRing usfn4974E).toPoly=usfn4974P := by
  change (reflectRing usfn4962E).toPoly.mul (reflectRing usfn4973E).toPoly=usfn4974P
  rw [usfn4962_norm, usfn4973_norm]
  exact eq_of_beq (by decide : usfn4962P.mul usfn4973P == usfn4974P)

def usfn4975E : RingExpr := (.mul (.int 9) (.mul (.var 4) (.var 9)))
def usfn4975P : Lean.Grind.CommRing.Poly := (.add (9) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (0)))
theorem usfn4975_norm : (reflectRing usfn4975E).toPoly=usfn4975P := by
  exact eq_of_beq (by decide : (reflectRing usfn4975E).toPoly == usfn4975P)

def usfn4976E : RingExpr := (.mul (.int 12) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))
def usfn4976P : Lean.Grind.CommRing.Poly := (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.num (0)))
theorem usfn4976_norm : (reflectRing usfn4976E).toPoly=usfn4976P := by
  exact eq_of_beq (by decide : (reflectRing usfn4976E).toPoly == usfn4976P)

def usfn4977E : RingExpr := (.mul (.int (-16)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))
def usfn4977P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))
theorem usfn4977_norm : (reflectRing usfn4977E).toPoly=usfn4977P := by
  exact eq_of_beq (by decide : (reflectRing usfn4977E).toPoly == usfn4977P)

def usfn4978E : RingExpr := (.mul (.int 6) (.mul (.var 0) (.mul (.var 7) (.mul (.var 3) (.var 8)))))
def usfn4978P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit)))) (.num (0)))
theorem usfn4978_norm : (reflectRing usfn4978E).toPoly=usfn4978P := by
  exact eq_of_beq (by decide : (reflectRing usfn4978E).toPoly == usfn4978P)

def usfn4979E : RingExpr := (.mul (.int (-20)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))
def usfn4979P : Lean.Grind.CommRing.Poly := (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.num (0)))
theorem usfn4979_norm : (reflectRing usfn4979E).toPoly=usfn4979P := by
  exact eq_of_beq (by decide : (reflectRing usfn4979E).toPoly == usfn4979P)

def usfn4980E : RingExpr := (.add (.mul (.int (-8)) (.mul (.var 7) (.mul (.var 8) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.pow (.var 3) 3)))))) (.add (.mul (.int (-24)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))) (.add (.mul (.int 24) (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))) (.mul (.int 32) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))))))))
def usfn4980P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.num (0))))))
theorem usfn4980_norm : (reflectRing usfn4980E).toPoly=usfn4980P := by
  exact eq_of_beq (by decide : (reflectRing usfn4980E).toPoly == usfn4980P)

def usfn4981E : RingExpr := (.add usfn4979E usfn4980E)
def usfn4981P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.num (0)))))))
theorem usfn4981_norm : (reflectRing usfn4981E).toPoly=usfn4981P := by
  change (reflectRing usfn4979E).toPoly.combine (reflectRing usfn4980E).toPoly=usfn4981P
  rw [usfn4979_norm, usfn4980_norm]
  exact eq_of_beq (by decide : usfn4979P.combine usfn4980P == usfn4981P)

def usfn4982E : RingExpr := (.add usfn4978E usfn4981E)
def usfn4982P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit)))) (.num (0))))))))
theorem usfn4982_norm : (reflectRing usfn4982E).toPoly=usfn4982P := by
  change (reflectRing usfn4978E).toPoly.combine (reflectRing usfn4981E).toPoly=usfn4982P
  rw [usfn4978_norm, usfn4981_norm]
  exact eq_of_beq (by decide : usfn4978P.combine usfn4981P == usfn4982P)

def usfn4983E : RingExpr := (.add usfn2150E usfn4982E)
def usfn4983P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit)))) (.num (0)))))))))
theorem usfn4983_norm : (reflectRing usfn4983E).toPoly=usfn4983P := by
  change (reflectRing usfn2150E).toPoly.combine (reflectRing usfn4982E).toPoly=usfn4983P
  rw [usfn2150_norm, usfn4982_norm]
  exact eq_of_beq (by decide : usfn2150P.combine usfn4982P == usfn4983P)

def usfn4984E : RingExpr := (.add usfn4977E usfn4983E)
def usfn4984P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit)))) (.num (0))))))))))
theorem usfn4984_norm : (reflectRing usfn4984E).toPoly=usfn4984P := by
  change (reflectRing usfn4977E).toPoly.combine (reflectRing usfn4983E).toPoly=usfn4984P
  rw [usfn4977_norm, usfn4983_norm]
  exact eq_of_beq (by decide : usfn4977P.combine usfn4983P == usfn4984P)

def usfn4985E : RingExpr := (.add usfn4976E usfn4984E)
def usfn4985P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit)))) (.num (0)))))))))))
theorem usfn4985_norm : (reflectRing usfn4985E).toPoly=usfn4985P := by
  change (reflectRing usfn4976E).toPoly.combine (reflectRing usfn4984E).toPoly=usfn4985P
  rw [usfn4976_norm, usfn4984_norm]
  exact eq_of_beq (by decide : usfn4976P.combine usfn4984P == usfn4985P)

def usfn4986E : RingExpr := (.add usfn2148E usfn4985E)
def usfn4986P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit)))) (.num (0))))))))))))
theorem usfn4986_norm : (reflectRing usfn4986E).toPoly=usfn4986P := by
  change (reflectRing usfn2148E).toPoly.combine (reflectRing usfn4985E).toPoly=usfn4986P
  rw [usfn2148_norm, usfn4985_norm]
  exact eq_of_beq (by decide : usfn2148P.combine usfn4985P == usfn4986P)

def usfn4987E : RingExpr := (.add usfn2147E usfn4986E)
def usfn4987P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit)))) (.num (0)))))))))))))
theorem usfn4987_norm : (reflectRing usfn4987E).toPoly=usfn4987P := by
  change (reflectRing usfn2147E).toPoly.combine (reflectRing usfn4986E).toPoly=usfn4987P
  rw [usfn2147_norm, usfn4986_norm]
  exact eq_of_beq (by decide : usfn2147P.combine usfn4986P == usfn4987P)

def usfn4988E : RingExpr := (.add usfn4975E usfn4987E)
def usfn4988P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (9) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (0))))))))))))))
theorem usfn4988_norm : (reflectRing usfn4988E).toPoly=usfn4988P := by
  change (reflectRing usfn4975E).toPoly.combine (reflectRing usfn4987E).toPoly=usfn4988P
  rw [usfn4975_norm, usfn4987_norm]
  exact eq_of_beq (by decide : usfn4975P.combine usfn4987P == usfn4988P)

def usfn4989E : RingExpr := (.add usfn3773E usfn4988E)
def usfn4989P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.add (9) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (0)))))))))))))))
theorem usfn4989_norm : (reflectRing usfn4989E).toPoly=usfn4989P := by
  change (reflectRing usfn3773E).toPoly.combine (reflectRing usfn4988E).toPoly=usfn4989P
  rw [usfn3773_norm, usfn4988_norm]
  exact eq_of_beq (by decide : usfn3773P.combine usfn4988P == usfn4989P)

def usfn4990E : RingExpr := (.add usfn2456E usfn4989E)
def usfn4990P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.add (9) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (-3)))))))))))))))
theorem usfn4990_norm : (reflectRing usfn4990E).toPoly=usfn4990P := by
  change (reflectRing usfn2456E).toPoly.combine (reflectRing usfn4989E).toPoly=usfn4990P
  rw [usfn2456_norm, usfn4989_norm]
  exact eq_of_beq (by decide : usfn2456P.combine usfn4989P == usfn4990P)

def usfn4991E : RingExpr := (.mul usfn185E usfn4990E)
def usfn4991P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ .unit)))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ .unit))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ .unit)))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,5⟩ .unit)))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ .unit)))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ .unit))) (.add (9) (.mult ⟨4,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ .unit))) (.add (-3) (.mult ⟨8,5⟩ .unit) (.num (0))))))))))))))))
theorem usfn4991_norm : (reflectRing usfn4991E).toPoly=usfn4991P := by
  change (reflectRing usfn185E).toPoly.mul (reflectRing usfn4990E).toPoly=usfn4991P
  rw [usfn185_norm, usfn4990_norm]
  exact eq_of_beq (by decide : usfn185P.mul usfn4990P == usfn4991P)

def usfn4992E : RingExpr := (.mul usfn184E usfn4991E)
def usfn4992P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨10,3⟩ .unit))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit)))) (.add (9) (.mult ⟨4,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))) (.add (-3) (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit)) (.num (0))))))))))))))))
theorem usfn4992_norm : (reflectRing usfn4992E).toPoly=usfn4992P := by
  change (reflectRing usfn184E).toPoly.mul (reflectRing usfn4991E).toPoly=usfn4992P
  rw [usfn184_norm, usfn4991_norm]
  exact eq_of_beq (by decide : usfn184P.mul usfn4991P == usfn4992P)

def usfn4993E : RingExpr := (.mul usfn3E usfn4992E)
def usfn4993P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (9) (.mult ⟨4,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))) (.add (-3) (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))) (.num (0))))))))))))))))
theorem usfn4993_norm : (reflectRing usfn4993E).toPoly=usfn4993P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn4992E).toPoly=usfn4993P
  rw [usfn3_norm, usfn4992_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn4992P == usfn4993P)

def usfn4994E : RingExpr := (.mul usfn362E usfn4993E)
def usfn4994P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,4⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (9) (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))) (.add (-3) (.mult ⟨4,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))) (.num (0))))))))))))))))
theorem usfn4994_norm : (reflectRing usfn4994E).toPoly=usfn4994P := by
  change (reflectRing usfn362E).toPoly.mul (reflectRing usfn4993E).toPoly=usfn4994P
  rw [usfn362_norm, usfn4993_norm]
  exact eq_of_beq (by decide : usfn362P.mul usfn4993P == usfn4994P)

def usfn4995E : RingExpr := (.mul usfn1E usfn4994E)
def usfn4995P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (9) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-3) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.num (0))))))))))))))))
theorem usfn4995_norm : (reflectRing usfn4995E).toPoly=usfn4995P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn4994E).toPoly=usfn4995P
  rw [usfn1_norm, usfn4994_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn4994P == usfn4995P)

def usfn4996E : RingExpr := (.mul usfn361E usfn4995E)
def usfn4996P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (64) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-32) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (18) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-6) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.num (0))))))))))))))))
theorem usfn4996_norm : (reflectRing usfn4996E).toPoly=usfn4996P := by
  change (reflectRing usfn361E).toPoly.mul (reflectRing usfn4995E).toPoly=usfn4996P
  rw [usfn361_norm, usfn4995_norm]
  exact eq_of_beq (by decide : usfn361P.mul usfn4995P == usfn4996P)

def usfn4997E : RingExpr := (.mul usfn4416E usfn4996E)
def usfn4997P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,2⟩ (.mult ⟨2,4⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))))) (.add (64) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨2,4⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨2,4⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨2,4⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (-32) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (-8) (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (16) (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (18) (.mult ⟨2,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-6) (.mult ⟨2,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.num (0))))))))))))))))
theorem usfn4997_norm : (reflectRing usfn4997E).toPoly=usfn4997P := by
  change (reflectRing usfn4416E).toPoly.mul (reflectRing usfn4996E).toPoly=usfn4997P
  rw [usfn4416_norm, usfn4996_norm]
  exact eq_of_beq (by decide : usfn4416P.mul usfn4996P == usfn4997P)

def usfn4998E : RingExpr := (.mul (.int 7) (.mul (.var 4) (.var 9)))
def usfn4998P : Lean.Grind.CommRing.Poly := (.add (7) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (0)))
theorem usfn4998_norm : (reflectRing usfn4998E).toPoly=usfn4998P := by
  exact eq_of_beq (by decide : (reflectRing usfn4998E).toPoly == usfn4998P)

def usfn4999E : RingExpr := (.mul (.int (-16)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))
def usfn4999P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit))) (.num (0)))
theorem usfn4999_norm : (reflectRing usfn4999E).toPoly=usfn4999P := by
  exact eq_of_beq (by decide : (reflectRing usfn4999E).toPoly == usfn4999P)

def usfn5000E : RingExpr := (.mul (.int (-12)) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))
def usfn5000P : Lean.Grind.CommRing.Poly := (.add (-12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.num (0)))
theorem usfn5000_norm : (reflectRing usfn5000E).toPoly=usfn5000P := by
  exact eq_of_beq (by decide : (reflectRing usfn5000E).toPoly == usfn5000P)

def usfn5001E : RingExpr := (.mul (.int 12) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))
def usfn5001P : Lean.Grind.CommRing.Poly := (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))
theorem usfn5001_norm : (reflectRing usfn5001E).toPoly=usfn5001P := by
  exact eq_of_beq (by decide : (reflectRing usfn5001E).toPoly == usfn5001P)

def usfn5002E : RingExpr := (.mul (.int (-40)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))
def usfn5002P : Lean.Grind.CommRing.Poly := (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.num (0)))
theorem usfn5002_norm : (reflectRing usfn5002E).toPoly=usfn5002P := by
  exact eq_of_beq (by decide : (reflectRing usfn5002E).toPoly == usfn5002P)

def usfn5003E : RingExpr := (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 8) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.pow (.var 3) 3))))))
def usfn5003P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.num (0)))
theorem usfn5003_norm : (reflectRing usfn5003E).toPoly=usfn5003P := by
  exact eq_of_beq (by decide : (reflectRing usfn5003E).toPoly == usfn5003P)

def usfn5004E : RingExpr := (.mul (.int 8) (.mul (.var 7) (.mul (.var 8) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))))
def usfn5004P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.num (0)))
theorem usfn5004_norm : (reflectRing usfn5004E).toPoly=usfn5004P := by
  exact eq_of_beq (by decide : (reflectRing usfn5004E).toPoly == usfn5004P)

def usfn5005E : RingExpr := (.add (.mul (.int (-16)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))) (.add (.mul (.int 16) (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 2) (.pow (.var 4) 4)))))))) (.add (.mul (.int 24) (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))) (.mul (.int 88) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))))))))
def usfn5005P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (88) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.num (0))))))
theorem usfn5005_norm : (reflectRing usfn5005E).toPoly=usfn5005P := by
  exact eq_of_beq (by decide : (reflectRing usfn5005E).toPoly == usfn5005P)

def usfn5006E : RingExpr := (.add usfn5004E usfn5005E)
def usfn5006P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (88) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.num (0)))))))
theorem usfn5006_norm : (reflectRing usfn5006E).toPoly=usfn5006P := by
  change (reflectRing usfn5004E).toPoly.combine (reflectRing usfn5005E).toPoly=usfn5006P
  rw [usfn5004_norm, usfn5005_norm]
  exact eq_of_beq (by decide : usfn5004P.combine usfn5005P == usfn5006P)

def usfn5007E : RingExpr := (.add usfn5003E usfn5006E)
def usfn5007P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (88) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.num (0))))))))
theorem usfn5007_norm : (reflectRing usfn5007E).toPoly=usfn5007P := by
  change (reflectRing usfn5003E).toPoly.combine (reflectRing usfn5006E).toPoly=usfn5007P
  rw [usfn5003_norm, usfn5006_norm]
  exact eq_of_beq (by decide : usfn5003P.combine usfn5006P == usfn5007P)

def usfn5008E : RingExpr := (.add usfn5002E usfn5007E)
def usfn5008P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (88) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.num (0)))))))))
theorem usfn5008_norm : (reflectRing usfn5008E).toPoly=usfn5008P := by
  change (reflectRing usfn5002E).toPoly.combine (reflectRing usfn5007E).toPoly=usfn5008P
  rw [usfn5002_norm, usfn5007_norm]
  exact eq_of_beq (by decide : usfn5002P.combine usfn5007P == usfn5008P)

def usfn5009E : RingExpr := (.add usfn5001E usfn5008E)
def usfn5009P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (88) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.num (0))))))))))
theorem usfn5009_norm : (reflectRing usfn5009E).toPoly=usfn5009P := by
  change (reflectRing usfn5001E).toPoly.combine (reflectRing usfn5008E).toPoly=usfn5009P
  rw [usfn5001_norm, usfn5008_norm]
  exact eq_of_beq (by decide : usfn5001P.combine usfn5008P == usfn5009P)

def usfn5010E : RingExpr := (.add usfn4891E usfn5009E)
def usfn5010P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (88) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit)))) (.num (0)))))))))))
theorem usfn5010_norm : (reflectRing usfn5010E).toPoly=usfn5010P := by
  change (reflectRing usfn4891E).toPoly.combine (reflectRing usfn5009E).toPoly=usfn5010P
  rw [usfn4891_norm, usfn5009_norm]
  exact eq_of_beq (by decide : usfn4891P.combine usfn5009P == usfn5010P)

def usfn5011E : RingExpr := (.add usfn3131E usfn5010E)
def usfn5011P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (88) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit)))) (.num (0))))))))))))
theorem usfn5011_norm : (reflectRing usfn5011E).toPoly=usfn5011P := by
  change (reflectRing usfn3131E).toPoly.combine (reflectRing usfn5010E).toPoly=usfn5011P
  rw [usfn3131_norm, usfn5010_norm]
  exact eq_of_beq (by decide : usfn3131P.combine usfn5010P == usfn5011P)

def usfn5012E : RingExpr := (.add usfn4976E usfn5011E)
def usfn5012P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (88) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit)))) (.num (0)))))))))))))
theorem usfn5012_norm : (reflectRing usfn5012E).toPoly=usfn5012P := by
  change (reflectRing usfn4976E).toPoly.combine (reflectRing usfn5011E).toPoly=usfn5012P
  rw [usfn4976_norm, usfn5011_norm]
  exact eq_of_beq (by decide : usfn4976P.combine usfn5011P == usfn5012P)

def usfn5013E : RingExpr := (.add usfn5000E usfn5012E)
def usfn5013P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (88) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit)))) (.num (0))))))))))))))
theorem usfn5013_norm : (reflectRing usfn5013E).toPoly=usfn5013P := by
  change (reflectRing usfn5000E).toPoly.combine (reflectRing usfn5012E).toPoly=usfn5013P
  rw [usfn5000_norm, usfn5012_norm]
  exact eq_of_beq (by decide : usfn5000P.combine usfn5012P == usfn5013P)

def usfn5014E : RingExpr := (.add usfn4999E usfn5013E)
def usfn5014P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (88) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit)))) (.num (0)))))))))))))))
theorem usfn5014_norm : (reflectRing usfn5014E).toPoly=usfn5014P := by
  change (reflectRing usfn4999E).toPoly.combine (reflectRing usfn5013E).toPoly=usfn5014P
  rw [usfn4999_norm, usfn5013_norm]
  exact eq_of_beq (by decide : usfn4999P.combine usfn5013P == usfn5014P)

def usfn5015E : RingExpr := (.add usfn4886E usfn5014E)
def usfn5015P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (88) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-20) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit)))) (.num (0))))))))))))))))
theorem usfn5015_norm : (reflectRing usfn5015E).toPoly=usfn5015P := by
  change (reflectRing usfn4886E).toPoly.combine (reflectRing usfn5014E).toPoly=usfn5015P
  rw [usfn4886_norm, usfn5014_norm]
  exact eq_of_beq (by decide : usfn4886P.combine usfn5014P == usfn5015P)

def usfn5016E : RingExpr := (.add usfn3128E usfn5015E)
def usfn5016P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (88) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-20) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.num (0)))))))))))))))))
theorem usfn5016_norm : (reflectRing usfn5016E).toPoly=usfn5016P := by
  change (reflectRing usfn3128E).toPoly.combine (reflectRing usfn5015E).toPoly=usfn5016P
  rw [usfn3128_norm, usfn5015_norm]
  exact eq_of_beq (by decide : usfn3128P.combine usfn5015P == usfn5016P)

def usfn5017E : RingExpr := (.add usfn4998E usfn5016E)
def usfn5017P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (88) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-20) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.add (7) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (0))))))))))))))))))
theorem usfn5017_norm : (reflectRing usfn5017E).toPoly=usfn5017P := by
  change (reflectRing usfn4998E).toPoly.combine (reflectRing usfn5016E).toPoly=usfn5017P
  rw [usfn4998_norm, usfn5016_norm]
  exact eq_of_beq (by decide : usfn4998P.combine usfn5016P == usfn5017P)

def usfn5018E : RingExpr := (.add usfn100E usfn5017E)
def usfn5018P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (88) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-20) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.add (7) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (-1))))))))))))))))))
theorem usfn5018_norm : (reflectRing usfn5018E).toPoly=usfn5018P := by
  change (reflectRing usfn100E).toPoly.combine (reflectRing usfn5017E).toPoly=usfn5018P
  rw [usfn100_norm, usfn5017_norm]
  exact eq_of_beq (by decide : usfn100P.combine usfn5017P == usfn5018P)

def usfn5019E : RingExpr := (.mul usfn185E usfn5018E)
def usfn5019P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (88) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ .unit))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ .unit)))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ .unit))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,5⟩ .unit)))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-20) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ .unit)))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,5⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ .unit)))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ .unit))) (.add (7) (.mult ⟨4,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ .unit))) (.add (-1) (.mult ⟨8,5⟩ .unit) (.num (0)))))))))))))))))))
theorem usfn5019_norm : (reflectRing usfn5019E).toPoly=usfn5019P := by
  change (reflectRing usfn185E).toPoly.mul (reflectRing usfn5018E).toPoly=usfn5019P
  rw [usfn185_norm, usfn5018_norm]
  exact eq_of_beq (by decide : usfn185P.mul usfn5018P == usfn5019P)

def usfn5020E : RingExpr := (.mul usfn184E usfn5019E)
def usfn5020P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (88) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-20) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨10,3⟩ .unit))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit)))) (.add (7) (.mult ⟨4,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))) (.add (-1) (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit)) (.num (0)))))))))))))))))))
theorem usfn5020_norm : (reflectRing usfn5020E).toPoly=usfn5020P := by
  change (reflectRing usfn184E).toPoly.mul (reflectRing usfn5019E).toPoly=usfn5020P
  rw [usfn184_norm, usfn5019_norm]
  exact eq_of_beq (by decide : usfn184P.mul usfn5019P == usfn5020P)

def usfn5021E : RingExpr := (.mul usfn3E usfn5020E)
def usfn5021P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (88) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-20) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (7) (.mult ⟨4,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))) (.add (-1) (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))) (.num (0)))))))))))))))))))
theorem usfn5021_norm : (reflectRing usfn5021E).toPoly=usfn5021P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn5020E).toPoly=usfn5021P
  rw [usfn3_norm, usfn5020_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn5020P == usfn5021P)

def usfn5022E : RingExpr := (.mul usfn1E usfn5021E)
def usfn5022P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (88) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-20) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (7) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))) (.num (0)))))))))))))))))))
theorem usfn5022_norm : (reflectRing usfn5022E).toPoly=usfn5022P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn5021E).toPoly=usfn5022P
  rw [usfn1_norm, usfn5021_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn5021P == usfn5022P)

def usfn5023E : RingExpr := (.mul usfn3771E usfn5022E)
def usfn5023P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))))) (.add (88) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,7⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))))) (.add (-12) (.mult ⟨0,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (-20) (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (7) (.mult ⟨2,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-1) (.mult ⟨2,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.num (0)))))))))))))))))))
theorem usfn5023_norm : (reflectRing usfn5023E).toPoly=usfn5023P := by
  change (reflectRing usfn3771E).toPoly.mul (reflectRing usfn5022E).toPoly=usfn5023P
  rw [usfn3771_norm, usfn5022_norm]
  exact eq_of_beq (by decide : usfn3771P.mul usfn5022P == usfn5023P)

def usfn5024E : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.pow (.var 9) 2)))))
def usfn5024P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))) (.num (0)))
theorem usfn5024_norm : (reflectRing usfn5024E).toPoly=usfn5024P := by
  exact eq_of_beq (by decide : (reflectRing usfn5024E).toPoly == usfn5024P)

def usfn5025E : RingExpr := (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 3)))))))
def usfn5025P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn5025_norm : (reflectRing usfn5025E).toPoly=usfn5025P := by
  exact eq_of_beq (by decide : (reflectRing usfn5025E).toPoly == usfn5025P)

def usfn5026E : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 3)))))))
def usfn5026P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn5026_norm : (reflectRing usfn5026E).toPoly=usfn5026P := by
  exact eq_of_beq (by decide : (reflectRing usfn5026E).toPoly == usfn5026P)

def usfn5027E : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.pow (.var 9) 2)))))))
def usfn5027P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.num (0)))
theorem usfn5027_norm : (reflectRing usfn5027E).toPoly=usfn5027P := by
  exact eq_of_beq (by decide : (reflectRing usfn5027E).toPoly == usfn5027P)

def usfn5028E : RingExpr := (.mul (.int 8) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.pow (.var 4) 3)))))))
def usfn5028P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn5028_norm : (reflectRing usfn5028E).toPoly=usfn5028P := by
  exact eq_of_beq (by decide : (reflectRing usfn5028E).toPoly == usfn5028P)

def usfn5029E : RingExpr := (.mul (.int 14) (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.pow (.var 9) 2)))))))
def usfn5029P : Lean.Grind.CommRing.Poly := (.add (14) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn5029_norm : (reflectRing usfn5029E).toPoly=usfn5029P := by
  exact eq_of_beq (by decide : (reflectRing usfn5029E).toPoly == usfn5029P)

def usfn5030E : RingExpr := (.mul (.int (-40)) (.mul (.var 0) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.pow (.var 9) 2))))))))
def usfn5030P : Lean.Grind.CommRing.Poly := (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.num (0)))
theorem usfn5030_norm : (reflectRing usfn5030E).toPoly=usfn5030P := by
  exact eq_of_beq (by decide : (reflectRing usfn5030E).toPoly == usfn5030P)

def usfn5031E : RingExpr := (.mul (.int (-32)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.pow (.var 4) 3))))))))
def usfn5031P : Lean.Grind.CommRing.Poly := (.add (-32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0)))
theorem usfn5031_norm : (reflectRing usfn5031E).toPoly=usfn5031P := by
  exact eq_of_beq (by decide : (reflectRing usfn5031E).toPoly == usfn5031P)

def usfn5032E : RingExpr := (.mul (.int (-24)) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 3) (.pow (.var 9) 2))))))))
def usfn5032P : Lean.Grind.CommRing.Poly := (.add (-24) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.num (0)))
theorem usfn5032_norm : (reflectRing usfn5032E).toPoly=usfn5032P := by
  exact eq_of_beq (by decide : (reflectRing usfn5032E).toPoly == usfn5032P)

def usfn5033E : RingExpr := (.mul (.int (-8)) (.mul (.var 7) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 4) (.pow (.var 9) 2))))))))
def usfn5033P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0)))
theorem usfn5033_norm : (reflectRing usfn5033E).toPoly=usfn5033P := by
  exact eq_of_beq (by decide : (reflectRing usfn5033E).toPoly == usfn5033P)

def usfn5034E : RingExpr := (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 3) (.pow (.var 9) 2))))))))
def usfn5034P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0)))
theorem usfn5034_norm : (reflectRing usfn5034E).toPoly=usfn5034P := by
  exact eq_of_beq (by decide : (reflectRing usfn5034E).toPoly == usfn5034P)

def usfn5035E : RingExpr := (.mul (.int (-4)) (.mul (.var 7) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.pow (.var 9) 2))))))))
def usfn5035P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0)))
theorem usfn5035_norm : (reflectRing usfn5035E).toPoly=usfn5035P := by
  exact eq_of_beq (by decide : (reflectRing usfn5035E).toPoly == usfn5035P)

def usfn5036E : RingExpr := (.mul (.int (-4)) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 5) (.pow (.var 9) 2))))))))
def usfn5036P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.num (0)))
theorem usfn5036_norm : (reflectRing usfn5036E).toPoly=usfn5036P := by
  exact eq_of_beq (by decide : (reflectRing usfn5036E).toPoly == usfn5036P)

def usfn5037E : RingExpr := (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.pow (.var 9) 2))))))))
def usfn5037P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0)))
theorem usfn5037_norm : (reflectRing usfn5037E).toPoly=usfn5037P := by
  exact eq_of_beq (by decide : (reflectRing usfn5037E).toPoly == usfn5037P)

def usfn5038E : RingExpr := (.mul (.int 4) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.pow (.var 8) 3))))))))
def usfn5038P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0)))
theorem usfn5038_norm : (reflectRing usfn5038E).toPoly=usfn5038P := by
  exact eq_of_beq (by decide : (reflectRing usfn5038E).toPoly == usfn5038P)

def usfn5039E : RingExpr := (.mul (.int 4) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 4) (.pow (.var 4) 2))))))))
def usfn5039P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0)))
theorem usfn5039_norm : (reflectRing usfn5039E).toPoly=usfn5039P := by
  exact eq_of_beq (by decide : (reflectRing usfn5039E).toPoly == usfn5039P)

def usfn5040E : RingExpr := (.mul (.int 10) (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 4))))))))
def usfn5040P : Lean.Grind.CommRing.Poly := (.add (10) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0)))
theorem usfn5040_norm : (reflectRing usfn5040E).toPoly=usfn5040P := by
  exact eq_of_beq (by decide : (reflectRing usfn5040E).toPoly == usfn5040P)

def usfn5041E : RingExpr := (.add (.mul (.int 16) (.mul (.pow (.var 0) 3) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 7) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 4) (.pow (.var 9) 2)))))))) (.add (.mul (.int 20) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.pow (.var 4) 2)))))))) (.mul (.int 48) (.mul (.var 0) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 4) (.pow (.var 9) 2))))))))))
def usfn5041P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (20) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0)))))
theorem usfn5041_norm : (reflectRing usfn5041E).toPoly=usfn5041P := by
  exact eq_of_beq (by decide : (reflectRing usfn5041E).toPoly == usfn5041P)

def usfn5042E : RingExpr := (.add usfn5040E usfn5041E)
def usfn5042P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (20) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (10) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0))))))
theorem usfn5042_norm : (reflectRing usfn5042E).toPoly=usfn5042P := by
  change (reflectRing usfn5040E).toPoly.combine (reflectRing usfn5041E).toPoly=usfn5042P
  rw [usfn5040_norm, usfn5041_norm]
  exact eq_of_beq (by decide : usfn5040P.combine usfn5041P == usfn5042P)

def usfn5043E : RingExpr := (.add usfn5039E usfn5042E)
def usfn5043P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (20) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (10) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0)))))))
theorem usfn5043_norm : (reflectRing usfn5043E).toPoly=usfn5043P := by
  change (reflectRing usfn5039E).toPoly.combine (reflectRing usfn5042E).toPoly=usfn5043P
  rw [usfn5039_norm, usfn5042_norm]
  exact eq_of_beq (by decide : usfn5039P.combine usfn5042P == usfn5043P)

def usfn5044E : RingExpr := (.add usfn5038E usfn5043E)
def usfn5044P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (20) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (10) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0))))))))
theorem usfn5044_norm : (reflectRing usfn5044E).toPoly=usfn5044P := by
  change (reflectRing usfn5038E).toPoly.combine (reflectRing usfn5043E).toPoly=usfn5044P
  rw [usfn5038_norm, usfn5043_norm]
  exact eq_of_beq (by decide : usfn5038P.combine usfn5043P == usfn5044P)

def usfn5045E : RingExpr := (.add usfn5037E usfn5044E)
def usfn5045P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (20) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (10) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0)))))))))
theorem usfn5045_norm : (reflectRing usfn5045E).toPoly=usfn5045P := by
  change (reflectRing usfn5037E).toPoly.combine (reflectRing usfn5044E).toPoly=usfn5045P
  rw [usfn5037_norm, usfn5044_norm]
  exact eq_of_beq (by decide : usfn5037P.combine usfn5044P == usfn5045P)

def usfn5046E : RingExpr := (.add usfn5036E usfn5045E)
def usfn5046P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (20) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (10) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0))))))))))
theorem usfn5046_norm : (reflectRing usfn5046E).toPoly=usfn5046P := by
  change (reflectRing usfn5036E).toPoly.combine (reflectRing usfn5045E).toPoly=usfn5046P
  rw [usfn5036_norm, usfn5045_norm]
  exact eq_of_beq (by decide : usfn5036P.combine usfn5045P == usfn5046P)

def usfn5047E : RingExpr := (.add usfn5035E usfn5046E)
def usfn5047P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (20) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (10) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0)))))))))))
theorem usfn5047_norm : (reflectRing usfn5047E).toPoly=usfn5047P := by
  change (reflectRing usfn5035E).toPoly.combine (reflectRing usfn5046E).toPoly=usfn5047P
  rw [usfn5035_norm, usfn5046_norm]
  exact eq_of_beq (by decide : usfn5035P.combine usfn5046P == usfn5047P)

def usfn5048E : RingExpr := (.add usfn5034E usfn5047E)
def usfn5048P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (20) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (10) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0))))))))))))
theorem usfn5048_norm : (reflectRing usfn5048E).toPoly=usfn5048P := by
  change (reflectRing usfn5034E).toPoly.combine (reflectRing usfn5047E).toPoly=usfn5048P
  rw [usfn5034_norm, usfn5047_norm]
  exact eq_of_beq (by decide : usfn5034P.combine usfn5047P == usfn5048P)

def usfn5049E : RingExpr := (.add usfn5033E usfn5048E)
def usfn5049P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (20) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (10) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0)))))))))))))
theorem usfn5049_norm : (reflectRing usfn5049E).toPoly=usfn5049P := by
  change (reflectRing usfn5033E).toPoly.combine (reflectRing usfn5048E).toPoly=usfn5049P
  rw [usfn5033_norm, usfn5048_norm]
  exact eq_of_beq (by decide : usfn5033P.combine usfn5048P == usfn5049P)

def usfn5050E : RingExpr := (.add usfn5032E usfn5049E)
def usfn5050P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-24) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (20) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (10) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0))))))))))))))
theorem usfn5050_norm : (reflectRing usfn5050E).toPoly=usfn5050P := by
  change (reflectRing usfn5032E).toPoly.combine (reflectRing usfn5049E).toPoly=usfn5050P
  rw [usfn5032_norm, usfn5049_norm]
  exact eq_of_beq (by decide : usfn5032P.combine usfn5049P == usfn5050P)

def usfn5051E : RingExpr := (.add usfn5031E usfn5050E)
def usfn5051P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-24) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (20) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (10) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0)))))))))))))))
theorem usfn5051_norm : (reflectRing usfn5051E).toPoly=usfn5051P := by
  change (reflectRing usfn5031E).toPoly.combine (reflectRing usfn5050E).toPoly=usfn5051P
  rw [usfn5031_norm, usfn5050_norm]
  exact eq_of_beq (by decide : usfn5031P.combine usfn5050P == usfn5051P)

def usfn5052E : RingExpr := (.add usfn5030E usfn5051E)
def usfn5052P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,3⟩ (.mult ⟨3,7⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-24) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-40) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (20) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (10) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.num (0))))))))))))))))
theorem usfn5052_norm : (reflectRing usfn5052E).toPoly=usfn5052P := by
  change (reflectRing usfn5030E).toPoly.combine (reflectRing usfn5051E).toPoly=usfn5052P
  rw [usfn5030_norm, usfn5051_norm]
  exact eq_of_beq (by decide : usfn5030P.combine usfn5051P == usfn5052P)

#print axioms usfn5052_norm
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
