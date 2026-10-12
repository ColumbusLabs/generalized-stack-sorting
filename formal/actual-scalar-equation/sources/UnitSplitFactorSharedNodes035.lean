import UnitSplitFactorSharedNodes034
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

def usfn1994E : RingExpr := (.add (.mul (.int (-16)) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.mul (.pow (.var 4) 2) (.pow (.var 9) 2)))))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2)))))))) (.mul (.int 16) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.mul (.pow (.var 4) 4) (.pow (.var 9) 2)))))))))))
def usfn1994P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.num (0))))))
theorem usfn1994_norm : (reflectRing usfn1994E).toPoly=usfn1994P := by
  exact eq_of_beq (by decide : (reflectRing usfn1994E).toPoly == usfn1994P)

def usfn1995E : RingExpr := (.add usfn1993E usfn1994E)
def usfn1995P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))
theorem usfn1995_norm : (reflectRing usfn1995E).toPoly=usfn1995P := by
  change (reflectRing usfn1993E).toPoly.combine (reflectRing usfn1994E).toPoly=usfn1995P
  rw [usfn1993_norm, usfn1994_norm]
  exact eq_of_beq (by decide : usfn1993P.combine usfn1994P == usfn1995P)

def usfn1996E : RingExpr := (.add usfn1992E usfn1995E)
def usfn1996P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))))
theorem usfn1996_norm : (reflectRing usfn1996E).toPoly=usfn1996P := by
  change (reflectRing usfn1992E).toPoly.combine (reflectRing usfn1995E).toPoly=usfn1996P
  rw [usfn1992_norm, usfn1995_norm]
  exact eq_of_beq (by decide : usfn1992P.combine usfn1995P == usfn1996P)

def usfn1997E : RingExpr := (.add usfn1991E usfn1996E)
def usfn1997P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-32) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))))
theorem usfn1997_norm : (reflectRing usfn1997E).toPoly=usfn1997P := by
  change (reflectRing usfn1991E).toPoly.combine (reflectRing usfn1996E).toPoly=usfn1997P
  rw [usfn1991_norm, usfn1996_norm]
  exact eq_of_beq (by decide : usfn1991P.combine usfn1996P == usfn1997P)

def usfn1998E : RingExpr := (.add usfn1990E usfn1997E)
def usfn1998P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-32) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))))))
theorem usfn1998_norm : (reflectRing usfn1998E).toPoly=usfn1998P := by
  change (reflectRing usfn1990E).toPoly.combine (reflectRing usfn1997E).toPoly=usfn1998P
  rw [usfn1990_norm, usfn1997_norm]
  exact eq_of_beq (by decide : usfn1990P.combine usfn1997P == usfn1998P)

def usfn1999E : RingExpr := (.add usfn1989E usfn1998E)
def usfn1999P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-32) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))))))
theorem usfn1999_norm : (reflectRing usfn1999E).toPoly=usfn1999P := by
  change (reflectRing usfn1989E).toPoly.combine (reflectRing usfn1998E).toPoly=usfn1999P
  rw [usfn1989_norm, usfn1998_norm]
  exact eq_of_beq (by decide : usfn1989P.combine usfn1998P == usfn1999P)

def usfn2000E : RingExpr := (.add usfn1988E usfn1999E)
def usfn2000P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-32) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))
theorem usfn2000_norm : (reflectRing usfn2000E).toPoly=usfn2000P := by
  change (reflectRing usfn1988E).toPoly.combine (reflectRing usfn1999E).toPoly=usfn2000P
  rw [usfn1988_norm, usfn1999_norm]
  exact eq_of_beq (by decide : usfn1988P.combine usfn1999P == usfn2000P)

def usfn2001E : RingExpr := (.add usfn1987E usfn2000E)
def usfn2001P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-32) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))))))))))))
theorem usfn2001_norm : (reflectRing usfn2001E).toPoly=usfn2001P := by
  change (reflectRing usfn1987E).toPoly.combine (reflectRing usfn2000E).toPoly=usfn2001P
  rw [usfn1987_norm, usfn2000_norm]
  exact eq_of_beq (by decide : usfn1987P.combine usfn2000P == usfn2001P)

def usfn2002E : RingExpr := (.add usfn1986E usfn2001E)
def usfn2002P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-32) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (10) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit))) (.num (0))))))))))))))
theorem usfn2002_norm : (reflectRing usfn2002E).toPoly=usfn2002P := by
  change (reflectRing usfn1986E).toPoly.combine (reflectRing usfn2001E).toPoly=usfn2002P
  rw [usfn1986_norm, usfn2001_norm]
  exact eq_of_beq (by decide : usfn1986P.combine usfn2001P == usfn2002P)

def usfn2003E : RingExpr := (.add usfn1985E usfn2002E)
def usfn2003P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-32) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (10) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit))) (.num (0)))))))))))))))
theorem usfn2003_norm : (reflectRing usfn2003E).toPoly=usfn2003P := by
  change (reflectRing usfn1985E).toPoly.combine (reflectRing usfn2002E).toPoly=usfn2003P
  rw [usfn1985_norm, usfn2002_norm]
  exact eq_of_beq (by decide : usfn1985P.combine usfn2002P == usfn2003P)

def usfn2004E : RingExpr := (.add usfn1984E usfn2003E)
def usfn2004P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-32) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (10) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit))) (.num (0))))))))))))))))
theorem usfn2004_norm : (reflectRing usfn2004E).toPoly=usfn2004P := by
  change (reflectRing usfn1984E).toPoly.combine (reflectRing usfn2003E).toPoly=usfn2004P
  rw [usfn1984_norm, usfn2003_norm]
  exact eq_of_beq (by decide : usfn1984P.combine usfn2003P == usfn2004P)

def usfn2005E : RingExpr := (.add usfn1983E usfn2004E)
def usfn2005P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-32) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit)) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (10) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit))) (.num (0)))))))))))))))))
theorem usfn2005_norm : (reflectRing usfn2005E).toPoly=usfn2005P := by
  change (reflectRing usfn1983E).toPoly.combine (reflectRing usfn2004E).toPoly=usfn2005P
  rw [usfn1983_norm, usfn2004_norm]
  exact eq_of_beq (by decide : usfn1983P.combine usfn2004P == usfn2005P)

def usfn2006E : RingExpr := (.add usfn1982E usfn2005E)
def usfn2006P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-32) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit)) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (10) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit))) (.add (-2) (.mult ⟨3,1⟩ .unit) (.num (0))))))))))))))))))
theorem usfn2006_norm : (reflectRing usfn2006E).toPoly=usfn2006P := by
  change (reflectRing usfn1982E).toPoly.combine (reflectRing usfn2005E).toPoly=usfn2006P
  rw [usfn1982_norm, usfn2005_norm]
  exact eq_of_beq (by decide : usfn1982P.combine usfn2005P == usfn2006P)

def usfn2007E : RingExpr := (.mul usfn133E usfn2006E)
def usfn2007P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-32) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit)))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (10) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨8,4⟩ .unit)) (.num (0))))))))))))))))))
theorem usfn2007_norm : (reflectRing usfn2007E).toPoly=usfn2007P := by
  change (reflectRing usfn133E).toPoly.mul (reflectRing usfn2006E).toPoly=usfn2007P
  rw [usfn133_norm, usfn2006_norm]
  exact eq_of_beq (by decide : usfn133P.mul usfn2006P == usfn2007P)

def usfn2008E : RingExpr := (.mul usfn2E usfn2007E)
def usfn2008P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-32) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (10) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))) (.num (0))))))))))))))))))
theorem usfn2008_norm : (reflectRing usfn2008E).toPoly=usfn2008P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn2007E).toPoly=usfn2008P
  rw [usfn2_norm, usfn2007_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn2007P == usfn2008P)

def usfn2009E : RingExpr := (.mul usfn1E usfn2008E)
def usfn2009P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-32) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (10) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))))))))
theorem usfn2009_norm : (reflectRing usfn2009E).toPoly=usfn2009P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn2008E).toPoly=usfn2009P
  rw [usfn1_norm, usfn2008_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn2008P == usfn2009P)

def usfn2010E : RingExpr := (.mul usfn100E usfn2009E)
def usfn2010P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (32) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (1) (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (-10) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))))))))
theorem usfn2010_norm : (reflectRing usfn2010E).toPoly=usfn2010P := by
  change (reflectRing usfn100E).toPoly.mul (reflectRing usfn2009E).toPoly=usfn2010P
  rw [usfn100_norm, usfn2009_norm]
  exact eq_of_beq (by decide : usfn100P.mul usfn2009P == usfn2010P)

def usfn2011E : RingExpr := (.mul usfn360E usfn2010E)
def usfn2011P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (32) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-16) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (1) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (-10) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.num (0))))))))))))))))))
theorem usfn2011_norm : (reflectRing usfn2011E).toPoly=usfn2011P := by
  change (reflectRing usfn360E).toPoly.mul (reflectRing usfn2010E).toPoly=usfn2011P
  rw [usfn360_norm, usfn2010_norm]
  exact eq_of_beq (by decide : usfn360P.mul usfn2010P == usfn2011P)

def usfn2012E : RingExpr := (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))
def usfn2012P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn2012_norm : (reflectRing usfn2012E).toPoly=usfn2012P := by
  exact eq_of_beq (by decide : (reflectRing usfn2012E).toPoly == usfn2012P)

def usfn2013E : RingExpr := (.mul (.int (-6)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))
def usfn2013P : Lean.Grind.CommRing.Poly := (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn2013_norm : (reflectRing usfn2013E).toPoly=usfn2013P := by
  exact eq_of_beq (by decide : (reflectRing usfn2013E).toPoly == usfn2013P)

def usfn2014E : RingExpr := (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int (-20)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.pow (.var 4) 2)))))))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))))) (.mul (.int 48) (.mul (.var 0) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 3) (.pow (.var 9) 2)))))))))))
def usfn2014P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))
theorem usfn2014_norm : (reflectRing usfn2014E).toPoly=usfn2014P := by
  exact eq_of_beq (by decide : (reflectRing usfn2014E).toPoly == usfn2014P)

def usfn2015E : RingExpr := (.add usfn2013E usfn2014E)
def usfn2015P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))
theorem usfn2015_norm : (reflectRing usfn2015E).toPoly=usfn2015P := by
  change (reflectRing usfn2013E).toPoly.combine (reflectRing usfn2014E).toPoly=usfn2015P
  rw [usfn2013_norm, usfn2014_norm]
  exact eq_of_beq (by decide : usfn2013P.combine usfn2014P == usfn2015P)

def usfn2016E : RingExpr := (.add usfn2012E usfn2015E)
def usfn2016P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))))
theorem usfn2016_norm : (reflectRing usfn2016E).toPoly=usfn2016P := by
  change (reflectRing usfn2012E).toPoly.combine (reflectRing usfn2015E).toPoly=usfn2016P
  rw [usfn2012_norm, usfn2015_norm]
  exact eq_of_beq (by decide : usfn2012P.combine usfn2015P == usfn2016P)

def usfn2017E : RingExpr := (.add usfn566E usfn2016E)
def usfn2017P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))
theorem usfn2017_norm : (reflectRing usfn2017E).toPoly=usfn2017P := by
  change (reflectRing usfn566E).toPoly.combine (reflectRing usfn2016E).toPoly=usfn2017P
  rw [usfn566_norm, usfn2016_norm]
  exact eq_of_beq (by decide : usfn566P.combine usfn2016P == usfn2017P)

def usfn2018E : RingExpr := (.add usfn508E usfn2017E)
def usfn2018P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))
theorem usfn2018_norm : (reflectRing usfn2018E).toPoly=usfn2018P := by
  change (reflectRing usfn508E).toPoly.combine (reflectRing usfn2017E).toPoly=usfn2018P
  rw [usfn508_norm, usfn2017_norm]
  exact eq_of_beq (by decide : usfn508P.combine usfn2017P == usfn2018P)

def usfn2019E : RingExpr := (.add usfn100E usfn2018E)
def usfn2019P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (-1))))))))))
theorem usfn2019_norm : (reflectRing usfn2019E).toPoly=usfn2019P := by
  change (reflectRing usfn100E).toPoly.combine (reflectRing usfn2018E).toPoly=usfn2019P
  rw [usfn100_norm, usfn2018_norm]
  exact eq_of_beq (by decide : usfn100P.combine usfn2018P == usfn2019P)

def usfn2020E : RingExpr := (.mul usfn4E usfn2019E)
def usfn2020P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨8,2⟩ .unit) (.num (0)))))))))))
theorem usfn2020_norm : (reflectRing usfn2020E).toPoly=usfn2020P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn2019E).toPoly=usfn2020P
  rw [usfn4_norm, usfn2019_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn2019P == usfn2020P)

def usfn2021E : RingExpr := (.mul usfn382E usfn2020E)
def usfn2021P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-6) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ .unit)) (.num (0)))))))))))
theorem usfn2021_norm : (reflectRing usfn2021E).toPoly=usfn2021P := by
  change (reflectRing usfn382E).toPoly.mul (reflectRing usfn2020E).toPoly=usfn2021P
  rw [usfn382_norm, usfn2020_norm]
  exact eq_of_beq (by decide : usfn382P.mul usfn2020P == usfn2021P)

def usfn2022E : RingExpr := (.mul usfn788E usfn2021E)
def usfn2022P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-6) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (-1) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨12,1⟩ .unit))))) (.num (0)))))))))))
theorem usfn2022_norm : (reflectRing usfn2022E).toPoly=usfn2022P := by
  change (reflectRing usfn788E).toPoly.mul (reflectRing usfn2021E).toPoly=usfn2022P
  rw [usfn788_norm, usfn2021_norm]
  exact eq_of_beq (by decide : usfn788P.mul usfn2021P == usfn2022P)

def usfn2023E : RingExpr := (.mul (.mul (.var 14) (.mul (.var 1) (.pow (.var 2) 2))) (.mul (.int (-1)) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))))))
def usfn2023P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit)))))))) (.add (1) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨14,1⟩ .unit))))) (.num (0))))
theorem usfn2023_norm : (reflectRing usfn2023E).toPoly=usfn2023P := by
  exact eq_of_beq (by decide : (reflectRing usfn2023E).toPoly == usfn2023P)

def usfn2024E : RingExpr := (.mul (.var 15) (.mul (.var 1) (.pow (.var 2) 2)))
def usfn2024P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨15,1⟩ .unit))) (.num (0)))
theorem usfn2024_norm : (reflectRing usfn2024E).toPoly=usfn2024P := by
  exact eq_of_beq (by decide : (reflectRing usfn2024E).toPoly == usfn2024P)

def usfn2025E : RingExpr := (.mul (.int (-4)) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.pow (.var 8) 3))))))
def usfn2025P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0)))
theorem usfn2025_norm : (reflectRing usfn2025E).toPoly=usfn2025P := by
  exact eq_of_beq (by decide : (reflectRing usfn2025E).toPoly == usfn2025P)

def usfn2026E : RingExpr := (.add (.mul (.int 2) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 8) (.mul (.var 3) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.pow (.var 9) 2))))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.pow (.var 4) 2)))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 3) (.pow (.var 9) 2)))))))))))
def usfn2026P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))
theorem usfn2026_norm : (reflectRing usfn2026E).toPoly=usfn2026P := by
  exact eq_of_beq (by decide : (reflectRing usfn2026E).toPoly == usfn2026P)

def usfn2027E : RingExpr := (.add usfn508E usfn2026E)
def usfn2027P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))
theorem usfn2027_norm : (reflectRing usfn2027E).toPoly=usfn2027P := by
  change (reflectRing usfn508E).toPoly.combine (reflectRing usfn2026E).toPoly=usfn2027P
  rw [usfn508_norm, usfn2026_norm]
  exact eq_of_beq (by decide : usfn508P.combine usfn2026P == usfn2027P)

def usfn2028E : RingExpr := (.add usfn945E usfn2027E)
def usfn2028P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))
theorem usfn2028_norm : (reflectRing usfn2028E).toPoly=usfn2028P := by
  change (reflectRing usfn945E).toPoly.combine (reflectRing usfn2027E).toPoly=usfn2028P
  rw [usfn945_norm, usfn2027_norm]
  exact eq_of_beq (by decide : usfn945P.combine usfn2027P == usfn2028P)

def usfn2029E : RingExpr := (.add usfn2025E usfn2028E)
def usfn2029P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))
theorem usfn2029_norm : (reflectRing usfn2029E).toPoly=usfn2029P := by
  change (reflectRing usfn2025E).toPoly.combine (reflectRing usfn2028E).toPoly=usfn2029P
  rw [usfn2025_norm, usfn2028_norm]
  exact eq_of_beq (by decide : usfn2025P.combine usfn2028P == usfn2029P)

def usfn2030E : RingExpr := (.add usfn100E usfn2029E)
def usfn2030P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (-1)))))))))
theorem usfn2030_norm : (reflectRing usfn2030E).toPoly=usfn2030P := by
  change (reflectRing usfn100E).toPoly.combine (reflectRing usfn2029E).toPoly=usfn2030P
  rw [usfn100_norm, usfn2029_norm]
  exact eq_of_beq (by decide : usfn100P.combine usfn2029P == usfn2030P)

def usfn2031E : RingExpr := (.mul usfn4E usfn2030E)
def usfn2031P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨8,2⟩ .unit) (.num (0))))))))))
theorem usfn2031_norm : (reflectRing usfn2031E).toPoly=usfn2031P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn2030E).toPoly=usfn2031P
  rw [usfn4_norm, usfn2030_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn2030P == usfn2031P)

def usfn2032E : RingExpr := (.mul usfn409E usfn2031E)
def usfn2032P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ .unit)) (.num (0))))))))))
theorem usfn2032_norm : (reflectRing usfn2032E).toPoly=usfn2032P := by
  change (reflectRing usfn409E).toPoly.mul (reflectRing usfn2031E).toPoly=usfn2032P
  rw [usfn409_norm, usfn2031_norm]
  exact eq_of_beq (by decide : usfn409P.mul usfn2031P == usfn2032P)

def usfn2033E : RingExpr := (.mul usfn362E usfn2032E)
def usfn2033P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit))) (.num (0))))))))))
theorem usfn2033_norm : (reflectRing usfn2033E).toPoly=usfn2033P := by
  change (reflectRing usfn362E).toPoly.mul (reflectRing usfn2032E).toPoly=usfn2033P
  rw [usfn362_norm, usfn2032_norm]
  exact eq_of_beq (by decide : usfn362P.mul usfn2032P == usfn2033P)

def usfn2034E : RingExpr := (.mul usfn361E usfn2033E)
def usfn2034P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit))) (.num (0))))))))))
theorem usfn2034_norm : (reflectRing usfn2034E).toPoly=usfn2034P := by
  change (reflectRing usfn361E).toPoly.mul (reflectRing usfn2033E).toPoly=usfn2034P
  rw [usfn361_norm, usfn2033_norm]
  exact eq_of_beq (by decide : usfn361P.mul usfn2033P == usfn2034P)

def usfn2035E : RingExpr := (.mul usfn2024E usfn2034E)
def usfn2035P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit)))))))))) (.add (16) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit)))))))))) (.add (-8) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-4) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨15,1⟩ .unit)))))) (.num (0))))))))))
theorem usfn2035_norm : (reflectRing usfn2035E).toPoly=usfn2035P := by
  change (reflectRing usfn2024E).toPoly.mul (reflectRing usfn2034E).toPoly=usfn2035P
  rw [usfn2024_norm, usfn2034_norm]
  exact eq_of_beq (by decide : usfn2024P.mul usfn2034P == usfn2035P)

def usfn2036E : RingExpr := (.mul (.mul (.var 16) (.mul (.var 1) (.pow (.var 2) 2))) (.mul (.int (-2)) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))))))))
def usfn2036P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨16,1⟩ .unit))))))))) (.add (2) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨16,1⟩ .unit)))))) (.num (0))))
theorem usfn2036_norm : (reflectRing usfn2036E).toPoly=usfn2036P := by
  exact eq_of_beq (by decide : (reflectRing usfn2036E).toPoly == usfn2036P)

def usfn2037E : RingExpr := (.mul (.int 2) (.mul (.var 9) (.pow (.var 8) 2)))
def usfn2037P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)) (.num (0)))
theorem usfn2037_norm : (reflectRing usfn2037E).toPoly=usfn2037P := by
  exact eq_of_beq (by decide : (reflectRing usfn2037E).toPoly == usfn2037P)

def usfn2038E : RingExpr := (.mul (.int (-1)) (.mul (.var 0) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))
def usfn2038P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ .unit))) (.num (0)))
theorem usfn2038_norm : (reflectRing usfn2038E).toPoly=usfn2038P := by
  exact eq_of_beq (by decide : (reflectRing usfn2038E).toPoly == usfn2038P)

def usfn2039E : RingExpr := (.mul (.int (-3)) (.mul (.var 10) (.mul (.var 9) (.pow (.var 8) 2))))
def usfn2039P : Lean.Grind.CommRing.Poly := (.add (-3) (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))
theorem usfn2039_norm : (reflectRing usfn2039E).toPoly=usfn2039P := by
  exact eq_of_beq (by decide : (reflectRing usfn2039E).toPoly == usfn2039P)

def usfn2040E : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.var 9))))
def usfn2040P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit))) (.num (0)))
theorem usfn2040_norm : (reflectRing usfn2040E).toPoly=usfn2040P := by
  exact eq_of_beq (by decide : (reflectRing usfn2040E).toPoly == usfn2040P)

def usfn2041E : RingExpr := (.mul (.int (-8)) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))
def usfn2041P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))
theorem usfn2041_norm : (reflectRing usfn2041E).toPoly=usfn2041P := by
  exact eq_of_beq (by decide : (reflectRing usfn2041E).toPoly == usfn2041P)

def usfn2042E : RingExpr := (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))
def usfn2042P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.num (0)))
theorem usfn2042_norm : (reflectRing usfn2042E).toPoly=usfn2042P := by
  exact eq_of_beq (by decide : (reflectRing usfn2042E).toPoly == usfn2042P)

def usfn2043E : RingExpr := (.mul (.int 4) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.pow (.var 8) 3))))))
def usfn2043P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn2043_norm : (reflectRing usfn2043E).toPoly=usfn2043P := by
  exact eq_of_beq (by decide : (reflectRing usfn2043E).toPoly == usfn2043P)

def usfn2044E : RingExpr := (.mul (.int 12) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))
def usfn2044P : Lean.Grind.CommRing.Poly := (.add (12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn2044_norm : (reflectRing usfn2044E).toPoly=usfn2044P := by
  exact eq_of_beq (by decide : (reflectRing usfn2044E).toPoly == usfn2044P)

def usfn2045E : RingExpr := (.mul (.int (-8)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 8) 3) (.pow (.var 4) 3)))))))
def usfn2045P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn2045_norm : (reflectRing usfn2045E).toPoly=usfn2045P := by
  exact eq_of_beq (by decide : (reflectRing usfn2045E).toPoly == usfn2045P)

def usfn2046E : RingExpr := (.mul (.int (-8)) (.mul (.var 7) (.mul (.var 3) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.pow (.var 9) 2)))))))
def usfn2046P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn2046_norm : (reflectRing usfn2046E).toPoly=usfn2046P := by
  exact eq_of_beq (by decide : (reflectRing usfn2046E).toPoly == usfn2046P)

def usfn2047E : RingExpr := (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))) (.add (.mul (.int 16) (.mul (.var 7) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 4) (.pow (.var 9) 2))))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.pow (.var 9) 2)))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 3) (.pow (.var 9) 2)))))))))))
def usfn2047P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))
theorem usfn2047_norm : (reflectRing usfn2047E).toPoly=usfn2047P := by
  exact eq_of_beq (by decide : (reflectRing usfn2047E).toPoly == usfn2047P)

def usfn2048E : RingExpr := (.add usfn2046E usfn2047E)
def usfn2048P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))
theorem usfn2048_norm : (reflectRing usfn2048E).toPoly=usfn2048P := by
  change (reflectRing usfn2046E).toPoly.combine (reflectRing usfn2047E).toPoly=usfn2048P
  rw [usfn2046_norm, usfn2047_norm]
  exact eq_of_beq (by decide : usfn2046P.combine usfn2047P == usfn2048P)

def usfn2049E : RingExpr := (.add usfn2045E usfn2048E)
def usfn2049P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))))
theorem usfn2049_norm : (reflectRing usfn2049E).toPoly=usfn2049P := by
  change (reflectRing usfn2045E).toPoly.combine (reflectRing usfn2048E).toPoly=usfn2049P
  rw [usfn2045_norm, usfn2048_norm]
  exact eq_of_beq (by decide : usfn2045P.combine usfn2048P == usfn2049P)

def usfn2050E : RingExpr := (.add usfn2044E usfn2049E)
def usfn2050P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))
theorem usfn2050_norm : (reflectRing usfn2050E).toPoly=usfn2050P := by
  change (reflectRing usfn2044E).toPoly.combine (reflectRing usfn2049E).toPoly=usfn2050P
  rw [usfn2044_norm, usfn2049_norm]
  exact eq_of_beq (by decide : usfn2044P.combine usfn2049P == usfn2050P)

def usfn2051E : RingExpr := (.add usfn2043E usfn2050E)
def usfn2051P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))
theorem usfn2051_norm : (reflectRing usfn2051E).toPoly=usfn2051P := by
  change (reflectRing usfn2043E).toPoly.combine (reflectRing usfn2050E).toPoly=usfn2051P
  rw [usfn2043_norm, usfn2050_norm]
  exact eq_of_beq (by decide : usfn2043P.combine usfn2050P == usfn2051P)

def usfn2052E : RingExpr := (.add usfn2042E usfn2051E)
def usfn2052P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))))
theorem usfn2052_norm : (reflectRing usfn2052E).toPoly=usfn2052P := by
  change (reflectRing usfn2042E).toPoly.combine (reflectRing usfn2051E).toPoly=usfn2052P
  rw [usfn2042_norm, usfn2051_norm]
  exact eq_of_beq (by decide : usfn2042P.combine usfn2051P == usfn2052P)

def usfn2053E : RingExpr := (.add usfn2041E usfn2052E)
def usfn2053P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0))))))))))))
theorem usfn2053_norm : (reflectRing usfn2053E).toPoly=usfn2053P := by
  change (reflectRing usfn2041E).toPoly.combine (reflectRing usfn2052E).toPoly=usfn2053P
  rw [usfn2041_norm, usfn2052_norm]
  exact eq_of_beq (by decide : usfn2041P.combine usfn2052P == usfn2053P)

def usfn2054E : RingExpr := (.add usfn2040E usfn2053E)
def usfn2054P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit))) (.num (0)))))))))))))
theorem usfn2054_norm : (reflectRing usfn2054E).toPoly=usfn2054P := by
  change (reflectRing usfn2040E).toPoly.combine (reflectRing usfn2053E).toPoly=usfn2054P
  rw [usfn2040_norm, usfn2053_norm]
  exact eq_of_beq (by decide : usfn2040P.combine usfn2053P == usfn2054P)

def usfn2055E : RingExpr := (.add usfn2039E usfn2054E)
def usfn2055P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-3) (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit))) (.num (0))))))))))))))
theorem usfn2055_norm : (reflectRing usfn2055E).toPoly=usfn2055P := by
  change (reflectRing usfn2039E).toPoly.combine (reflectRing usfn2054E).toPoly=usfn2055P
  rw [usfn2039_norm, usfn2054_norm]
  exact eq_of_beq (by decide : usfn2039P.combine usfn2054P == usfn2055P)

def usfn2056E : RingExpr := (.add usfn2038E usfn2055E)
def usfn2056P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ .unit))) (.add (-3) (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit))) (.num (0)))))))))))))))
theorem usfn2056_norm : (reflectRing usfn2056E).toPoly=usfn2056P := by
  change (reflectRing usfn2038E).toPoly.combine (reflectRing usfn2055E).toPoly=usfn2056P
  rw [usfn2038_norm, usfn2055_norm]
  exact eq_of_beq (by decide : usfn2038P.combine usfn2055P == usfn2056P)

def usfn2057E : RingExpr := (.add usfn2037E usfn2056E)
def usfn2057P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,2⟩ .unit))) (.add (-3) (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit))) (.add (2) (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)) (.num (0))))))))))))))))
theorem usfn2057_norm : (reflectRing usfn2057E).toPoly=usfn2057P := by
  change (reflectRing usfn2037E).toPoly.combine (reflectRing usfn2056E).toPoly=usfn2057P
  rw [usfn2037_norm, usfn2056_norm]
  exact eq_of_beq (by decide : usfn2037P.combine usfn2056P == usfn2057P)

def usfn2058E : RingExpr := (.mul usfn4E usfn2057E)
def usfn2058P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,4⟩ .unit))) (.add (-3) (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (2) (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)) (.num (0))))))))))))))))
theorem usfn2058_norm : (reflectRing usfn2058E).toPoly=usfn2058P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn2057E).toPoly=usfn2058P
  rw [usfn4_norm, usfn2057_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn2057P == usfn2058P)

def usfn2059E : RingExpr := (.mul usfn382E usfn2058E)
def usfn2059P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (12) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,4⟩ .unit))) (.add (-3) (.mult ⟨3,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))) (.num (0))))))))))))))))
theorem usfn2059_norm : (reflectRing usfn2059E).toPoly=usfn2059P := by
  change (reflectRing usfn382E).toPoly.mul (reflectRing usfn2058E).toPoly=usfn2059P
  rw [usfn382_norm, usfn2058_norm]
  exact eq_of_beq (by decide : usfn382P.mul usfn2058P == usfn2059P)

def usfn2060E : RingExpr := (.mul usfn2E usfn2059E)
def usfn2060P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (12) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-3) (.mult ⟨3,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))))))
theorem usfn2060_norm : (reflectRing usfn2060E).toPoly=usfn2060P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn2059E).toPoly=usfn2060P
  rw [usfn2_norm, usfn2059_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn2059P == usfn2060P)

def usfn2061E : RingExpr := (.mul usfn1E usfn2060E)
def usfn2061P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (12) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-3) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))))))
theorem usfn2061_norm : (reflectRing usfn2061E).toPoly=usfn2061P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn2060E).toPoly=usfn2061P
  rw [usfn1_norm, usfn2060_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn2060P == usfn2061P)

def usfn2062E : RingExpr := (.mul usfn100E usfn2061E)
def usfn2062P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-12) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))))))
theorem usfn2062_norm : (reflectRing usfn2062E).toPoly=usfn2062P := by
  change (reflectRing usfn100E).toPoly.mul (reflectRing usfn2061E).toPoly=usfn2062P
  rw [usfn100_norm, usfn2061_norm]
  exact eq_of_beq (by decide : usfn100P.mul usfn2061P == usfn2062P)

def usfn2063E : RingExpr := (.mul usfn381E usfn2062E)
def usfn2063P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-16) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (8) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (8) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-12) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-4) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (8) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (3) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.num (0))))))))))))))))
theorem usfn2063_norm : (reflectRing usfn2063E).toPoly=usfn2063P := by
  change (reflectRing usfn381E).toPoly.mul (reflectRing usfn2062E).toPoly=usfn2063P
  rw [usfn381_norm, usfn2062_norm]
  exact eq_of_beq (by decide : usfn381P.mul usfn2062P == usfn2063P)

def usfn2064E : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.pow (.var 8) 2))))
def usfn2064P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))
theorem usfn2064_norm : (reflectRing usfn2064E).toPoly=usfn2064P := by
  exact eq_of_beq (by decide : (reflectRing usfn2064E).toPoly == usfn2064P)

def usfn2065E : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2)))))
def usfn2065P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.num (0)))
theorem usfn2065_norm : (reflectRing usfn2065E).toPoly=usfn2065P := by
  exact eq_of_beq (by decide : (reflectRing usfn2065E).toPoly == usfn2065P)

def usfn2066E : RingExpr := (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))
def usfn2066P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn2066_norm : (reflectRing usfn2066E).toPoly=usfn2066P := by
  exact eq_of_beq (by decide : (reflectRing usfn2066E).toPoly == usfn2066P)

def usfn2067E : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.var 9))))))
def usfn2067P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn2067_norm : (reflectRing usfn2067E).toPoly=usfn2067P := by
  exact eq_of_beq (by decide : (reflectRing usfn2067E).toPoly == usfn2067P)

def usfn2068E : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.pow (.var 8) 3)))))))
def usfn2068P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn2068_norm : (reflectRing usfn2068E).toPoly=usfn2068P := by
  exact eq_of_beq (by decide : (reflectRing usfn2068E).toPoly == usfn2068P)

def usfn2069E : RingExpr := (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.pow (.var 9) 2)))))))) (.add (.mul (.int (-3)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))) (.mul (.int 16) (.mul (.var 0) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 3) (.pow (.var 9) 2)))))))))))
def usfn2069P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.num (0))))))
theorem usfn2069_norm : (reflectRing usfn2069E).toPoly=usfn2069P := by
  exact eq_of_beq (by decide : (reflectRing usfn2069E).toPoly == usfn2069P)

def usfn2070E : RingExpr := (.add usfn1606E usfn2069E)
def usfn2070P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.num (0)))))))
theorem usfn2070_norm : (reflectRing usfn2070E).toPoly=usfn2070P := by
  change (reflectRing usfn1606E).toPoly.combine (reflectRing usfn2069E).toPoly=usfn2070P
  rw [usfn1606_norm, usfn2069_norm]
  exact eq_of_beq (by decide : usfn1606P.combine usfn2069P == usfn2070P)

def usfn2071E : RingExpr := (.add usfn2068E usfn2070E)
def usfn2071P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.num (0))))))))
theorem usfn2071_norm : (reflectRing usfn2071E).toPoly=usfn2071P := by
  change (reflectRing usfn2068E).toPoly.combine (reflectRing usfn2070E).toPoly=usfn2071P
  rw [usfn2068_norm, usfn2070_norm]
  exact eq_of_beq (by decide : usfn2068P.combine usfn2070P == usfn2071P)

def usfn2072E : RingExpr := (.add usfn2067E usfn2071E)
def usfn2072P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))
theorem usfn2072_norm : (reflectRing usfn2072E).toPoly=usfn2072P := by
  change (reflectRing usfn2067E).toPoly.combine (reflectRing usfn2071E).toPoly=usfn2072P
  rw [usfn2067_norm, usfn2071_norm]
  exact eq_of_beq (by decide : usfn2067P.combine usfn2071P == usfn2072P)

def usfn2073E : RingExpr := (.add usfn2066E usfn2072E)
def usfn2073P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))
theorem usfn2073_norm : (reflectRing usfn2073E).toPoly=usfn2073P := by
  change (reflectRing usfn2066E).toPoly.combine (reflectRing usfn2072E).toPoly=usfn2073P
  rw [usfn2066_norm, usfn2072_norm]
  exact eq_of_beq (by decide : usfn2066P.combine usfn2072P == usfn2073P)

#print axioms usfn2073_norm
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
