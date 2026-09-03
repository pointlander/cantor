/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Screen
import ToE.Information

/-!
# Horizon readouts along the Page curve

Bekenstein–Hawking entropy is the length of a simultaneous occupation
tuple on the remaining antichain. Early, that tuple is the two-bit
horizon `{2,3}`. At the Page time it shrinks to `{3}` while radiation
is read at `{4}`. Late, the screen is gone and the two occupations sit
on `{4,5}`. The diamond stays finite: interior events are not a
continuum of extra number operators.
-/

namespace ToE

/-- Occupations of a finite carrier packet (remaining hole or
radiation). -/
def packetReadout (P : InformationPacket standardDiamond) (f : FockNat) :
    Fin P.bits → Nat :=
  fun i => occupation (P.events i) f

theorem packetReadout_vacuum (P : InformationPacket standardDiamond)
    (i : Fin P.bits) :
    packetReadout P FockNat.vacuum i = 0 :=
  occupation_vacuum (P.events i)

noncomputable section

/-- Joint readout on the standard horizon `{2,3}`. -/
def horizonReadout (f : FockNat) :
    Fin midRealizedScreen.screen.bits → Nat :=
  screenReadout midRealizedScreen f

theorem horizonReadout_entropy :
    standardBlackHole.entropy = midRealizedScreen.screen.bits :=
  rfl

theorem horizonReadout_vacuum :
    horizonReadout FockNat.vacuum = fun _ => 0 := by
  funext i
  exact screenReadout_vacuum midRealizedScreen i

theorem horizonReadout_basis2_left :
    horizonReadout (FockNat.basis 2) ⟨0, by decide⟩ = 1 := by
  simp [horizonReadout, screenReadout, occupation, midRealizedScreen,
    FockNat.basis]

theorem horizonReadout_basis2_right :
    horizonReadout (FockNat.basis 2) ⟨1, by decide⟩ = 0 := by
  simp [horizonReadout, screenReadout, occupation, midRealizedScreen,
    FockNat.basis]

theorem pageEarly_slots :
    pageEarly.remaining.bits + pageEarly.radiation.bits = 2 :=
  rfl

theorem pageLate_slots :
    pageLate.remaining.bits = 0 ∧ pageLate.radiation.bits = 2 :=
  ⟨rfl, rfl⟩

theorem page_slots_conserved :
    pageEarly.remaining.bits + pageEarly.radiation.bits =
      pageLate.remaining.bits + pageLate.radiation.bits :=
  rfl

/-- After the first quantum leaves the hole, the remaining readout is
the one-bit screen `{3}`. -/
theorem leftoverReadout_basis3 :
    screenReadout leftoverScreen (FockNat.basis 3)
      ⟨0, leftoverScreen.screen.bits_pos⟩ = 1 := by
  simp [screenReadout, occupation, leftoverScreen, FockNat.basis]

theorem leftoverReadout_basis2 :
    screenReadout leftoverScreen (FockNat.basis 2)
      ⟨0, leftoverScreen.screen.bits_pos⟩ = 0 := by
  simp [screenReadout, occupation, leftoverScreen, FockNat.basis]

theorem radiationReadout_first :
    packetReadout firstRadiation (FockNat.basis 4)
      ⟨0, by decide⟩ = 1 := by
  simp [packetReadout, occupation, firstRadiation, FockNat.basis]

/-- Interior plus horizon plus exterior of the diamond is a finite
set of carrier events, not a continuum of independent number
operators. -/
theorem diamond_readouts_finite :
    ¬ HasRealInfinity (Fin standardDiamond.size) :=
  standardDiamond.not_real_infinity

end

end ToE
