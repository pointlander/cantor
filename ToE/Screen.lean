/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Number

/-!
# Simultaneous readouts on a spacelike screen

A holographic screen is an antichain of carrier events. The joint
readout of a state on that screen is the tuple of number operators

\[
R_S(f)_i = N_{s_i}(f) = \langle e_{s_i}, f\rangle.
\]

The events are spacelike, so the tuple is simultaneous: it is not a
timelike sequence and has no proper time. A finite-area screen has
finitely many readouts, not the infinity of the reals.
-/

namespace ToE

/-- Joint occupation readout of `f` on the events of a realized
screen whose carrier is `Nat`. -/
def screenReadout (S : RealizedScreen standardCausal) (f : FockNat) :
    Fin S.screen.bits → Nat :=
  fun i => occupation (S.events i) f

theorem screenReadout_eq_inner (S : RealizedScreen standardCausal)
    (f : FockNat) (i : Fin S.screen.bits) :
    screenReadout S f i = inner (FockNat.basis (S.events i)) f :=
  occupation_eq_inner (S.events i) f

theorem screenReadout_vacuum (S : RealizedScreen standardCausal)
    (i : Fin S.screen.bits) :
    screenReadout S FockNat.vacuum i = 0 :=
  occupation_vacuum (S.events i)

/-- Screen events are pairwise spacelike, so the readout is joint
rather than ordered in time. -/
theorem screenReadout_spacelike (S : RealizedScreen standardCausal)
    (i j : Fin S.screen.bits) (hne : i ≠ j) :
    ¬ standardCausal.Rel (S.events i) (S.events j) :=
  (S.antichain i j hne).1

theorem screenReadout_not_chain (S : RealizedScreen standardCausal)
    (hbits : 1 < S.screen.bits) :
    ¬ standardCausal.IsChain S.events :=
  S.not_a_chain hbits

theorem screenReadout_finite (S : RealizedScreen standardCausal) :
    ¬ HasRealInfinity (Fin S.screen.bits) :=
  S.screen.no_real_infinity_on_screen

noncomputable section

theorem pairReadout_vacuum :
    screenReadout pairRealizedScreen FockNat.vacuum = fun _ => 0 := by
  funext i
  exact screenReadout_vacuum pairRealizedScreen i

theorem pairReadout_basis0_left :
    screenReadout pairRealizedScreen (FockNat.basis 0)
      ⟨0, by decide⟩ = 1 := by
  simp [screenReadout, occupation, pairRealizedScreen, FockNat.basis]

theorem pairReadout_basis0_right :
    screenReadout pairRealizedScreen (FockNat.basis 0)
      ⟨1, by decide⟩ = 0 := by
  simp [screenReadout, occupation, pairRealizedScreen, FockNat.basis]

theorem pairReadout_spacelike
    (i j : Fin pairRealizedScreen.screen.bits) (hne : i ≠ j) :
    ¬ standardCausal.Rel
        (pairRealizedScreen.events i) (pairRealizedScreen.events j) :=
  screenReadout_spacelike pairRealizedScreen i j hne

theorem pairReadout_not_chain :
    ¬ standardCausal.IsChain pairRealizedScreen.events :=
  pairRealizedScreen_not_a_chain

theorem pairReadout_finite :
    ¬ HasRealInfinity (Fin pairRealizedScreen.screen.bits) :=
  screenReadout_finite pairRealizedScreen

end

end ToE
