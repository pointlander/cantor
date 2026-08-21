/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Infinity
import ToE.Physics
import ToE.Cosmology

/-!
# A Theory of Everything

At the origin of time, quantum field theory and general relativity are
one theory, whose kinematic infinity is that of the countable numbers `ℕ`.

After time passes they separate:

* quantum field theory retains the countable infinity (a separable Fock
  space, modes labelled by `ℕ`);
* general relativity is carried by the infinity of the reals, realised
  as the power object of that same countable carrier — the Cantor space
  `ℕ → Bool`, equinumerous with `ℝ`.

The separation is forced: Cantor's diagonal argument shows the two
infinities are not equinumerous, so the theories cannot be identified
once the continuum has appeared.
-/

namespace ToE

/-- The theory of everything.

1. There is a unified theory whose carrier has the infinity of the
   countable numbers.
2. After time, that theory splits into QFT and GR.
3. QFT has the infinity of the countable numbers.
4. GR has the infinity of the reals.
5. Those two infinities are distinct, so the split is sharp. -/
theorem theory_of_everything :
    HasCountableInfinity unifiedAtOrigin.Carrier ∧
    (let (Q, G) := separate unifiedAtOrigin
     HasCountableInfinity Q.Modes ∧
     HasRealInfinity G.Spacetime ∧
     ¬ Equinumerous Q.Modes G.Spacetime) := by
  refine ⟨unifiedAtOrigin.countableInfinity, ?_⟩
  exact ⟨qft_keeps_countable_infinity unifiedAtOrigin,
         gr_acquires_real_infinity unifiedAtOrigin,
         qft_ne_gr unifiedAtOrigin⟩

/-- Equivalent packaging along cosmic time: at time zero the cosmos is
unified and countable; at every later time it is split, with QFT countable
and GR continuum. -/
theorem theory_of_everything_in_time :
    (epoch 0 = .origin ∧
      HasCountableInfinity (atTime 0).Carrier) ∧
    (∀ n : Time,
      epoch (n + 1) = .afterTime ∧
      HasCountableInfinity (atTime (n + 1)).1.Modes ∧
      HasRealInfinity (atTime (n + 1)).2.Spacetime ∧
      ¬ Equinumerous
          (atTime (n + 1)).1.Modes
          (atTime (n + 1)).2.Spacetime) := by
  refine ⟨⟨rfl, at_origin_unified_countable⟩, ?_⟩
  intro n
  exact ⟨rfl,
         after_time_qft_countable,
         after_time_gr_real,
         after_time_separated⟩

/-- The countable numbers are infinite, the reals are infinite, and
the infinities are not the same. -/
theorem two_infinities :
    Infinite Nat ∧ Infinite Continuum ∧ ¬ Equinumerous Nat Continuum :=
  ⟨infinite_nat, infinite_continuum, not_equinumerous_nat_continuum⟩

end ToE
