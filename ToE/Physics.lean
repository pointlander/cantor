/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Infinity

/-!
# Physical theories

A physical theory, in this formalization, is a kinematic carrier together
with the infinity that carrier bears.

* **Quantum field theory** is separable: its Fock space (constructed in
  `ToE.Fock`) admits a countable basis of finite-support occupation-number
  states, so it carries the infinity of the countable numbers.
* **General relativity** is a continuum theory: spacetime is locally
  modelled on `ℝ⁴`, and `|ℝ⁴| = |ℝ|`, so it carries the infinity of the
  reals.
* **The unified theory** at the origin is a single countable carrier.
  Gravity has not yet opened onto the power object of that carrier.
-/

namespace ToE

/-- The unified theory: one countable ontology of events and quanta. -/
structure UnifiedTheory where
  Carrier : Type
  countableInfinity : HasCountableInfinity Carrier

/-- Quantum field theory: a countable mode set, as in a separable
Fock space `⊕ₙ ℓ²(ℕ)ˢʸᵐⁿ`. -/
structure QuantumFieldTheory where
  Modes : Type
  countableInfinity : HasCountableInfinity Modes

/-- General relativity: a spacetime continuum equinumerous with the reals. -/
structure GeneralRelativity where
  Spacetime : Type
  realInfinity : HasRealInfinity Spacetime

/-- The unified theory at the origin of time. -/
def unifiedAtOrigin : UnifiedTheory :=
  { Carrier := Nat
    countableInfinity := nat_has_countable_infinity }

/-- Standard QFT: modes labelled by the countable numbers. -/
def standardQFT : QuantumFieldTheory :=
  { Modes := Nat
    countableInfinity := nat_has_countable_infinity }

/-- Standard GR: spacetime as the continuum. -/
def standardGR : GeneralRelativity :=
  { Spacetime := Continuum
    realInfinity := continuum_has_real_infinity }

/-- Time's action: the quantum sector keeps the original countable carrier;
the gravitational sector is the function-space `Carrier → Bool`, i.e. the
power object, which is the infinity of the reals. -/
def separate (U : UnifiedTheory) : QuantumFieldTheory × GeneralRelativity :=
  ({ Modes := U.Carrier
     countableInfinity := U.countableInfinity },
   { Spacetime := U.Carrier → Bool
     realInfinity :=
       (equinumerous_arrow_bool U.countableInfinity).trans
         continuum_has_real_infinity })

/-- QFT after the split is the unified carrier. -/
theorem qft_is_the_origin (U : UnifiedTheory) :
    (separate U).1.Modes = U.Carrier := rfl

/-- GR after the split is the power object of the unified carrier. -/
theorem gr_is_the_power_object (U : UnifiedTheory) :
    (separate U).2.Spacetime = (U.Carrier → Bool) := rfl

/-- QFT keeps the countable infinity of the origin. -/
theorem qft_keeps_countable_infinity (U : UnifiedTheory) :
    HasCountableInfinity (separate U).1.Modes :=
  (separate U).1.countableInfinity

/-- GR acquires the infinity of the reals. -/
theorem gr_acquires_real_infinity (U : UnifiedTheory) :
    HasRealInfinity (separate U).2.Spacetime :=
  (separate U).2.realInfinity

/-- The split is sharp: after separation the two theories cannot be
identified, because their infinities differ. -/
theorem qft_ne_gr (U : UnifiedTheory) :
    ¬ Equinumerous (separate U).1.Modes (separate U).2.Spacetime := by
  intro h
  exact countable_infinity_ne_real_infinity
    (separate U).1.countableInfinity
    (h.trans (separate U).2.realInfinity)

end ToE
