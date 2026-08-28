/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Infinity
import ToE.Physics
import ToE.Cosmology
import ToE.Geometry
import ToE.Information
import ToE.Dimension
import ToE.Fock
import ToE.Causal
import ToE.Growth
import ToE.Inner
import ToE.Modes
import ToE.Interval

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

/-- After the split the countable carrier sits in the continuum as a
Delone set: a positive gap, a covering radius, a positive density, and
a positive Newton constant \(G \sim (\mathrm{gap})^2\). A dense embedding
is forbidden. -/
theorem theory_of_everything_geometry :
    (separate unifiedAtOrigin).1.Modes = standardDelone.Carrier ∧
    (separate unifiedAtOrigin).2.Spacetime = standardDelone.Spacetime ∧
    0 < standardDelone.gap ∧
    0 < standardDelone.coveringRadius ∧
    0 < standardDelone.density ∧
    0 < standardDelone.newtonG ∧
    Function.Injective standardDelone.realize ∧
    ¬ Function.Surjective standardDelone.realize ∧
    ¬ MetricallyDense standardDelone.realize standardDelone.dist :=
  ⟨origin_split_realized.1,
   origin_split_realized.2,
   standardDelone.gap_pos,
   standardDelone.coveringRadius_pos,
   standardDelone.density_pos,
   standardDelone.newtonG_pos,
   standardDelone.realize_injective,
   standardDelone.realize_not_surjective,
   standardDelone.not_metrically_dense⟩

/-- A finite-area holographic screen counts carrier bits by the law
\(A = 4 N G\). Its information is finite, hence not the continuum. -/
theorem theory_of_everything_holography :
    standardScreen.area =
      (4 : Rat) * (standardScreen.bits : Rat) * standardDelone.newtonG ∧
    0 < standardScreen.area ∧
    0 < standardScreen.bits ∧
    0 < standardDelone.newtonG ∧
    ¬ HasRealInfinity (Fin standardScreen.bits) :=
  ⟨standardScreen_area_law,
   standardScreen.area_pos,
   standardScreen.bits_pos,
   standardDelone.newtonG_pos,
   standardScreen_no_continuum⟩

/-- The carrier carries a locally finite causal order. A holographic
screen is \(N\) incomparable events: the one-bit cell is a single event,
and two spacelike neighbours form a two-bit screen, which is not a chain. -/
theorem theory_of_everything_causal :
    (∀ x, ¬ standardCausal.Rel x x) ∧
    (∀ x y, ¬ Infinite
      { z // standardCausal.Rel x z ∧ standardCausal.Rel z y }) ∧
    Function.Injective standardRealizedScreen.events ∧
    standardRealizedScreen.screen.bits = 1 ∧
    pairRealizedScreen.screen.bits = 2 ∧
    pairRealizedScreen.screen.area =
      (4 : Rat) * (pairRealizedScreen.screen.bits : Rat) *
        standardDelone.newtonG ∧
    ¬ standardCausal.IsChain pairRealizedScreen.events :=
  ⟨standardCausal.irrefl,
   standardCausal.interval_finite,
   standardRealizedScreen.events_injective,
   rfl,
   rfl,
   pairRealizedScreen.area_law,
   pairRealizedScreen_not_a_chain⟩

/-- A finite causal diamond splits across a maximal screen into past,
the screen, and future. The three classes are exclusive; past and future
are nonempty in the standard example; none of them carries the continuum. -/
theorem theory_of_everything_horizon :
    (∀ i, standardDiamond.mem (midRealizedScreen.events i)) ∧
    InPast midRealizedScreen standardDiamond (0 : Nat) ∧
    RealizedScreen.OnScreen midRealizedScreen (2 : Nat) ∧
    InFuture midRealizedScreen standardDiamond (4 : Nat) ∧
    ¬ (InPast midRealizedScreen standardDiamond (0 : Nat) ∧
        InFuture midRealizedScreen standardDiamond (0 : Nat)) ∧
    midRealizedScreen.screen.area =
      (4 : Rat) * (midRealizedScreen.screen.bits : Rat) *
        standardDelone.newtonG ∧
    ¬ HasRealInfinity (Fin standardDiamond.size) :=
  ⟨standardHorizon.screen_in_diamond,
   standardHorizon_has_past,
   ⟨⟨0, by decide⟩, rfl⟩,
   standardHorizon_has_future,
   standardHorizon_past_not_future,
   midRealizedScreen.area_law,
   standardDiamond.not_real_infinity⟩

/-- A finite-area black hole has Bekenstein–Hawking entropy equal to
its bit count. The interior cannot carry the continuum. Evaporation
conserves that count along the Page curve: the bits start on the hole
and end in the radiation, with no continuum remnant. -/
theorem theory_of_everything_information :
    standardBlackHole.entropy = 2 ∧
    standardBlackHole.area =
      (4 : Rat) * (standardBlackHole.entropy : Rat) *
        standardDelone.newtonG ∧
    standardBlackHole.Interior (0 : Nat) ∧
    standardBlackHole.Exterior (4 : Nat) ∧
    ¬ HasRealInfinity (Fin standardInterior.bits) ∧
    standardPage.early.pageSum = standardPage.totalBits ∧
    standardPage.middle.pageSum = standardPage.totalBits ∧
    standardPage.late.pageSum = standardPage.totalBits ∧
    standardPage.early.remaining.bits = 2 ∧
    standardPage.late.remaining.bits = 0 ∧
    standardPage.late.radiation.bits = 2 ∧
    ¬ HasRealInfinity (Fin standardPage.late.remaining.bits) :=
  ⟨rfl,
   standardBlackHole.area_law,
   standardBlackHole_has_interior,
   standardBlackHole_has_exterior,
   standardInterior_no_real_infinity,
   standardPage.early_sum,
   standardPage.middle_sum,
   standardPage.late_sum,
   rfl, rfl, rfl,
   standardPage_no_continuum_remnant⟩

/-- Spacetime is four copies of the continuum, which is still the
infinity of the reals. Extra axes do not undo the split. Packing
identifies bulk density with holographic \(G\); on the standard
realization it is \(1\) in lattice units. -/
theorem theory_of_everything_dimension :
    spacetimeDimension = 4 ∧
    Equinumerous Spacetime4 Continuum ∧
    HasRealInfinity Spacetime4 ∧
    ¬ Equinumerous standardDelone.Carrier Spacetime4 ∧
    standardFour.dimension = 4 ∧
    0 < standardDelone.packing ∧
    standardDelone.areaPerBit * standardDelone.packing =
      standardDelone.newtonG ∧
    standardDelone.packing = (1 : Rat) :=
  ⟨rfl,
   spacetime4_equinumerous_continuum,
   spacetime4_has_real_infinity,
   countable_ne_spacetime4 standardDelone.countableInfinity,
   rfl,
   standardDelone.packing_pos,
   standardDelone.areaPerBit_mul_packing,
   standardDelone_packing⟩

/-- QFT is a separable Fock space: finite-support occupations of a
countable mode set, equinumerous with `ℕ`. Unrestricted occupations
and a continuum of independent modes are not countable. -/
theorem theory_of_everything_fock :
    HasCountableInfinity FockNat ∧
    HasCountableInfinity standardQFT.fock ∧
    ¬ HasRealInfinity FockNat ∧
    FockNat.vacuum.val 0 = 0 ∧
    (FockNat.basis 0).val 0 = 1 ∧
    Function.Injective FockNat.basis ∧
    ¬ HasCountableInfinity (Nat → Nat) ∧
    ¬ HasCountableInfinity (Occupations Continuum) :=
  ⟨fockNat_has_countable_infinity,
   qft_fock_countable standardQFT,
   fockNat_not_real_infinity,
   rfl,
   FockNat.basis_at 0,
   FockNat.basis_injective,
   unrestricted_not_countable,
   occupations_continuum_not_countable⟩

/-- The Delone embedding samples the carrier's causal order into the
continuum. Screens that are spacelike on the carrier are spacelike in
spacetime. There are no closed timelike curves. -/
theorem theory_of_everything_causal_metric :
    (∀ a b,
      standardCausal.Rel a b ↔
        standardCausalMetric.Precedes
          (standardDelone.realize a) (standardDelone.realize b)) ∧
    Function.Injective standardDelone.realize ∧
    ¬ standardCausal.IsChain pairRealizedScreen.events ∧
    ¬ standardCausalMetric.IsChain pairRealizedScreen.events ∧
    (∀ p, ¬ standardCausalMetric.Precedes p p) ∧
    standardCausalMetric.Spacelike
      (standardDelone.realize (0 : Nat))
      (standardDelone.realize (1 : Nat)) :=
  ⟨standard_realize_iff,
   standardDelone.realize_injective,
   pairRealizedScreen_not_a_chain,
   pairRealizedScreen_not_spacetime_chain,
   standard_no_ctc,
   standard_neighbours_spacelike⟩

/-- Cosmic time is a growing causal set. The origin is a first finite
instant; later diamonds are nested, of size `n + 1`, and never carry
the continuum. The two-bit screen appears after the origin. -/
theorem theory_of_everything_growth :
    (standardGrowth.region 0).size = 1 ∧
    (standardGrowth.region 0).mem (0 : Nat) ∧
    ¬ (standardGrowth.region 0).mem (1 : Nat) ∧
    (∀ n : Time,
      (standardGrowth.region n).subset (standardGrowth.region (n + 1))) ∧
    (∀ n : Time, (standardGrowth.region n).size = n + 1) ∧
    (∀ n : Time,
      ¬ HasRealInfinity (Fin (standardGrowth.region n).size)) ∧
    ¬ Infinite (Fin (standardGrowth.region 0).size) ∧
    epoch 0 = .origin ∧
    (∀ n : Time, epoch (n + 1) = .afterTime) ∧
    (standardGrowth.region 1).mem (0 : Nat) ∧
    (standardGrowth.region 1).mem (1 : Nat) :=
  ⟨standardGrowth_origin,
   standardGrowth_origin_event,
   pair_screen_after_origin.1,
   standardGrowth_nested,
   standardGrowth_size,
   standardGrowth_not_real,
   standardGrowth_origin_not_infinite,
   epoch_zero,
   epoch_succ,
   pair_screen_after_origin.2.1,
   pair_screen_after_origin.2.2⟩

/-- Algebraic Fock space has a positive-definite inner product. The
one-particle states are orthonormal, and a continuum of orthonormal
modes is forbidden. -/
theorem theory_of_everything_inner :
    inner FockNat.vacuum FockNat.vacuum = 0 ∧
    (∀ f, inner f f = 0 ↔ f = FockNat.vacuum) ∧
    (∀ n, inner (FockNat.basis n) (FockNat.basis n) = 1) ∧
    (∀ n m, n ≠ m → inner (FockNat.basis n) (FockNat.basis m) = 0) ∧
    ¬ ∃ φ : Continuum → FockNat,
        (∀ p, inner (φ p) (φ p) = 1) ∧
        (∀ p q, p ≠ q → inner (φ p) (φ q) = 0) :=
  ⟨inner_vacuum,
   fun f => inner_self_eq_zero (f := f),
   inner_basis_self,
   fun _ _ h => inner_basis_off h,
   no_continuum_orthonormal⟩

/-- Quantum modes are carrier events of the growing diamond. Particle
number is a finite sum; at time `n` only modes `k ≤ n` are available.
The origin has no trans-Planckian modes. The sum is never over the
reals. -/
theorem theory_of_everything_modes :
    particleNumber FockNat.vacuum = 0 ∧
    (∀ n, particleNumber (FockNat.basis n) = 1) ∧
    (∀ n k, modeAvailable n k ↔ k ≤ n) ∧
    modeAvailable 0 0 ∧
    ¬ modeAvailable 0 1 ∧
    (∀ n f, truncatedNumber n f = sumTo f.val (n + 1)) ∧
    (∀ n, ¬ HasRealInfinity (Fin (n + 1))) :=
  ⟨particleNumber_vacuum,
   particleNumber_basis,
   modeAvailable_iff_le,
   modeAvailable_origin,
   not_modeAvailable_of_gt (Nat.zero_lt_one),
   truncatedNumber_eq,
   truncated_modes_not_real⟩

/-- A signed interval on the carrier: zero on the diagonal, negative
timelike, positive spacelike with minimum \(G\). Immediate neighbours
are spacelike at one Planck area. -/
theorem theory_of_everything_interval :
    intervalSq (0 : Nat) 0 = 0 ∧
    0 < intervalSq (0 : Nat) 1 ∧
    intervalSq (0 : Nat) 1 = standardDelone.newtonG ∧
    intervalSq (0 : Nat) 2 < 0 ∧
    standardCausalMetric.Spacelike
      (standardDelone.realize (0 : Nat))
      (standardDelone.realize (1 : Nat)) ∧
    (∀ a b, standardCausal.Rel a b → intervalSq a b < 0) ∧
    (∀ a b, a ≠ b →
      ¬ standardCausal.Rel a b → ¬ standardCausal.Rel b a →
        0 < intervalSq a b) :=
  ⟨intervalSq_zero_zero,
   intervalSq_zero_one_pos,
   intervalSq_zero_one_G,
   intervalSq_zero_two,
   standard_neighbours_spacelike,
   fun _ _ h => intervalSq_timelike h,
   fun _ _ hne hab hba => intervalSq_spacelike_pos hne hab hba⟩

end ToE
