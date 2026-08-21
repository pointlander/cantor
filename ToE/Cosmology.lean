/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Physics

/-!
# Cosmological time

Time is indexed by the countable numbers.  At cosmic time zero the
contents of the universe are a single unified theory.  At every later
instant the contents are a split pair: QFT with countable infinity,
GR with the infinity of the reals.
-/

namespace ToE

/-- Cosmic time, with the origin at zero. -/
abbrev Time : Type := Nat

/-- The two epochs of the theory of everything. -/
inductive Epoch where
  | origin
  | afterTime
  deriving DecidableEq, Repr

/-- The origin is time zero; every positive time is after the split. -/
def epoch : Time → Epoch
  | 0 => .origin
  | _ + 1 => .afterTime

@[simp] theorem epoch_zero : epoch 0 = .origin := rfl

@[simp] theorem epoch_succ (n : Time) : epoch (n + 1) = .afterTime := rfl

theorem epoch_origin_iff {t : Time} : epoch t = .origin ↔ t = 0 := by
  cases t with
  | zero => simp
  | succ n => simp

theorem epoch_afterTime_iff {t : Time} : epoch t = .afterTime ↔ t ≠ 0 := by
  cases t with
  | zero => simp
  | succ n => simp

/-- What the cosmos contains depends on the epoch: a single theory at
the origin, a split pair after time. -/
def Contents : Epoch → Type 1
  | .origin => UnifiedTheory
  | .afterTime => QuantumFieldTheory × GeneralRelativity

/-- The history of the universe. -/
def history : (e : Epoch) → Contents e
  | .origin => unifiedAtOrigin
  | .afterTime => separate unifiedAtOrigin

/-- At the origin there is one theory, and it has the infinity of the
countable numbers. -/
theorem at_origin_unified_countable :
    HasCountableInfinity (history .origin).Carrier :=
  (history .origin).countableInfinity

/-- After time, QFT has the infinity of the countable numbers. -/
theorem after_time_qft_countable :
    HasCountableInfinity (history .afterTime).1.Modes :=
  (history .afterTime).1.countableInfinity

/-- After time, GR has the infinity of the reals. -/
theorem after_time_gr_real :
    HasRealInfinity (history .afterTime).2.Spacetime :=
  (history .afterTime).2.realInfinity

/-- After time, the two theories are not equinumerous. -/
theorem after_time_separated :
    ¬ Equinumerous
        (history .afterTime).1.Modes
        (history .afterTime).2.Spacetime :=
  qft_ne_gr unifiedAtOrigin

/-- Contents of the cosmos at an arbitrary cosmic time. -/
def atTime (t : Time) : Contents (epoch t) :=
  history (epoch t)

theorem at_time_zero_is_unified :
    atTime 0 = unifiedAtOrigin := rfl

theorem at_time_succ_is_split (n : Time) :
    atTime (n + 1) = separate unifiedAtOrigin := rfl

end ToE
