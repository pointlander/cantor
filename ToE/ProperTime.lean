/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Interval

/-!
# Proper time of a finite timelike chain

The Lorentzian interval is a signed pair. Proper time is that interval
summed along a finite carrier chain, without square roots:

\[
\Delta\tau^2(a,b) = -\tau^2(a,b) \quad (a \prec b), \qquad
T(s) = \sum_i \Delta\tau^2(s_i,s_{i+1}).
\]

A hop has positive duration. Immediate neighbours are not a chain, so
they have no proper time. Between two events there is still no injective
copy of `ℕ`. The clock is a rational attached to a finite sequence of
carrier events, not a continuum of ticks.
-/

namespace ToE

/-- Duration of a timelike hop: \(-\tau^2(a,b)\). -/
def hopDuration (a b : Nat) : Rat := - intervalSq a b

theorem rat_pos_of_neg {q : Rat} (h : q < 0) : 0 < -q := by
  have hlt := (Rat.add_lt_add_right (c := -q)).mpr h
  have hz : q + -q = 0 := Rat.add_neg_cancel q
  have h0 : (0 : Rat) + -q = -q := Rat.zero_add _
  -- hlt : q + -q < 0 + -q, i.e. 0 < -q after rewrite
  rw [hz, Rat.zero_add] at hlt
  exact hlt

theorem hopDuration_timelike {a b : Nat} (h : standardRel a b) :
    0 < hopDuration a b :=
  rat_pos_of_neg (intervalSq_timelike h)

theorem hopDuration_eq_natDist {a b : Nat} (h : standardRel a b) :
    hopDuration a b = (natDist a b : Rat) := by
  have hd : 2 ≤ natDist a b := standardRel_natDist h
  have h0 : natDist a b ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hd)
  have h1 : natDist a b ≠ 1 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hd)
  unfold hopDuration intervalSq
  simp [h0, h1]

theorem hopDuration_shortest {a b : Nat} (h : standardRel a b) :
    (2 : Rat) ≤ hopDuration a b := by
  have hd : 2 ≤ natDist a b := standardRel_natDist h
  rw [hopDuration_eq_natDist h]
  exact (Rat.natCast_le_natCast (a := 2) (b := natDist a b)).mpr hd

/-- Sum of hop durations over the first `k` consecutive pairs of `s`. -/
def sumHops {n : Nat} (s : Fin n → Nat) : Nat → Rat
  | 0 => 0
  | k + 1 =>
    if hk : k + 1 < n then
      sumHops s k +
        hopDuration (s ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk⟩) (s ⟨k + 1, hk⟩)
    else
      0

/-- Proper time of a finite tuple: sum of consecutive hop durations. -/
def chainDuration {n : Nat} (s : Fin n → Nat) : Rat :=
  match n with
  | 0 => 0
  | n + 1 => sumHops s n

theorem sumHops_zero {n : Nat} (s : Fin n → Nat) : sumHops s 0 = 0 := rfl

theorem chainDuration_pair (s : Fin 2 → Nat) :
    chainDuration s = hopDuration (s ⟨0, by decide⟩) (s ⟨1, by decide⟩) := by
  simp [chainDuration, sumHops]
  exact Rat.zero_add _

/-- Two-event timelike chain `{0,2}`. -/
def hop02 : Fin 2 → Nat := fun i => i.val * 2

theorem hop02_isChain : standardCausal.IsChain hop02 := by
  intro i j hij
  change standardRel (i.val * 2) (j.val * 2)
  simp [standardRel]
  omega

theorem hop02_duration : chainDuration hop02 = (2 : Rat) := by
  rw [chainDuration_pair]
  simp [hop02]
  have hrel : standardRel 0 2 := by simp [standardRel]
  have hdist : natDist 0 2 = 2 := by simp [natDist]
  rw [hopDuration_eq_natDist hrel, hdist]
  rfl

theorem hop02_duration_pos : 0 < chainDuration hop02 := by
  rw [hop02_duration]
  exact rat_two_pos

/-- Two-event timelike chain `{2,4}`. -/
def hop24 : Fin 2 → Nat := fun i => 2 + i.val * 2

theorem hop24_isChain : standardCausal.IsChain hop24 := by
  intro i j hij
  change standardRel (2 + i.val * 2) (2 + j.val * 2)
  simp [standardRel]
  omega

theorem hop24_duration : chainDuration hop24 = (2 : Rat) := by
  rw [chainDuration_pair]
  simp [hop24]
  have hrel : standardRel 2 4 := by simp [standardRel]
  have hdist : natDist 2 4 = 2 := by simp [natDist]
  rw [hopDuration_eq_natDist hrel, hdist]
  rfl

/-- Three-event timelike chain `{0,2,4}`. -/
def hop024 : Fin 3 → Nat := fun i => i.val * 2

theorem hop024_isChain : standardCausal.IsChain hop024 := by
  intro i j hij
  change standardRel (i.val * 2) (j.val * 2)
  simp [standardRel]
  omega

theorem hop024_duration : chainDuration hop024 = (4 : Rat) := by
  simp [chainDuration, sumHops, hop024]
  have h02 : standardRel 0 2 := by simp [standardRel]
  have h24 : standardRel 2 4 := by simp [standardRel]
  have d02 : natDist 0 2 = 2 := by simp [natDist]
  have d24 : natDist 2 4 = 2 := by simp [natDist]
  rw [hopDuration_eq_natDist h02, hopDuration_eq_natDist h24, d02, d24]
  rw [Rat.zero_add, ← Rat.natCast_add]
  rfl

theorem hop024_splits :
    chainDuration hop024 = chainDuration hop02 + chainDuration hop24 := by
  rw [hop024_duration, hop02_duration, hop24_duration]
  have h2 : (2 : Rat) = ((2 : Nat) : Rat) := rfl
  have h4 : (4 : Rat) = ((4 : Nat) : Rat) := rfl
  rw [h4, h2, ← Rat.natCast_add]

theorem pairScreen_not_chain :
    ¬ standardCausal.IsChain pairRealizedScreen.events :=
  pairRealizedScreen_not_a_chain

theorem proper_time_no_continuum_ticks (x y : Nat) :
    ¬ Infinite { z // standardCausal.Rel x z ∧ standardCausal.Rel z y } :=
  standardCausal.interval_finite x y

end ToE
