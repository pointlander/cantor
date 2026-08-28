/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Causal

/-!
# Lorentzian interval on the carrier

The Fock pairing is a positive-definite sum on occupations. The GR
counterpart is a **signed interval** on carrier events, not a Minkowski
product on the Cantor space.

\[
\tau^2(a,a) = 0, \qquad
\tau^2 < 0 \text{ timelike}, \qquad
\tau^2 > 0 \text{ spacelike}.
\]

On a spacelike pair the interval is at least \(G = (\mathrm{gap})^2\).
Immediate neighbours sit at that minimum. The Lorentzian sign does not
add a second infinity: it is a `Rat` on the countable carrier.
-/

namespace ToE

/-- Causal separation on the standard carrier: `a + 2 ≤ b` iff
`natDist a b ≥ 2`. -/
theorem standardRel_natDist {a b : Nat} (h : standardRel a b) :
    2 ≤ natDist a b := by
  simp [standardRel, natDist] at h ⊢
  omega

theorem spacelike_natDist {a b : Nat}
    (hne : a ≠ b) (hab : ¬ standardRel a b) (hba : ¬ standardRel b a) :
    natDist a b = 1 := by
  have hd0 : natDist a b ≠ 0 := mt natDist_eq_zero.mp hne
  simp [standardRel] at hab hba
  have : natDist a b < 2 := by
    simp [natDist]
    omega
  omega

/-- Signed interval squared on the standard carrier.
Zero on the diagonal, `+1` on immediate neighbours (spacelike, one
Planck area), negative when `natDist ≥ 2` (timelike). -/
def intervalSq (a b : Nat) : Rat :=
  if natDist a b = 0 then 0
  else if natDist a b = 1 then 1
  else - (natDist a b : Rat)

theorem rat_neg_of_pos {q : Rat} (h : 0 < q) : -q < 0 := by
  have hlt := (Rat.add_lt_add_right (c := -q)).mpr h
  have hz : (0 : Rat) + -q = -q := Rat.zero_add _
  have hq : q + -q = 0 := Rat.add_neg_cancel q
  rw [hz, hq] at hlt
  exact hlt

theorem intervalSq_self (a : Nat) : intervalSq a a = 0 := by
  simp [intervalSq, natDist_self]

theorem intervalSq_comm (a b : Nat) : intervalSq a b = intervalSq b a := by
  simp [intervalSq, natDist_comm]

theorem intervalSq_zero (a b : Nat) : intervalSq a b = 0 ↔ a = b := by
  constructor
  · intro h
    by_cases h0 : natDist a b = 0
    · exact natDist_eq_zero.mp h0
    · by_cases h1 : natDist a b = 1
      · unfold intervalSq at h
        rw [if_neg h0, if_pos h1] at h
        exact absurd h (Rat.ne_of_gt rat_one_pos)
      · unfold intervalSq at h
        rw [if_neg h0, if_neg h1] at h
        have hpos : 0 < ((natDist a b : Nat) : Rat) :=
          Rat.natCast_pos.mpr (Nat.pos_of_ne_zero h0)
        have hlt := rat_neg_of_pos hpos
        rw [h] at hlt
        exact (Rat.lt_irrefl hlt).elim
  · intro h
    subst h
    exact intervalSq_self a

theorem intervalSq_timelike {a b : Nat} (h : standardRel a b) :
    intervalSq a b < 0 := by
  have hd : 2 ≤ natDist a b := standardRel_natDist h
  have h0 : natDist a b ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hd)
  have h1 : natDist a b ≠ 1 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hd)
  unfold intervalSq
  simp [h0, h1]
  have hpos : 0 < ((natDist a b : Nat) : Rat) :=
    Rat.natCast_pos.mpr (Nat.lt_of_lt_of_le (by decide) hd)
  exact rat_neg_of_pos hpos

theorem intervalSq_spacelike {a b : Nat}
    (hne : a ≠ b) (hab : ¬ standardRel a b) (hba : ¬ standardRel b a) :
    intervalSq a b = (1 : Rat) := by
  have hd : natDist a b = 1 := spacelike_natDist hne hab hba
  unfold intervalSq
  simp [hd]

theorem intervalSq_spacelike_pos {a b : Nat}
    (hne : a ≠ b) (hab : ¬ standardRel a b) (hba : ¬ standardRel b a) :
    0 < intervalSq a b := by
  rw [intervalSq_spacelike hne hab hba]
  exact rat_one_pos

noncomputable section

theorem standardDelone_newtonG_one : standardDelone.newtonG = (1 : Rat) := by
  change standardDelone.gap * standardDelone.gap = 1
  change (1 : Rat) * 1 = 1
  rw [Rat.one_mul]

theorem intervalSq_gap_le {a b : Nat}
    (hne : a ≠ b) (hab : ¬ standardRel a b) (hba : ¬ standardRel b a) :
    standardDelone.newtonG ≤ intervalSq a b := by
  rw [intervalSq_spacelike hne hab hba, standardDelone_newtonG_one]
  exact Rat.le_refl

/-- A signed interval on a causal Delone carrier: Lorentzian signs,
zero on the diagonal, and \(G\) as the spacelike minimum. -/
structure LorentzInterval {D : DeloneSplit} (C : CausalSplit D) where
  sq : D.Carrier → D.Carrier → Rat
  sq_self : ∀ a, sq a a = 0
  sq_comm : ∀ a b, sq a b = sq b a
  timelike_neg : ∀ a b, C.Rel a b → sq a b < 0
  spacelike_pos :
    ∀ a b, a ≠ b → ¬ C.Rel a b → ¬ C.Rel b a → 0 < sq a b
  gap_le_spacelike :
    ∀ a b, a ≠ b → ¬ C.Rel a b → ¬ C.Rel b a → D.newtonG ≤ sq a b

noncomputable def standardInterval : LorentzInterval standardCausal where
  sq := intervalSq
  sq_self := intervalSq_self
  sq_comm := intervalSq_comm
  timelike_neg := fun _ _ h => intervalSq_timelike h
  spacelike_pos := fun _ _ hne hab hba => intervalSq_spacelike_pos hne hab hba
  gap_le_spacelike := fun _ _ hne hab hba => intervalSq_gap_le hne hab hba

theorem intervalSq_zero_zero : intervalSq (0 : Nat) 0 = 0 :=
  intervalSq_self 0

theorem intervalSq_zero_one : intervalSq (0 : Nat) 1 = 1 := by
  have hd : natDist 0 1 = 1 := by simp [natDist]
  unfold intervalSq
  simp [hd]

theorem intervalSq_zero_one_pos : 0 < intervalSq (0 : Nat) 1 := by
  rw [intervalSq_zero_one]
  exact rat_one_pos

theorem intervalSq_zero_one_G :
    intervalSq (0 : Nat) 1 = standardDelone.newtonG := by
  rw [intervalSq_zero_one, standardDelone_newtonG_one]

theorem intervalSq_zero_two : intervalSq (0 : Nat) 2 < 0 :=
  intervalSq_timelike (show standardRel 0 2 from by simp [standardRel])

theorem intervalSq_neighbours_spacelike :
    standardCausalMetric.Spacelike
      (standardDelone.realize (0 : Nat))
      (standardDelone.realize (1 : Nat)) :=
  standard_neighbours_spacelike

theorem pairScreen_interval_spacelike
    (i j : Fin pairRealizedScreen.screen.bits) (hne : i ≠ j) :
    0 < intervalSq (pairRealizedScreen.events i)
      (pairRealizedScreen.events j) := by
  have hs :=
    standardCausalMetric.screen_spacelike pairRealizedScreen i j hne
  have hne' : pairRealizedScreen.events i ≠ pairRealizedScreen.events j :=
    fun h => hne (pairRealizedScreen.events_injective h)
  have hab : ¬ standardCausal.Rel
      (pairRealizedScreen.events i) (pairRealizedScreen.events j) := by
    intro h
    exact hs.1 ((standardCausalMetric.realize_iff _ _).mp h)
  have hba : ¬ standardCausal.Rel
      (pairRealizedScreen.events j) (pairRealizedScreen.events i) := by
    intro h
    exact hs.2 ((standardCausalMetric.realize_iff _ _).mp h)
  exact intervalSq_spacelike_pos hne' hab hba

end

end ToE
