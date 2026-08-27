/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Inner
import ToE.Growth

/-!
# Discrete mode sum on the growing region

Quantum modes are carrier events. At cosmic time `n` the available
modes are `{0,…,n}`, the events of the grown diamond. Occupations sum
over that finite set, not over the reals. A mode that has not yet
appeared is trans-Planckian: it is not a quantum label at that time.

The split does not change. After time, spacetime is already the
continuum; the mode sum stays a finite sum of countable occupations.
-/

namespace ToE

/-- Total particle number \(N(f) = \sum_k f(k)\). Finite because
support is finite. -/
noncomputable def particleNumber (f : FockNat) : Nat :=
  sumTo f.val (supportBound f)

theorem particleNumber_eq_sumTo (f : FockNat) {N : Nat}
    (hN : isBound f.val N) :
    particleNumber f = sumTo f.val N :=
  sumTo_eq_of_bounds (supportBound_spec f) hN

theorem vacuum_isBound : isBound FockNat.vacuum.val 0 :=
  fun _ _ => rfl

theorem basis_isBound (n : Nat) :
    isBound (FockNat.basis n).val (n + 1) := by
  intro k hk
  simp [FockNat.basis]
  omega

theorem particleNumber_vacuum : particleNumber FockNat.vacuum = 0 := by
  rw [particleNumber_eq_sumTo FockNat.vacuum vacuum_isBound]
  rfl

theorem particleNumber_basis (n : Nat) :
    particleNumber (FockNat.basis n) = 1 := by
  rw [particleNumber_eq_sumTo (FockNat.basis n) (basis_isBound n)]
  have hfun : (FockNat.basis n).val = fun k => if k = n then 1 else 0 := by
    funext k
    simp [FockNat.basis]
  rw [hfun]
  exact sumTo_indicator (Nat.lt_succ_self n)

/-- Mode `k` is available at cosmic time `n` when it is an event of
the grown diamond `{0,…,n}`. -/
def modeAvailable (n k : Nat) : Prop := k ≤ n

theorem modeAvailable_iff_mem (n k : Nat) :
    modeAvailable n k ↔ (standardGrowth.region n).mem k := by
  constructor
  · intro h
    exact prefixDiamond_mem.mpr (Nat.lt_succ_of_le h)
  · intro h
    have hk : k < n + 1 := (prefixDiamond_mem (n := n) (x := k)).mp h
    exact Nat.lt_succ_iff.mp hk

theorem modeAvailable_origin : modeAvailable 0 0 :=
  Nat.le_refl 0

theorem modeAvailable_origin_only (k : Nat) :
    modeAvailable 0 k ↔ k = 0 := by
  constructor
  · intro h
    exact Nat.le_zero.mp h
  · intro h
    subst h
    exact modeAvailable_origin

/-- Trans-Planckian: a mode that has not yet appeared is not a
quantum label at that time. -/
theorem not_modeAvailable_of_gt {n k : Nat} (h : n < k) :
    ¬ modeAvailable n k :=
  Nat.not_le.mpr h

theorem modeAvailable_iff_le (n k : Nat) :
    modeAvailable n k ↔ k ≤ n :=
  Iff.rfl

/-- Occupations summed only over modes that exist at time `n`. -/
def truncatedNumber (n : Time) (f : FockNat) : Nat :=
  sumTo f.val (n + 1)

theorem truncatedNumber_eq (n : Time) (f : FockNat) :
    truncatedNumber n f = sumTo f.val (n + 1) :=
  rfl

theorem truncatedNumber_vacuum (n : Time) :
    truncatedNumber n FockNat.vacuum = 0 :=
  sumTo_zero (n + 1)

/-- One-particle state in mode `k`, summed at time `n`: `1` if the
mode has appeared, `0` if it is still trans-Planckian. -/
theorem truncatedNumber_basis (n k : Nat) :
    truncatedNumber n (FockNat.basis k) = if k ≤ n then 1 else 0 := by
  simp [truncatedNumber, FockNat.basis]
  by_cases hkn : k ≤ n
  · have : k < n + 1 := Nat.lt_succ_of_le hkn
    simp [hkn, sumTo_indicator this]
  · have hgt : n < k := Nat.not_le.mp hkn
    have h0 :
        sumTo (fun i => if i = k then 1 else 0) (n + 1) = 0 :=
      sumTo_eq_zero.mpr fun i hi => by
        have : i ≠ k := Nat.ne_of_lt (Nat.lt_of_lt_of_le hi hgt)
        simp [this]
    simp [hkn, h0]

/-- A state whose support already lies in the grown diamond has
truncated number equal to total particle number. -/
theorem truncatedNumber_eq_particleNumber {n : Time} {f : FockNat}
    (h : isBound f.val (n + 1)) :
    truncatedNumber n f = particleNumber f :=
  (particleNumber_eq_sumTo f h).symm

/-- The primordial mode sum is over a finite set of countable modes,
never over the continuum. -/
theorem truncated_modes_not_real (n : Time) :
    ¬ HasRealInfinity (Fin (n + 1)) :=
  (prefixDiamond n).not_real_infinity

theorem truncated_modes_eq_region (n : Time) :
    ¬ HasRealInfinity (Fin (standardGrowth.region n).size) := by
  have hsz : (standardGrowth.region n).size = n + 1 :=
    standardGrowth.size_eq n
  simpa [hsz] using truncated_modes_not_real n

end ToE
