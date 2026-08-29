/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Modes

/-!
# Hamiltonian on the grown diamond

The first dynamical pairing: at cosmic time `n`,

\[
\langle f, H_n f\rangle = \sum_{k=0}^{n} \omega(k)\,f(k), \qquad
\omega(k) = k+1.
\]

The sum is over available modes only. Trans-Planckian occupations do
not contribute. Energy is a natural number, not a continuum of
frequencies. This is a lattice Hamiltonian, not \(e^{-iHt}\).
-/

namespace ToE

/-- Lattice frequency of mode `k`. Mode `0` has \(\omega = 1\), so the
origin is not a zero-energy ghost. -/
def freq (k : Nat) : Nat := k + 1

theorem freq_pos (k : Nat) : 0 < freq k :=
  Nat.succ_pos k

/-- Cutoff Hamiltonian quadratic form at time `n`:
\(\sum_{k\le n} \omega(k)\,f(k)\). -/
def energy (n : Time) (f : FockNat) : Nat :=
  sumTo (fun k => freq k * f.val k) (n + 1)

theorem energy_vacuum (n : Time) : energy n FockNat.vacuum = 0 := by
  simp [energy, FockNat.vacuum, freq, sumTo_zero]

theorem sumTo_single {k N c : Nat} (h : k < N) :
    sumTo (fun i => if i = k then c else 0) N = c := by
  induction N with
  | zero =>
    omega
  | succ N ih =>
    simp [sumTo]
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with
    | inl hlt =>
      have hne : ¬ N = k := (Nat.ne_of_lt hlt).symm
      simp [hne, ih hlt]
    | inr he =>
      subst he
      have h0 : sumTo (fun i => if i = k then c else 0) k = 0 :=
        sumTo_eq_zero.mpr fun i hi => by simp [Nat.ne_of_lt hi]
      simp [h0]

theorem energy_basis (n k : Nat) :
    energy n (FockNat.basis k) = if k ≤ n then freq k else 0 := by
  simp [energy, freq, FockNat.basis]
  have hfun :
      (fun i => (i + 1) * (if i = k then 1 else 0)) =
        fun i => if i = k then k + 1 else 0 := by
    funext i
    by_cases hik : i = k
    · simp [hik]
    · simp [hik]
  rw [hfun]
  by_cases hkn : k ≤ n
  · have : k < n + 1 := Nat.lt_succ_of_le hkn
    simp [hkn, sumTo_single this]
  · have hgt : n < k := Nat.not_le.mp hkn
    have h0 :
        sumTo (fun i => if i = k then k + 1 else 0) (n + 1) = 0 :=
      sumTo_eq_zero.mpr fun i hi => by
        have : i ≠ k := Nat.ne_of_lt (Nat.lt_of_lt_of_le hi hgt)
        simp [this]
    simp [hkn, h0]

theorem energy_origin_ground : energy 0 (FockNat.basis 0) = 1 := by
  simp [energy_basis, freq]

theorem energy_origin_transPlanckian : energy 0 (FockNat.basis 1) = 0 := by
  simp [energy_basis]

/-- If `f` lives on the grown diamond and has zero energy, it is the
vacuum: every available frequency is positive. -/
theorem energy_eq_zero_of_supported {n : Time} {f : FockNat}
    (hsup : isBound f.val (n + 1)) :
    energy n f = 0 ↔ f = FockNat.vacuum := by
  constructor
  · intro hE
    have hall : ∀ k, k < n + 1 → f.val k = 0 := by
      intro k hk
      have hterm : freq k * f.val k = 0 :=
        (sumTo_eq_zero.mp hE) k hk
      cases Nat.mul_eq_zero.mp hterm with
      | inl hω =>
        exact absurd hω (Nat.ne_of_gt (freq_pos k))
      | inr hf =>
        exact hf
    apply Subtype.ext
    funext k
    cases Nat.lt_or_ge k (n + 1) with
    | inl hlt =>
      simp [FockNat.vacuum, hall k hlt]
    | inr hge =>
      simp [FockNat.vacuum, hsup k hge]
  · intro hf
    subst hf
    exact energy_vacuum n

/-- One-particle energies at time `n` are \(\omega(0),\ldots,\omega(n)\):
a finite set, not the continuum. -/
theorem energy_levels_not_real (n : Time) :
    ¬ HasRealInfinity (Fin (n + 1)) :=
  truncated_modes_not_real n

end ToE
