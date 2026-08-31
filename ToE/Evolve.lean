/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Hamiltonian

/-!
# Isometric inclusion along growth

A tick is not a unitary on a fixed Hilbert space: the physical
subspace grows by one mode. A state supported on `{0,…,n}` is already
a state on `{0,…,n+1}` with the newborn mode empty. Inner product and
\(H_n\) energy are preserved. Existing quanta are not disturbed.

This is not \(e^{-iHt}\). Occupations are unchanged; the theorems are
the support hypotheses.
-/

namespace ToE

/-- No trans-Planckian occupation at time `n`: support lies in
`{0,…,n}`. -/
def supported (n : Time) (f : FockNat) : Prop :=
  isBound f.val (n + 1)

theorem isBound_mono {f : Nat → Nat} {N M : Nat}
    (h : isBound f N) (hNM : N ≤ M) : isBound f M :=
  fun k hk => h k (Nat.le_trans hNM hk)

theorem supported_vacuum (n : Time) : supported n FockNat.vacuum :=
  isBound_mono vacuum_isBound (Nat.zero_le _)

theorem supported_basis {n k : Nat} (h : k ≤ n) :
    supported n (FockNat.basis k) :=
  isBound_mono (basis_isBound k) (Nat.succ_le_succ h)

theorem supported_succ {n : Time} {f : FockNat}
    (h : supported n f) : supported (n + 1) f :=
  isBound_mono h (Nat.le_succ _)

theorem supported_newborn {n : Time} {f : FockNat}
    (h : supported n f) : f.val (n + 1) = 0 :=
  h (n + 1) (Nat.le_refl _)

/-- Inclusion of time-`n` states into time `n+1`: occupations are
unchanged, and the new mode is empty if `f` was supported. -/
def includeTick (_n : Time) (f : FockNat) : FockNat := f

theorem includeTick_eq (n : Time) (f : FockNat) :
    includeTick n f = f :=
  rfl

theorem includeTick_vacuum (n : Time) :
    includeTick n FockNat.vacuum = FockNat.vacuum :=
  rfl

theorem includeTick_newborn {n : Time} {f : FockNat}
    (h : supported n f) :
    (includeTick n f).val (n + 1) = 0 :=
  supported_newborn h

/-- Inclusion is an isometry on the physical subspace at time `n`. -/
theorem includeTick_inner {n : Time} {f g : FockNat}
    (_hf : supported n f) (_hg : supported n g) :
    inner (includeTick n f) (includeTick n g) = inner f g :=
  rfl

theorem energy_succ (n : Time) (f : FockNat) :
    energy (n + 1) f = energy n f + freq (n + 1) * f.val (n + 1) := by
  simp [energy, sumTo]

/-- Growing the diamond does not change the energy of an already
supported state: the newborn mode is empty. -/
theorem includeTick_energy {n : Time} {f : FockNat}
    (h : supported n f) :
    energy (n + 1) (includeTick n f) = energy n f := by
  rw [includeTick_eq, energy_succ, supported_newborn h, Nat.mul_zero,
    Nat.add_zero]

theorem includeTick_energy_basis {n k : Nat} (h : k ≤ n) :
    energy (n + 1) (FockNat.basis k) = energy n (FockNat.basis k) :=
  includeTick_energy (supported_basis h)

end ToE
