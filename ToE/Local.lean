/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Number

/-!
# Reconstruction from a finite diamond

A supported state at cosmic time `n` is the finite list of occupations
on `{0,…,n}`:

\[
R_n(f)_k = N_k(f) = \langle e_k, f\rangle = f(k), \qquad k\le n.
\]

That tuple determines the state, and every finite tuple is a unique
supported state. Screen and horizon readouts are coordinates of this
list. The list is finite, not the infinity of the reals.
-/

namespace ToE

/-- Occupations of the grown diamond `{0,…,n}`. -/
def diamondReadout (n : Time) (f : FockNat) : Fin (n + 1) → Nat :=
  fun i => occupation i.val f

theorem diamondReadout_eq_occupation (n : Time) (f : FockNat)
    (i : Fin (n + 1)) :
    diamondReadout n f i = occupation i.val f :=
  rfl

theorem diamondReadout_eq_inner (n : Time) (f : FockNat)
    (i : Fin (n + 1)) :
    diamondReadout n f i = inner (FockNat.basis i.val) f :=
  occupation_eq_inner i.val f

theorem diamondReadout_vacuum (n : Time) :
    diamondReadout n FockNat.vacuum = fun _ => 0 := by
  funext i
  exact occupation_vacuum i.val

theorem diamondReadout_basis (n k : Nat) :
    diamondReadout n (FockNat.basis k) =
      fun i => if i.val = k then 1 else 0 := by
  funext i
  simp [diamondReadout, occupation, FockNat.basis]

theorem diamondReadout_basis_self {n k : Nat} (h : k ≤ n) :
    diamondReadout n (FockNat.basis k) ⟨k, Nat.lt_succ_of_le h⟩ = 1 := by
  simp [diamondReadout, occupation, FockNat.basis]

theorem diamondReadout_basis_off {n k : Nat} {i : Fin (n + 1)}
    (hne : i.val ≠ k) :
    diamondReadout n (FockNat.basis k) i = 0 := by
  simp [diamondReadout, occupation, FockNat.basis, hne]

theorem originReadout_vacuum :
    diamondReadout 0 FockNat.vacuum ⟨0, by decide⟩ = 0 :=
  rfl

theorem originReadout_basis0 :
    diamondReadout 0 (FockNat.basis 0) ⟨0, by decide⟩ = 1 := by
  simp [diamondReadout, occupation, FockNat.basis]

theorem diamondReadout_basis0_right :
    diamondReadout 1 (FockNat.basis 0) ⟨1, by decide⟩ = 0 := by
  simp [diamondReadout, occupation, FockNat.basis]

/-- Rebuild a supported state from its occupation tuple. -/
def ofReadout (n : Time) (r : Fin (n + 1) → Nat) : FockNat :=
  ⟨fun k => if h : k < n + 1 then r ⟨k, h⟩ else 0,
   ⟨n + 1, fun _ hk => dif_neg (Nat.not_lt.mpr hk)⟩⟩

theorem ofReadout_supported (n : Time) (r : Fin (n + 1) → Nat) :
    supported n (ofReadout n r) :=
  fun _ hk => dif_neg (Nat.not_lt.mpr hk)

theorem ofReadout_vacuum (n : Time) :
    ofReadout n (fun _ => 0) = FockNat.vacuum := by
  apply Subtype.ext
  funext k
  simp [ofReadout, FockNat.vacuum]

/-- Every finite tuple is the readout of a unique supported state. -/
theorem diamondReadout_ofReadout (n : Time) (r : Fin (n + 1) → Nat) :
    diamondReadout n (ofReadout n r) = r := by
  funext i
  simp only [diamondReadout, occupation, ofReadout]
  rw [dif_pos i.isLt]

/-- A supported state is recovered from its occupation tuple. -/
theorem ofReadout_diamondReadout {n : Time} {f : FockNat}
    (hf : supported n f) :
    ofReadout n (diamondReadout n f) = f := by
  apply Subtype.ext
  funext k
  simp only [ofReadout, diamondReadout, occupation]
  by_cases hk : k < n + 1
  · simp [hk]
  · simp [hk, hf k (Nat.not_lt.mp hk)]

/-- Two supported states with the same occupations on the grown
diamond are equal. -/
theorem diamondReadout_injective {n : Time} {f g : FockNat}
    (hf : supported n f) (hg : supported n g)
    (h : diamondReadout n f = diamondReadout n g) : f = g := by
  have := congrArg (ofReadout n) h
  rw [ofReadout_diamondReadout hf, ofReadout_diamondReadout hg] at this
  exact this

/-- Particle number on the grown diamond is the sum of the readout. -/
theorem truncatedNumber_as_readout (n : Time) (f : FockNat) :
    truncatedNumber n f = sumTo (fun k => occupation k f) (n + 1) :=
  rfl

/-- The occupation tuple is finite, hence not the continuum. -/
theorem diamondReadout_not_real (n : Time) :
    ¬ HasRealInfinity (Fin (n + 1)) :=
  truncated_modes_not_real n

end ToE
