/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Evolve

/-!
# Number operators

Occupation of mode `k` is the inner-product readout

\[
N_k(f) = \langle e_k, f\rangle = f(k).
\]

At cosmic time `n` this is a physical observable only for
`k ≤ n`. Trans-Planckian occupations of a supported state vanish.
Particle number and energy are sums of these readouts. A continuum of
independent number operators would inject the reals into the countable
Fock space.
-/

namespace ToE

/-- Occupation of mode `k`: the number-operator readout. -/
def occupation (k : Nat) (f : FockNat) : Nat := f.val k

theorem inner_basis_apply (k : Nat) (f : FockNat) :
    inner (FockNat.basis k) f = f.val k := by
  have hB : isBound (fun i => (FockNat.basis k).val i * f.val i)
      (Nat.max (k + 1) (supportBound f)) := by
    intro i hi
    have hfB := supportBound_spec f
    cases Nat.le_total (k + 1) (supportBound f) with
    | inl hle =>
      have : supportBound f ≤ i := by
        simpa [Nat.max_eq_right hle] using hi
      simp [hfB i this]
    | inr hge =>
      have : k + 1 ≤ i := by
        simpa [Nat.max_eq_left hge] using hi
      have hik : i ≠ k := Nat.ne_of_gt (Nat.lt_of_succ_le this)
      simp [FockNat.basis, hik]
  rw [inner_eq_sumTo _ _ hB]
  have hfun :
      (fun i => (FockNat.basis k).val i * f.val i) =
        fun i => if i = k then f.val k else 0 := by
    funext i
    simp [FockNat.basis]
    by_cases hik : i = k
    · simp [hik]
    · simp [hik]
  rw [hfun]
  have : k < Nat.max (k + 1) (supportBound f) :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_max_left _ _)
  exact sumTo_single this

theorem occupation_eq_inner (k : Nat) (f : FockNat) :
    occupation k f = inner (FockNat.basis k) f :=
  (inner_basis_apply k f).symm

theorem occupation_vacuum (k : Nat) :
    occupation k FockNat.vacuum = 0 :=
  rfl

theorem inner_basis_vacuum (k : Nat) :
    inner (FockNat.basis k) FockNat.vacuum = 0 := by
  rw [inner_basis_apply]
  rfl

theorem occupation_basis (k n : Nat) :
    occupation k (FockNat.basis n) = if k = n then 1 else 0 := by
  simp [occupation, FockNat.basis]

theorem inner_basis_basis (k n : Nat) :
    inner (FockNat.basis k) (FockNat.basis n) =
      if k = n then 1 else 0 := by
  rw [inner_basis_apply]
  simp [FockNat.basis]

/-- A supported state has no trans-Planckian occupation. -/
theorem occupation_transPlanckian {n k : Nat} {f : FockNat}
    (h : supported n f) (hk : n < k) :
    occupation k f = 0 :=
  h k (Nat.succ_le_of_lt hk)

theorem inner_transPlanckian {n k : Nat} {f : FockNat}
    (h : supported n f) (hk : n < k) :
    inner (FockNat.basis k) f = 0 := by
  rw [inner_basis_apply]
  exact occupation_transPlanckian h hk

/-- Particle number on the grown diamond is the sum of number-operator
readouts. -/
theorem truncatedNumber_as_occupations {n : Time} {f : FockNat}
    (_h : supported n f) :
    truncatedNumber n f =
      sumTo (fun k => inner (FockNat.basis k) f) (n + 1) := by
  simp [truncatedNumber]
  congr 1
  funext k
  exact (inner_basis_apply k f).symm

theorem energy_as_occupations (n : Time) (f : FockNat) :
    energy n f =
      sumTo (fun k => freq k * inner (FockNat.basis k) f) (n + 1) := by
  simp [energy]
  congr 1
  funext k
  rw [inner_basis_apply]

/-- Independent unit readouts labelled by the continuum would inject
the reals into the countable Fock space. -/
theorem no_continuum_number_ops :
    ¬ ∃ φ : Continuum → FockNat,
        Function.Injective φ ∧
        (∀ p, inner (φ p) (φ p) = 1) := by
  intro ⟨φ, hinj, _hon⟩
  obtain ⟨toNat, ofNat, hgf, _⟩ := fockNat_has_countable_infinity
  have hcomp : Function.Injective (toNat ∘ φ) := by
    intro x y hx
    have heq : φ x = φ y := by
      simpa [hgf] using congrArg ofNat hx
    exact hinj heq
  have : Equinumerous Continuum Nat :=
    Equinumerous.of_injections (toNat ∘ φ) embedNat
      hcomp embedNat_injective
  exact not_equinumerous_nat_continuum this.symm

end ToE
