/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Fock

/-!
# Inner product on Fock space

The algebraic Fock space of finite-support occupations carries a
positive-definite pairing

\[
\langle f,g\rangle = \sum_k f(k)\,g(k)
\]

with values in `Nat`. The sum is finite. One-particle states `basis n`
are orthonormal. A continuum of orthonormal modes would inject the
reals into a countable space, which is forbidden.

This is not completed \(\ell^2\). Completeness and a Hamiltonian can
wait; the split only needs a countable orthonormal set of matter
states.
-/

namespace ToE

/-! ## Finite sums -/

/-- Sum of `f 0 + ⋯ + f (n-1)`. -/
def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo f n + f n

theorem sumTo_zero (n : Nat) : sumTo (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [sumTo, ih]

theorem sumTo_eq_zero {f : Nat → Nat} :
    ∀ {N}, sumTo f N = 0 ↔ ∀ k, k < N → f k = 0
  | 0 => by
    constructor
    · intro _ k hk
      omega
    · intro
      rfl
  | N + 1 => by
    constructor
    · intro h k hk
      have hsum : sumTo f N + f N = 0 := h
      have ⟨hN, hlast⟩ := Nat.add_eq_zero_iff.mp hsum
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with
      | inl hlt =>
        exact (sumTo_eq_zero.mp hN) k hlt
      | inr he =>
        subst he
        exact hlast
    · intro hf
      simp [sumTo]
      have hN : sumTo f N = 0 :=
        sumTo_eq_zero.mpr fun k hk => hf k (Nat.lt_succ_of_lt hk)
      have hlast : f N = 0 := hf N (Nat.lt_succ_self N)
      omega

theorem sumTo_of_le {f : Nat → Nat} {N : Nat} (hz : isBound f N) :
    ∀ {M}, N ≤ M → sumTo f M = sumTo f N
  | 0, hM => by
    have : N = 0 := Nat.eq_zero_of_le_zero hM
    subst this
    rfl
  | M + 1, hM => by
    cases Nat.eq_or_lt_of_le hM with
    | inl he =>
      subst he
      rfl
    | inr hlt =>
      have hNM : N ≤ M := Nat.le_of_lt_succ hlt
      simp [sumTo]
      have hlast : f M = 0 := hz M hNM
      rw [hlast, Nat.add_zero, sumTo_of_le hz hNM]

theorem sumTo_eq_of_bounds {f : Nat → Nat} {N M : Nat}
    (hN : isBound f N) (hM : isBound f M) :
    sumTo f N = sumTo f M := by
  cases Nat.le_total N M with
  | inl h =>
    exact (sumTo_of_le hN h).symm
  | inr h =>
    exact sumTo_of_le hM h

theorem sumTo_indicator {n N : Nat} (h : n < N) :
    sumTo (fun k => if k = n then 1 else 0) N = 1 := by
  induction N with
  | zero =>
    omega
  | succ N ih =>
    simp [sumTo]
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with
    | inl hlt =>
      have hne : ¬ N = n := (Nat.ne_of_lt hlt).symm
      simp [hne, ih hlt]
    | inr he =>
      subst he
      have h0 : sumTo (fun k => if k = n then 1 else 0) n = 0 :=
        sumTo_eq_zero.mpr fun k hk => by simp [Nat.ne_of_lt hk]
      simp [h0]

theorem sumTo_indicator_off {n m N : Nat} (hne : n ≠ m) :
    sumTo (fun k =>
        (if k = n then 1 else 0) * (if k = m then 1 else 0)) N = 0 := by
  refine sumTo_eq_zero.mpr ?_
  intro k _
  split <;> split <;> simp_all

/-! ## The pairing -/

noncomputable def supportBound (f : FockNat) : Nat :=
  Classical.choose f.property

theorem supportBound_spec (f : FockNat) :
    isBound f.val (supportBound f) :=
  Classical.choose_spec f.property

theorem product_bound (f g : FockNat) :
    isBound (fun k => f.val k * g.val k)
      (Nat.max (supportBound f) (supportBound g)) := by
  intro k hk
  have hf : isBound f.val (supportBound f) := supportBound_spec f
  have hg : isBound g.val (supportBound g) := supportBound_spec g
  cases Nat.le_total (supportBound f) (supportBound g) with
  | inl hfg =>
    have : supportBound g ≤ k := by
      simpa [Nat.max_eq_right hfg] using hk
    have : g.val k = 0 := hg k this
    simp [this]
  | inr hgf =>
    have : supportBound f ≤ k := by
      simpa [Nat.max_eq_left hgf] using hk
    have : f.val k = 0 := hf k this
    simp [this]

/-- Finite-support inner product \(\langle f,g\rangle = \sum_k f(k)g(k)\). -/
noncomputable def inner (f g : FockNat) : Nat :=
  sumTo (fun k => f.val k * g.val k)
    (Nat.max (supportBound f) (supportBound g))

theorem inner_eq_sumTo (f g : FockNat) {N : Nat}
    (hN : isBound (fun k => f.val k * g.val k) N) :
    inner f g = sumTo (fun k => f.val k * g.val k) N :=
  sumTo_eq_of_bounds (product_bound f g) hN

theorem inner_comm (f g : FockNat) : inner f g = inner g f := by
  have h1 := product_bound f g
  have h2 := product_bound g f
  have hmax : Nat.max (supportBound f) (supportBound g) =
      Nat.max (supportBound g) (supportBound f) := Nat.max_comm _ _
  unfold inner
  simp [Nat.mul_comm, hmax]

theorem inner_vacuum_left (f : FockNat) : inner FockNat.vacuum f = 0 := by
  have hz : isBound (fun k => FockNat.vacuum.val k * f.val k) 0 := by
    intro k _
    simp [FockNat.vacuum]
  rw [inner_eq_sumTo FockNat.vacuum f hz]
  rfl

theorem inner_vacuum : inner FockNat.vacuum FockNat.vacuum = 0 :=
  inner_vacuum_left FockNat.vacuum

theorem inner_self_eq_zero {f : FockNat} :
    inner f f = 0 ↔ f = FockNat.vacuum := by
  constructor
  · intro h
    have hN := product_bound f f
    have hs : sumTo (fun k => f.val k * f.val k)
        (Nat.max (supportBound f) (supportBound f)) = 0 := by
      simpa [inner] using h
    have hall : ∀ k, f.val k = 0 := by
      intro k
      have hb := supportBound_spec f
      cases Nat.lt_or_ge k (supportBound f) with
      | inl hlt =>
        have hterm : f.val k * f.val k = 0 := by
          have hz := (sumTo_eq_zero.mp (by
            simpa [Nat.max_self] using hs)) k (by
            simpa [Nat.max_self] using hlt)
          exact hz
        cases Nat.mul_eq_zero.mp hterm with
        | inl h0 => exact h0
        | inr h0 => exact h0
      | inr hge =>
        exact hb k hge
    apply Subtype.ext
    funext k
    simp [FockNat.vacuum, hall]
  · intro hf
    subst hf
    exact inner_vacuum

theorem inner_basis_bound (n m : Nat) :
    isBound (fun k =>
        (FockNat.basis n).val k * (FockNat.basis m).val k)
      (Nat.max n m + 1) := by
  intro k hk
  have hmax : Nat.max n m < k := Nat.lt_of_succ_le hk
  have hkn : k ≠ n :=
    Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.le_max_left n m) hmax)
  have hkm : k ≠ m :=
    Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.le_max_right n m) hmax)
  simp [FockNat.basis, hkn, hkm]

theorem inner_basis (n m : Nat) :
    inner (FockNat.basis n) (FockNat.basis m) =
      if n = m then 1 else 0 := by
  have hB := inner_basis_bound n m
  rw [inner_eq_sumTo _ _ hB]
  by_cases hnm : n = m
  · subst hnm
    have hfun :
        (fun k => (FockNat.basis n).val k * (FockNat.basis n).val k) =
          fun k => if k = n then 1 else 0 := by
      funext k
      simp [FockNat.basis]
      split <;> simp
    rw [hfun, if_pos rfl]
    have : n < Nat.max n n + 1 := Nat.lt_succ_of_le (Nat.le_max_left n n)
    exact sumTo_indicator this
  · simp [hnm, FockNat.basis]
    exact sumTo_indicator_off (N := Nat.max n m + 1) hnm

theorem inner_basis_self (n : Nat) :
    inner (FockNat.basis n) (FockNat.basis n) = 1 := by
  simp [inner_basis]

theorem inner_basis_off {n m : Nat} (h : n ≠ m) :
    inner (FockNat.basis n) (FockNat.basis m) = 0 := by
  simp [inner_basis, h]

/-- A continuum of orthonormal modes would inject the reals into the
countable Fock space. -/
theorem no_continuum_orthonormal :
    ¬ ∃ φ : Continuum → FockNat,
        (∀ p, inner (φ p) (φ p) = 1) ∧
        (∀ p q, p ≠ q → inner (φ p) (φ q) = 0) := by
  intro ⟨φ, hon, hoff⟩
  have hinj : Function.Injective φ := by
    intro p q hpq
    by_cases heq : p = q
    · exact heq
    · have h0 : inner (φ p) (φ q) = 0 := hoff p q heq
      have h1 : inner (φ p) (φ p) = 1 := hon p
      have : inner (φ p) (φ q) = inner (φ p) (φ p) := by rw [hpq]
      omega
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
