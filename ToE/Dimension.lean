/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Geometry

/-!
# Four dimensions and packing

After time, GR spacetime is locally four copies of the continuum. That
is still the infinity of the reals: extra axes do not create a new
infinity, so \(\lvert\mathbb{R}^4\rvert = \lvert\mathbb{R}\rvert\). QFT
and GR still cannot be identified.

The Delone packing factor converts bulk volume-per-point into Planck
area, so the holographic \(G\) and the bulk density describe the same
scale:

\[
(\mathrm{area\ per\ bit})\times(\mathrm{packing}) = G.
\]

On the standard realization, packing is \(1\) in lattice units.
-/

namespace ToE

/-- Spacetime dimension after the split. -/
def spacetimeDimension : Nat := 4

/-- Two copies of the continuum. -/
abbrev Continuum2 : Type := Continuum × Continuum

/-- Four copies of the continuum: the local model of GR spacetime. -/
abbrev Spacetime4 : Type := Continuum × Continuum × Continuum × Continuum

/-! ## Equinumerosity of products -/

theorem Equinumerous.prod {α α' β β' : Type}
    (hα : Equinumerous α α') (hβ : Equinumerous β β') :
    Equinumerous (α × β) (α' × β') := by
  obtain ⟨fa, ga, hga, hfgα⟩ := hα
  obtain ⟨fb, gb, hgb, hfgβ⟩ := hβ
  refine ⟨fun p => (fa p.1, fb p.2), fun q => (ga q.1, gb q.2), ?_, ?_⟩
  · intro p
    apply Prod.ext
    · exact hga p.1
    · exact hgb p.2
  · intro q
    apply Prod.ext
    · exact hfgα q.1
    · exact hfgβ q.2

/-! ## Interleaving: `ℕ ≃ ℕ × Bool`, hence `2^ℕ ≃ 2^ℕ × 2^ℕ` -/

/-- Even/odd pairing: `(k, false) ↦ 2k`, `(k, true) ↦ 2k+1`. -/
def pairNat : Nat → Bool → Nat
  | k, false => 2 * k
  | k, true => 2 * k + 1

/-- Inverse of `pairNat`: quotient by two, with the remainder as a bit. -/
def unpairNat (n : Nat) : Nat × Bool :=
  (n / 2, decide (n % 2 = 1))

theorem pairNat_unpairNat (n : Nat) :
    pairNat (unpairNat n).1 (unpairNat n).2 = n := by
  have hdiv : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
  by_cases h : n % 2 = 1
  · have hb : decide (n % 2 = 1) = true := by simp [h]
    simp [unpairNat, pairNat, hb]
    omega
  · have h0 : n % 2 = 0 := by
      have : n % 2 < 2 := Nat.mod_lt n (by decide)
      omega
    have hb : decide (n % 2 = 1) = false := by simp [h0]
    simp [unpairNat, pairNat, hb]
    omega

theorem unpairNat_pairNat (k : Nat) (b : Bool) :
    unpairNat (pairNat k b) = (k, b) := by
  cases b with
  | false =>
    apply Prod.ext
    · change (2 * k) / 2 = k
      exact Nat.mul_div_right k (by decide)
    · change decide ((2 * k) % 2 = 1) = false
      have : (2 * k) % 2 = 0 := Nat.mul_mod_right 2 k
      simp [this]
  | true =>
    apply Prod.ext
    · change (2 * k + 1) / 2 = k
      omega
    · change decide ((2 * k + 1) % 2 = 1) = true
      have : (2 * k + 1) % 2 = 1 := by omega
      simp [this]

/-- Interleave two continuum points by even/odd bits. -/
def interleave (p : Continuum2) : Continuum :=
  fun n =>
    match unpairNat n with
    | (k, false) => p.1 k
    | (k, true) => p.2 k

/-- Split a continuum point into even and odd bits. -/
def splitCont (f : Continuum) : Continuum2 :=
  (fun k => f (pairNat k false), fun k => f (pairNat k true))

theorem splitCont_interleave (p : Continuum2) :
    splitCont (interleave p) = p := by
  apply Prod.ext
  · funext k
    change interleave p (pairNat k false) = p.1 k
    have h := unpairNat_pairNat k false
    simp [interleave, h]
  · funext k
    change interleave p (pairNat k true) = p.2 k
    have h := unpairNat_pairNat k true
    simp [interleave, h]

theorem interleave_splitCont (f : Continuum) :
    interleave (splitCont f) = f := by
  funext n
  have hp := pairNat_unpairNat n
  cases h : unpairNat n with
  | mk k b =>
    have hp' : pairNat k b = n := by
      simpa [h] using hp
    cases b with
    | false =>
      simp [interleave, splitCont, h, hp']
    | true =>
      simp [interleave, splitCont, h, hp']

/-- Two copies of the continuum are still the continuum. -/
theorem continuum2_equinumerous_continuum :
    Equinumerous Continuum2 Continuum :=
  ⟨interleave, splitCont, splitCont_interleave, interleave_splitCont⟩

/-- Three copies of the continuum are still the continuum. -/
theorem continuum3_equinumerous_continuum :
    Equinumerous (Continuum × Continuum × Continuum) Continuum :=
  (Equinumerous.prod (Equinumerous.refl Continuum)
      continuum2_equinumerous_continuum).trans
    continuum2_equinumerous_continuum

/-- Four copies of the continuum are still the continuum:
\(\lvert\mathbb{R}^4\rvert = \lvert\mathbb{R}\rvert\). Extra spacetime
axes do not create a new infinity. -/
theorem spacetime4_equinumerous_continuum :
    Equinumerous Spacetime4 Continuum :=
  (Equinumerous.prod (Equinumerous.refl Continuum)
      continuum3_equinumerous_continuum).trans
    continuum2_equinumerous_continuum

theorem spacetime4_has_real_infinity : HasRealInfinity Spacetime4 :=
  spacetime4_equinumerous_continuum

/-- Four-dimensional spacetime is still not the countable carrier. -/
theorem countable_ne_spacetime4 {α : Type}
    (h : HasCountableInfinity α) : ¬ Equinumerous α Spacetime4 := by
  intro he
  exact countable_infinity_ne_real_infinity h
    (he.trans spacetime4_has_real_infinity)

/-- After the split, GR may be read as four copies of the continuum
without changing its infinity. -/
theorem gr_equinumerous_spacetime4 (U : UnifiedTheory) :
    Equinumerous (separate U).2.Spacetime Spacetime4 :=
  (separate U).2.realInfinity.trans spacetime4_equinumerous_continuum.symm

theorem origin_gr_equinumerous_spacetime4 :
    Equinumerous (separate unifiedAtOrigin).2.Spacetime Spacetime4 :=
  gr_equinumerous_spacetime4 unifiedAtOrigin

theorem qft_ne_spacetime4 (U : UnifiedTheory) :
    ¬ Equinumerous (separate U).1.Modes Spacetime4 :=
  countable_ne_spacetime4 (separate U).1.countableInfinity

/-! ## Standard four-dimensional geometry -/

/-- The standard Delone realization, read as four-dimensional, with
packing that identifies bulk density and holographic \(G\). -/
structure FourGeometry where
  split : DeloneSplit
  dimension : Nat
  dimension_eq : dimension = spacetimeDimension

namespace FourGeometry

variable (F : FourGeometry)

theorem packing_agrees :
    F.split.areaPerBit * F.split.packing = F.split.newtonG :=
  F.split.areaPerBit_mul_packing

theorem packing_pos : 0 < F.split.packing :=
  F.split.packing_pos

end FourGeometry

noncomputable def standardFour : FourGeometry where
  split := standardDelone
  dimension := 4
  dimension_eq := rfl

theorem standardFour_dimension : standardFour.dimension = 4 := rfl

theorem standardFour_packing :
    standardFour.split.packing = (1 : Rat) :=
  standardDelone_packing

theorem standardFour_packing_agrees :
    standardFour.split.areaPerBit * standardFour.split.packing =
      standardFour.split.newtonG :=
  standardFour.packing_agrees

theorem standardFour_carrier_ne_spacetime4 :
    ¬ Equinumerous standardFour.split.Carrier Spacetime4 :=
  countable_ne_spacetime4 standardFour.split.countableInfinity

end ToE
