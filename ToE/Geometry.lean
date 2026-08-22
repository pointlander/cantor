/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Physics

/-!
# How the countable carrier sits in the continuum

Cardinality alone does not place the QFT carrier inside GR spacetime.
A **Delone realization** does: an injective embedding of the countable
carrier into the continuum that is

* **uniformly discrete** — distinct realized events have a positive
  minimum separation (a gap);
* **relatively dense** — continuum holes are bounded (a covering radius);
* equipped with a positive finite **density**.

The gap is the geometric reason \(G\) is finite and nonzero: it is the
area per carrier bit, in units \(\hbar = c = 1\). A dense embedding
(like \(\mathbb{Q}\subset\mathbb{R}\)) is forbidden, because it would
collapse the gap and with it \(G\).
-/

namespace ToE

/-! ## Rational arithmetic used as a scale -/

theorem rat_one_pos : 0 < (1 : Rat) :=
  Rat.natCast_pos.mpr (by decide)

theorem rat_two_pos : 0 < (2 : Rat) :=
  Rat.natCast_pos.mpr (by decide)

theorem rat_zero_le_one : (0 : Rat) ≤ 1 :=
  Rat.le_of_lt rat_one_pos

theorem rat_add_le_add {a b c d : Rat} (hab : a ≤ b) (hcd : c ≤ d) :
    a + c ≤ b + d :=
  Rat.le_trans
    ((Rat.add_le_add_right (c := c)).mpr hab)
    ((Rat.add_le_add_left (c := b)).mpr hcd)

theorem rat_two_eq : (2 : Rat) = 1 + 1 :=
  Rat.natCast_add 1 1

theorem rat_add_self (a : Rat) : a + a = 2 * a := by
  rw [rat_two_eq, Rat.add_mul, Rat.one_mul]

theorem rat_half_add_half (a : Rat) : a / 2 + a / 2 = a := by
  have h2 : (2 : Rat) ≠ 0 := Rat.ne_of_gt rat_two_pos
  rw [Rat.div_def, ← Rat.add_mul, rat_add_self, Rat.mul_comm (2 : Rat) a,
    Rat.mul_assoc, Rat.mul_inv_cancel _ h2, Rat.mul_one]

theorem rat_two_mul_half (a : Rat) : 2 * (a / 2) = a := by
  rw [← rat_add_self, rat_half_add_half]

theorem rat_div_two_pos {a : Rat} (ha : 0 < a) : 0 < a / 2 :=
  Rat.mul_pos ha (Rat.inv_pos.mpr rat_two_pos)

theorem rat_lt_trans {a b c : Rat} (hab : a < b) (hbc : b < c) : a < c :=
  Rat.lt_of_le_of_ne
    (Rat.le_trans (Rat.le_of_lt hab) (Rat.le_of_lt hbc))
    (fun h => (Rat.not_le.mpr hab) (h ▸ Rat.le_of_lt hbc))

theorem rat_lt_of_le_of_lt {a b c : Rat} (hab : a ≤ b) (hbc : b < c) : a < c :=
  Rat.lt_of_le_of_ne
    (Rat.le_trans hab (Rat.le_of_lt hbc))
    (fun h => (Rat.not_le.mpr hbc) (h ▸ hab))

theorem rat_add_eq_zero_of_nonneg {a b : Rat}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) : a = 0 ∧ b = 0 := by
  have ha0 : a ≤ 0 := by
    have : a + 0 ≤ a + b := (Rat.add_le_add_left (c := a)).mpr hb
    simpa [Rat.add_zero, h] using this
  have hb0 : b ≤ 0 := by
    have : 0 + b ≤ a + b := (Rat.add_le_add_right (c := b)).mpr ha
    simpa [Rat.zero_add, h] using this
  exact ⟨Rat.le_antisymm ha0 ha, Rat.le_antisymm hb0 hb⟩

/-! ## Discrete distance on `Nat` -/

/-- Symmetric difference of two naturals. -/
def natDist (a b : Nat) : Nat := (a - b) + (b - a)

theorem natDist_self (a : Nat) : natDist a a = 0 := by
  simp [natDist]

theorem natDist_comm (a b : Nat) : natDist a b = natDist b a := by
  simp [natDist, Nat.add_comm]

theorem natDist_eq_zero {a b : Nat} : natDist a b = 0 ↔ a = b := by
  constructor
  · intro h
    have : a - b = 0 ∧ b - a = 0 := Nat.eq_zero_of_add_eq_zero h
    have hab : a ≤ b := Nat.sub_eq_zero_iff_le.mp this.1
    have hba : b ≤ a := Nat.sub_eq_zero_iff_le.mp this.2
    exact Nat.le_antisymm hab hba
  · intro h
    simp [natDist, h]

theorem natDist_triangle (a b c : Nat) :
    natDist a c ≤ natDist a b + natDist b c := by
  simp [natDist]
  omega

theorem natDist_nonneg_rat (a b : Nat) : 0 ≤ ((natDist a b : Nat) : Rat) :=
  Rat.natCast_nonneg (a := natDist a b)

/-! ## Delone realization -/

/-- A type is metrically dense in a space when every continuum point is
an arbitrarily close limit of realized carrier points. -/
def MetricallyDense {α β : Type} (realize : α → β) (dist : β → β → Rat) : Prop :=
  ∀ p : β, ∀ ε : Rat, 0 < ε → ∃ a : α, dist p (realize a) < ε

/-- After the split, the countable carrier sits in the GR continuum as a
Delone set: a gap (uniform discreteness), a covering radius (relative
density), and a positive finite density. -/
structure DeloneSplit where
  Carrier : Type
  countableInfinity : HasCountableInfinity Carrier
  Spacetime : Type
  realInfinity : HasRealInfinity Spacetime
  dist : Spacetime → Spacetime → Rat
  dist_self : ∀ x, dist x x = 0
  dist_comm : ∀ x y, dist x y = dist y x
  dist_nonneg : ∀ x y, 0 ≤ dist x y
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z
  dist_eq_zero_iff : ∀ x y, dist x y = 0 ↔ x = y
  /-- The countable carrier as events in the continuum. -/
  realize : Carrier → Spacetime
  /-- Minimum separation of distinct realized events. -/
  gap : Rat
  gap_pos : 0 < gap
  uniformly_discrete :
    ∀ c₁ c₂ : Carrier, c₁ ≠ c₂ → gap ≤ dist (realize c₁) (realize c₂)
  /-- Every continuum point lies within this radius of some event. -/
  coveringRadius : Rat
  coveringRadius_pos : 0 < coveringRadius
  relatively_dense :
    ∀ p : Spacetime, ∃ c : Carrier, dist p (realize c) ≤ coveringRadius
  /-- Points of the carrier per unit continuum volume. -/
  density : Rat
  density_pos : 0 < density

namespace DeloneSplit

variable (D : DeloneSplit)

/-- The gap separates carrier points, so the realization is injective. -/
theorem realize_injective : Function.Injective D.realize := by
  intro c₁ c₂ h
  cases Classical.em (c₁ = c₂) with
  | inl hEq => exact hEq
  | inr hne =>
    have hg : D.gap ≤ D.dist (D.realize c₁) (D.realize c₂) :=
      D.uniformly_discrete c₁ c₂ hne
    have : D.gap ≤ 0 := by
      rw [h, D.dist_self] at hg
      exact hg
    exact (Rat.not_le.mpr D.gap_pos this).elim

/-- The carrier cannot fill the continuum: the infinities differ. -/
theorem realize_not_surjective : ¬ Function.Surjective D.realize := by
  intro hsurj
  have : Equinumerous D.Carrier D.Spacetime :=
    ⟨D.realize,
     fun y => Classical.choose (hsurj y),
     fun x => D.realize_injective (Classical.choose_spec (hsurj (D.realize x))),
     fun y => Classical.choose_spec (hsurj y)⟩
  exact countable_infinity_ne_real_infinity D.countableInfinity
    (this.trans D.realInfinity)

/-- Newton's constant in units \(\hbar = c = 1\): the Planck area is the
square of the gap (area per carrier bit). -/
def newtonG : Rat := D.gap * D.gap

theorem newtonG_pos : 0 < D.newtonG :=
  Rat.mul_pos D.gap_pos D.gap_pos

/-- Holographic area per bit from the bulk density. Agrees with `newtonG`
only after a dimension-dependent packing factor, which is not yet in the
model. -/
def areaPerBit : Rat := D.density⁻¹

theorem areaPerBit_pos : 0 < D.areaPerBit :=
  Rat.inv_pos.mpr D.density_pos

/-- A gap forbids a dense embedding: the carrier cannot accumulate at a
continuum point without two events falling inside the gap. -/
theorem not_metrically_dense : ¬ MetricallyDense D.realize D.dist := by
  intro hdense
  have hns := D.realize_not_surjective
  have ⟨p, hp⟩ : ∃ p : D.Spacetime, ∀ c, D.realize c ≠ p := by
    cases Classical.em (∃ p, ∀ c, D.realize c ≠ p) with
    | inl h => exact h
    | inr h =>
      refine (hns fun q => ?_).elim
      cases Classical.em (∃ c, D.realize c = q) with
      | inl hc => exact hc
      | inr hc =>
        exact (h ⟨q, fun c hc' => hc ⟨c, hc'⟩⟩).elim
  let ε : Rat := D.gap / 2
  have hε : 0 < ε := rat_div_two_pos D.gap_pos
  obtain ⟨c₁, hc₁⟩ := hdense p ε hε
  have hne1 : D.realize c₁ ≠ p := hp c₁
  have hδpos : 0 < D.dist p (D.realize c₁) :=
    Rat.lt_of_le_of_ne (D.dist_nonneg _ _) fun h0 =>
      hne1 ((D.dist_eq_zero_iff p (D.realize c₁)).mp h0.symm).symm
  obtain ⟨c₂, hc₂⟩ := hdense p (D.dist p (D.realize c₁)) hδpos
  have hne12 : c₁ ≠ c₂ := by
    intro h
    subst h
    exact Rat.lt_irrefl hc₂
  have hgap : D.gap ≤ D.dist (D.realize c₁) (D.realize c₂) :=
    D.uniformly_discrete c₁ c₂ hne12
  have htri : D.dist (D.realize c₁) (D.realize c₂) ≤
      D.dist p (D.realize c₁) + D.dist p (D.realize c₂) := by
    simpa [D.dist_comm (D.realize c₁) p] using
      D.dist_triangle (D.realize c₁) p (D.realize c₂)
  have hd2ε : D.dist p (D.realize c₂) < ε := rat_lt_trans hc₂ hc₁
  have hsum : D.dist p (D.realize c₁) + D.dist p (D.realize c₂) < ε + ε :=
    rat_lt_trans
      ((Rat.add_lt_add_left (c := D.dist p (D.realize c₁))).mpr hd2ε)
      ((Rat.add_lt_add_right (c := ε)).mpr hc₁)
  have hsum' : D.dist p (D.realize c₁) + D.dist p (D.realize c₂) < D.gap := by
    simpa [ε, rat_half_add_half] using hsum
  exact Rat.lt_irrefl (rat_lt_of_le_of_lt hgap (rat_lt_of_le_of_lt htri hsum'))

end DeloneSplit

/-! ## Finite information cannot fill a finite set of holes -/

/-- There is no injection of `{0, …, n}` into `{0, …, n − 1}`. -/
theorem no_inj_upto {n : Nat} (a : Nat → Nat)
    (hbound : ∀ i, i ≤ n → a i < n)
    (hinj : ∀ i j, i ≤ n → j ≤ n → a i = a j → i = j) : False := by
  induction n generalizing a with
  | zero =>
    exact Nat.not_lt_zero (a 0) (hbound 0 (Nat.le_refl 0))
  | succ n ih =>
    cases Classical.em (∃ k, k ≤ n + 1 ∧ a k = n) with
    | inr hnone =>
      apply ih a
      · intro i hi
        have hlt : a i < n + 1 := hbound i (Nat.le_succ_of_le hi)
        have hne : a i ≠ n := fun he => hnone ⟨i, Nat.le_succ_of_le hi, he⟩
        omega
      · intro i j hi hj hij
        exact hinj i j (Nat.le_succ_of_le hi) (Nat.le_succ_of_le hj) hij
    | inl hex =>
      obtain ⟨k, hk, hkval⟩ := hex
      let a' : Nat → Nat := fun i => if i < k then a i else a (i + 1)
      apply ih a'
      · intro i hi
        have hi1 : i + 1 ≤ n + 1 := Nat.succ_le_succ hi
        cases Nat.lt_or_ge i k with
        | inl hlt =>
          have hle : i ≤ n + 1 := Nat.le_trans (Nat.le_of_lt hlt) hk
          have hlt' : a i < n + 1 := hbound i hle
          have hne : a i ≠ n := by
            intro he
            have : i = k := hinj i k hle hk (he.trans hkval.symm)
            subst this
            exact Nat.lt_irrefl _ hlt
          have : a' i = a i := if_pos hlt
          omega
        | inr hge =>
          have hge' : ¬ i < k := Nat.not_lt.mpr hge
          have ha' : a' i = a (i + 1) := if_neg hge'
          have hlt' : a (i + 1) < n + 1 := hbound (i + 1) hi1
          have hne : a (i + 1) ≠ n := by
            intro he
            have : i + 1 = k := hinj (i + 1) k hi1 hk (he.trans hkval.symm)
            omega
          omega
      · intro i j hi hj hij
        have hi1 : i + 1 ≤ n + 1 := Nat.succ_le_succ hi
        have hj1 : j + 1 ≤ n + 1 := Nat.succ_le_succ hj
        cases Nat.lt_or_ge i k with
        | inl hi_lt =>
          have hai : a' i = a i := if_pos hi_lt
          cases Nat.lt_or_ge j k with
          | inl hj_lt =>
            have haj : a' j = a j := if_pos hj_lt
            have : a i = a j := by
              rw [hai, haj] at hij
              exact hij
            exact hinj i j
              (Nat.le_trans (Nat.le_of_lt hi_lt) hk)
              (Nat.le_trans (Nat.le_of_lt hj_lt) hk) this
          | inr hj_ge =>
            have haj : a' j = a (j + 1) := if_neg (Nat.not_lt.mpr hj_ge)
            have : a i = a (j + 1) := by
              rw [hai, haj] at hij
              exact hij
            have heq : i = j + 1 := hinj i (j + 1)
              (Nat.le_trans (Nat.le_of_lt hi_lt) hk) hj1 this
            omega
        | inr hi_ge =>
          have hai : a' i = a (i + 1) := if_neg (Nat.not_lt.mpr hi_ge)
          cases Nat.lt_or_ge j k with
          | inl hj_lt =>
            have haj : a' j = a j := if_pos hj_lt
            have : a (i + 1) = a j := by
              rw [hai, haj] at hij
              exact hij
            have heq : i + 1 = j := hinj (i + 1) j hi1
              (Nat.le_trans (Nat.le_of_lt hj_lt) hk) this
            omega
          | inr hj_ge =>
            have haj : a' j = a (j + 1) := if_neg (Nat.not_lt.mpr hj_ge)
            have : a (i + 1) = a (j + 1) := by
              rw [hai, haj] at hij
              exact hij
            have heq : i + 1 = j + 1 := hinj (i + 1) (j + 1) hi1 hj1 this
            omega

theorem not_injective_nat_fin {n : Nat} (f : Nat → Fin n)
    (hf : Function.Injective f) : False := by
  cases n with
  | zero => nomatch f 0
  | succ n =>
    exact no_inj_upto (n := n + 1) (fun i => (f i).val)
      (fun i _ => (f i).isLt)
      (fun i j _ _ h => hf (Fin.ext h))

/-! ## Holographic screens -/

theorem rat_four_pos : 0 < (4 : Rat) :=
  Rat.natCast_pos.mpr (by decide)

/-- A finite-area 2-surface in the continuum whose independent information
is a finite number of carrier bits. In units \(\hbar = c = k_B = 1\) the
Bekenstein–Hawking law is \(A = 4 N G\). -/
structure HolographicScreen (D : DeloneSplit) where
  area : Rat
  area_pos : 0 < area
  /-- Number of accessible bits of the countable carrier. -/
  bits : Nat
  bits_pos : 0 < bits
  /-- Area law: `area = 4 * bits * G`. -/
  area_law : (bits : Rat) * 4 * D.newtonG = area

namespace HolographicScreen

variable {D : DeloneSplit} (S : HolographicScreen D)

theorem bits_ne_zero : S.bits ≠ 0 :=
  Nat.ne_of_gt S.bits_pos

theorem bits_pos_rat : 0 < (S.bits : Rat) :=
  Rat.natCast_pos.mpr S.bits_pos

/-- Restatement of the area law as \(A = 4 N G\). -/
theorem area_eq_four_mul_bits_mul_G :
    S.area = (4 : Rat) * (S.bits : Rat) * D.newtonG := by
  rw [← S.area_law, Rat.mul_comm (S.bits : Rat) (4 : Rat)]

/-- The area is four Planck areas per carrier bit. -/
theorem area_eq_four_bits_gap_sq :
    S.area = (4 : Rat) * (S.bits : Rat) * (D.gap * D.gap) := by
  rw [S.area_eq_four_mul_bits_mul_G, DeloneSplit.newtonG]

/-- Screen information injects into the countable numbers. -/
theorem information_injects_into_nat :
    ∃ f : Fin S.bits → Nat, Function.Injective f :=
  ⟨fun i => i.val, fun _ _ h => Fin.ext h⟩

/-- A finite-area screen cannot carry the infinity of the reals. -/
theorem no_real_infinity_on_screen : ¬ HasRealInfinity (Fin S.bits) := by
  intro h
  obtain ⟨_to, g, _, hfg⟩ := h
  have hg : Function.Injective g := by
    intro y₁ y₂ hy
    have := congrArg _to hy
    simpa [hfg] using this
  exact not_injective_nat_fin (g ∘ embedNat) fun i j hij =>
    embedNat_injective (hg hij)

end HolographicScreen

/-! ## Causal order and realized screens -/

/-- After the split the countable carrier is a causal set: a strict
partial order with finite open intervals. Time stays countable; a
continuum of interpolating events is forbidden. -/
structure CausalSplit (D : DeloneSplit) where
  Rel : D.Carrier → D.Carrier → Prop
  irrefl : ∀ x, ¬ Rel x x
  trans : ∀ {x y z}, Rel x y → Rel y z → Rel x z
  /-- Strictly between two events there is no injective copy of `Nat`. -/
  interval_finite :
    ∀ x y, ¬ Infinite { z : D.Carrier // Rel x z ∧ Rel z y }

namespace CausalSplit

variable {D : DeloneSplit} (C : CausalSplit D)

theorem asymm {x y : D.Carrier} (h : C.Rel x y) : ¬ C.Rel y x :=
  fun hyx => C.irrefl x (C.trans h hyx)

/-- A totally ordered finite tuple of carrier events. -/
def IsChain {n : Nat} (s : Fin n → D.Carrier) : Prop :=
  ∀ i j : Fin n, i.val < j.val → C.Rel (s i) (s j)

end CausalSplit

/-- The \(N\) bits of a holographic screen as \(N\) incomparable
(spacelike) carrier events. -/
structure RealizedScreen {D : DeloneSplit} (C : CausalSplit D) where
  screen : HolographicScreen D
  events : Fin screen.bits → D.Carrier
  events_injective : Function.Injective events
  antichain :
    ∀ i j : Fin screen.bits, i ≠ j →
      ¬ C.Rel (events i) (events j) ∧ ¬ C.Rel (events j) (events i)

namespace RealizedScreen

variable {D : DeloneSplit} {C : CausalSplit D} (S : RealizedScreen C)

theorem bits_eq_event_count : S.screen.bits = S.screen.bits := rfl

/-- A timelike chain of two or more events cannot be a holographic screen. -/
theorem not_a_chain (hbits : 1 < S.screen.bits) : ¬ C.IsChain S.events := by
  intro hc
  let i0 : Fin S.screen.bits := ⟨0, S.screen.bits_pos⟩
  let i1 : Fin S.screen.bits := ⟨1, hbits⟩
  have hne : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hlt : i0.val < i1.val := Nat.zero_lt_one
  have hrel : C.Rel (S.events i0) (S.events i1) := hc i0 i1 hlt
  exact (S.antichain i0 i1 hne).1 hrel

theorem area_law :
    S.screen.area =
      (4 : Rat) * (S.screen.bits : Rat) * D.newtonG :=
  S.screen.area_eq_four_mul_bits_mul_G

end RealizedScreen

/-- Causal precedence on the standard carrier `Nat`: `a` can influence
`b` only if `a + 2 ≤ b`. Immediate neighbours are spacelike, so a
two-event screen exists. -/
def standardRel (a b : Nat) : Prop := a + 2 ≤ b

theorem standardRel_irrefl (x : Nat) : ¬ standardRel x x := by
  intro h
  simp [standardRel] at h
  omega

theorem standardRel_trans {x y z : Nat}
    (hxy : standardRel x y) (hyz : standardRel y z) : standardRel x z := by
  simp [standardRel] at hxy hyz ⊢
  omega

theorem standardRel_interval_finite (x y : Nat) :
    ¬ Infinite { z : Nat // standardRel x z ∧ standardRel z y } := by
  intro ⟨f, hf⟩
  have hz := (f 0).2
  have hspan : x + 4 ≤ y := by
    simp [standardRel] at hz
    omega
  let n := y - x - 3
  have hnpos : 0 < n := by omega
  let g : Nat → Fin n := fun k =>
    ⟨(f k).val - (x + 2), by
      have hk := (f k).2
      simp [standardRel] at hk
      omega⟩
  refine not_injective_nat_fin g fun i j hij => ?_
  have hidx : (g i).val = (g j).val := congrArg Fin.val hij
  have hi := (f i).2
  have hj := (f j).2
  simp [standardRel] at hi hj
  have : (f i).val = (f j).val := by
    dsimp [g] at hidx
    omega
  exact hf (Subtype.ext this)

/-! ## Least-true index on the Cantor space -/

/-- The least `m ≤ n` at which `P` holds, if any. -/
def leastLE (P : Nat → Prop) [DecidablePred P] : Nat → Option Nat
  | 0 => if P 0 then some 0 else none
  | n + 1 =>
    match leastLE P n with
    | some m => some m
    | none => if P (n + 1) then some (n + 1) else none

theorem leastLE_none_of_not {P : Nat → Prop} [DecidablePred P] {n : Nat}
    (h : ∀ k, k ≤ n → ¬ P k) : leastLE P n = none := by
  induction n with
  | zero =>
    simp [leastLE, h 0 (Nat.le_refl 0)]
  | succ n ih =>
    have hnone : leastLE P n = none :=
      ih fun k hk => h k (Nat.le_succ_of_le hk)
    simp [leastLE, hnone, h (n + 1) (Nat.le_refl _)]

theorem leastLE_at_min {P : Nat → Prop} [DecidablePred P] {n : Nat}
    (hP : P n) (hmin : ∀ k, k < n → ¬ P k) : leastLE P n = some n := by
  cases n with
  | zero =>
    simp [leastLE, hP]
  | succ n =>
    have hnone : leastLE P n = none :=
      leastLE_none_of_not fun k hk => hmin k (Nat.lt_succ_of_le hk)
    simp [leastLE, hnone, hP]

theorem embedNat_true_iff {n k : Nat} : embedNat n k = true ↔ n = k := by
  simp [embedNat]

/-! ## A standard Delone realization on the continuum -/

noncomputable section
open Classical
set_option maxHeartbeats 4000000

/-- Position of a continuum point along a countable axis: the least bit
that is `true`, or `0` if there is none. -/
@[irreducible] noncomputable def idx (f : Continuum) : Nat :=
  if h : ∃ n, f n = true then
    match leastLE (fun n => f n = true) (Classical.choose h) with
    | some m => m
    | none => 0
  else 0

theorem idx_embedNat (n : Nat) : idx (embedNat n) = n := by
  have hex : ∃ k, embedNat n k = true := ⟨n, embedNat_true_iff.mpr rfl⟩
  unfold idx
  rw [dif_pos hex]
  have hch : Classical.choose hex = n := by
    have := Classical.choose_spec hex
    exact (embedNat_true_iff.mp this).symm
  rw [hch]
  have hsome :
      leastLE (fun k => embedNat n k = true) n = some n :=
    leastLE_at_min (embedNat_true_iff.mpr rfl) fun k hk hP =>
      (Nat.ne_of_lt hk) (embedNat_true_iff.mp hP).symm
  simp [hsome]

/-- Unbounded product metric: lattice distance along `idx`, plus a discrete
metric on the Cantor fibre. Lattice points recede without bound; every
continuum point still sits in a bounded neighbourhood of one of them. -/
@[irreducible] noncomputable def geometricDist (f g : Continuum) : Rat :=
  ((natDist (idx f) (idx g) : Nat) : Rat) +
    if f = g then (0 : Rat) else 1

theorem geometricDist_self (x : Continuum) : geometricDist x x = 0 := by
  unfold geometricDist
  rw [natDist_self, if_pos rfl]
  change (0 : Rat) + 0 = 0
  exact Rat.add_zero 0

theorem geometricDist_comm (x y : Continuum) :
    geometricDist x y = geometricDist y x := by
  unfold geometricDist
  rw [natDist_comm]
  cases Classical.em (x = y) with
  | inl h => rw [if_pos h, if_pos h.symm]
  | inr h => rw [if_neg h, if_neg (fun h' => h h'.symm)]

theorem apart_nonneg (x y : Continuum) :
    0 ≤ (if x = y then (0 : Rat) else 1) := by
  cases Classical.em (x = y) with
  | inl h => rw [if_pos h]; exact Rat.le_refl
  | inr h => rw [if_neg h]; exact rat_zero_le_one

theorem geometricDist_nonneg (x y : Continuum) : 0 ≤ geometricDist x y := by
  unfold geometricDist
  exact Rat.add_nonneg (natDist_nonneg_rat _ _) (apart_nonneg x y)

theorem apart_triangle (x y z : Continuum) :
    (if x = z then (0 : Rat) else 1) ≤
      (if x = y then (0 : Rat) else 1) +
        (if y = z then (0 : Rat) else 1) := by
  cases Classical.em (x = z) with
  | inl hxz =>
    rw [if_pos hxz]
    exact Rat.add_nonneg (apart_nonneg x y) (apart_nonneg y z)
  | inr hxz =>
    rw [if_neg hxz]
    cases Classical.em (x = y) with
    | inl hxy =>
      rw [if_pos hxy, Rat.zero_add, if_neg (fun hyz => hxz (hxy.trans hyz))]
      exact Rat.le_refl
    | inr hxy =>
      rw [if_neg hxy]
      cases Classical.em (y = z) with
      | inl hyz =>
        rw [if_pos hyz, Rat.add_zero]
        exact Rat.le_refl
      | inr hyz =>
        rw [if_neg hyz]
        have : (1 : Rat) + 0 ≤ 1 + 1 :=
          (Rat.add_le_add_left (c := (1 : Rat))).mpr rat_zero_le_one
        simpa [Rat.add_zero] using this

theorem geometricDist_triangle (x y z : Continuum) :
    geometricDist x z ≤ geometricDist x y + geometricDist y z := by
  unfold geometricDist
  have hd : ((natDist (idx x) (idx z) : Nat) : Rat) ≤
      ((natDist (idx x) (idx y) : Nat) : Rat) +
        ((natDist (idx y) (idx z) : Nat) : Rat) := by
    have := natDist_triangle (idx x) (idx y) (idx z)
    have := (Rat.natCast_le_natCast
      (a := natDist (idx x) (idx z))
      (b := natDist (idx x) (idx y) + natDist (idx y) (idx z))).mpr this
    simpa [Rat.natCast_add] using this
  have ha := apart_triangle x y z
  have hsum := rat_add_le_add hd ha
  simpa [Rat.add_assoc, Rat.add_left_comm, Rat.add_comm] using hsum

theorem geometricDist_eq_zero_iff (x y : Continuum) :
    geometricDist x y = 0 ↔ x = y := by
  constructor
  · intro h
    unfold geometricDist at h
    have hparts :=
      rat_add_eq_zero_of_nonneg (natDist_nonneg_rat _ _) (apart_nonneg x y) h
    cases Classical.em (x = y) with
    | inl heq => exact heq
    | inr hne =>
      have : (if x = y then (0 : Rat) else 1) = 1 := if_neg hne
      rw [this] at hparts
      exact absurd hparts.2 (Rat.ne_of_gt rat_one_pos)
  · intro h
    subst h
    exact geometricDist_self x

theorem geometricDist_of_ne {f g : Continuum} (h : f ≠ g) :
    geometricDist f g =
      ((natDist (idx f) (idx g) : Nat) : Rat) + 1 := by
  unfold geometricDist
  rw [if_neg h]

theorem geometricDist_ge_one_of_ne {f g : Continuum} (h : f ≠ g) :
    1 ≤ geometricDist f g := by
  have heq := geometricDist_of_ne h
  refine heq.symm ▸ ?_
  have hle : (0 : Rat) + 1 ≤
      ((natDist (idx f) (idx g) : Nat) : Rat) + 1 :=
    (Rat.add_le_add_right (c := (1 : Rat))).mpr
      (natDist_nonneg_rat (idx f) (idx g))
  simpa [Rat.zero_add] using hle

theorem geometricDist_cover (p : Continuum) :
    geometricDist p (embedNat (idx p)) ≤ 1 := by
  have hid : idx (embedNat (idx p)) = idx p := idx_embedNat (idx p)
  have hnat : natDist (idx p) (idx (embedNat (idx p))) = 0 := by
    rw [hid, natDist_self]
  unfold geometricDist
  rw [hnat]
  change (0 : Rat) + (if p = embedNat (idx p) then (0 : Rat) else 1) ≤ 1
  rw [Rat.zero_add]
  cases Classical.em (p = embedNat (idx p)) with
  | inl h => rw [if_pos h]; exact rat_zero_le_one
  | inr h => rw [if_neg h]; exact Rat.le_refl

/-- The standard realization: the origin's countable carrier as a Delone
subset of the GR continuum, with gap, covering radius, and density all
equal to `1` in lattice units. -/
noncomputable def standardDelone : DeloneSplit where
  Carrier := Nat
  countableInfinity := nat_has_countable_infinity
  Spacetime := Continuum
  realInfinity := continuum_has_real_infinity
  dist := geometricDist
  dist_self := geometricDist_self
  dist_comm := geometricDist_comm
  dist_nonneg := geometricDist_nonneg
  dist_triangle := geometricDist_triangle
  dist_eq_zero_iff := geometricDist_eq_zero_iff
  realize := embedNat
  gap := 1
  gap_pos := rat_one_pos
  uniformly_discrete := by
    intro c₁ c₂ hne
    exact geometricDist_ge_one_of_ne fun h => hne (embedNat_injective h)
  coveringRadius := 1
  coveringRadius_pos := rat_one_pos
  relatively_dense := by
    intro p
    exact ⟨idx p, geometricDist_cover p⟩
  density := 1
  density_pos := rat_one_pos

/-- After time, the split of the origin admits this Delone realization:
QFT modes are `Nat`, GR spacetime is the continuum, and the carrier sits
in that continuum with gap `1` and density `1`. -/
theorem origin_split_realized :
    (separate unifiedAtOrigin).1.Modes = standardDelone.Carrier ∧
    (separate unifiedAtOrigin).2.Spacetime = standardDelone.Spacetime :=
  ⟨rfl, rfl⟩

theorem standardDelone_gap_pos : 0 < standardDelone.gap :=
  standardDelone.gap_pos

theorem standardDelone_density_pos : 0 < standardDelone.density :=
  standardDelone.density_pos

theorem standardDelone_G_pos : 0 < standardDelone.newtonG :=
  standardDelone.newtonG_pos

theorem standardDelone_not_dense :
    ¬ MetricallyDense standardDelone.realize standardDelone.dist :=
  standardDelone.not_metrically_dense

/-- One Planck cell of the standard realization: area `4` in lattice
units, one carrier bit, \(G = 1\), so \(A = 4 N G\). -/
noncomputable def standardScreen : HolographicScreen standardDelone where
  area := 4
  area_pos := rat_four_pos
  bits := 1
  bits_pos := Nat.succ_pos 0
  area_law := by
    change (1 : Rat) * 4 * (standardDelone.gap * standardDelone.gap) = 4
    change (1 : Rat) * 4 * (1 * 1) = 4
    rw [Rat.one_mul, Rat.one_mul, Rat.mul_one]

theorem standardScreen_area_law :
    standardScreen.area =
      (4 : Rat) * (standardScreen.bits : Rat) * standardDelone.newtonG :=
  standardScreen.area_eq_four_mul_bits_mul_G

theorem standardScreen_no_continuum :
    ¬ HasRealInfinity (Fin standardScreen.bits) :=
  standardScreen.no_real_infinity_on_screen

/-- The standard carrier as a causal set. Neighbours are spacelike. -/
noncomputable def standardCausal : CausalSplit standardDelone where
  Rel := standardRel
  irrefl := standardRel_irrefl
  trans := standardRel_trans
  interval_finite := standardRel_interval_finite

/-- The one-bit Planck cell as a single carrier event (a trivial antichain). -/
noncomputable def standardRealizedScreen : RealizedScreen standardCausal where
  screen := standardScreen
  events := fun _ => (0 : Nat)
  events_injective := by
    intro i j _
    have hi : i.val = 0 := Nat.lt_one_iff.mp i.isLt
    have hj : j.val = 0 := Nat.lt_one_iff.mp j.isLt
    exact Fin.ext (hi.trans hj.symm)
  antichain := by
    intro i j hne
    have hi : i.val = 0 := Nat.lt_one_iff.mp i.isLt
    have hj : j.val = 0 := Nat.lt_one_iff.mp j.isLt
    exact (hne (Fin.ext (hi.trans hj.symm))).elim

/-- Two spacelike neighbours `{0, 1}` as a two-bit screen of area `8`. -/
noncomputable def pairScreen : HolographicScreen standardDelone where
  area := 8
  area_pos := Rat.natCast_pos.mpr (by decide)
  bits := 2
  bits_pos := by decide
  area_law := by
    change ((2 : Nat) : Rat) * 4 * (standardDelone.gap * standardDelone.gap) = 8
    change ((2 : Nat) : Rat) * 4 * (1 * 1) = 8
    rw [Rat.one_mul, Rat.mul_one]
    have h4 : (4 : Rat) = ((4 : Nat) : Rat) := rfl
    have h8 : (8 : Rat) = ((8 : Nat) : Rat) := rfl
    rw [h4, h8, ← Rat.natCast_mul]

noncomputable def pairRealizedScreen : RealizedScreen standardCausal where
  screen := pairScreen
  events := fun i => i.val
  events_injective := fun i j h => Fin.ext h
  antichain := by
    intro i j hne
    constructor
    · intro hrel
      simp [standardCausal, standardRel] at hrel
      have hi : i.val < 2 := i.isLt
      have hj : j.val < 2 := j.isLt
      omega
    · intro hrel
      simp [standardCausal, standardRel] at hrel
      have hi : i.val < 2 := i.isLt
      have hj : j.val < 2 := j.isLt
      omega

theorem pairRealizedScreen_not_a_chain :
    ¬ standardCausal.IsChain pairRealizedScreen.events :=
  pairRealizedScreen.not_a_chain (by decide)

end

end ToE
