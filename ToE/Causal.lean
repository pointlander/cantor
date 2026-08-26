/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Geometry

/-!
# Causal–metric compatibility

The Delone embedding samples the same causal order into the continuum.
A spacetime point precedes another when both lie on the carrier and the
carrier events are related. Screens that are antichains on the carrier
are therefore spacelike in spacetime, not only as abstract labels.
There are no closed timelike curves. The Lorentzian content is an order
(comparable vs incomparable), not a quadratic form on the Cantor space.
-/

namespace ToE

/-- Push the carrier order into spacetime along `realize`. Continuum
points off the carrier image are causally incomparable with everything:
they are geometric labels, not extra instants. -/
def pushPrecedes {D : DeloneSplit} (C : CausalSplit D)
    (p q : D.Spacetime) : Prop :=
  ∃ a b : D.Carrier, D.realize a = p ∧ D.realize b = q ∧ C.Rel a b

theorem pushPrecedes_irrefl {D : DeloneSplit} (C : CausalSplit D)
    (p : D.Spacetime) : ¬ pushPrecedes C p p := by
  intro ⟨a, b, ha, hb, hrel⟩
  have : a = b := D.realize_injective (ha.trans hb.symm)
  subst this
  exact C.irrefl a hrel

theorem pushPrecedes_trans {D : DeloneSplit} (C : CausalSplit D)
    {p q r : D.Spacetime}
    (hpq : pushPrecedes C p q) (hqr : pushPrecedes C q r) :
    pushPrecedes C p r := by
  obtain ⟨a, b, ha, hb, hab⟩ := hpq
  obtain ⟨c, d, hc, hd, hcd⟩ := hqr
  have : b = c := D.realize_injective (hb.trans hc.symm)
  subst this
  exact ⟨a, d, ha, hd, C.trans hab hcd⟩

theorem pushPrecedes_realize_iff {D : DeloneSplit} (C : CausalSplit D)
    (a b : D.Carrier) :
    C.Rel a b ↔ pushPrecedes C (D.realize a) (D.realize b) := by
  constructor
  · intro h
    exact ⟨a, b, rfl, rfl, h⟩
  · intro ⟨a', b', ha', hb', hrel⟩
    have haa : a' = a := D.realize_injective ha'
    have hbb : b' = b := D.realize_injective hb'
    subst haa
    subst hbb
    exact hrel

theorem pushPrecedes_asymm {D : DeloneSplit} (C : CausalSplit D)
    {p q : D.Spacetime} (h : pushPrecedes C p q) :
    ¬ pushPrecedes C q p :=
  fun hqp => pushPrecedes_irrefl C p (pushPrecedes_trans C h hqp)

theorem pushPrecedes_in_image {D : DeloneSplit} (C : CausalSplit D)
    {p q : D.Spacetime} (h : pushPrecedes C p q) :
    (∃ a, D.realize a = p) ∧ (∃ b, D.realize b = q) := by
  obtain ⟨a, b, ha, hb, _⟩ := h
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩

theorem pushPrecedes_interval_finite {D : DeloneSplit} (C : CausalSplit D)
    (p q : D.Spacetime) :
    ¬ Infinite
      { r : D.Spacetime // pushPrecedes C p r ∧ pushPrecedes C r q } := by
  intro ⟨φ, hφ⟩
  obtain ⟨a, _, ha, _, _⟩ := (φ 0).property.1
  obtain ⟨_, b, _, hb, _⟩ := (φ 0).property.2
  have hmid :
      ∀ k, ∃ c, D.realize c = (φ k).val ∧ C.Rel a c ∧ C.Rel c b := by
    intro k
    obtain ⟨a', c, ha', hc, relac⟩ := (φ k).property.1
    obtain ⟨d, b', hd, hb', relcb⟩ := (φ k).property.2
    have haa : a' = a := D.realize_injective (ha'.trans ha.symm)
    have hbb : b' = b := D.realize_injective (hb'.trans hb.symm)
    have hcd : c = d := D.realize_injective (hc.trans hd.symm)
    subst haa
    subst hbb
    subst hcd
    exact ⟨c, hc, relac, relcb⟩
  let ψ : Nat → { z : D.Carrier // C.Rel a z ∧ C.Rel z b } := fun k =>
    ⟨Classical.choose (hmid k),
      let h := Classical.choose_spec (hmid k)
      ⟨h.2.1, h.2.2⟩⟩
  have hψ : Function.Injective ψ := by
    intro i j hij
    have hi := (Classical.choose_spec (hmid i)).1
    have hj := (Classical.choose_spec (hmid j)).1
    have hcarr : (ψ i).val = (ψ j).val := congrArg Subtype.val hij
    have : (φ i).val = (φ j).val :=
      hi.symm.trans ((congrArg D.realize hcarr).trans hj)
    exact hφ (Subtype.ext this)
  exact C.interval_finite a b ⟨ψ, hψ⟩

/-- A spacetime causal order compatible with a Delone realization:
the carrier order is sampled into the continuum, intervals stay
locally finite, and there are no closed timelike curves. -/
structure CausalMetric {D : DeloneSplit} (C : CausalSplit D) where
  Precedes : D.Spacetime → D.Spacetime → Prop
  irrefl : ∀ p, ¬ Precedes p p
  trans : ∀ {p q r}, Precedes p q → Precedes q r → Precedes p r
  /-- The embedding is a causal isomorphism onto its image. -/
  realize_iff :
    ∀ a b, C.Rel a b ↔ Precedes (D.realize a) (D.realize b)
  interval_finite :
    ∀ p q, ¬ Infinite { r // Precedes p r ∧ Precedes r q }

namespace CausalMetric

variable {D : DeloneSplit} {C : CausalSplit D} (M : CausalMetric C)

theorem asymm {p q : D.Spacetime} (h : M.Precedes p q) :
    ¬ M.Precedes q p :=
  fun hqp => M.irrefl p (M.trans h hqp)

/-- Timelike: comparable in the spacetime order. -/
def Timelike (p q : D.Spacetime) : Prop :=
  M.Precedes p q ∨ M.Precedes q p

/-- Spacelike: incomparable in the spacetime order. -/
def Spacelike (p q : D.Spacetime) : Prop :=
  ¬ M.Precedes p q ∧ ¬ M.Precedes q p

theorem spacelike_comm {p q : D.Spacetime} :
    M.Spacelike p q ↔ M.Spacelike q p := by
  constructor <;> intro h <;> exact ⟨h.2, h.1⟩

/-- A totally ordered finite tuple of carrier events, read in spacetime. -/
def IsChain {n : Nat} (s : Fin n → D.Carrier) : Prop :=
  ∀ i j : Fin n, i.val < j.val → M.Precedes (D.realize (s i)) (D.realize (s j))

theorem chain_iff {n : Nat} (s : Fin n → D.Carrier) :
    C.IsChain s ↔ M.IsChain s := by
  constructor
  · intro hc i j hij
    exact (M.realize_iff (s i) (s j)).mp (hc i j hij)
  · intro hc i j hij
    exact (M.realize_iff (s i) (s j)).mpr (hc i j hij)

/-- A realized screen is spacelike in the continuum, not only on the
carrier. -/
theorem screen_spacelike (S : RealizedScreen C)
    (i j : Fin S.screen.bits) (hne : i ≠ j) :
    M.Spacelike (D.realize (S.events i)) (D.realize (S.events j)) := by
  have h := S.antichain i j hne
  constructor
  · intro hp
    exact h.1 ((M.realize_iff _ _).mpr hp)
  · intro hp
    exact h.2 ((M.realize_iff _ _).mpr hp)

theorem screen_not_chain (S : RealizedScreen C) (hbits : 1 < S.screen.bits) :
    ¬ M.IsChain S.events := by
  intro hc
  exact S.not_a_chain hbits ((M.chain_iff S.events).mpr hc)

end CausalMetric

/-- The canonical spacetime order of a causal Delone split. -/
def CausalMetric.ofSplit {D : DeloneSplit} (C : CausalSplit D) :
    CausalMetric C where
  Precedes := pushPrecedes C
  irrefl := pushPrecedes_irrefl C
  trans := pushPrecedes_trans C
  realize_iff := pushPrecedes_realize_iff C
  interval_finite := pushPrecedes_interval_finite C

/-! ## Standard lift along `embedNat` -/

noncomputable section

/-- Standard spacetime order: carrier precedence sampled into the
continuum. -/
noncomputable def standardCausalMetric : CausalMetric standardCausal :=
  CausalMetric.ofSplit standardCausal

theorem standard_realize_iff (a b : Nat) :
    standardCausal.Rel a b ↔
      standardCausalMetric.Precedes
        (standardDelone.realize a) (standardDelone.realize b) :=
  standardCausalMetric.realize_iff a b

theorem standard_no_ctc (p : Continuum) :
    ¬ standardCausalMetric.Precedes p p :=
  standardCausalMetric.irrefl p

theorem standard_neighbours_spacelike :
    standardCausalMetric.Spacelike
      (standardDelone.realize (0 : Nat))
      (standardDelone.realize (1 : Nat)) := by
  constructor
  · intro h
    have : standardRel 0 1 := (standard_realize_iff 0 1).mpr h
    simp [standardRel] at this
  · intro h
    have : standardRel 1 0 := (standard_realize_iff 1 0).mpr h
    simp [standardRel] at this

theorem pairRealizedScreen_spacelike
    (i j : Fin pairRealizedScreen.screen.bits) (hne : i ≠ j) :
    standardCausalMetric.Spacelike
      (standardDelone.realize (pairRealizedScreen.events i))
      (standardDelone.realize (pairRealizedScreen.events j)) :=
  standardCausalMetric.screen_spacelike pairRealizedScreen i j hne

theorem pairRealizedScreen_not_spacetime_chain :
    ¬ standardCausalMetric.IsChain pairRealizedScreen.events :=
  standardCausalMetric.screen_not_chain pairRealizedScreen (by decide)

theorem standard_interval_finite (p q : Continuum) :
    ¬ Infinite
      { r // standardCausalMetric.Precedes p r ∧
          standardCausalMetric.Precedes r q } :=
  standardCausalMetric.interval_finite p q

end

end ToE
