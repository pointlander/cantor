/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Geometry

/-!
# Black holes and information

A black hole in this formalization is a horizon in a finite diamond.
Its Bekenstein–Hawking entropy is the bit count of the screen:

\[
S = N = A / (4G)
\]

in units \(\hbar = c = k_B = 1\). The interior is the past of that
screen. Interior, screen, Hawking radiation, and any remnant are finite
packets of the countable carrier, so none of them can carry the infinity
of the reals.

Hawking evaporation is not a dynamical law here. It is a partition of a
conserved bit count into remaining hole bits and radiation bits (the
Page curve). Information returns because it was countable and the
diamond is finite. A remnant that stores a continuum of independent
information is impossible.
-/

namespace ToE

/-! ## Finite packets of carrier information -/

/-- A finite collection of distinct carrier events inside a diamond.
This is the common kinematics of a holographic screen, of Hawking
radiation, and of any purported remnant. -/
structure InformationPacket {D : DeloneSplit} {C : CausalSplit D}
    (Δ : CausalDiamond C) where
  bits : Nat
  events : Fin bits → D.Carrier
  events_injective : Function.Injective events
  in_diamond : ∀ i, Δ.mem (events i)

namespace InformationPacket

variable {D : DeloneSplit} {C : CausalSplit D} {Δ : CausalDiamond C}
  (P : InformationPacket Δ)

/-- Holographic area that these bits would occupy as a screen:
\(A = 4 N G\). -/
def area : Rat := (4 : Rat) * (P.bits : Rat) * D.newtonG

theorem area_eq_four_bits_G :
    P.area = (4 : Rat) * (P.bits : Rat) * D.newtonG :=
  rfl

/-- Packet data inject into the countable carrier. -/
theorem injects_into_carrier :
    ∃ f : Fin P.bits → D.Carrier, Function.Injective f :=
  ⟨P.events, P.events_injective⟩

/-- Packet data inject into `Nat`, so they are a QFT resource. -/
theorem injects_into_nat :
    ∃ f : Fin P.bits → Nat, Function.Injective f := by
  obtain ⟨toNat, invFun, hgf, _⟩ := D.countableInfinity
  refine ⟨fun i => toNat (P.events i), ?_⟩
  intro i j hij
  have hinj : Function.Injective toNat := by
    intro x y h
    calc x
        = invFun (toNat x) := (hgf x).symm
      _ = invFun (toNat y) := congrArg invFun h
      _ = y := hgf y
  exact P.events_injective (hinj hij)

/-- A finite packet cannot carry the infinity of the reals. -/
theorem no_real_infinity : ¬ HasRealInfinity (Fin P.bits) := by
  intro h
  obtain ⟨toFun, g, _, hfg⟩ := h
  have hg : Function.Injective g := by
    intro y₁ y₂ hy
    have := congrArg toFun hy
    simpa [hfg] using this
  exact not_injective_nat_fin (g ∘ embedNat) fun i j hij =>
    embedNat_injective (hg hij)

end InformationPacket

/-- The empty packet: no remaining hole, or no radiation yet. -/
def emptyPacket {D : DeloneSplit} {C : CausalSplit D}
    (Δ : CausalDiamond C) : InformationPacket Δ where
  bits := 0
  events := fun i => nomatch i
  events_injective := fun i _ _ => nomatch i
  in_diamond := fun i => nomatch i

/-- The bits of a realized screen, as a packet in a diamond that
contains them. -/
def RealizedScreen.toPacket {D : DeloneSplit} {C : CausalSplit D}
    (S : RealizedScreen C) (Δ : CausalDiamond C)
    (h : ∀ i, Δ.mem (S.events i)) : InformationPacket Δ where
  bits := S.screen.bits
  events := S.events
  events_injective := S.events_injective
  in_diamond := h

/-! ## Bekenstein–Hawking entropy -/

namespace HolographicScreen

variable {D : DeloneSplit} (S : HolographicScreen D)

/-- Bekenstein–Hawking entropy: the number of carrier bits.
In units \(\hbar = c = k_B = 1\), \(S = A / (4G) = N\). -/
def entropy : Nat := S.bits

theorem entropy_eq_bits : S.entropy = S.bits := rfl

/-- The area law as \(A = 4 S G\). -/
theorem area_eq_four_entropy_G :
    S.area = (4 : Rat) * (S.entropy : Rat) * D.newtonG :=
  S.area_eq_four_mul_bits_mul_G

theorem entropy_eq_area_div_four_G :
    (S.entropy : Rat) = S.area / ((4 : Rat) * D.newtonG) := by
  have hden : (4 : Rat) * D.newtonG ≠ 0 :=
    Rat.ne_of_gt (Rat.mul_pos rat_four_pos D.newtonG_pos)
  have h :
      (4 : Rat) * (S.entropy : Rat) * D.newtonG =
        (S.entropy : Rat) * ((4 : Rat) * D.newtonG) := by
    rw [Rat.mul_comm (4 : Rat), Rat.mul_assoc]
  rw [S.area_eq_four_entropy_G, h, Rat.div_def, Rat.mul_assoc,
    Rat.mul_inv_cancel _ hden, Rat.mul_one]

end HolographicScreen

/-! ## Black holes -/

/-- A black hole: a maximal holographic screen in a finite causal
diamond. The interior is the past of the screen; the exterior, from
which radiation can be collected, is the future. -/
structure BlackHole {D : DeloneSplit} {C : CausalSplit D} where
  realized : RealizedScreen C
  diamond : CausalDiamond C
  maximal : Horizon realized diamond

namespace BlackHole

variable {D : DeloneSplit} {C : CausalSplit D} (BH : @BlackHole D C)

/-- Bekenstein–Hawking entropy of the hole: the bit count of the
horizon screen. -/
def entropy : Nat := BH.realized.screen.entropy

def area : Rat := BH.realized.screen.area

theorem entropy_pos : 0 < BH.entropy :=
  BH.realized.screen.bits_pos

theorem area_pos : 0 < BH.area :=
  BH.realized.screen.area_pos

theorem area_law :
    BH.area = (4 : Rat) * (BH.entropy : Rat) * D.newtonG :=
  BH.realized.area_law

theorem entropy_eq_area_div_four_G :
    (BH.entropy : Rat) = BH.area / ((4 : Rat) * D.newtonG) :=
  BH.realized.screen.entropy_eq_area_div_four_G

/-- Event `x` lies on the horizon screen. -/
def OnHorizon (x : D.Carrier) : Prop :=
  RealizedScreen.OnScreen BH.realized x

/-- Interior: in the diamond, strictly in the past of the screen. -/
def Interior (x : D.Carrier) : Prop :=
  InPast BH.realized BH.diamond x

/-- Exterior: in the diamond, strictly in the future of the screen. -/
def Exterior (x : D.Carrier) : Prop :=
  InFuture BH.realized BH.diamond x

theorem interior_in_diamond {x : D.Carrier} (h : BH.Interior x) :
    BH.diamond.mem x :=
  h.1

theorem exterior_in_diamond {x : D.Carrier} (h : BH.Exterior x) :
    BH.diamond.mem x :=
  h.1

theorem onHorizon_not_interior {x : D.Carrier}
    (hon : BH.OnHorizon x) (hp : BH.Interior x) : False :=
  Horizon.onScreen_not_past hon hp.2.1

theorem onHorizon_not_exterior {x : D.Carrier}
    (hon : BH.OnHorizon x) (hf : BH.Exterior x) : False :=
  Horizon.onScreen_not_future hon hf.2.1

theorem interior_not_exterior {x : D.Carrier}
    (hp : BH.Interior x) (hf : BH.Exterior x) : False :=
  Horizon.past_not_future hp.2.1 hf.2.1

/-- The region that contains the interior is finite, so the interior
cannot carry the infinity of the reals. It is not a second,
continuum-sized set of independent degrees of freedom. -/
theorem interior_no_real_infinity :
    ¬ HasRealInfinity (Fin BH.diamond.size) :=
  BH.diamond.not_real_infinity

/-- The horizon screen cannot carry the infinity of the reals. -/
theorem screen_no_real_infinity :
    ¬ HasRealInfinity (Fin BH.realized.screen.bits) :=
  BH.realized.screen.no_real_infinity_on_screen

/-- Horizon bits as a packet in the diamond. -/
def screenPacket : InformationPacket BH.diamond :=
  BH.realized.toPacket BH.diamond BH.maximal.screen_in_diamond

end BlackHole

/-! ## Page curve: conserved bits, returning radiation -/

/-- One stage of Hawking evaporation: the original information is
partitioned into remaining hole bits and radiation bits. Remaining
bits, if any, are still spacelike (an antichain). Evaporation is a
count of bits, not an identification of individual events. -/
structure EvaporationStage {D : DeloneSplit} {C : CausalSplit D}
    (Δ : CausalDiamond C) where
  remaining : InformationPacket Δ
  radiation : InformationPacket Δ
  remaining_antichain :
    ∀ i j : Fin remaining.bits, i ≠ j →
      ¬ C.Rel (remaining.events i) (remaining.events j) ∧
      ¬ C.Rel (remaining.events j) (remaining.events i)
  disjoint :
    ∀ i : Fin remaining.bits, ∀ j : Fin radiation.bits,
      remaining.events i ≠ radiation.events j

namespace EvaporationStage

variable {D : DeloneSplit} {C : CausalSplit D} {Δ : CausalDiamond C}
  (E : EvaporationStage Δ)

/-- Conserved information at this stage: remaining plus radiated. -/
def pageSum : Nat := E.remaining.bits + E.radiation.bits

/-- Hawking radiation is QFT: a finite subset of the countable
carrier, hence not the continuum. -/
theorem radiation_is_qft :
    (∃ f : Fin E.radiation.bits → Nat, Function.Injective f) ∧
    ¬ HasRealInfinity (Fin E.radiation.bits) :=
  ⟨E.radiation.injects_into_nat, E.radiation.no_real_infinity⟩

/-- A remnant is leftover remaining bits, claimed as a store of
information that never returned. It is a finite packet, so it cannot
carry the infinity of the reals. -/
theorem remnant_no_real_infinity :
    ¬ HasRealInfinity (Fin E.remaining.bits) :=
  E.remaining.no_real_infinity

end EvaporationStage

/-- The Page curve of a finite black hole: information starts on the
hole, is split at the Page time, and ends in the radiation. The bit
count is conserved at every stage. -/
structure PageCurve {D : DeloneSplit} {C : CausalSplit D}
    (Δ : CausalDiamond C) where
  totalBits : Nat
  totalBits_pos : 0 < totalBits
  early : EvaporationStage Δ
  middle : EvaporationStage Δ
  late : EvaporationStage Δ
  early_sum : early.pageSum = totalBits
  middle_sum : middle.pageSum = totalBits
  late_sum : late.pageSum = totalBits
  starts_on_hole :
    early.remaining.bits = totalBits ∧ early.radiation.bits = 0
  page_turn :
    0 < middle.remaining.bits ∧ 0 < middle.radiation.bits
  ends_in_radiation :
    late.remaining.bits = 0 ∧ late.radiation.bits = totalBits

namespace PageCurve

variable {D : DeloneSplit} {C : CausalSplit D} {Δ : CausalDiamond C}
  (P : PageCurve Δ)

/-- Complete evaporation leaves no remnant bits. -/
theorem no_remnant : P.late.remaining.bits = 0 :=
  P.ends_in_radiation.1

/-- Information has returned: the radiation carries the original
bit count. -/
theorem information_returns : P.late.radiation.bits = P.totalBits :=
  P.ends_in_radiation.2

/-- A remnant after complete evaporation cannot carry the continuum:
there are no remnant bits at all, and `Fin 0` is not equinumerous with
the reals. -/
theorem no_continuum_remnant :
    ¬ HasRealInfinity (Fin P.late.remaining.bits) :=
  P.late.remnant_no_real_infinity

/-- Late radiation is still a finite QFT packet, not a continuum of
independent modes. -/
theorem late_radiation_no_real_infinity :
    ¬ HasRealInfinity (Fin P.late.radiation.bits) :=
  P.late.radiation.no_real_infinity

end PageCurve

/-! ## Standard black hole on `{0,…,6}` -/

noncomputable section

/-- The standard two-bit hole: mid-slice `{2,3}` in the diamond
`{0,…,6}`. Entropy `2`, area `8`, \(G = 1\). -/
noncomputable def standardBlackHole : @BlackHole standardDelone standardCausal where
  realized := midRealizedScreen
  diamond := standardDiamond
  maximal := standardHorizon

theorem standardBlackHole_entropy : standardBlackHole.entropy = 2 := rfl

theorem standardBlackHole_area_law :
    standardBlackHole.area =
      (4 : Rat) * (standardBlackHole.entropy : Rat) *
        standardDelone.newtonG :=
  standardBlackHole.area_law

theorem standardBlackHole_has_interior :
    standardBlackHole.Interior (0 : Nat) :=
  standardHorizon_has_past

theorem standardBlackHole_has_exterior :
    standardBlackHole.Exterior (4 : Nat) :=
  standardHorizon_has_future

/-- Interior events `{0,1}` of the standard hole. -/
noncomputable def standardInterior : InformationPacket standardDiamond where
  bits := 2
  events := fun i => i.val
  events_injective := fun i j h => Fin.ext h
  in_diamond := by
    intro i
    refine ⟨⟨i.val, Nat.lt_trans i.isLt (by decide)⟩, rfl⟩

theorem standardInterior_one :
    standardBlackHole.Interior (1 : Nat) := by
  refine ⟨⟨⟨1, by decide⟩, rfl⟩, ⟨⟨1, by decide⟩, ?_⟩, ?_⟩
  · change standardRel (1 : Nat) (midRealizedScreen.events ⟨1, by decide⟩)
    simp [midRealizedScreen, standardCausal, standardRel]
  · intro ⟨j, hj⟩
    have hbits : midRealizedScreen.screen.bits = 2 := rfl
    have hj' : j.val < 2 := Nat.lt_of_lt_of_eq j.isLt hbits
    have : j.val + 2 = (1 : Nat) := hj
    omega

theorem standardInterior_is_interior
    (i : Fin standardInterior.bits) :
    standardBlackHole.Interior (standardInterior.events i) := by
  have hI : standardInterior.bits = 2 := rfl
  have hi : i.val < 2 := Nat.lt_of_lt_of_eq i.isLt hI
  have hev : standardInterior.events i = i.val := rfl
  rw [hev]
  match h : i.val with
  | 0 => exact standardBlackHole_has_interior
  | 1 => exact standardInterior_one
  | n + 2 => omega

theorem standardInterior_no_real_infinity :
    ¬ HasRealInfinity (Fin standardInterior.bits) :=
  standardInterior.no_real_infinity

/-- Remaining one-bit screen `{3}` after the first bit has radiated. -/
noncomputable def leftoverScreen : RealizedScreen standardCausal where
  screen := standardScreen
  events := fun _ => (3 : Nat)
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

theorem leftover_in_diamond (i : Fin leftoverScreen.screen.bits) :
    standardDiamond.mem (leftoverScreen.events i) :=
  ⟨⟨3, by decide⟩, rfl⟩

/-- One quantum of Hawking radiation at event `4`, in the exterior. -/
noncomputable def firstRadiation : InformationPacket standardDiamond where
  bits := 1
  events := fun _ => (4 : Nat)
  events_injective := by
    intro i j _
    have hi : i.val = 0 := Nat.lt_one_iff.mp i.isLt
    have hj : j.val = 0 := Nat.lt_one_iff.mp j.isLt
    exact Fin.ext (hi.trans hj.symm)
  in_diamond := fun _ => ⟨⟨4, by decide⟩, rfl⟩

/-- Late radiation `{4,5}`: both bits have left the hole. -/
noncomputable def lateRadiation : InformationPacket standardDiamond where
  bits := 2
  events := fun i => i.val + 4
  events_injective := by
    intro i j h
    have : i.val + 4 = j.val + 4 := h
    exact Fin.ext (by omega)
  in_diamond := by
    intro i
    have hsz : standardDiamond.size = 7 := rfl
    have hi : i.val < 2 := i.isLt
    refine ⟨⟨i.val + 4, by omega⟩, rfl⟩

/-- Early Page stage: two bits on the hole, no radiation. -/
noncomputable def pageEarly : EvaporationStage standardDiamond where
  remaining :=
    midRealizedScreen.toPacket standardDiamond
      standardHorizon.screen_in_diamond
  radiation := emptyPacket standardDiamond
  remaining_antichain := midRealizedScreen.antichain
  disjoint := fun _ j => nomatch j

/-- Page time: one bit still on the hole, one bit in the radiation. -/
noncomputable def pageMiddle : EvaporationStage standardDiamond where
  remaining := leftoverScreen.toPacket standardDiamond leftover_in_diamond
  radiation := firstRadiation
  remaining_antichain := leftoverScreen.antichain
  disjoint := by
    intro i j h
    simp [leftoverScreen, firstRadiation, RealizedScreen.toPacket] at h
    exact (by decide : ¬ ((3 : Nat) = 4)) h

/-- Late Page stage: no remaining hole, two bits in the radiation. -/
noncomputable def pageLate : EvaporationStage standardDiamond where
  remaining := emptyPacket standardDiamond
  radiation := lateRadiation
  remaining_antichain := fun i _ _ => nomatch i
  disjoint := fun i _ => nomatch i

/-- Standard Page curve of the two-bit hole. The conserved total is
the original entropy. Remaining area drops `8 → 4 → 0` while radiation
area rises `0 → 4 → 8`. -/
noncomputable def standardPage : PageCurve standardDiamond where
  totalBits := 2
  totalBits_pos := by decide
  early := pageEarly
  middle := pageMiddle
  late := pageLate
  early_sum := rfl
  middle_sum := rfl
  late_sum := rfl
  starts_on_hole := ⟨rfl, rfl⟩
  page_turn := ⟨Nat.succ_pos 0, Nat.succ_pos 0⟩
  ends_in_radiation := ⟨rfl, rfl⟩

theorem page_conserves_entropy :
    standardBlackHole.entropy = standardPage.totalBits :=
  rfl

theorem pageEarly_remaining_eq_horizon :
    pageEarly.remaining.events = midRealizedScreen.events :=
  rfl

theorem pageMiddle_radiation_exterior :
    standardBlackHole.Exterior (firstRadiation.events ⟨0, by decide⟩) :=
  standardHorizon_has_future

theorem pageLate_radiation_five :
    standardBlackHole.Exterior (5 : Nat) := by
  refine ⟨⟨⟨5, by decide⟩, rfl⟩, ⟨⟨1, by decide⟩, ?_⟩, ?_⟩
  · change standardRel (midRealizedScreen.events ⟨1, by decide⟩) (5 : Nat)
    simp [midRealizedScreen, standardCausal, standardRel]
  · intro ⟨j, hj⟩
    have hbits : midRealizedScreen.screen.bits = 2 := rfl
    have hj' : j.val < 2 := Nat.lt_of_lt_of_eq j.isLt hbits
    have : j.val + 2 = (5 : Nat) := hj
    omega

theorem pageLate_radiation_exterior (i : Fin lateRadiation.bits) :
    standardBlackHole.Exterior (lateRadiation.events i) := by
  have hR : lateRadiation.bits = 2 := rfl
  have hi : i.val < 2 := Nat.lt_of_lt_of_eq i.isLt hR
  have hev : lateRadiation.events i = i.val + 4 := rfl
  rw [hev]
  match h : i.val with
  | 0 => exact standardBlackHole_has_exterior
  | 1 => exact pageLate_radiation_five
  | n + 2 => omega

theorem pageEarly_remaining_area :
    pageEarly.remaining.area = (8 : Rat) := by
  change (4 : Rat) * ((2 : Nat) : Rat) *
      (standardDelone.gap * standardDelone.gap) = 8
  change (4 : Rat) * ((2 : Nat) : Rat) * (1 * 1) = 8
  rw [Rat.one_mul, Rat.mul_one]
  have h4 : (4 : Rat) = ((4 : Nat) : Rat) := rfl
  have h8 : (8 : Rat) = ((8 : Nat) : Rat) := rfl
  rw [h4, h8, ← Rat.natCast_mul]

theorem pageMiddle_remaining_area :
    pageMiddle.remaining.area = (4 : Rat) := by
  change (4 : Rat) * ((1 : Nat) : Rat) *
      (standardDelone.gap * standardDelone.gap) = 4
  change (4 : Rat) * ((1 : Nat) : Rat) * (1 * 1) = 4
  rw [Rat.one_mul, Rat.mul_one]
  have h1 : ((1 : Nat) : Rat) = (1 : Rat) := rfl
  rw [h1, Rat.mul_one]

theorem pageLate_remaining_area :
    pageLate.remaining.area = (0 : Rat) := by
  change (4 : Rat) * ((0 : Nat) : Rat) *
      (standardDelone.gap * standardDelone.gap) = 0
  change (4 : Rat) * ((0 : Nat) : Rat) * (1 * 1) = 0
  rw [Rat.one_mul, Rat.mul_one]
  have h0 : ((0 : Nat) : Rat) = (0 : Rat) := rfl
  rw [h0, Rat.mul_zero]

theorem pageLate_radiation_area :
    pageLate.radiation.area = (8 : Rat) := by
  change (4 : Rat) * ((2 : Nat) : Rat) *
      (standardDelone.gap * standardDelone.gap) = 8
  change (4 : Rat) * ((2 : Nat) : Rat) * (1 * 1) = 8
  rw [Rat.one_mul, Rat.mul_one]
  have h4 : (4 : Rat) = ((4 : Nat) : Rat) := rfl
  have h8 : (8 : Rat) = ((8 : Nat) : Rat) := rfl
  rw [h4, h8, ← Rat.natCast_mul]

theorem standardPage_no_continuum_remnant :
    ¬ HasRealInfinity (Fin standardPage.late.remaining.bits) :=
  standardPage.no_continuum_remnant

end

end ToE
