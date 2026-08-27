/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Cosmology
import ToE.Geometry

/-!
# Sequential growth

Cosmic time is not only an epoch tag. After the origin the realized
region of the countable carrier grows: a nested sequence of finite
causal diamonds. Time zero is a first instant. Every later diamond is
larger, still finite, and still unable to carry the infinity of the
reals. The split does not change kind — QFT stays countable, GR stays
continuum — what grows is the sample of the carrier.

This is kinematic sequential growth, not a probability on births.
-/

namespace ToE

/-- Diamond `Δ` is a subregion of `Δ'`. -/
def CausalDiamond.subset {D : DeloneSplit} {C : CausalSplit D}
    (Δ Δ' : CausalDiamond C) : Prop :=
  ∀ x, Δ.mem x → Δ'.mem x

/-- A growing causal set indexed by cosmic time: nested finite diamonds
whose size at time `n` is `n + 1`. -/
structure SequentialGrowth {D : DeloneSplit} (C : CausalSplit D) where
  region : Time → CausalDiamond C
  nested : ∀ n, (region n).subset (region (n + 1))
  size_eq : ∀ n, (region n).size = n + 1

namespace SequentialGrowth

variable {D : DeloneSplit} {C : CausalSplit D} (G : SequentialGrowth C)

theorem origin_size : (G.region 0).size = 1 :=
  G.size_eq 0

theorem origin_size_pos : 0 < (G.region 0).size :=
  (G.region 0).size_pos

/-- The region at time `n` is finite, hence not the continuum. -/
theorem region_not_real_infinity (n : Time) :
    ¬ HasRealInfinity (Fin (G.region n).size) :=
  (G.region n).not_real_infinity

end SequentialGrowth

/-! ## Standard prefixes `{0,…,n}` -/

noncomputable section

/-- The standard diamond of the first `n + 1` carrier events. -/
noncomputable def prefixDiamond (n : Time) : CausalDiamond standardCausal where
  size := n + 1
  size_pos := Nat.succ_pos n
  points := fun i => i.val
  points_injective := fun _ _ h => Fin.ext h

theorem prefixDiamond_mem {n x : Nat} :
    (prefixDiamond n).mem x ↔ x < n + 1 := by
  constructor
  · intro ⟨i, hi⟩
    have hlt : i.val < n + 1 := i.isLt
    have : x = i.val := hi.symm
    omega
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

theorem prefixDiamond_nested (n : Time) :
    (prefixDiamond n).subset (prefixDiamond (n + 1)) := by
  intro x hx
  obtain ⟨i, hi⟩ := hx
  refine ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, hi⟩

theorem prefixDiamond_size (n : Time) : (prefixDiamond n).size = n + 1 := rfl

/-- The standard growing universe: at time `n` the events `{0,…,n}`. -/
noncomputable def standardGrowth : SequentialGrowth standardCausal where
  region := prefixDiamond
  nested := prefixDiamond_nested
  size_eq := prefixDiamond_size

theorem standardGrowth_origin :
    (standardGrowth.region 0).size = 1 :=
  standardGrowth.origin_size

theorem standardGrowth_origin_event :
    (standardGrowth.region 0).mem (0 : Nat) :=
  prefixDiamond_mem.mpr (by decide)

theorem standardGrowth_origin_only (x : Nat) :
    (standardGrowth.region 0).mem x ↔ x = 0 := by
  constructor
  · intro h
    have : x < 1 := prefixDiamond_mem.mp h
    omega
  · intro h
    subst h
    exact standardGrowth_origin_event

/-- The origin is a first instant: it is finite and not Dedekind infinite. -/
theorem standardGrowth_origin_not_infinite :
    ¬ Infinite (Fin (standardGrowth.region 0).size) := by
  intro ⟨φ, hφ⟩
  have h0 : (φ 0).val = 0 := Nat.lt_one_iff.mp (Nat.lt_of_lt_of_eq (φ 0).isLt (by
    have : (standardGrowth.region 0).size = 1 := rfl
    simp [this]))
  have h1 : (φ 1).val = 0 := Nat.lt_one_iff.mp (Nat.lt_of_lt_of_eq (φ 1).isLt (by
    have : (standardGrowth.region 0).size = 1 := rfl
    simp [this]))
  exact Nat.zero_ne_one (hφ (Fin.ext (h0.trans h1.symm)))

theorem standardGrowth_not_real (n : Time) :
    ¬ HasRealInfinity (Fin (standardGrowth.region n).size) :=
  standardGrowth.region_not_real_infinity n

/-- If `b` is already in the region and `a` precedes `b`, then `a` is
already in the region: the growing sample is causally downward-closed. -/
theorem prefixDiamond_past_closed {n a b : Nat}
    (hb : (prefixDiamond n).mem b) (hrel : standardRel a b) :
    (prefixDiamond n).mem a := by
  have hb' : b < n + 1 := prefixDiamond_mem.mp hb
  have : a + 2 ≤ b := hrel
  exact prefixDiamond_mem.mpr (by omega)

/-- There is no infinite past before a finite time: a predecessor of a
region event is still in that finite diamond. -/
theorem prefixDiamond_no_infinite_past {n a b : Nat}
    (hb : (prefixDiamond n).mem b) (hrel : standardRel a b) :
    (prefixDiamond n).mem a ∧
      ¬ HasRealInfinity (Fin (prefixDiamond n).size) :=
  ⟨prefixDiamond_past_closed hb hrel, (prefixDiamond n).not_real_infinity⟩

/-- The two-bit screen `{0,1}` is not present at the origin and is
present at time `1`. -/
theorem pair_screen_after_origin :
    ¬ (standardGrowth.region 0).mem (1 : Nat) ∧
    (standardGrowth.region 1).mem (0 : Nat) ∧
    (standardGrowth.region 1).mem (1 : Nat) := by
  refine ⟨?_, prefixDiamond_mem.mpr (by decide), prefixDiamond_mem.mpr (by decide)⟩
  intro h
  have : 1 < 1 := prefixDiamond_mem.mp h
  exact Nat.lt_irrefl _ this

theorem standardGrowth_nested (n : Time) :
    (standardGrowth.region n).subset (standardGrowth.region (n + 1)) :=
  standardGrowth.nested n

theorem standardGrowth_size (n : Time) :
    (standardGrowth.region n).size = n + 1 :=
  standardGrowth.size_eq n

end

end ToE
