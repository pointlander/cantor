/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

/-!
# The two infinities

The countable numbers `Nat` and the continuum `Nat → Bool` (equinumerous with
the reals) are both infinite, but they are not equinumerous.  Cantor's
diagonal argument is the engine of the cosmological split in this theory:
once the power object of the countable carrier appears, it cannot be
identified with that carrier.
-/

namespace ToE

/-- Two types have the same infinity when there are mutually inverse maps
between them. -/
def Equinumerous (α β : Type) : Prop :=
  ∃ (toFun : α → β) (invFun : β → α),
    (∀ x, invFun (toFun x) = x) ∧ (∀ y, toFun (invFun y) = y)

@[refl] theorem Equinumerous.refl (α : Type) : Equinumerous α α :=
  ⟨id, id, fun _ => rfl, fun _ => rfl⟩

theorem Equinumerous.symm {α β : Type} :
    Equinumerous α β → Equinumerous β α := by
  rintro ⟨f, g, hgf, hfg⟩
  exact ⟨g, f, hfg, hgf⟩

theorem Equinumerous.trans {α β γ : Type} :
    Equinumerous α β → Equinumerous β γ → Equinumerous α γ := by
  rintro ⟨f, g, hgf, hfg⟩ ⟨f', g', hg'f', hf'g'⟩
  refine ⟨f' ∘ f, g ∘ g', ?_, ?_⟩
  · intro x
    calc (g ∘ g') ((f' ∘ f) x)
        = g (g' (f' (f x))) := rfl
      _ = g (f x) := by rw [hg'f']
      _ = x := hgf x
  · intro z
    calc (f' ∘ f) ((g ∘ g') z)
        = f' (f (g (g' z))) := rfl
      _ = f' (g' z) := by rw [hfg]
      _ = z := hf'g' z

/-- Transport of function-spaces into `Bool` along an equinumerosity.
If `α ≃ β` then `α → Bool ≃ β → Bool`.  This is how the continuum is
inherited from a countable carrier. -/
theorem equinumerous_arrow_bool {α β : Type}
    (h : Equinumerous α β) : Equinumerous (α → Bool) (β → Bool) := by
  obtain ⟨f, g, hgf, hfg⟩ := h
  refine ⟨fun u : α → Bool => u ∘ g, fun v : β → Bool => v ∘ f, ?_, ?_⟩
  · intro u
    funext x
    change u (g (f x)) = u x
    rw [hgf]
  · intro v
    funext y
    change v (f (g y)) = v y
    rw [hfg]

/-- The Cantor space.  Classically this is equinumerous with `ℝ`
(binary expansions, up to a countable set of dyadic identifications,
which do not change the cardinality).  We take it as the canonical
representative of **the infinity of the reals**. -/
abbrev Continuum : Type := Nat → Bool

/-- A type has **the infinity of the countable numbers** when it is
equinumerous with `Nat`. -/
def HasCountableInfinity (α : Type) : Prop := Equinumerous α Nat

/-- A type has **the infinity of the reals** when it is equinumerous
with the continuum. -/
def HasRealInfinity (α : Type) : Prop := Equinumerous α Continuum

theorem nat_has_countable_infinity : HasCountableInfinity Nat :=
  Equinumerous.refl Nat

theorem continuum_has_real_infinity : HasRealInfinity Continuum :=
  Equinumerous.refl Continuum

/-- The diagonal point of a putative enumeration of the continuum. -/
def diagonal (f : Nat → Continuum) : Continuum :=
  fun n => !(f n n)

theorem ne_not_self : ∀ b : Bool, b ≠ !b
  | true => by decide
  | false => by decide

/-- Cantor's diagonal argument: nothing countable can enumerate the
continuum. -/
theorem no_surjection_nat_continuum (f : Nat → Continuum) :
    ¬ Function.Surjective f := by
  intro hf
  obtain ⟨n, hn⟩ := hf (diagonal f)
  have h1 : f n n = diagonal f n := congrFun hn n
  have h2 : diagonal f n = !(f n n) := rfl
  exact (ne_not_self (f n n)) (h1.trans h2)

/-- The two infinities are distinct: there is no identification of the
countable numbers with the reals. -/
theorem not_equinumerous_nat_continuum : ¬ Equinumerous Nat Continuum := by
  rintro ⟨f, g, _, hfg⟩
  exact no_surjection_nat_continuum f (fun y => ⟨g y, hfg y⟩)

theorem countable_infinity_ne_real_infinity {α : Type} :
    HasCountableInfinity α → HasRealInfinity α → False := by
  intro hc hr
  exact not_equinumerous_nat_continuum
    (hc.symm.trans hr)

/-- The countable numbers embed in the continuum (the standard basis
vectors).  Both infinities are infinite; one is strictly larger. -/
def embedNat : Nat → Continuum :=
  fun n k => decide (n = k)

theorem embedNat_injective : Function.Injective embedNat := by
  intro n m h
  have : embedNat n n = embedNat m n := congrFun h n
  simp [embedNat] at this
  exact this.symm

/-- A type is (Dedekind) infinite when the countable numbers embed in it. -/
def Infinite (α : Type) : Prop :=
  ∃ f : Nat → α, Function.Injective f

theorem infinite_nat : Infinite Nat :=
  ⟨id, fun _ _ h => h⟩

theorem infinite_continuum : Infinite Continuum :=
  ⟨embedNat, embedNat_injective⟩

end ToE
