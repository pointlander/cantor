/-
Copyright (c) 2026 G. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: G
-/

import ToE.Physics

/-!
# Separable Fock space

After the split, QFT is a countable mode set together with its Fock
space: finite-support occupation numbers. That space is equinumerous
with `ℕ`. Unrestricted occupations of even a countable mode set are
already not countable — they hide a copy of the continuum. A continuum
of independent modes is the wrong kinematics: the one-particle sector
would carry the infinity of the reals.

Continuum labels belong to GR, not to matter.
-/

namespace ToE

/-! ## Pairing on `Nat` -/

/-- \( (a,b) \mapsto 2^a(2b+1)-1 \). Injective encoding of pairs. -/
def pair2 (a b : Nat) : Nat := 2 ^ a * (2 * b + 1) - 1

theorem two_pow_pos (a : Nat) : 0 < 2 ^ a := by
  induction a with
  | zero => decide
  | succ a ih =>
    rw [Nat.pow_succ]
    omega

theorem pair2_prod_pos (a b : Nat) : 0 < 2 ^ a * (2 * b + 1) :=
  Nat.mul_pos (two_pow_pos a) (by omega)

theorem two_pow_succ_even (a : Nat) : (2 ^ (a + 1)) % 2 = 0 := by
  rw [Nat.pow_succ, Nat.mul_mod]
  simp

theorem two_pow_mul_odd_eq {a c oddA oddC : Nat}
    (hoA : oddA % 2 = 1) (hoC : oddC % 2 = 1)
    (h : 2 ^ a * oddA = 2 ^ c * oddC) : a = c ∧ oddA = oddC := by
  induction a generalizing c with
  | zero =>
    cases c with
    | zero =>
      simp at h
      exact ⟨rfl, h⟩
    | succ c =>
      have hL : (oddA) % 2 = 1 := hoA
      have hR : (2 ^ (c + 1) * oddC) % 2 = 0 := by
        have : (2 ^ (c + 1)) % 2 = 0 := two_pow_succ_even c
        rw [Nat.mul_mod, this]
        simp
      have : oddA = 2 ^ (c + 1) * oddC := by simpa using h
      rw [this] at hL
      simp [hR] at hL
  | succ a ih =>
    cases c with
    | zero =>
      have hL : (2 ^ (a + 1) * oddA) % 2 = 0 := by
        have : (2 ^ (a + 1)) % 2 = 0 := two_pow_succ_even a
        rw [Nat.mul_mod, this]
        simp
      have : 2 ^ (a + 1) * oddA = oddC := by simpa using h
      rw [this] at hL
      simp [hoC] at hL
    | succ c =>
      have hdiv : 2 ^ a * oddA = 2 ^ c * oddC := by
        have h2 : 2 ^ (a + 1) * oddA = 2 * (2 ^ a * oddA) := by
          rw [Nat.pow_succ]
          ac_rfl
        have h2' : 2 ^ (c + 1) * oddC = 2 * (2 ^ c * oddC) := by
          rw [Nat.pow_succ]
          ac_rfl
        have := h
        rw [h2, h2'] at this
        exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) this
      have ⟨hac, hodd⟩ := ih hdiv
      exact ⟨by omega, hodd⟩

theorem pair2_inj {a b c d : Nat} (h : pair2 a b = pair2 c d) :
    a = c ∧ b = d := by
  have hp := pair2_prod_pos a b
  have hq := pair2_prod_pos c d
  have hp1 : 1 ≤ 2 ^ a * (2 * b + 1) := Nat.succ_le_of_lt hp
  have hq1 : 1 ≤ 2 ^ c * (2 * d + 1) := Nat.succ_le_of_lt hq
  have hprod : 2 ^ a * (2 * b + 1) = 2 ^ c * (2 * d + 1) := by
    have := congrArg (fun n => n + 1) h
    simp only [pair2] at this
    rw [Nat.sub_add_cancel hp1, Nat.sub_add_cancel hq1] at this
    exact this
  have hoddp : (2 * b + 1) % 2 = 1 := by omega
  have hoddq : (2 * d + 1) % 2 = 1 := by omega
  have ⟨ha, hb⟩ := two_pow_mul_odd_eq hoddp hoddq hprod
  exact ⟨ha, by omega⟩

/-! ## Schroeder–Bernstein -/

noncomputable section SchroederBernstein
open Classical

variable {α β : Type}

/-- Elements of `α` reached from the complement of `range g` by iterating
`g ∘ f`. -/
inductive SBChain (f : α → β) (g : β → α) : α → Prop where
  | missing {x : α} : (∀ y, g y ≠ x) → SBChain f g x
  | next {x : α} : SBChain f g x → SBChain f g (g (f x))

theorem not_chain_in_range {f : α → β} {g : β → α} {x : α}
    (h : ¬ SBChain f g x) : ∃ y, g y = x :=
  (Classical.em (∃ y, g y = x)).elim id
    (fun hx => (h (SBChain.missing fun y hy => hx ⟨y, hy⟩)).elim)

noncomputable def sbTo (f : α → β) (g : β → α) (x : α) : β :=
  if h : SBChain f g x then f x
  else Classical.choose (not_chain_in_range h)

noncomputable def sbFrom (f : α → β) (g : β → α) (y : β) : α :=
  if h : ∃ x, SBChain f g x ∧ f x = y then Classical.choose h
  else g y

theorem sbTo_sbFrom {f : α → β} {g : β → α}
    (_hf : Function.Injective f) (hg : Function.Injective g) (y : β) :
    sbTo f g (sbFrom f g y) = y := by
  unfold sbFrom
  split
  · rename_i h
    have hx := Classical.choose_spec h
    unfold sbTo
    simp [hx.1]
    exact hx.2
  · rename_i hnone
    unfold sbTo
    have hnot : ¬ SBChain f g (g y) := by
      intro hc
      generalize hz : g y = z
      rw [hz] at hc
      induction hc generalizing y with
      | missing hm =>
        subst hz
        exact hm y rfl
      | next hx _ =>
        exact hnone ⟨_, hx, hg hz.symm⟩
    simp [hnot]
    exact hg (Classical.choose_spec (not_chain_in_range hnot))

theorem sbFrom_sbTo {f : α → β} {g : β → α}
    (hf : Function.Injective f) (x : α) :
    sbFrom f g (sbTo f g x) = x := by
  unfold sbTo
  split
  · rename_i hchain
    unfold sbFrom
    have hex : ∃ z, SBChain f g z ∧ f z = f x := ⟨x, hchain, rfl⟩
    simp [hex]
    have hspec := Classical.choose_spec hex
    exact hf hspec.2
  · rename_i hnot
    have hy := Classical.choose_spec (not_chain_in_range hnot)
    unfold sbFrom
    have hnone :
        ¬ ∃ z, SBChain f g z ∧
            f z = Classical.choose (not_chain_in_range hnot) := by
      intro ⟨z, hz, hfz⟩
      have hxg : g (f z) = x := by
        rw [hfz, hy]
      have : SBChain f g x := hxg ▸ SBChain.next hz
      exact hnot this
    simp [hnone]
    exact hy

/-- Two injections yield a bijection. -/
theorem Equinumerous.of_injections {α β : Type}
    (f : α → β) (g : β → α)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Equinumerous α β :=
  ⟨sbTo f g, sbFrom f g, sbFrom_sbTo hf, sbTo_sbFrom hf hg⟩

end SchroederBernstein

/-! ## Finite-support occupation numbers -/

/-- A mode occupation that vanishes after some index. -/
def EventuallyZero (f : Nat → Nat) : Prop :=
  ∃ N, ∀ k, N ≤ k → f k = 0

/-- The Fock space of a countable mode set labelled by `Nat`: finitely
many occupied modes, the rest vacuum. -/
abbrev FockNat : Type := { f : Nat → Nat // EventuallyZero f }

/-- Occupations of an arbitrary mode set, with Dedekind-finite support. -/
def FiniteSupport {α : Type} (f : α → Nat) : Prop :=
  ¬ Infinite { x : α // f x ≠ 0 }

def Occupations (α : Type) : Type :=
  { f : α → Nat // FiniteSupport f }

/-- The Fock space of any QFT: its modes enumerate to `Nat`, so the
states are `FockNat`. -/
def QuantumFieldTheory.fock (_Q : QuantumFieldTheory) : Type := FockNat

namespace FockNat

/-- The vacuum: every mode empty. -/
def vacuum : FockNat :=
  ⟨fun _ => 0, ⟨0, fun _ _ => rfl⟩⟩

theorem vacuum_occ (n : Nat) : vacuum.val n = 0 := rfl

/-- One particle in mode `n`. -/
def basis (n : Nat) : FockNat :=
  ⟨fun k => if k = n then 1 else 0, ⟨n + 1, by
    intro k hk
    simp
    omega⟩⟩

theorem basis_at (n : Nat) : (basis n).val n = 1 := by
  simp [basis]

theorem basis_injective : Function.Injective basis := by
  intro n m h
  have hn : (basis n).val n = (basis m).val n :=
    congrArg Subtype.val h ▸ rfl
  simp [basis] at hn
  exact hn

/-- Two occupation units: modes `n` and `m` (doubled if `n = m`). -/
def twoParticle (n m : Nat) : FockNat :=
  ⟨fun k =>
    (if k = n then 1 else 0) + (if k = m then 1 else 0),
    ⟨Nat.max n m + 1, by
      intro k hk
      have hnle : n ≤ Nat.max n m := Nat.le_max_left n m
      have hmle : m ≤ Nat.max n m := Nat.le_max_right n m
      simp
      omega⟩⟩

end FockNat

/-! ## Encoding lists, hence an injection `FockNat → Nat` -/

def encodeList : List Nat → Nat
  | [] => 0
  | x :: xs => pair2 x (encodeList xs) + 1

theorem encodeList_injective : Function.Injective encodeList := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons _ _ =>
      simp [encodeList] at h
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil =>
      simp [encodeList] at h
    | cons y ys =>
      have hpair : pair2 x (encodeList xs) = pair2 y (encodeList ys) := by
        simp [encodeList] at h
        omega
      have ⟨hx, hxs⟩ := pair2_inj hpair
      subst hx
      exact congrArg (List.cons x) (ih hxs)

def isBound (f : Nat → Nat) (N : Nat) : Prop :=
  ∀ k, N ≤ k → f k = 0

def trim (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | N + 1 => if f N = 0 then trim f N else N + 1

theorem trim_bound {f : Nat → Nat} :
    ∀ {N}, isBound f N → isBound f (trim f N)
  | 0, h => h
  | N + 1, h => by
    simp only [trim]
    split
    · rename_i hz
      refine trim_bound (N := N) ?_
      intro k hk
      cases Nat.lt_or_ge k (N + 1) with
      | inl hlt =>
        have : k = N := Nat.eq_of_le_of_lt_succ hk hlt
        subst this
        exact hz
      | inr hge =>
        exact h k hge
    · exact h

theorem isBound_of_succ_zero {f : Nat → Nat} {N : Nat}
    (hN : isBound f (N + 1)) (hz : f N = 0) : isBound f N := by
  intro k hk
  cases Nat.eq_or_lt_of_le hk with
  | inl he =>
    subst he
    exact hz
  | inr hlt =>
    exact hN k (Nat.succ_le_of_lt hlt)

theorem trim_least {f : Nat → Nat} :
    ∀ {N}, isBound f N → ∀ M, isBound f M → trim f N ≤ M
  | 0, _, M, _ => Nat.zero_le M
  | N + 1, hN, M, hM => by
    simp only [trim]
    split
    · rename_i hz
      exact trim_least (isBound_of_succ_zero hN hz) M hM
    · rename_i hne
      have : ¬ M ≤ N := by
        intro hMN
        exact hne (hM N hMN)
      omega

def prefixList (f : Nat → Nat) : Nat → List Nat
  | 0 => []
  | N + 1 => prefixList f N ++ [f N]

theorem prefixList_length (f : Nat → Nat) :
    ∀ N, (prefixList f N).length = N
  | 0 => rfl
  | N + 1 => by simp [prefixList, prefixList_length f N]

theorem prefixList_ext {f g : Nat → Nat} :
    ∀ {N}, prefixList f N = prefixList g N → ∀ i, i < N → f i = g i
  | 0, _, i, hi => by omega
  | N + 1, h, i, hi => by
    simp [prefixList] at h
    obtain ⟨hp, hlast⟩ := h
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with
    | inl hlt =>
      exact prefixList_ext hp i hlt
    | inr he =>
      subst he
      exact hlast

noncomputable def toList (f : FockNat) : List Nat :=
  let N := Classical.choose f.property
  prefixList f.val (trim f.val N)

noncomputable def encodeFock (f : FockNat) : Nat :=
  encodeList (toList f)

theorem toList_bound (f : FockNat) :
    isBound f.val (toList f).length := by
  dsimp [toList]
  have hN : isBound f.val (Classical.choose f.property) :=
    Classical.choose_spec f.property
  have hT := trim_bound hN
  simpa [prefixList_length] using hT

theorem toList_least (f : FockNat) {M : Nat} (hM : isBound f.val M) :
    (toList f).length ≤ M := by
  dsimp [toList]
  have hN : isBound f.val (Classical.choose f.property) :=
    Classical.choose_spec f.property
  simpa [prefixList_length] using trim_least hN M hM

theorem toList_prefix (f : FockNat) :
    toList f = prefixList f.1 (toList f).length := by
  unfold toList
  simp [prefixList_length]

theorem encodeFock_injective : Function.Injective encodeFock := by
  intro f g h
  have hl : toList f = toList g := encodeList_injective h
  have hlen : (toList f).length = (toList g).length := congrArg List.length hl
  apply Subtype.ext
  funext k
  have hfB : isBound f.val (toList f).length := toList_bound f
  have hgB : isBound g.val (toList g).length := toList_bound g
  cases Nat.lt_or_ge k (toList f).length with
  | inl hlt =>
    have hpre : prefixList f.1 (toList f).length =
        prefixList g.1 (toList f).length := by
      calc prefixList f.1 (toList f).length
          = toList f := (toList_prefix f).symm
        _ = toList g := hl
        _ = prefixList g.1 (toList g).length := toList_prefix g
        _ = prefixList g.1 (toList f).length := by rw [hlen]
    exact prefixList_ext hpre k hlt
  | inr hge =>
    have hf0 : f.val k = 0 := hfB k hge
    have hg0 : g.val k = 0 := hgB k (hlen ▸ hge)
    rw [hf0, hg0]

/-- The Fock space of countable modes is countable. -/
theorem fockNat_has_countable_infinity : HasCountableInfinity FockNat :=
  Equinumerous.of_injections encodeFock FockNat.basis
    encodeFock_injective FockNat.basis_injective

theorem fockNat_not_real_infinity : ¬ HasRealInfinity FockNat :=
  fun h =>
    countable_infinity_ne_real_infinity
      fockNat_has_countable_infinity h

theorem qft_fock_countable (Q : QuantumFieldTheory) :
    HasCountableInfinity Q.fock :=
  fockNat_has_countable_infinity

theorem qft_fock_not_real (Q : QuantumFieldTheory) :
    ¬ HasRealInfinity Q.fock :=
  fockNat_not_real_infinity

/-! ## Unrestricted occupations and continuum modes -/

/-- Continuum points as 0-1 occupation sequences. -/
def embedCont : Continuum → (Nat → Nat) :=
  fun f n => if f n then 1 else 0

theorem embedCont_injective : Function.Injective embedCont := by
  intro f g h
  funext n
  have := congrFun h n
  simp [embedCont] at this
  cases hf : f n with
  | true =>
    simp [hf] at this
    cases hg : g n with
    | true => rfl
    | false => simp [hg] at this
  | false =>
    simp [hf] at this
    cases hg : g n with
    | true => simp [hg] at this
    | false => rfl

/-- Unrestricted occupations of a countable mode set already hide the
continuum, so they are not a countable Fock space. -/
theorem unrestricted_not_countable : ¬ HasCountableInfinity (Nat → Nat) := by
  intro h
  obtain ⟨toNat, ofNat, hgf, _⟩ := h
  have hinj : Function.Injective (toNat ∘ embedCont) := by
    intro x y hx
    have heq : embedCont x = embedCont y := by
      simpa [hgf] using congrArg ofNat hx
    exact embedCont_injective heq
  have : Equinumerous Continuum Nat :=
    Equinumerous.of_injections (toNat ∘ embedCont) embedNat
      hinj embedNat_injective
  exact not_equinumerous_nat_continuum this.symm

/-! ## One-particle states of arbitrary modes -/

noncomputable section
open Classical

def oneParticleOcc {α : Type} (a : α) : α → Nat :=
  fun x => if x = a then 1 else 0

theorem oneParticleOcc_finiteSupport {α : Type} (a : α) :
    FiniteSupport (oneParticleOcc a) := by
  intro ⟨φ, hφ⟩
  have supp : ∀ i, (φ i).val = a := by
    intro i
    have hi : oneParticleOcc a (φ i).val ≠ 0 := (φ i).property
    dsimp [oneParticleOcc] at hi
    split at hi
    · assumption
    · simp at hi
  have : φ 0 = φ 1 := Subtype.ext ((supp 0).trans (supp 1).symm)
  exact Nat.zero_ne_one (hφ this)

def oneParticle {α : Type} (a : α) : Occupations α :=
  ⟨oneParticleOcc a, oneParticleOcc_finiteSupport a⟩

theorem oneParticle_injective {α : Type} :
    Function.Injective (oneParticle : α → Occupations α) := by
  intro a b h
  have hfun := congrFun (congrArg Subtype.val h) a
  change oneParticleOcc a a = oneParticleOcc b a at hfun
  have ha : oneParticleOcc a a = 1 := if_pos rfl
  rw [ha] at hfun
  by_cases hab : a = b
  · exact hab
  · have : oneParticleOcc b a = 0 := if_neg hab
    rw [this] at hfun
    cases hfun

/-- A continuum of independent modes is not a countable quantum
kinematics: already the one-particle sector carries `|ℝ|`. -/
theorem occupations_continuum_not_countable :
    ¬ HasCountableInfinity (Occupations Continuum) := by
  intro h
  obtain ⟨toNat, ofNat, hgf, _⟩ := h
  have hinj : Function.Injective (toNat ∘ oneParticle) := by
    intro x y hx
    have heq : oneParticle x = oneParticle y := by
      simpa [hgf] using congrArg ofNat hx
    exact oneParticle_injective heq
  have : Equinumerous Continuum Nat :=
    Equinumerous.of_injections (toNat ∘ oneParticle) embedNat
      hinj embedNat_injective
  exact not_equinumerous_nat_continuum this.symm

theorem occupations_continuum_real_from_one_particle :
    Infinite (Occupations Continuum) :=
  ⟨oneParticle ∘ embedNat, by
    intro n m h
    exact embedNat_injective (oneParticle_injective h)⟩

end

end ToE

