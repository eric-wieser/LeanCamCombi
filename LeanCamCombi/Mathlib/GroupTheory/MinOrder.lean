/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Nat.Prime
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Torsion
import LeanCamCombi.Mathlib.Data.ZMod.Quotient

/-!
# Minimum order of an element

This file defines the minimum order of an element of a monoid.

## Main declarations

* `monoid.min_order`: The minimum order of an element of a given monoid.
* `monoid.min_order_eq_top`: The minimum order is infinite iff the monoid is torsion-free.
* `zmod.min_order`: The minimum order of $$ℤ/nℤ$$ is the smallest factor of `n`, unless `n = 0, 1`.
-/

section Monoid
variable (α) [Monoid α]

/-- The minimum order of a non-identity element. Also the minimum size of a nontrivial subgroup.
Returns `∞` if the monoid is torsion-free. -/
@[to_additive
      "The minimum order of a non-identity element. Also the minimum size of a nontrivial\nsubgroup. Returns `∞` if the monoid is torsion-free."]
noncomputable def minOrder : ℕ∞ :=
  ⨅ (a : α) (ha : a ≠ 1) (ha' : IsOfFinOrder a), orderOf a

variable {α} {a : α}

@[to_additive (attr := simp)]
lemma minOrder_eq_top : minOrder α = ⊤ ↔ IsTorsionFree α := by simpa [min_order]

@[to_additive (attr := simp)]
protected lemma IsTorsionFree.minOrder : IsTorsionFree α → minOrder α = ⊤ :=
  minOrder_eq_top.2

@[to_additive (attr := simp)]
lemma le_minOrder {n : ℕ∞} : n ≤ minOrder α ↔ ∀ ⦃a : α⦄, a ≠ 1 → IsOfFinOrder a → n ≤ orderOf a := by simp [min_order]

@[to_additive]
lemma minOrder_le_orderOf (ha : a ≠ 1) (ha' : IsOfFinOrder a) : minOrder α ≤ orderOf a :=
  le_minOrder.1 le_rfl ha ha'

end Monoid

variable [Group α] {s : Subgroup α} {n : ℕ}

@[to_additive]
lemma le_min_order' {n : ℕ∞} :
    n ≤ minOrder α ↔ ∀ ⦃s : Subgroup α⦄, s ≠ ⊥ → (s : Set α).Finite → n ≤ Nat.card s := by
  rw [le_min_order]
  refine' ⟨fun h s hs hs' => _, fun h a ha ha' => _⟩
  · obtain ⟨a, has, ha⟩ := s.bot_or_exists_ne_one.resolve_left hs
    exact
      (h ha <| finite_zpowers.1 <| hs'.subset <| zpowers_le.2 has).trans
        (WithTop.coe_le_coe.2 <| orderOf_le_card hs' has)
  · simpa using h (zpowers_ne_bot.2 ha) ha'.finite_zpowers'

@[to_additive]
lemma minOrder_le_nat_card (hs : s ≠ ⊥) (hs' : (s : Set α).Finite) : minOrder α ≤ Nat.card s :=
  le_min_order'.1 le_rfl hs hs'

end Monoid

open AddMonoid AddSubgroup Nat Set

namespace ZMod

@[simp]
protected lemma minOrder {n : ℕ} (hn : n ≠ 0) (hn₁ : n ≠ 1) : minOrder (ZMod n) = n.minFac := by
  haveI : Fact (1 < n) := by
    obtain _ | _ | n := n <;>
      first
      | contradiction
      | exact ⟨n.one_lt_succ_succ⟩
  classical
  have : (↑(n / n.min_fac) : ZMod n) ≠ 0 := by
    rw [Ne.def, ringChar.spec, ringChar.eq (ZMod n) n]
    exact
      not_dvd_of_pos_of_lt (Nat.div_pos (min_fac_le hn.bot_lt) n.min_fac_pos)
        (div_lt_self hn.bot_lt (min_fac_prime hn₁).one_lt)
  refine'
    ((min_order_le_nat_card (zmultiples_eq_bot.not.2 this) <| to_finite _).trans _).antisymm
      (le_min_order'.2 fun s hs _ => _)
  · rw [card_eq_fintype_card, ← addOrderOf_eq_card_zmultiples, ZMod.addOrderOf_coe _ hn,
      gcd_eq_right (div_dvd_of_dvd n.min_fac_dvd), Nat.div_div_self n.min_fac_dvd hn]
    exact le_rfl
  · rw [card_eq_fintype_card]
    haveI : Nontrivial s := s.bot_or_nontrivial.resolve_left hs
    exact
      WithTop.coe_le_coe.2
        (min_fac_le_of_dvd Fintype.one_lt_card <|
          (card_add_subgroup_dvd_card _).trans (ZMod.card _).Dvd)

@[simp]
lemma minOrder_of_prime {p : ℕ} (hp : p.Prime) : minOrder (ZMod p) = p := by
  rw [ZMod.minOrder hp.ne_zero hp.ne_one, hp.min_fac_eq]

end ZMod
