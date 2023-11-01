/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import LeanCamCombi.Mathlib.Data.Finset.Pointwise
import LeanCamCombi.Mathlib.GroupTheory.SpecificGroups.Cyclic
import LeanCamCombi.Kneser.Kneser

#align_import LeanCamCombi.Kneser.cauchy_davenport_from_kneser

/-!
# The Cauchy-Davenport lemma as a corollary of Kneser's lemma

This file proves the Cauchy-Davenport lemma as a corollary of Kneser's lemma.

## Main declarations

* `zmod.min_le_card_add`: The Cauchy-Davenport lemma.

## Tags

additive combinatorics, number theory, sumset, cauchy-davenport
-/

open Finset

open scoped Pointwise

/-- The **Cauchy-Davenport lemma**. -/
lemma ZMod.min_le_card_add' {p : ℕ} (hp : p.Prime) {s t : Finset (ZMod p)} (hs : s.Nonempty)
    (ht : t.Nonempty) : min p (s.card + t.card - 1) ≤ (s + t).card := by
  haveI : Fact p.prime := ⟨hp⟩
  cases eq_bot_or_eq_top (AddAction.stabilizer (ZMod p) (s + t))
  · refine' min_le_of_right_le _
    rw [← AddSubgroup.coe_eq_zero, ← coe_add_stab (hs.add ht), coe_eq_zero] at h
    simpa [*] using add_kneser s t
  · rw [← AddSubgroup.coe_eq_univ, ← coe_add_stab (hs.add ht), coe_eq_univ] at h
    refine' card_add_stab_le_card.trans' _
    simp [*, card_univ]
