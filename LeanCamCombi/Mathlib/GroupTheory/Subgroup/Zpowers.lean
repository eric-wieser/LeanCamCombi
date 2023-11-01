import Mathlib.GroupTheory.Subgroup.Zpowers

#align_import mathlib.group_theory.subgroup.zpowers

section Group

variable {α : Type*} [Group α] {s : Subgroup α} {a : α} {m n : ℤ}

open Function Int Set Subgroup Submonoid

@[to_additive]
lemma range_zpow (a : α) : (range fun n : ℤ => a ^ n) = zpowers a :=
  rfl

end Group
