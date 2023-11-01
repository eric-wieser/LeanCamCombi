import Mathlib.GroupTheory.Submonoid.Membership

#align_import mathlib.group_theory.submonoid.membership

open Set

namespace Submonoid

variable {α : Type*} [Monoid α]

@[to_additive]
lemma range_pow (a : α) : (range fun n : ℕ => a ^ n) = powers a :=
  rfl

end Submonoid
