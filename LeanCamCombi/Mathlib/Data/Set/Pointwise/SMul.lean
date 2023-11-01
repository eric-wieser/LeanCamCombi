import Mathlib.Data.Set.Pointwise.SMul

#align_import mathlib.data.set.pointwise.smul

open MulOpposite

open scoped Pointwise

namespace Set

variable {α : Type*} [Mul α]

@[to_additive (attr := simp)]
lemma singleton_mul' (a : α) (s : Set α) : {a} * s = a • s :=
  singleton_mul

@[to_additive (attr := simp)]
lemma mul_singleton' (s : Set α) (a : α) : s * {a} = op a • s :=
  mul_singleton

end Set
