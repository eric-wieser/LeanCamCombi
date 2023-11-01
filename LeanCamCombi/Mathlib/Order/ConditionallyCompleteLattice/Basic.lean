import Mathlib.Order.ConditionallyCompleteLattice.Basic

#align_import mathlib.order.conditionally_complete_lattice.basic

section

variable {ι : Sort _} {α : Type*} [ConditionallyCompleteLinearOrderBot α] {f : ι → α} {a : α}

lemma cinfi_le_of_le' (c : ι) : f c ≤ a → iInf f ≤ a :=
  ciInf_le_of_le (OrderBot.bddBelow _) _

end
