import Mathlib.Order.Partition.Equipartition
import Mathlib.Data.Set.Equitable

#align_import mathlib.order.partition.equipartition

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s : Finset α} {P : Finpartition s}

@[simp]
lemma not_isEquipartition :
    ¬P.IsEquipartition ↔ ∃ a ∈ P.parts, ∃ b ∈ P.parts, Finset.card b + 1 < Finset.card a :=
  Set.not_equitableOn

end Finpartition
