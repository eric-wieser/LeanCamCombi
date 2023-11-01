import Mathlib.Data.Nat.Lattice

#align_import mathlib.data.nat.lattice

namespace Nat

variable {ι : Sort _}

@[simp]
lemma iInf_empty [IsEmpty ι] (f : ι → ℕ) : (⨅ i : ι, f i) = 0 := by
  rw [iInf, Set.range_eq_empty, sInf_empty]

@[simp]
lemma iInf_const_zero : (⨅ i : ι, 0) = 0 := by
  cases isEmpty_or_nonempty ι
  · exact infi_empty _
  · exact ciInf_const

end Nat
