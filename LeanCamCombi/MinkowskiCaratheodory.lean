/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.LocallyConvex.WithSeminorms

#align_import minkowski_caratheodory

/-!
# The Minkowski-Carathéodory lemma
-/

open scoped Affine BigOperators Classical

open Set

--TODO: Generalise to LCTVS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E} {s B : Set E}

/-- **Minkowski-Carathéodory lemma** -/
lemma convexHull_extremePoints [FiniteDimensional ℝ E] (hscomp : IsCompact s)
    (hsconv : Convex ℝ s) : convexHull ℝ (s.extremePoints ℝ) = s := by sorry

/-let B := convex_hull ℝ (s.extreme_points ℝ),
  have hBA : B ⊆ s :=
    convex_hull_min (λ x hx, hx.1) hsconv,
  refine subset.antisymm _ hBA, by_contra hAB,
  have hABdiff : (s \ B).nonempty := nonempty_diff.2 hAB,
  obtain ⟨x, hxA, hxB⟩ := id hABdiff,
  sorry-/
lemma closed_convexHull_extremePoints_of_compact_of_convex [FiniteDimensional ℝ E]
    (hscomp : IsCompact s) (hsconv : Convex ℝ s) : IsClosed (convexHull ℝ <| s.extremePoints ℝ) :=
  closure_eq_iff_isClosed.1 <| by
    rw [closure_convexHull_extremePoints hscomp hsconv, convexHull_extremePoints hscomp hsconv]
