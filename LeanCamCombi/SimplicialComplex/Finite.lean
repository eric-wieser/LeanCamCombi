/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import LeanCamCombi.SimplicialComplex.Basic

#align_import simplicial_complex.finite

/-!
# Finite simplicial complexes
-/

  {X Y : Finset E}

/-- A simplicial complex is finite iff it has finitely many faces. -/
protected def Finite (S : SimplicialComplex 𝕜 E) : Prop :=
  S.faces.Finite

noncomputable def facesFinset (S : SimplicialComplex 𝕜 E) (hS : S.Finite) : Finset (Finset E) :=
  hS.toFinset

@[simp]
lemma mem_facesFinset (hS : S.Finite) : X ∈ S.facesFinset hS ↔ X ∈ S.faces :=
  Set.Finite.mem_toFinset _

/-- A simplicial complex `S` is locally finite at the face `X` iff `X` is a subface of finitely many
faces in `S`. -/
def LocallyFiniteAt (S : SimplicialComplex 𝕜 E) (X : Finset E) : Prop :=
  {Y ∈ S.faces | X ⊆ Y}.Finite

/-- A simplicial complex `S` is locally finite at the face `X` iff `X` is a subface of infinitely
many faces in `S`. -/
def LocallyInfiniteAt (S : SimplicialComplex 𝕜 E) (X : Finset E) : Prop :=
  {Y ∈ S.faces | X ⊆ Y}.Infinite

@[simp]
lemma not_locallyInfiniteAt_iff : ¬S.LocallyInfiniteAt X ↔ S.LocallyFiniteAt X :=
  Classical.not_not

/-- A simplicial complex is locally finite iff each of its nonempty faces belongs to finitely many
faces. -/
def LocallyFinite (S : SimplicialComplex 𝕜 E) : Prop :=
  ∀ ⦃X : Finset _⦄, X ∈ S.faces → X.Nonempty → S.LocallyFiniteAt X

lemma LocallyFiniteAt.mono (hX : S.LocallyFiniteAt X) (hXY : X ⊆ Y) : S.LocallyFiniteAt Y := by
  apply hX.subset
  rintro Z ⟨_, _⟩
  exact ⟨‹Z ∈ S.faces›, hXY.trans ‹Y ⊆ Z›⟩

lemma LocallyInfiniteAt.mono (hXY : X ⊆ Y) (hY : S.LocallyInfiniteAt Y) : S.LocallyInfiniteAt X :=
  fun t => hY <| LocallyFiniteAt.mono t hXY

protected lemma Finite.locallyFinite (hS : S.Finite) : S.LocallyFinite := fun X hX _ =>
  hS.Subset fun Y hY => hY.1

/-- A simplicial complex is locally finite iff each point belongs to finitely many faces. -/
lemma locallyFinite_iff_mem_finitely_many_faces [DecidableEq E] :
    S.LocallyFinite ↔ ∀ x, {X | X ∈ S.faces ∧ x ∈ convexHull 𝕜 (X : Set E)}.Finite := by
  constructor
  · unfold LocallyFinite
    contrapose!
    rintro ⟨x, hx⟩ by_cases hxspace : x ∈ S.space
    · obtain ⟨X, ⟨hX, hXhull, hXbound⟩, hXunique⟩ := combiInteriors_partition hxspace
      simp at hXunique
      refine'
        ⟨X, hX, Finset.nonempty_of_ne_empty _, fun hXlocallyfinite =>
          hx <| hXlocallyfinite.Subset fun Y hY => ⟨hY.1, _⟩⟩
      · rintro rfl
        simpa using hXhull
      have hXYhull := S.inter_subset_convex_hull hX hY.1 ⟨hXhull, hY.2⟩
      rw [← Finset.coe_inter] at hXYhull by_contra hXY
      exact
        hXbound
          (mem_combiFrontier_iff.2
            ⟨X ∩ Y,
              ⟨Finset.inter_subset_left X Y, fun hXXY => hXY (Finset.subset_inter_iff.1 hXXY).2⟩,
              hXYhull⟩)
    · cases hx _
      convert finite_empty
      exact eq_empty_of_forall_not_mem fun X hX => hxspace <| mem_bUnion hX.1 hX.2
  · rintro hS X hX ⟨x, hx⟩
    exact (hS x).Subset fun t => And.imp_right fun ht => subset_convexHull _ _ <| ht hx

end Geometry.SimplicialComplex
