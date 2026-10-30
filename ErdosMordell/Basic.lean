import Mathlib

/-!
# Basic definitions and bridges for the Erdős–Mordell / Fermat–Torricelli development

`footDist X Y Z` is the distance from `X` to the line `line[ℝ, Y, Z]`, measured with Mathlib's
`EuclideanGeometry.orthogonalProjection`. The bridges below compute it in terms of inner products,
and express a point of the closed triangle by its barycentric weights.
-/

open Affine EuclideanGeometry AffineMap
open scoped RealInnerProductSpace

namespace ErdosMordell

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Distance from `X` to the line through `Y` and `Z`, via Mathlib's orthogonal projection. -/
noncomputable def footDist (X Y Z : P) : ℝ :=
  dist X (orthogonalProjection line[ℝ, Y, Z] X : P)

/-- Orthogonal projection onto `line[ℝ, Y, Z]`, given the parameter explicitly. -/
lemma proj_eq_lineMap (Y Z Q : P) (r : ℝ)
    (h : ⟪Q -ᵥ Y, Z -ᵥ Y⟫ = r * dist Y Z ^ 2) :
    (orthogonalProjection line[ℝ, Y, Z] Q : P) = lineMap Y Z r := by
  rw [coe_orthogonalProjection_eq_iff_mem]
  refine ⟨AffineMap.lineMap_mem_affineSpan_pair _ _ _, ?_⟩
  rw [direction_affineSpan, vectorSpan_pair, Submodule.mem_orthogonal_singleton_iff_inner_right,
    lineMap_apply, vsub_vadd_eq_vsub_sub, ← neg_vsub_eq_vsub_rev Z Y, inner_neg_left,
    inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub V Z Y,
    real_inner_comm, h, dist_comm]
  ring

/-- Orthogonal projections onto equal subspaces agree. -/
lemma proj_congr {S T : AffineSubspace ℝ P} [Nonempty S] [S.direction.HasOrthogonalProjection]
    [Nonempty T] [T.direction.HasOrthogonalProjection] (h : S = T) (X : P) :
    (orthogonalProjection S X : P) = orthogonalProjection T X := by
  subst h; rfl

lemma footDist_comm (X Y Z : P) : footDist X Y Z = footDist X Z Y := by
  unfold footDist
  rw [proj_congr (show line[ℝ, Y, Z] = line[ℝ, Z, Y] by rw [Set.pair_comm]) X]

/-- Squared distance to a line, times the squared length of the defining segment. -/
lemma footDist_sq_mul {X Y Z : P} (hYZ : Y ≠ Z) :
    footDist X Y Z ^ 2 * ‖Z -ᵥ Y‖ ^ 2 =
      ‖X -ᵥ Y‖ ^ 2 * ‖Z -ᵥ Y‖ ^ 2 - ⟪X -ᵥ Y, Z -ᵥ Y⟫ ^ 2 := by
  have hd : ‖Z -ᵥ Y‖ ≠ 0 := by
    rw [norm_ne_zero_iff, vsub_ne_zero]; exact hYZ.symm
  have hp := proj_eq_lineMap Y Z X (⟪X -ᵥ Y, Z -ᵥ Y⟫ / ‖Z -ᵥ Y‖ ^ 2)
    (by rw [dist_comm, dist_eq_norm_vsub V Z Y]; field_simp)
  rw [footDist, hp, dist_eq_norm_vsub V, lineMap_apply, vsub_vadd_eq_vsub_sub, norm_sub_sq_real,
    norm_smul, real_inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  ring

/-- Inner product of two combinations of `p`, `q`. -/
lemma inner_comb (p q : V) (α β γ δ : ℝ) :
    ⟪α • p + β • q, γ • p + δ • q⟫ =
      α * γ * ‖p‖ ^ 2 + (α * δ + β * γ) * ⟪p, q⟫ + β * δ * ‖q‖ ^ 2 := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm p q]
  ring

/-- Barycentric bridge: a point given by weights summing to one, seen from vertex `i`. -/
lemma affineCombination_vsub (t : Triangle ℝ P) (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1)
    (i : Fin 3) :
    Finset.univ.affineCombination ℝ t.points w -ᵥ t.points i =
      ∑ j, w j • (t.points j -ᵥ t.points i) := by
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ hw (t.points i),
    vadd_vsub, Finset.weightedVSubOfPoint_apply]

lemma affineCombination_vsub_zero (t : Triangle ℝ P) (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination ℝ t.points w -ᵥ t.points 0 =
      w 1 • (t.points 1 -ᵥ t.points 0) + w 2 • (t.points 2 -ᵥ t.points 0) := by
  rw [affineCombination_vsub t w hw, Fin.sum_univ_three]; simp

lemma affineCombination_vsub_one (t : Triangle ℝ P) (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination ℝ t.points w -ᵥ t.points 1 =
      w 2 • (t.points 2 -ᵥ t.points 1) + w 0 • (t.points 0 -ᵥ t.points 1) := by
  rw [affineCombination_vsub t w hw, Fin.sum_univ_three]; simp [add_comm]

lemma affineCombination_vsub_two (t : Triangle ℝ P) (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination ℝ t.points w -ᵥ t.points 2 =
      w 0 • (t.points 0 -ᵥ t.points 2) + w 1 • (t.points 1 -ᵥ t.points 2) := by
  rw [affineCombination_vsub t w hw, Fin.sum_univ_three]; simp

lemma points_ne (t : Triangle ℝ P) {i j : Fin 3} (h : i ≠ j) : t.points i ≠ t.points j :=
  t.independent.injective.ne h

/-- The Gram determinant of a nondegenerate triangle is positive. -/
lemma gram_pos (t : Triangle ℝ P) :
    0 < dist (t.points 2) (t.points 0) ^ 2 * dist (t.points 0) (t.points 1) ^ 2 -
      ⟪t.points 1 -ᵥ t.points 0, t.points 2 -ᵥ t.points 0⟫ ^ 2 := by
  have hncol : ¬ Collinear ℝ ({t.points 1, t.points 0, t.points 2} : Set P) := by
    rw [← affineIndependent_iff_not_collinear_of_ne (p := t.points) (i₁ := 1) (i₂ := 0) (i₃ := 2)
      (by decide) (by decide) (by decide)]
    exact t.independent
  have hsin := sin_pos_of_not_collinear hncol
  have h1 := InnerProductGeometry.cos_angle_mul_norm_mul_norm (t.points 1 -ᵥ t.points 0)
    (t.points 2 -ᵥ t.points 0)
  have h2 := Real.sin_sq_add_cos_sq (∠ (t.points 1) (t.points 0) (t.points 2))
  have hb : dist (t.points 2) (t.points 0) = ‖t.points 2 -ᵥ t.points 0‖ := dist_eq_norm_vsub V _ _
  have hc : dist (t.points 0) (t.points 1) = ‖t.points 1 -ᵥ t.points 0‖ := by
    rw [dist_comm]; exact dist_eq_norm_vsub V _ _
  have hpn : 0 < ‖t.points 1 -ᵥ t.points 0‖ :=
    norm_pos_iff.2 (vsub_ne_zero.2 (points_ne t (by decide)))
  have hqn : 0 < ‖t.points 2 -ᵥ t.points 0‖ :=
    norm_pos_iff.2 (vsub_ne_zero.2 (points_ne t (by decide)))
  rw [hb, hc, ← h1]
  change 0 < _ - (Real.cos (∠ (t.points 1) (t.points 0) (t.points 2)) * _) ^ 2
  have : 0 < ‖t.points 2 -ᵥ t.points 0‖ ^ 2 * ‖t.points 1 -ᵥ t.points 0‖ ^ 2 := by positivity
  nlinarith [pow_pos hsin 2]

end ErdosMordell
