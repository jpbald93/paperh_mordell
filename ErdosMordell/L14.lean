import ErdosMordell.Mordell
import ErdosMordell.Fermat
import ErdosMordell.Barrow

/-!
# Layer 14: Mathlib-only restatements and witnesses

Each `l14_*` theorem restates a main theorem with a type that mentions only Mathlib notions.
The library's distance from `X` to a side line, `dist X (orthogonalProjection line[ℝ, Y, Z] X)`,
is replaced by Mathlib's `Metric.infDist X line[ℝ, Y, Z]` (bridge:
`EuclideanGeometry.dist_orthogonalProjection_eq_infDist`), and the barycentric hypotheses "`X` is
in the closed triangle" / "`X` is strictly inside" by Mathlib's `t.closedInterior` /
`t.interior` (bridges `l14_of_mem_closedInterior`, `l14_of_mem_interior`). The Fermat theorems are
already stated with Mathlib notions only and are restated verbatim.
The `l14w_*` theorems are explicit witnesses in `EuclideanSpace ℝ (Fin 2)`.
-/

open Affine EuclideanGeometry AffineMap Real
open scoped RealInnerProductSpace

namespace ErdosMordell

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! ### Bridges -/

theorem l14_of_mem_closedInterior {t : Triangle ℝ P} {X : P} (hX : X ∈ t.closedInterior) :
    ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      X = Finset.univ.affineCombination ℝ t.points w := by
  obtain ⟨w, hw, hi, rfl⟩ := hX
  exact ⟨w, fun i => (hi i).1, hw, rfl⟩

theorem l14_of_mem_interior {t : Triangle ℝ P} {X : P} (hX : X ∈ t.interior) :
    ∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
      X = Finset.univ.affineCombination ℝ t.points w := by
  obtain ⟨w, hw, hi, rfl⟩ := hX
  exact ⟨w, fun i => (hi i).1, hw, rfl⟩

/-! ### Mathlib-only restatements -/

theorem l14_key_lemma_zero (t : Triangle ℝ P) (X : P) (hX : X ∈ t.closedInterior) :
    dist (t.points 2) (t.points 0) * Metric.infDist X (line[ℝ, t.points 0, t.points 1] : Set P) +
      dist (t.points 0) (t.points 1) * Metric.infDist X (line[ℝ, t.points 2, t.points 0] : Set P) ≤
      dist (t.points 1) (t.points 2) * dist X (t.points 0) := by
  rw [← dist_orthogonalProjection_eq_infDist, ← dist_orthogonalProjection_eq_infDist]
  exact key_lemma_zero t X (l14_of_mem_closedInterior hX)

theorem l14_key_lemma_one (t : Triangle ℝ P) (X : P) (hX : X ∈ t.closedInterior) :
    dist (t.points 0) (t.points 1) * Metric.infDist X (line[ℝ, t.points 1, t.points 2] : Set P) +
      dist (t.points 1) (t.points 2) * Metric.infDist X (line[ℝ, t.points 0, t.points 1] : Set P) ≤
      dist (t.points 2) (t.points 0) * dist X (t.points 1) := by
  rw [← dist_orthogonalProjection_eq_infDist, ← dist_orthogonalProjection_eq_infDist]
  exact key_lemma_one t X (l14_of_mem_closedInterior hX)

theorem l14_key_lemma_two (t : Triangle ℝ P) (X : P) (hX : X ∈ t.closedInterior) :
    dist (t.points 1) (t.points 2) * Metric.infDist X (line[ℝ, t.points 2, t.points 0] : Set P) +
      dist (t.points 2) (t.points 0) * Metric.infDist X (line[ℝ, t.points 1, t.points 2] : Set P) ≤
      dist (t.points 0) (t.points 1) * dist X (t.points 2) := by
  rw [← dist_orthogonalProjection_eq_infDist, ← dist_orthogonalProjection_eq_infDist]
  exact key_lemma_two t X (l14_of_mem_closedInterior hX)

theorem l14_erdos_mordell (t : Triangle ℝ P) (X : P) (hX : X ∈ t.closedInterior) :
    2 * (Metric.infDist X (line[ℝ, t.points 1, t.points 2] : Set P) +
      Metric.infDist X (line[ℝ, t.points 2, t.points 0] : Set P) +
      Metric.infDist X (line[ℝ, t.points 0, t.points 1] : Set P)) ≤
      dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2) := by
  rw [← dist_orthogonalProjection_eq_infDist, ← dist_orthogonalProjection_eq_infDist,
    ← dist_orthogonalProjection_eq_infDist]
  exact erdos_mordell t X (l14_of_mem_closedInterior hX)

theorem l14_erdos_mordell_eq_iff (t : Triangle ℝ P) (X : P) (hX : X ∈ t.closedInterior) :
    2 * (Metric.infDist X (line[ℝ, t.points 1, t.points 2] : Set P) +
      Metric.infDist X (line[ℝ, t.points 2, t.points 0] : Set P) +
      Metric.infDist X (line[ℝ, t.points 0, t.points 1] : Set P)) =
      dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2) ↔
    (dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) ∧ dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0)) ∧
      X = Finset.univ.centroid ℝ t.points := by
  rw [← dist_orthogonalProjection_eq_infDist, ← dist_orthogonalProjection_eq_infDist,
    ← dist_orthogonalProjection_eq_infDist]
  exact erdos_mordell_eq_iff t X (l14_of_mem_closedInterior hX)

theorem l14_barrow (t : Triangle ℝ P) (X U V' W : P) (hX : X ∈ t.interior)
    (hU : Wbtw ℝ (t.points 1) U (t.points 2)) (hV : Wbtw ℝ (t.points 2) V' (t.points 0))
    (hW : Wbtw ℝ (t.points 0) W (t.points 1))
    (hUa : ∠ (t.points 1) X U = ∠ U X (t.points 2))
    (hVa : ∠ (t.points 2) X V' = ∠ V' X (t.points 0))
    (hWa : ∠ (t.points 0) X W = ∠ W X (t.points 1)) :
    2 * (dist X U + dist X V' + dist X W) ≤ dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2) :=
  barrow t X U V' W (l14_of_mem_interior hX) hU hV hW hUa hVa hWa

theorem l14_fermat_min (A B C F : P) (hAB : ∠ A F B = 2 * π / 3) (hBC : ∠ B F C = 2 * π / 3)
    (hCA : ∠ C F A = 2 * π / 3) (X : P) :
    dist F A + dist F B + dist F C ≤ dist X A + dist X B + dist X C :=
  fermat_min A B C F hAB hBC hCA X

theorem l14_fermat_exists (t : Triangle ℝ P)
    (hA : ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3)
    (hB : ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3)
    (hC : ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3) :
    ∃ F : P, ∠ (t.points 0) F (t.points 1) = 2 * π / 3 ∧
      ∠ (t.points 1) F (t.points 2) = 2 * π / 3 ∧ ∠ (t.points 2) F (t.points 0) = 2 * π / 3 :=
  fermat_exists t hA hB hC

theorem l14_fermat_torricelli (t : Triangle ℝ P)
    (hA : ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3)
    (hB : ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3)
    (hC : ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3) :
    ∃ F : P, ∠ (t.points 0) F (t.points 1) = 2 * π / 3 ∧
      ∠ (t.points 1) F (t.points 2) = 2 * π / 3 ∧
      ∠ (t.points 2) F (t.points 0) = 2 * π / 3 ∧
      ∀ X : P, dist F (t.points 0) + dist F (t.points 1) + dist F (t.points 2) ≤
        dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2) :=
  fermat_torricelli t hA hB hC

/-! ### Witness helpers -/

theorem l14_dist_sq (x y : (EuclideanSpace ℝ (Fin 2))) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two,
    Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

theorem l14_dist (x y : (EuclideanSpace ℝ (Fin 2))) (r : ℝ) (hr : 0 ≤ r)
    (h : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = r ^ 2) : dist x y = r := by
  rw [← sq_eq_sq₀ dist_nonneg hr, l14_dist_sq, h]

theorem l14_not_collinear (X Y Z : (EuclideanSpace ℝ (Fin 2)))
    (h : (Y 0 - X 0) * (Z 1 - X 1) - (Y 1 - X 1) * (Z 0 - X 0) ≠ 0) :
    ¬ Collinear ℝ ({X, Y, Z} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro hc
  rw [collinear_iff_of_mem (Set.mem_insert _ _)] at hc
  obtain ⟨v, hv⟩ := hc
  obtain ⟨r, hr⟩ := hv Y (by simp)
  obtain ⟨s, hs⟩ := hv Z (by simp)
  apply h
  have h0 := congrArg (· 0) hr; have h1 := congrArg (· 1) hr
  have h2 := congrArg (· 0) hs; have h3 := congrArg (· 1) hs
  simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h0 h1 h2 h3
  rw [h0, h1, h2, h3]; ring

theorem l14_ne (X Y : (EuclideanSpace ℝ (Fin 2))) (h : X 0 ≠ Y 0 ∨ X 1 ≠ Y 1) : X ≠ Y := by
  rintro rfl; tauto

theorem l14_inner (x y : (EuclideanSpace ℝ (Fin 2))) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

theorem l14_mem_line (Y Z Q : (EuclideanSpace ℝ (Fin 2))) (r : ℝ) (h0 : Q 0 = Y 0 + r * (Z 0 - Y 0))
    (h1 : Q 1 = Y 1 + r * (Z 1 - Y 1)) : Q ∈ line[ℝ, Y, Z] := by
  have : Q = AffineMap.lineMap Y Z r := by
    rw [AffineMap.lineMap_apply_module']
    ext i; fin_cases i <;> simp [h0, h1] <;> ring
  rw [this]; exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

theorem l14_ac (t : Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (w : Fin 3 → ℝ) (hw : w 0 + w 1 + w 2 = 1) :
    Finset.univ.affineCombination ℝ t.points w =
      !₂[w 0 * t.points 0 0 + w 1 * t.points 1 0 + w 2 * t.points 2 0,
        w 0 * t.points 0 1 + w 1 * t.points 1 1 + w 2 * t.points 2 1] := by
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa [Fin.sum_univ_three] using hw)]
  ext i; fin_cases i <;> simp [Fin.sum_univ_three]

/-- An angle with nonnegative inner product is `< 2π/3`. -/
theorem l14_angle_lt {A B C : P} (h : 0 ≤ ⟪A -ᵥ B, C -ᵥ B⟫) : ∠ A B C < 2 * π / 3 := by
  have : ∠ A B C ≤ π / 2 := by
    rw [EuclideanGeometry.angle, InnerProductGeometry.angle, Real.arccos_le_pi_div_two]
    exact div_nonneg h (by positivity)
  linarith [Real.pi_pos]

theorem l14_angle_eq {A F B : P} (hi : ⟪A -ᵥ F, B -ᵥ F⟫ = -2) (ha : dist A F = 2)
    (hb : dist B F = 2) : ∠ A F B = 2 * π / 3 := by
  rw [EuclideanGeometry.angle, InnerProductGeometry.angle, ← dist_eq_norm_vsub V,
    ← dist_eq_norm_vsub V, hi, ha, hb, show (-2 : ℝ) / (2 * 2) = -(1 / 2) by norm_num]
  exact arccos_neg_half

/-- The 3-4-5 witness triangle `(0,0), (4,0), (0,3)`. -/
noncomputable def l14T : Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨![!₂[0, 0], !₂[4, 0], !₂[0, 3]],
    affineIndependent_iff_not_collinear_set.2 (l14_not_collinear _ _ _ (by simp))⟩

theorem l14T_sides : dist (l14T.points 1) (l14T.points 2) = 5 ∧
    dist (l14T.points 2) (l14T.points 0) = 3 ∧ dist (l14T.points 0) (l14T.points 1) = 4 :=
  ⟨l14_dist _ _ _ (by norm_num) (by simp [l14T] <;> norm_num),
    l14_dist _ _ _ (by norm_num) (by simp [l14T]),
    l14_dist _ _ _ (by norm_num) (by simp [l14T])⟩

theorem l14T_incenter_mem : !₂[1, 1] ∈ l14T.interior := by
  have h : Finset.univ.affineCombination ℝ l14T.points ![5 / 12, 1 / 4, 1 / 3] = !₂[1, 1] := by
    rw [l14_ac _ _ (by simp <;> norm_num)]
    ext i; fin_cases i <;> simp [l14T]
  rw [← h, Affine.Simplex.affineCombination_mem_interior_iff (by simp [Fin.sum_univ_three] <;> norm_num)]
  intro i; fin_cases i <;> simp <;> norm_num

/-! ### Witnesses -/

/-- Witness for the key lemmas and Erdős–Mordell: the 3-4-5 triangle and its incentre
`X = (1,1)`, strictly inside, at distance `≤ 1` (in fact `= 1`) from the three side lines, with
`XA² = 2`, `XB² = 10`, `XC² = 5`. All three key lemmas and the inequality are strict
(`7 < 5√2`, `9 < 3√10`, `8 < 4√5`, `6 < √2 + √10 + √5`); the triangle is not equilateral, so the
right side of `erdos_mordell_eq_iff` fails, and `X` is distinct from the vertices. -/
theorem l14w_erdos_mordell : ∃ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), ∃ X : (EuclideanSpace ℝ (Fin 2)),
    t.points = ![!₂[0, 0], !₂[4, 0], !₂[0, 3]] ∧ X = !₂[1, 1] ∧
    X ∈ t.interior ∧ X ∈ t.closedInterior ∧
    X ≠ t.points 0 ∧ X ≠ t.points 1 ∧ X ≠ t.points 2 ∧
    dist (t.points 2) (t.points 0) * Metric.infDist X (line[ℝ, t.points 0, t.points 1] : Set (EuclideanSpace ℝ (Fin 2))) + dist (t.points 0) (t.points 1) * Metric.infDist X (line[ℝ, t.points 2, t.points 0] : Set (EuclideanSpace ℝ (Fin 2))) <
      dist (t.points 1) (t.points 2) * dist X (t.points 0) ∧
    dist (t.points 0) (t.points 1) * Metric.infDist X (line[ℝ, t.points 1, t.points 2] : Set (EuclideanSpace ℝ (Fin 2))) + dist (t.points 1) (t.points 2) * Metric.infDist X (line[ℝ, t.points 0, t.points 1] : Set (EuclideanSpace ℝ (Fin 2))) <
      dist (t.points 2) (t.points 0) * dist X (t.points 1) ∧
    dist (t.points 1) (t.points 2) * Metric.infDist X (line[ℝ, t.points 2, t.points 0] : Set (EuclideanSpace ℝ (Fin 2))) + dist (t.points 2) (t.points 0) * Metric.infDist X (line[ℝ, t.points 1, t.points 2] : Set (EuclideanSpace ℝ (Fin 2))) <
      dist (t.points 0) (t.points 1) * dist X (t.points 2) ∧
    2 * (Metric.infDist X (line[ℝ, t.points 1, t.points 2] : Set (EuclideanSpace ℝ (Fin 2))) + Metric.infDist X (line[ℝ, t.points 2, t.points 0] : Set (EuclideanSpace ℝ (Fin 2))) + Metric.infDist X (line[ℝ, t.points 0, t.points 1] : Set (EuclideanSpace ℝ (Fin 2)))) < dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2) ∧
    ¬ (dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) ∧ dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0)) := by
  obtain ⟨ha, hb, hc⟩ := l14T_sides
  have hX := l14T_incenter_mem
  have dA : Metric.infDist !₂[1, 1] (line[ℝ, l14T.points 1, l14T.points 2] : Set (EuclideanSpace ℝ (Fin 2))) ≤ 1 :=
    (Metric.infDist_le_dist_of_mem (l14_mem_line _ _ !₂[8 / 5, 9 / 5] (3 / 5)
      (by simp [l14T] <;> norm_num) (by simp [l14T] <;> norm_num))).trans_eq
      (l14_dist _ _ _ (by norm_num) (by simp <;> norm_num))
  have dB : Metric.infDist !₂[1, 1] (line[ℝ, l14T.points 2, l14T.points 0] : Set (EuclideanSpace ℝ (Fin 2))) ≤ 1 :=
    (Metric.infDist_le_dist_of_mem (l14_mem_line _ _ !₂[0, 1] (2 / 3)
      (by simp [l14T]) (by simp [l14T] <;> norm_num))).trans_eq
      (l14_dist _ _ _ (by norm_num) (by simp))
  have dC : Metric.infDist !₂[1, 1] (line[ℝ, l14T.points 0, l14T.points 1] : Set (EuclideanSpace ℝ (Fin 2))) ≤ 1 :=
    (Metric.infDist_le_dist_of_mem (l14_mem_line _ _ !₂[1, 0] (1 / 4)
      (by simp [l14T] <;> norm_num) (by simp [l14T]))).trans_eq
      (l14_dist _ _ _ (by norm_num) (by simp))
  have dA0 := Metric.infDist_nonneg (x := (!₂[1, 1] : (EuclideanSpace ℝ (Fin 2))))
    (s := (line[ℝ, l14T.points 1, l14T.points 2] : Set (EuclideanSpace ℝ (Fin 2))))
  have dB0 := Metric.infDist_nonneg (x := (!₂[1, 1] : (EuclideanSpace ℝ (Fin 2))))
    (s := (line[ℝ, l14T.points 2, l14T.points 0] : Set (EuclideanSpace ℝ (Fin 2))))
  have dC0 := Metric.infDist_nonneg (x := (!₂[1, 1] : (EuclideanSpace ℝ (Fin 2))))
    (s := (line[ℝ, l14T.points 0, l14T.points 1] : Set (EuclideanSpace ℝ (Fin 2))))
  have hXA : dist (!₂[1, 1] : (EuclideanSpace ℝ (Fin 2))) (l14T.points 0) ^ 2 = 2 := by
    rw [l14_dist_sq]; simp [l14T]; norm_num
  have hXB : dist (!₂[1, 1] : (EuclideanSpace ℝ (Fin 2))) (l14T.points 1) ^ 2 = 10 := by
    rw [l14_dist_sq]; simp [l14T]; norm_num
  have hXC : dist (!₂[1, 1] : (EuclideanSpace ℝ (Fin 2))) (l14T.points 2) ^ 2 = 5 := by
    rw [l14_dist_sq]; simp [l14T]; norm_num
  have xA := dist_nonneg (x := (!₂[1, 1] : (EuclideanSpace ℝ (Fin 2)))) (y := l14T.points 0)
  have xB := dist_nonneg (x := (!₂[1, 1] : (EuclideanSpace ℝ (Fin 2)))) (y := l14T.points 1)
  have xC := dist_nonneg (x := (!₂[1, 1] : (EuclideanSpace ℝ (Fin 2)))) (y := l14T.points 2)
  have lA : 141 / 100 < dist (!₂[1, 1] : (EuclideanSpace ℝ (Fin 2))) (l14T.points 0) := by nlinarith
  have lB : 316 / 100 < dist (!₂[1, 1] : (EuclideanSpace ℝ (Fin 2))) (l14T.points 1) := by nlinarith
  have lC : 223 / 100 < dist (!₂[1, 1] : (EuclideanSpace ℝ (Fin 2))) (l14T.points 2) := by nlinarith
  refine ⟨l14T, !₂[1, 1], rfl, rfl, hX, Affine.Simplex.interior_subset_closedInterior _ hX,
    l14_ne _ _ (by simp [l14T]), l14_ne _ _ (by simp [l14T]), l14_ne _ _ (by simp [l14T]),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha, hb, hc]; nlinarith
  · rw [ha, hb, hc]; nlinarith
  · rw [ha, hb, hc]; nlinarith
  · linarith
  · rw [ha, hb, hc]; norm_num

/-- Equality witness for `erdos_mordell_eq_iff`: the equilateral triangle `(0,0), (2,0), (1,√3)`
with `X` its centroid. (An equilateral triangle has no rational coordinates in the plane.) -/
theorem l14w_erdos_mordell_eq : ∃ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), ∃ X : (EuclideanSpace ℝ (Fin 2)),
    t.points = ![!₂[0, 0], !₂[2, 0], !₂[1, √3]] ∧ X = Finset.univ.centroid ℝ t.points ∧
    X ∈ t.closedInterior ∧
    2 * (Metric.infDist X (line[ℝ, t.points 1, t.points 2] : Set (EuclideanSpace ℝ (Fin 2))) + Metric.infDist X (line[ℝ, t.points 2, t.points 0] : Set (EuclideanSpace ℝ (Fin 2))) + Metric.infDist X (line[ℝ, t.points 0, t.points 1] : Set (EuclideanSpace ℝ (Fin 2)))) = dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2) := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  let t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)) := ⟨![!₂[0, 0], !₂[2, 0], !₂[1, √3]],
    affineIndependent_iff_not_collinear_set.2 (l14_not_collinear _ _ _ (by simp))⟩
  have hab : dist (t.points 0) (t.points 1) = 2 := l14_dist _ _ _ (by norm_num) (by simp [t] <;> norm_num)
  have hbc : dist (t.points 1) (t.points 2) = 2 := l14_dist _ _ _ (by norm_num) (by simp [t]; nlinarith)
  have hca : dist (t.points 2) (t.points 0) = 2 := l14_dist _ _ _ (by norm_num) (by simp [t]; nlinarith)
  have hmem : Finset.univ.centroid ℝ t.points ∈ t.closedInterior := by
    rw [Finset.centroid_def, Affine.Simplex.affineCombination_mem_closedInterior_iff
      (Finset.sum_centroidWeights_eq_one_of_card_ne_zero _ _ (by simp))]
    intro i; simp [Finset.centroidWeights_apply]; norm_num
  exact ⟨t, _, rfl, rfl, hmem,
    (l14_erdos_mordell_eq_iff t _ hmem).2 ⟨⟨hab.trans hbc.symm, hbc.trans hca.symm⟩, rfl⟩⟩

/-- Witness for Barrow: the triangle `A = (5,0)`, `B = (-3,4)`, `C = (-3,-4)` with `X = (0,0)`
(its circumcentre, strictly inside with weights `3/8, 5/16, 5/16`). Since `XA = XB = XC = 5`, the
bisector feet are the midpoints `U = (-3,0)`, `V = (1,-2)`, `W = (1,2)`. The inequality is strict
(`6 + 4√5 < 15`), and `U, V, W` are pairwise distinct. -/
theorem l14w_barrow : ∃ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), ∃ X U V' W : (EuclideanSpace ℝ (Fin 2)),
    t.points = ![!₂[5, 0], !₂[-3, 4], !₂[-3, -4]] ∧ X = !₂[0, 0] ∧ U = !₂[-3, 0] ∧
    V' = !₂[1, -2] ∧ W = !₂[1, 2] ∧ X ∈ t.interior ∧
    Wbtw ℝ (t.points 1) U (t.points 2) ∧ Wbtw ℝ (t.points 2) V' (t.points 0) ∧
    Wbtw ℝ (t.points 0) W (t.points 1) ∧
    ∠ (t.points 1) X U = ∠ U X (t.points 2) ∧ ∠ (t.points 2) X V' = ∠ V' X (t.points 0) ∧
    ∠ (t.points 0) X W = ∠ W X (t.points 1) ∧ U ≠ V' ∧ V' ≠ W ∧ W ≠ U ∧
    2 * (dist X U + dist X V' + dist X W) < dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2) := by
  let t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)) := ⟨![!₂[5, 0], !₂[-3, 4], !₂[-3, -4]],
    affineIndependent_iff_not_collinear_set.2 (l14_not_collinear _ _ _ (by simp <;> norm_num))⟩
  have hX : (!₂[0, 0] : (EuclideanSpace ℝ (Fin 2))) ∈ t.interior := by
    have h : Finset.univ.affineCombination ℝ t.points ![3 / 8, 5 / 16, 5 / 16] = !₂[0, 0] := by
      rw [l14_ac _ _ (by simp <;> norm_num)]
      ext i; fin_cases i <;> simp [t] <;> norm_num
    rw [← h, Affine.Simplex.affineCombination_mem_interior_iff
      (by simp [Fin.sum_univ_three] <;> norm_num)]
    intro i; fin_cases i <;> simp <;> norm_num
  have mid : ∀ Y Z M : (EuclideanSpace ℝ (Fin 2)), M 0 = (Y 0 + Z 0) / 2 → M 1 = (Y 1 + Z 1) / 2 → Wbtw ℝ Y M Z := by
    intro Y Z M h0 h1
    have : M = midpoint ℝ Y Z := by
      ext i; fin_cases i <;> simp [midpoint_eq_smul_add, h0, h1] <;> ring
    rw [this]; exact wbtw_midpoint _ _ _
  have ang : ∀ Y Z M : (EuclideanSpace ℝ (Fin 2)), ⟪Y -ᵥ !₂[0, 0], M -ᵥ !₂[0, 0]⟫ = ⟪Z -ᵥ !₂[0, 0], M -ᵥ !₂[0, 0]⟫ →
      dist Y !₂[0, 0] = dist Z !₂[0, 0] → ∠ Y !₂[0, 0] M = ∠ M !₂[0, 0] Z := by
    intro Y Z M hi hd
    rw [dist_eq_norm_vsub (EuclideanSpace ℝ (Fin 2)), dist_eq_norm_vsub (EuclideanSpace ℝ (Fin 2))] at hd
    rw [angle_comm M]
    simp only [EuclideanGeometry.angle, InnerProductGeometry.angle, hi, hd]
  have five : ∀ Y : (EuclideanSpace ℝ (Fin 2)), Y 0 ^ 2 + Y 1 ^ 2 = 25 → dist Y !₂[0, 0] = 5 := fun Y h =>
    l14_dist _ _ _ (by norm_num) (by simp; linarith)
  have hXA : dist (!₂[0, 0] : (EuclideanSpace ℝ (Fin 2))) (t.points 0) = 5 := l14_dist _ _ _ (by norm_num) (by simp [t])
  have hXB : dist (!₂[0, 0] : (EuclideanSpace ℝ (Fin 2))) (t.points 1) = 5 :=
    l14_dist _ _ _ (by norm_num) (by simp [t] <;> norm_num)
  have hXC : dist (!₂[0, 0] : (EuclideanSpace ℝ (Fin 2))) (t.points 2) = 5 :=
    l14_dist _ _ _ (by norm_num) (by simp [t] <;> norm_num)
  have hU : dist (!₂[0, 0] : (EuclideanSpace ℝ (Fin 2))) !₂[-3, 0] = 3 := l14_dist _ _ _ (by norm_num) (by simp)
  have hV : dist (!₂[0, 0] : (EuclideanSpace ℝ (Fin 2))) !₂[1, -2] ^ 2 = 5 := by rw [l14_dist_sq]; simp; norm_num
  have hW : dist (!₂[0, 0] : (EuclideanSpace ℝ (Fin 2))) !₂[1, 2] ^ 2 = 5 := by rw [l14_dist_sq]; simp; norm_num
  have hVW : dist (!₂[0, 0] : (EuclideanSpace ℝ (Fin 2))) !₂[1, -2] = dist (!₂[0, 0] : (EuclideanSpace ℝ (Fin 2))) !₂[1, 2] := by
    rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, hV, hW]
  have hV0 := dist_nonneg (x := (!₂[0, 0] : (EuclideanSpace ℝ (Fin 2)))) (y := !₂[1, -2])
  refine ⟨t, _, _, _, _, rfl, rfl, rfl, rfl, rfl, hX,
    mid _ _ _ (by simp [t]) (by simp [t]), mid _ _ _ (by simp [t] <;> norm_num) (by simp [t] <;> norm_num),
    mid _ _ _ (by simp [t] <;> norm_num) (by simp [t] <;> norm_num),
    ang _ _ _ (by simp [t, l14_inner]) (by rw [five _ (by simp [t] <;> norm_num),
      five _ (by simp [t] <;> norm_num)]),
    ang _ _ _ (by simp [t, l14_inner] <;> norm_num) (by rw [five _ (by simp [t] <;> norm_num),
      five _ (by simp [t] <;> norm_num)]),
    ang _ _ _ (by simp [t, l14_inner] <;> norm_num) (by rw [five _ (by simp [t] <;> norm_num),
      five _ (by simp [t] <;> norm_num)]),
    l14_ne _ _ (by simp <;> norm_num), l14_ne _ _ (by simp <;> norm_num), l14_ne _ _ (by simp <;> norm_num),
    ?_⟩
  rw [hXA, hXB, hXC, hU, ← hVW]
  nlinarith

/-- Witness for `fermat_min`: `F = (0,0)` sees `A = (2,0)`, `B = (-1,√3)`, `C = (-1,-√3)` under
`2π/3` (an exact `2π/3` angle between rational vectors is impossible, since `tan (2π/3) = -√3`).
The minimum is strict at `X = A`: `6 < 4√3`. -/
theorem l14w_fermat_min : ∃ A B C F X : (EuclideanSpace ℝ (Fin 2)),
    A = !₂[2, 0] ∧ B = !₂[-1, √3] ∧ C = !₂[-1, -√3] ∧ F = !₂[0, 0] ∧ X = A ∧
    ∠ A F B = 2 * π / 3 ∧ ∠ B F C = 2 * π / 3 ∧ ∠ C F A = 2 * π / 3 ∧
    A ≠ B ∧ B ≠ C ∧ C ≠ A ∧
    dist F A + dist F B + dist F C < dist X A + dist X B + dist X C := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h3p : 0 < √3 := by positivity
  have hA : dist (!₂[2, 0] : (EuclideanSpace ℝ (Fin 2))) !₂[0, 0] = 2 := l14_dist _ _ _ (by norm_num) (by simp)
  have hB : dist (!₂[-1, √3] : (EuclideanSpace ℝ (Fin 2))) !₂[0, 0] = 2 := l14_dist _ _ _ (by norm_num) (by simp; nlinarith)
  have hC : dist (!₂[-1, -√3] : (EuclideanSpace ℝ (Fin 2))) !₂[0, 0] = 2 :=
    l14_dist _ _ _ (by norm_num) (by simp; nlinarith)
  have hAB : dist (!₂[2, 0] : (EuclideanSpace ℝ (Fin 2))) !₂[-1, √3] ^ 2 = 12 := by rw [l14_dist_sq]; simp; nlinarith
  have hAC : dist (!₂[2, 0] : (EuclideanSpace ℝ (Fin 2))) !₂[-1, -√3] ^ 2 = 12 := by rw [l14_dist_sq]; simp; nlinarith
  have n1 := dist_nonneg (x := (!₂[2, 0] : (EuclideanSpace ℝ (Fin 2)))) (y := !₂[-1, √3])
  have n2 := dist_nonneg (x := (!₂[2, 0] : (EuclideanSpace ℝ (Fin 2)))) (y := !₂[-1, -√3])
  refine ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl,
    l14_angle_eq (by simp [l14_inner]) hA hB, l14_angle_eq (by simp [l14_inner]; nlinarith) hB hC,
    l14_angle_eq (by simp [l14_inner]) hC hA,
    l14_ne _ _ (by simp <;> norm_num), l14_ne _ _ (by simp; intro h; linarith),
    l14_ne _ _ (by simp <;> norm_num), ?_⟩
  have l1 : 3 < dist (!₂[2, 0] : (EuclideanSpace ℝ (Fin 2))) !₂[-1, √3] := by nlinarith
  have l2 : 3 < dist (!₂[2, 0] : (EuclideanSpace ℝ (Fin 2))) !₂[-1, -√3] := by nlinarith
  rw [dist_comm _ (!₂[2, 0] : (EuclideanSpace ℝ (Fin 2))), dist_comm _ (!₂[-1, √3] : (EuclideanSpace ℝ (Fin 2))),
    dist_comm _ (!₂[-1, -√3] : (EuclideanSpace ℝ (Fin 2))), hA, hB, hC, dist_self]
  linarith

/-- Witness for `fermat_exists` / `fermat_torricelli`: the 3-4-5 triangle has all angles
`< 2π/3` (inner products `0, 16, 9 ≥ 0` at the vertices); the Fermat point given by the theorem is
distinct from the three vertices. -/
theorem l14w_fermat_torricelli : ∃ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)),
    t.points = ![!₂[0, 0], !₂[4, 0], !₂[0, 3]] ∧
    ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3 ∧
    ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3 ∧
    ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3 ∧
    ∃ F : (EuclideanSpace ℝ (Fin 2)), ∠ (t.points 0) F (t.points 1) = 2 * π / 3 ∧
      ∠ (t.points 1) F (t.points 2) = 2 * π / 3 ∧ ∠ (t.points 2) F (t.points 0) = 2 * π / 3 ∧
      F ≠ t.points 0 ∧ F ≠ t.points 1 ∧ F ≠ t.points 2 ∧
      ∀ X : (EuclideanSpace ℝ (Fin 2)), dist F (t.points 0) + dist F (t.points 1) + dist F (t.points 2) ≤
        dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2) := by
  have hA : ∠ (l14T.points 1) (l14T.points 0) (l14T.points 2) < 2 * π / 3 :=
    l14_angle_lt (by simp [l14T, l14_inner])
  have hB : ∠ (l14T.points 2) (l14T.points 1) (l14T.points 0) < 2 * π / 3 :=
    l14_angle_lt (by simp [l14T, l14_inner])
  have hC : ∠ (l14T.points 0) (l14T.points 2) (l14T.points 1) < 2 * π / 3 :=
    l14_angle_lt (by simp [l14T, l14_inner])
  obtain ⟨F, h1, h2, h3, hmin⟩ := l14_fermat_torricelli l14T hA hB hC
  exact ⟨l14T, rfl, hA, hB, hC, F, h1, h2, h3, (ne_of_angle h1).symm, (ne_of_angle h2).symm,
    (ne_of_angle h3).symm, hmin⟩

end ErdosMordell
