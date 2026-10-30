import ErdosMordell.Basic

/-!
# The Fermat–Torricelli point

* `fermat_min`: if `∠AFB = ∠BFC = ∠CFA = 2π/3` then `F` minimises `XA + XB + XC`.
  Proof: the unit vectors `uᵢ` from `F` to the vertices have pairwise inner products `-1/2`,
  so `u_A + u_B + u_C = 0`, and `XA ≥ ⟪u_A, A - X⟫ = FA + ⟪u_A, F - X⟫` (Cauchy–Schwarz); sum up.
* `fermat_torricelli`: existence, by the explicit point
  `F = A + (x_A x_C / T) (B - A) + (x_A x_B / T) (C - A)` with `x_A = G + √3 ⟪B-A, C-A⟫`,
  `x_B = G + √3 ⟪A-B, C-B⟫`, `x_C = G + √3 ⟪A-C, B-C⟫`, `G` = twice the area,
  `T = x_B x_C + x_A x_C + x_A x_B` (barycentric weights `∝ 1/x_i`). The angle condition `< 2π/3`
  is exactly what makes every `x_i > 0`.
-/

open Affine EuclideanGeometry AffineMap Real
open scoped RealInnerProductSpace

namespace ErdosMordell

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

lemma cos_two_pi_div_three : Real.cos (2 * π / 3) = -(1 / 2) := by
  rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]

lemma arccos_neg_half : Real.arccos (-(1 / 2)) = 2 * π / 3 := by
  rw [Real.arccos_neg, Real.arccos_eq_of_eq_cos (by positivity) (by linarith [Real.pi_pos])
    Real.cos_pi_div_three.symm]
  ring

/-- An angle of `2π/3` between two vectors means inner product `-1/2 ‖x‖ ‖y‖`. -/
lemma inner_of_angle {x y : V} (h : InnerProductGeometry.angle x y = 2 * π / 3) :
    ⟪x, y⟫ = -(1 / 2) * (‖x‖ * ‖y‖) := by
  rw [← InnerProductGeometry.cos_angle_mul_norm_mul_norm, h, cos_two_pi_div_three]

lemma ne_of_angle {A B F : P} (h : ∠ A F B = 2 * π / 3) : A ≠ F := by
  rintro rfl
  rw [angle_self_left] at h
  linarith [Real.pi_pos]

/-- H2.4 (minimality): a point seeing the three sides under `2π/3` minimises the sum of the
distances to the vertices, over all points of the space. -/
theorem fermat_min (A B C F : P) (hAB : ∠ A F B = 2 * π / 3) (hBC : ∠ B F C = 2 * π / 3)
    (hCA : ∠ C F A = 2 * π / 3) (X : P) :
    dist F A + dist F B + dist F C ≤ dist X A + dist X B + dist X C := by
  have hA : 0 < ‖A -ᵥ F‖ := norm_pos_iff.2 (vsub_ne_zero.2 (ne_of_angle hAB))
  have hB : 0 < ‖B -ᵥ F‖ := norm_pos_iff.2 (vsub_ne_zero.2 (ne_of_angle hBC))
  have hC : 0 < ‖C -ᵥ F‖ := norm_pos_iff.2 (vsub_ne_zero.2 (ne_of_angle hCA))
  have iAB := inner_of_angle hAB
  have iBC := inner_of_angle hBC
  have iCA := inner_of_angle hCA
  set u := ‖A -ᵥ F‖⁻¹ • (A -ᵥ F)
  set v := ‖B -ᵥ F‖⁻¹ • (B -ᵥ F)
  set w := ‖C -ᵥ F‖⁻¹ • (C -ᵥ F)
  have hu : ‖u‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hA.ne']
  have hv : ‖v‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hB.ne']
  have hw : ‖w‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hC.ne']
  have uv : ⟪u, v⟫ = -(1 / 2) := by
    simp only [u, v, real_inner_smul_left, real_inner_smul_right]
    rw [iAB]; field_simp
  have vw : ⟪v, w⟫ = -(1 / 2) := by
    simp only [v, w, real_inner_smul_left, real_inner_smul_right]
    rw [iBC]; field_simp
  have wu : ⟪w, u⟫ = -(1 / 2) := by
    simp only [w, u, real_inner_smul_left, real_inner_smul_right]
    rw [iCA]; field_simp
  have hsum : u + v + w = 0 := by
    rw [← norm_eq_zero, ← sq_eq_zero_iff, ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_self_eq_norm_sq, hu, hv, hw]
    rw [real_inner_comm u v, real_inner_comm v w, real_inner_comm w u] at *
    linarith
  -- `dist X A ≥ ⟪u, A - X⟫ = FA + ⟪u, F - X⟫`
  have key : ∀ (Y : P) (z : V), ‖z‖ = 1 → ‖Y -ᵥ F‖⁻¹ • (Y -ᵥ F) = z → 0 < ‖Y -ᵥ F‖ →
      dist F Y + ⟪z, F -ᵥ X⟫ ≤ dist X Y := by
    intro Y z hz hzY hY
    have h1 : ⟪z, Y -ᵥ X⟫ ≤ dist X Y := by
      rw [dist_comm, dist_eq_norm_vsub V]
      simpa [hz] using real_inner_le_norm z (Y -ᵥ X)
    have h2 : ⟪z, Y -ᵥ F⟫ = dist F Y := by
      rw [← hzY, real_inner_smul_left, real_inner_self_eq_norm_sq, dist_comm,
        dist_eq_norm_vsub V]
      field_simp
    have h3 : Y -ᵥ X = (Y -ᵥ F) + (F -ᵥ X) := (vsub_add_vsub_cancel Y F X).symm
    rw [h3, inner_add_right, h2] at h1
    exact h1
  have kA := key A u hu rfl hA
  have kB := key B v hv rfl hB
  have kC := key C w hw rfl hC
  have : ⟪u, F -ᵥ X⟫ + ⟪v, F -ᵥ X⟫ + ⟪w, F -ᵥ X⟫ = 0 := by
    rw [← inner_add_left, ← inner_add_left, hsum, inner_zero_left]
  linarith

/-- The algebraic certificate behind the explicit Fermat point: with `xᵢ = G + √3 kᵢ`,
`T = x_B x_C + x_A x_C + x_A x_B`, `N = 3 (b² + c² - k + √3 G)`, the vectors `uᵢ` (coefficients
w.r.t. `p = B - A`, `q = C - A`) have `N ⟪uᵢ, uᵢ⟫ = T²`, `N ⟪uᵢ, uⱼ⟫ = -T²/2`. -/
lemma fermat_alg {G s b2 c2 k xA xB xC T N : ℝ} (hG : G ^ 2 = b2 * c2 - k ^ 2) (hs : s ^ 2 = 3)
    (hA : xA = G + s * k) (hB : xB = G + s * (c2 - k)) (hC : xC = G + s * (b2 - k))
    (hT : T = xB * xC + xA * xC + xA * xB) (hN : N = 3 * (b2 + c2 - k + s * G)) :
    N * ((-xC) * (-xC) * c2 + ((-xC) * (-xB) + (-xB) * (-xC)) * k + (-xB) * (-xB) * b2) = T ^ 2 ∧
    N * ((xC + xA) * (xC + xA) * c2 + ((xC + xA) * (-xA) + (-xA) * (xC + xA)) * k + (-xA) * (-xA) * b2) = T ^ 2 ∧
    N * ((-xA) * (-xA) * c2 + ((-xA) * (xB + xA) + (xB + xA) * (-xA)) * k + (xB + xA) * (xB + xA) * b2) = T ^ 2 ∧
    N * ((-xC) * (xC + xA) * c2 + ((-xC) * (-xA) + (-xB) * (xC + xA)) * k + (-xB) * (-xA) * b2) = -T ^ 2 / 2 ∧
    N * ((xC + xA) * (-xA) * c2 + ((xC + xA) * (xB + xA) + (-xA) * (-xA)) * k + (-xA) * (xB + xA) * b2) = -T ^ 2 / 2 ∧
    N * ((-xA) * (-xC) * c2 + ((-xA) * (-xB) + (xB + xA) * (-xC)) * k + (xB + xA) * (-xB) * b2) = -T ^ 2 / 2 := by
  subst hT hN hA hB hC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (-9*G^2 - 9*G*b2*s - 9*G*c2*s + 18*G*k*s - 4*b2^2*s^2 + 3*b2^2 - 2*b2*c2*s^2 - 3*b2*c2 + 8*b2*k*s^2 + 3*b2*k - 4*c2^2*s^2 + 3*c2^2 + 8*c2*k*s^2 + 3*c2*k - 10*k^2*s^2 + 3*k^2) * hG + (-G*b2^2*c2*s - G*b2*c2^2*s - 2*G*b2*c2*k*s + G*b2*k^2*s + G*c2*k^2*s + 2*G*k^3*s - b2^3*c2 - b2^2*c2^2*s^2 + b2^2*c2^2 - b2^2*c2*k + b2^2*k^2 - b2*c2^3 - b2*c2^2*k + 2*b2*c2*k^2*s^2 - 2*b2*c2*k^2 + b2*k^3 + c2^2*k^2 + c2*k^3 - k^4*s^2 + k^4) * hs
  · linear_combination (-9*G^2 - 9*G*b2*s - 4*b2^2*s^2 + 3*b2^2 - 2*b2*c2*s^2 + 6*b2*c2 + 8*b2*k*s^2 - 15*b2*k - 4*c2^2*s^2 + 12*c2^2 + 8*c2*k*s^2 - 24*c2*k - 10*k^2*s^2 + 21*k^2) * hG + (-G*b2^2*c2*s - 4*G*b2*c2^2*s + 4*G*b2*c2*k*s + G*b2*k^2*s + 4*G*c2*k^2*s - 4*G*k^3*s - b2^3*c2 - b2^2*c2^2*s^2 - 2*b2^2*c2^2 + 5*b2^2*c2*k + b2^2*k^2 - 4*b2*c2^3 + 8*b2*c2^2*k + 2*b2*c2*k^2*s^2 - 5*b2*c2*k^2 - 5*b2*k^3 + 4*c2^2*k^2 - 8*c2*k^3 - k^4*s^2 + 7*k^4) * hs
  · linear_combination (-9*G^2 - 9*G*c2*s - 4*b2^2*s^2 + 12*b2^2 - 2*b2*c2*s^2 + 6*b2*c2 + 8*b2*k*s^2 - 24*b2*k - 4*c2^2*s^2 + 3*c2^2 + 8*c2*k*s^2 - 15*c2*k - 10*k^2*s^2 + 21*k^2) * hG + (-4*G*b2^2*c2*s - G*b2*c2^2*s + 4*G*b2*c2*k*s + 4*G*b2*k^2*s + G*c2*k^2*s - 4*G*k^3*s - 4*b2^3*c2 - b2^2*c2^2*s^2 - 2*b2^2*c2^2 + 8*b2^2*c2*k + 4*b2^2*k^2 - b2*c2^3 + 5*b2*c2^2*k + 2*b2*c2*k^2*s^2 - 5*b2*c2*k^2 - 8*b2*k^3 + c2^2*k^2 - 5*c2*k^3 - k^4*s^2 + 7*k^4) * hs
  · linear_combination (9*G^2/2 + 9*G*b2*s - 9*G*k*s + 2*b2^2*s^2 + 3*b2^2 + b2*c2*s^2 + 3*b2*c2/2 - 4*b2*k*s^2 - 6*b2*k + 2*c2^2*s^2 - 6*c2^2 - 4*c2*k*s^2 + 3*c2*k + 5*k^2*s^2 - 3*k^2/2) * hG + (-G*b2^2*c2*s + 2*G*b2*c2^2*s + G*b2*c2*k*s + G*b2*k^2*s - 2*G*c2*k^2*s - G*k^3*s - b2^3*c2 + b2^2*c2^2*s^2/2 - b2^2*c2^2/2 + 2*b2^2*c2*k + b2^2*k^2 + 2*b2*c2^3 - b2*c2^2*k - b2*c2*k^2*s^2 + b2*c2*k^2 - 2*b2*k^3 - 2*c2^2*k^2 + c2*k^3 + k^4*s^2/2 - k^4/2) * hs
  · linear_combination (9*G^2/2 + 9*G*k*s + 2*b2^2*s^2 - 6*b2^2 + b2*c2*s^2 - 15*b2*c2/2 - 4*b2*k*s^2 + 21*b2*k + 2*c2^2*s^2 - 6*c2^2 - 4*c2*k*s^2 + 21*c2*k + 5*k^2*s^2 - 39*k^2/2) * hG + (2*G*b2^2*c2*s + 2*G*b2*c2^2*s - 5*G*b2*c2*k*s - 2*G*b2*k^2*s - 2*G*c2*k^2*s + 5*G*k^3*s + 2*b2^3*c2 + b2^2*c2^2*s^2/2 + 5*b2^2*c2^2/2 - 7*b2^2*c2*k - 2*b2^2*k^2 + 2*b2*c2^3 - 7*b2*c2^2*k - b2*c2*k^2*s^2 + 4*b2*c2*k^2 + 7*b2*k^3 - 2*c2^2*k^2 + 7*c2*k^3 + k^4*s^2/2 - 13*k^4/2) * hs
  · linear_combination (9*G^2/2 + 9*G*c2*s - 9*G*k*s + 2*b2^2*s^2 - 6*b2^2 + b2*c2*s^2 + 3*b2*c2/2 - 4*b2*k*s^2 + 3*b2*k + 2*c2^2*s^2 + 3*c2^2 - 4*c2*k*s^2 - 6*c2*k + 5*k^2*s^2 - 3*k^2/2) * hG + (2*G*b2^2*c2*s - G*b2*c2^2*s + G*b2*c2*k*s - 2*G*b2*k^2*s + G*c2*k^2*s - G*k^3*s + 2*b2^3*c2 + b2^2*c2^2*s^2/2 - b2^2*c2^2/2 - b2^2*c2*k - 2*b2^2*k^2 - b2*c2^3 + 2*b2*c2^2*k - b2*c2*k^2*s^2 + b2*c2*k^2 + b2*k^3 + c2^2*k^2 - 2*c2*k^3 + k^4*s^2/2 - k^4/2) * hs

/-- Two vectors with `N ‖U‖² = N ‖W‖² = T²`, `N ⟪U, W⟫ = -T²/2` make the angle `2π/3`. -/
lemma angle_of_alg {U W : V} {N T : ℝ} (hN : 0 < N) (hT : T ≠ 0) (h1 : N * ⟪U, U⟫ = T ^ 2)
    (h2 : N * ⟪W, W⟫ = T ^ 2) (h12 : N * ⟪U, W⟫ = -T ^ 2 / 2) :
    InnerProductGeometry.angle U W = 2 * π / 3 := by
  rw [real_inner_self_eq_norm_sq] at h1 h2
  have hU : ‖U‖ = ‖W‖ := by
    have : ‖U‖ ^ 2 = ‖W‖ ^ 2 := by
      have := h1.trans h2.symm
      exact mul_left_cancel₀ hN.ne' this
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  have hU0 : ‖U‖ ^ 2 ≠ 0 := by
    intro h; rw [h, mul_zero] at h1; exact hT (pow_eq_zero_iff two_ne_zero |>.1 h1.symm)
  have e : ⟪U, W⟫ / (‖U‖ * ‖U‖) = -(1 / 2) := by
    rw [← sq, div_eq_iff hU0]
    apply mul_left_cancel₀ hN.ne'
    linear_combination h12 + h1 / 2
  unfold InnerProductGeometry.angle
  rw [← hU, e, arccos_neg_half]

/-- An angle `< 2π/3` between nonzero vectors gives `⟪x, y⟫ > -1/2 ‖x‖ ‖y‖`. -/
lemma inner_gt_of_angle_lt {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : InnerProductGeometry.angle x y < 2 * π / 3) :
    -(1 / 2) * (‖x‖ * ‖y‖) < ⟪x, y⟫ := by
  have hc : Real.cos (2 * π / 3) < Real.cos (InnerProductGeometry.angle x y) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg x y)
      (by linarith [Real.pi_pos]) h
  rw [cos_two_pi_div_three] at hc
  rw [← InnerProductGeometry.cos_angle_mul_norm_mul_norm]
  have : 0 < ‖x‖ * ‖y‖ := mul_pos (norm_pos_iff.2 hx) (norm_pos_iff.2 hy)
  nlinarith

/-- Positivity of the weights `x_i = G + √3 mᵢ` from the angle condition `mᵢ > -P/2`. -/
lemma x_pos {G s m Q : ℝ} (hG : 0 < G) (hs : s ^ 2 = 3) (hs0 : 0 < s)
    (hGm : G ^ 2 = Q ^ 2 - m ^ 2) (hm : -(1 / 2) * Q < m) : 0 < G + s * m := by
  rcases le_or_gt 0 m with h | h
  · positivity
  · by_contra hc
    replace hc := not_lt.1 hc
    have h1 : G ^ 2 ≤ (s * m) ^ 2 := by nlinarith
    nlinarith

/-- `x • U` with `x > 0`, rewritten. -/
lemma vsub_F_eq {p q : V} {T x α β γ δ : ℝ} (hT : T ≠ 0) (h1 : α * T = x * γ) (h2 : β * T = x * δ) :
    α • p + β • q = (x / T) • (γ • p + δ • q) := by
  rw [smul_add, smul_smul, smul_smul]
  congr 2 <;> field_simp <;> linarith

/-- Existence of the Fermat point, by explicit barycentric weights. -/
theorem fermat_exists (t : Triangle ℝ P)
    (hA : ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3)
    (hB : ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3)
    (hC : ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3) :
    ∃ F : P, ∠ (t.points 0) F (t.points 1) = 2 * π / 3 ∧
      ∠ (t.points 1) F (t.points 2) = 2 * π / 3 ∧ ∠ (t.points 2) F (t.points 0) = 2 * π / 3 := by
  set A := t.points 0
  set p := t.points 1 -ᵥ A with hp
  set q := t.points 2 -ᵥ A with hq
  have hB' : t.points 1 = p +ᵥ A := (vsub_vadd _ _).symm
  have hC' : t.points 2 = q +ᵥ A := (vsub_vadd _ _).symm
  have hp0 : p ≠ 0 := vsub_ne_zero.2 (points_ne t (by decide : (1 : Fin 3) ≠ 0))
  have hq0 : q ≠ 0 := vsub_ne_zero.2 (points_ne t (by decide : (2 : Fin 3) ≠ 0))
  have hqp0 : q - p ≠ 0 := by
    rw [hp, hq, vsub_sub_vsub_cancel_right]
    exact vsub_ne_zero.2 (points_ne t (by decide : (2 : Fin 3) ≠ 1))
  have hncol : ¬ Collinear ℝ ({t.points 1, A, t.points 2} : Set P) := by
    rw [← affineIndependent_iff_not_collinear_of_ne (p := t.points) (i₁ := 1) (i₂ := 0) (i₃ := 2)
      (by decide) (by decide) (by decide)]
    exact t.independent
  have hsin := sin_pos_of_not_collinear hncol
  -- the angles as vector angles
  have eA : ∠ (t.points 1) A (t.points 2) = InnerProductGeometry.angle p q := rfl
  have eB : ∠ (t.points 2) (t.points 1) A = InnerProductGeometry.angle (q - p) (-p) := by
    rw [EuclideanGeometry.angle, hp, hq, vsub_sub_vsub_cancel_right, neg_vsub_eq_vsub_rev]
  have eC : ∠ A (t.points 2) (t.points 1) = InnerProductGeometry.angle (-q) (p - q) := by
    rw [EuclideanGeometry.angle, hp, hq, vsub_sub_vsub_cancel_right, neg_vsub_eq_vsub_rev]
  rw [eA] at hA hsin
  rw [eB] at hB
  rw [eC] at hC
  set b2 := ‖q‖ ^ 2 with hb2
  set c2 := ‖p‖ ^ 2 with hc2
  set k := ⟪p, q⟫ with hk
  -- Gram determinant
  have hgram : 0 < b2 * c2 - k ^ 2 := by
    have h1 := InnerProductGeometry.cos_angle_mul_norm_mul_norm p q
    have h2 := Real.sin_sq_add_cos_sq (InnerProductGeometry.angle p q)
    have hpn := norm_pos_iff.2 hp0
    have hqn := norm_pos_iff.2 hq0
    have : k ^ 2 = Real.cos (InnerProductGeometry.angle p q) ^ 2 * (b2 * c2) := by
      rw [hk, ← h1, hb2, hc2]; ring
    rw [this]
    have : 0 < b2 * c2 := by positivity
    nlinarith [pow_pos hsin 2]
  set G := Real.sqrt (b2 * c2 - k ^ 2) with hGdef
  have hG : G ^ 2 = b2 * c2 - k ^ 2 := Real.sq_sqrt hgram.le
  have hG0 : 0 < G := Real.sqrt_pos.2 hgram
  set s := Real.sqrt 3 with hsdef
  have hs : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by norm_num)
  set xA := G + s * k with hxA
  set xB := G + s * (c2 - k) with hxB
  set xC := G + s * (b2 - k) with hxC
  -- positivity of the weights from the angle hypotheses
  have pA : 0 < xA := by
    refine x_pos hG0 hs hs0 (Q := ‖p‖ * ‖q‖) (by rw [hG]; ring) ?_
    exact inner_gt_of_angle_lt hp0 hq0 hA
  have pB : 0 < xB := by
    have h := inner_gt_of_angle_lt hqp0 (neg_ne_zero.2 hp0) hB
    have e : ⟪q - p, -p⟫ = c2 - k := by
      rw [inner_neg_right, inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm]; ring
    have e2 : ‖q - p‖ ^ 2 = b2 + c2 - 2 * k := by
      rw [norm_sub_sq_real, real_inner_comm]; ring
    rw [e, norm_neg] at h
    refine x_pos hG0 hs hs0 (Q := ‖q - p‖ * ‖p‖) ?_ h
    rw [hG, mul_pow, e2]; ring
  have pC : 0 < xC := by
    have h := inner_gt_of_angle_lt (neg_ne_zero.2 hq0) (sub_ne_zero.2 ?_) hC
    · have e : ⟪-q, p - q⟫ = b2 - k := by
        rw [inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm]; ring
      have e2 : ‖p - q‖ ^ 2 = b2 + c2 - 2 * k := by
        rw [norm_sub_sq_real]; ring
      rw [e, norm_neg] at h
      refine x_pos hG0 hs hs0 (Q := ‖q‖ * ‖p - q‖) ?_ h
      rw [hG, mul_pow, e2]; ring
    · intro h; exact hqp0 (by rw [h, sub_self])
  set T := xB * xC + xA * xC + xA * xB with hT
  have hT0 : 0 < T := by positivity
  set N := 3 * (b2 + c2 - k + s * G) with hN
  have hN0 : 0 < N := by
    have : k ≤ ‖p‖ * ‖q‖ := real_inner_le_norm p q
    have : 0 < b2 + c2 - k := by
      nlinarith [sq_nonneg (‖p‖ - ‖q‖), norm_pos_iff.2 hp0, norm_pos_iff.2 hq0]
    positivity
  obtain ⟨a11, a22, a33, a12, a23, a31⟩ := fermat_alg hG hs hxA hxB hxC hT hN
  let U1 : V := (-xC) • p + (-xB) • q
  let U2 : V := (xC + xA) • p + (-xA) • q
  let U3 : V := (-xA) • p + (xB + xA) • q
  let F : P := ((xA * xC / T) • p + (xA * xB / T) • q) +ᵥ A
  have fA : A -ᵥ F = (xA / T) • U1 := by
    rw [vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, neg_add, ← neg_smul, ← neg_smul]
    exact vsub_F_eq hT0.ne' (by field_simp; try ring) (by field_simp; try ring)
  have fB : t.points 1 -ᵥ F = (xB / T) • U2 := by
    rw [hB', vadd_vsub_vadd_cancel_right]
    have : p - ((xA * xC / T) • p + (xA * xB / T) • q) =
        (1 - xA * xC / T) • p + (-(xA * xB / T)) • q := by
      rw [sub_smul, one_smul, neg_smul]; abel
    rw [this]
    exact vsub_F_eq hT0.ne' (by field_simp; try (rw [hT]; ring)) (by field_simp; try ring)
  have fC : t.points 2 -ᵥ F = (xC / T) • U3 := by
    rw [hC', vadd_vsub_vadd_cancel_right]
    have : q - ((xA * xC / T) • p + (xA * xB / T) • q) =
        (-(xA * xC / T)) • p + (1 - xA * xB / T) • q := by
      rw [sub_smul, one_smul, neg_smul]; abel
    rw [this]
    exact vsub_F_eq hT0.ne' (by field_simp; try ring) (by field_simp; try (rw [hT]; ring))
  have i11 : N * ⟪U1, U1⟫ = T ^ 2 := by rw [inner_comb]; exact a11
  have i22 : N * ⟪U2, U2⟫ = T ^ 2 := by rw [inner_comb]; exact a22
  have i33 : N * ⟪U3, U3⟫ = T ^ 2 := by rw [inner_comb]; exact a33
  have i12 : N * ⟪U1, U2⟫ = -T ^ 2 / 2 := by rw [inner_comb]; exact a12
  have i23 : N * ⟪U2, U3⟫ = -T ^ 2 / 2 := by rw [inner_comb]; exact a23
  have i31 : N * ⟪U3, U1⟫ = -T ^ 2 / 2 := by rw [inner_comb]; exact a31
  have dA : 0 < xA / T := div_pos pA hT0
  have dB : 0 < xB / T := div_pos pB hT0
  have dC : 0 < xC / T := div_pos pC hT0
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [EuclideanGeometry.angle, fA, fB, InnerProductGeometry.angle_smul_left_of_pos _ _ dA,
      InnerProductGeometry.angle_smul_right_of_pos _ _ dB]
    exact angle_of_alg hN0 hT0.ne' i11 i22 i12
  · rw [EuclideanGeometry.angle, fB, fC, InnerProductGeometry.angle_smul_left_of_pos _ _ dB,
      InnerProductGeometry.angle_smul_right_of_pos _ _ dC]
    exact angle_of_alg hN0 hT0.ne' i22 i33 i23
  · rw [EuclideanGeometry.angle, fC, fA, InnerProductGeometry.angle_smul_left_of_pos _ _ dC,
      InnerProductGeometry.angle_smul_right_of_pos _ _ dA]
    exact angle_of_alg hN0 hT0.ne' i33 i11 i31

/-- H2.4 (Fermat–Torricelli point): if all angles of `t` are `< 2π/3`, there is a point `F`
with `∠AFB = ∠BFC = ∠CFA = 2π/3`, and it minimises `XA + XB + XC`. -/
theorem fermat_torricelli (t : Triangle ℝ P)
    (hA : ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3)
    (hB : ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3)
    (hC : ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3) :
    ∃ F : P, ∠ (t.points 0) F (t.points 1) = 2 * π / 3 ∧
      ∠ (t.points 1) F (t.points 2) = 2 * π / 3 ∧
      ∠ (t.points 2) F (t.points 0) = 2 * π / 3 ∧
      ∀ X : P, dist F (t.points 0) + dist F (t.points 1) + dist F (t.points 2) ≤
        dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2) := by
  suffices h : ∃ F : P, ∠ (t.points 0) F (t.points 1) = 2 * π / 3 ∧
      ∠ (t.points 1) F (t.points 2) = 2 * π / 3 ∧ ∠ (t.points 2) F (t.points 0) = 2 * π / 3 by
    obtain ⟨F, h1, h2, h3⟩ := h
    exact ⟨F, h1, h2, h3, fermat_min _ _ _ F h1 h2 h3⟩
  exact fermat_exists t hA hB hC

end ErdosMordell
