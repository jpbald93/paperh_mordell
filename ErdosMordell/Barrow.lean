import ErdosMordell.Basic

/-!
# Barrow's inequality

For `X` strictly inside the triangle `ABC` and `U, V, W` the feet on `BC, CA, AB` of the internal
bisectors of `∠BXC, ∠CXA, ∠AXB`: `XA + XB + XC ≥ 2 (XU + XV + XW)`.

Angle-free proof. With `a = A - X`, `b = B - X`, `c = C - X`, `x = ‖a‖`, `y = ‖b‖`, `z = ‖c‖`,
`p = ⟪b, c⟫`, `q = ⟪c, a⟫`, `r = ⟪a, b⟫`:
* bisector theorem: `XU² (y + z)² = 2yz (yz + p)`, hence `XU ≤ √y √z α` with
  `α² = (yz + p) / (2yz)` (the half-angle cosine);
* `w₀ a + w₁ b + w₂ c = 0` gives `T = xyz + xp + yq + zr ≤ 0` and the vanishing of the 3×3 Gram
  determinant, which together give `α² + β² + γ² + 2αβγ = 1`;
* Wolstenholme: then `X² + Y² + Z² ≥ 2 (αYZ + βZX + γXY)` (a sum of squares), with
  `X = √x`, `Y = √y`, `Z = √z`.
-/

open Affine EuclideanGeometry AffineMap
open scoped RealInnerProductSpace

namespace ErdosMordell

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Wolstenholme's inequality, in the form needed (cosines of three angles summing to `π`). -/
lemma wolstenholme {α β γ X Y Z : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hγ1 : γ ^ 2 ≤ 1)
    (hR : α ^ 2 + β ^ 2 + γ ^ 2 + 2 * α * β * γ = 1) :
    2 * (α * Y * Z + β * Z * X + γ * X * Y) ≤ X ^ 2 + Y ^ 2 + Z ^ 2 := by
  have key : (1 - γ ^ 2) * (X ^ 2 + Y ^ 2 + Z ^ 2 - 2 * (α * Y * Z + β * Z * X + γ * X * Y)) =
      (1 - γ ^ 2) * (X - γ * Y - β * Z) ^ 2 + ((1 - γ ^ 2) * Y - (α + β * γ) * Z) ^ 2 := by
    linear_combination (-Z ^ 2) * hR
  rcases hγ1.lt_or_eq with h | h
  · have h1 : 0 < 1 - γ ^ 2 := by linarith
    have hq : 0 ≤ (1 - γ ^ 2) *
        (X ^ 2 + Y ^ 2 + Z ^ 2 - 2 * (α * Y * Z + β * Z * X + γ * X * Y)) := by
      rw [key]; positivity
    have := (mul_nonneg_iff_of_pos_left h1).1 hq
    linarith
  · have hγ' : γ = 1 := by nlinarith
    subst hγ'
    have hab : (α + β) ^ 2 = 0 := by linarith
    have hab' : α + β = 0 := pow_eq_zero_iff two_ne_zero |>.1 hab
    have ha : α = 0 := by linarith
    have hb : β = 0 := by linarith
    subst ha hb
    nlinarith [sq_nonneg (X - Y), sq_nonneg Z]

/-- From `w₀ a + w₁ b + w₂ c = 0` with positive weights: `T = xyz + xp + yq + zr ≤ 0`. -/
lemma barrow_T {x y z p q r w0 w1 w2 : ℝ} (hx : 0 < x)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2)
    (hL1 : w0 * x ^ 2 + w1 * r + w2 * q = 0) (hL2 : w0 * r + w1 * y ^ 2 + w2 * p = 0)
    (hL3 : w0 * q + w1 * p + w2 * z ^ 2 = 0)
    (hp : 0 ≤ y * z + p) (hq : 0 ≤ z * x + q) (hr : 0 ≤ x * y + r) :
    x * y * z + x * p + y * q + z * r ≤ 0 := by
  by_contra hT
  replace hT := lt_of_not_ge hT
  have e1 : w2 * (x * y * z + x * p + y * q + z * r) +
      (x * y + r) * (w0 * x + w1 * y - w2 * z) = 0 := by linear_combination y * hL1 + x * hL2
  have e2 : w0 * (x * y * z + x * p + y * q + z * r) +
      (y * z + p) * (w1 * y + w2 * z - w0 * x) = 0 := by linear_combination z * hL2 + y * hL3
  have e3 : w1 * (x * y * z + x * p + y * q + z * r) +
      (z * x + q) * (w2 * z + w0 * x - w1 * y) = 0 := by linear_combination z * hL1 + x * hL3
  have f1 : w0 * x + w1 * y - w2 * z < 0 := by
    by_contra h; replace h := le_of_not_gt h
    linarith [mul_nonneg hr h, mul_pos hw2 hT]
  have f2 : w1 * y + w2 * z - w0 * x < 0 := by
    by_contra h; replace h := le_of_not_gt h
    linarith [mul_nonneg hp h, mul_pos hw0 hT]
  have f3 : w2 * z + w0 * x - w1 * y < 0 := by
    by_contra h; replace h := le_of_not_gt h
    linarith [mul_nonneg hq h, mul_pos hw1 hT]
  linarith [mul_pos hw0 hx]

/-- From `w₀ a + w₁ b + w₂ c = 0` with weights summing to `1`: the 3×3 Gram determinant of
`a, b, c` vanishes. -/
lemma barrow_gram {x y z p q r w0 w1 w2 : ℝ} (hw : w0 + w1 + w2 = 1)
    (hL1 : w0 * x ^ 2 + w1 * r + w2 * q = 0) (hL2 : w0 * r + w1 * y ^ 2 + w2 * p = 0)
    (hL3 : w0 * q + w1 * p + w2 * z ^ 2 = 0) :
    x ^ 2 * y ^ 2 * z ^ 2 - x ^ 2 * p ^ 2 - y ^ 2 * q ^ 2 - z ^ 2 * r ^ 2 + 2 * p * q * r = 0 := by
  linear_combination (-p ^ 2 + p * q + p * r - q * y ^ 2 - r * z ^ 2 + y ^ 2 * z ^ 2) * hL1 +
    (p * q - p * x ^ 2 - q ^ 2 + q * r - r * z ^ 2 + x ^ 2 * z ^ 2) * hL2 +
    (p * r - p * x ^ 2 + q * r - q * y ^ 2 - r ^ 2 + x ^ 2 * y ^ 2) * hL3 -
    (x ^ 2 * y ^ 2 * z ^ 2 - x ^ 2 * p ^ 2 - y ^ 2 * q ^ 2 - z ^ 2 * r ^ 2 + 2 * p * q * r) * hw

/-- The half-angle cosines satisfy `α² + β² + γ² + 2αβγ = 1`. -/
lemma barrow_halfangle {x y z p q r α β γ : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hγ0 : 0 ≤ γ)
    (hα : α ^ 2 = (y * z + p) / (2 * y * z)) (hβ : β ^ 2 = (z * x + q) / (2 * z * x))
    (hγ : γ ^ 2 = (x * y + r) / (2 * x * y))
    (hT : x * y * z + x * p + y * q + z * r ≤ 0)
    (hG : x ^ 2 * y ^ 2 * z ^ 2 - x ^ 2 * p ^ 2 - y ^ 2 * q ^ 2 - z ^ 2 * r ^ 2 + 2 * p * q * r
      = 0) :
    α ^ 2 + β ^ 2 + γ ^ 2 + 2 * α * β * γ = 1 := by
  have hE : α ^ 2 + β ^ 2 + γ ^ 2 - 1 = (x * y * z + x * p + y * q + z * r) / (2 * x * y * z) := by
    rw [hα, hβ, hγ]; field_simp; ring
  have hE2 : (α ^ 2 + β ^ 2 + γ ^ 2 - 1) ^ 2 - 4 * (α ^ 2 * β ^ 2 * γ ^ 2) =
      -(x ^ 2 * y ^ 2 * z ^ 2 - x ^ 2 * p ^ 2 - y ^ 2 * q ^ 2 - z ^ 2 * r ^ 2 + 2 * p * q * r) /
        (4 * x ^ 2 * y ^ 2 * z ^ 2) := by
    rw [hα, hβ, hγ]; field_simp; ring
  rw [hG, neg_zero, zero_div] at hE2
  have hEn : α ^ 2 + β ^ 2 + γ ^ 2 - 1 ≤ 0 := by
    rw [hE]; exact div_nonpos_of_nonpos_of_nonneg hT (by positivity)
  have h0 : 0 ≤ 2 * α * β * γ := by positivity
  have : (-(α ^ 2 + β ^ 2 + γ ^ 2 - 1)) ^ 2 = (2 * α * β * γ) ^ 2 := by
    linear_combination hE2
  have := (pow_left_inj₀ (by linarith) h0 two_ne_zero).1 this
  linarith

/-- A bisector length is at most `√s √t · cos(half angle)`. -/
lemma barrow_bound {u s t m e : ℝ} (hs : 0 < s) (ht : 0 < t) (hu : 0 ≤ u) (hm : 0 ≤ s * t + m)
    (he : e ^ 2 = (s * t + m) / (2 * s * t)) (h : u ^ 2 * (s + t) ^ 2 = 2 * s * t * (s * t + m)) :
    u ≤ Real.sqrt s * Real.sqrt t * |e| := by
  have h1 : u ^ 2 ≤ (Real.sqrt s * Real.sqrt t * |e|) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hs.le, Real.sq_sqrt ht.le, sq_abs, he]
    have e1 : s * t * ((s * t + m) / (2 * s * t)) = (s * t + m) / 2 := by field_simp
    rw [e1]
    have hst : 0 < (s + t) ^ 2 := by positivity
    have : u ^ 2 * (s + t) ^ 2 ≤ (s * t + m) / 2 * (s + t) ^ 2 := by
      rw [h]; nlinarith [mul_nonneg hm (sq_nonneg (s - t))]
    exact le_of_mul_le_mul_right this hst
  exact (pow_le_pow_iff_left₀ hu (by positivity) two_ne_zero).1 h1

/-- The scalar core of Barrow's inequality. -/
lemma barrow_scalar {x y z p q r w0 w1 w2 U V W : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hw : w0 + w1 + w2 = 1)
    (hL1 : w0 * x ^ 2 + w1 * r + w2 * q = 0) (hL2 : w0 * r + w1 * y ^ 2 + w2 * p = 0)
    (hL3 : w0 * q + w1 * p + w2 * z ^ 2 = 0)
    (hp : 0 ≤ y * z + p) (hq : 0 ≤ z * x + q) (hr : r ≤ x * y) (hr' : 0 ≤ x * y + r)
    (hU0 : 0 ≤ U) (hV0 : 0 ≤ V) (hW0 : 0 ≤ W)
    (hU : U ^ 2 * (y + z) ^ 2 = 2 * y * z * (y * z + p))
    (hV : V ^ 2 * (z + x) ^ 2 = 2 * z * x * (z * x + q))
    (hW : W ^ 2 * (x + y) ^ 2 = 2 * x * y * (x * y + r)) :
    2 * (U + V + W) ≤ x + y + z := by
  have hT := barrow_T hx hw0 hw1 hw2 hL1 hL2 hL3 hp hq hr'
  have hG := barrow_gram hw hL1 hL2 hL3
  have hA0 : 0 ≤ (y * z + p) / (2 * y * z) := div_nonneg hp (by positivity)
  have hB0 : 0 ≤ (z * x + q) / (2 * z * x) := div_nonneg hq (by positivity)
  have hC0 : 0 ≤ (x * y + r) / (2 * x * y) := div_nonneg hr' (by positivity)
  have hα := Real.sq_sqrt hA0
  have hβ := Real.sq_sqrt hB0
  have hγ := Real.sq_sqrt hC0
  have hγ1 : Real.sqrt ((x * y + r) / (2 * x * y)) ^ 2 ≤ 1 := by
    rw [hγ, div_le_one (by positivity)]; linarith
  have hR := barrow_halfangle hx hy hz (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) hα hβ hγ hT hG
  have bU := barrow_bound hy hz hU0 hp hα hU
  have bV := barrow_bound hz hx hV0 hq hβ hV
  have bW := barrow_bound hx hy hW0 hr' hγ hW
  rw [abs_of_nonneg (Real.sqrt_nonneg _)] at bU bV bW
  have hQ := wolstenholme (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hγ1 hR
    (X := Real.sqrt x) (Y := Real.sqrt y) (Z := Real.sqrt z)
  rw [Real.sq_sqrt hx.le, Real.sq_sqrt hy.le, Real.sq_sqrt hz.le] at hQ
  linarith

/-- The Gram determinant of `B - X`, `C - X` in terms of the barycentric weight of `A`. -/
lemma gram_frame {A B C X : P} {w1 w2 : ℝ} (hX : X -ᵥ A = w1 • (B -ᵥ A) + w2 • (C -ᵥ A)) :
    ‖B -ᵥ X‖ ^ 2 * ‖C -ᵥ X‖ ^ 2 - ⟪B -ᵥ X, C -ᵥ X⟫ ^ 2 =
      (1 - w1 - w2) ^ 2 * (‖B -ᵥ A‖ ^ 2 * ‖C -ᵥ A‖ ^ 2 - ⟪B -ᵥ A, C -ᵥ A⟫ ^ 2) := by
  rw [← vsub_sub_vsub_cancel_right B X A, ← vsub_sub_vsub_cancel_right C X A, hX]
  generalize B -ᵥ A = p
  generalize C -ᵥ A = q
  have e1 : p - (w1 • p + w2 • q) = (1 - w1) • p + (-w2) • q := by module
  have e2 : q - (w1 • p + w2 • q) = (-w1) • p + (1 - w2) • q := by module
  rw [e1, e2, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_comb, inner_comb,
    inner_comb]
  ring

/-- Positivity of the Gram determinant for three non-collinear points. -/
lemma gram_pos_of_not_collinear {A B C : P} (h : ¬ Collinear ℝ ({B, A, C} : Set P)) :
    0 < ‖B -ᵥ A‖ ^ 2 * ‖C -ᵥ A‖ ^ 2 - ⟪B -ᵥ A, C -ᵥ A⟫ ^ 2 := by
  have hsin := sin_pos_of_not_collinear h
  have h1 := InnerProductGeometry.cos_angle_mul_norm_mul_norm (B -ᵥ A) (C -ᵥ A)
  have h2 := Real.sin_sq_add_cos_sq (∠ B A C)
  have hpn : 0 < ‖B -ᵥ A‖ := norm_pos_iff.2 (vsub_ne_zero.2 (ne₁₂_of_not_collinear h))
  have hqn : 0 < ‖C -ᵥ A‖ := norm_pos_iff.2 (vsub_ne_zero.2 (ne₂₃_of_not_collinear h).symm)
  rw [← h1]
  change 0 < _ - (Real.cos (∠ B A C) * _) ^ 2
  have : 0 < ‖B -ᵥ A‖ ^ 2 * ‖C -ᵥ A‖ ^ 2 := by positivity
  nlinarith [pow_pos hsin 2]

/-- The bisector theorem, in squared-length form. -/
lemma bisector_dist {X B C U : P} (hU : Wbtw ℝ B U C) (hang : ∠ B X U = ∠ U X C)
    (hg : 0 < ‖B -ᵥ X‖ ^ 2 * ‖C -ᵥ X‖ ^ 2 - ⟪B -ᵥ X, C -ᵥ X⟫ ^ 2) :
    dist X U ^ 2 * (‖B -ᵥ X‖ + ‖C -ᵥ X‖) ^ 2 =
      2 * ‖B -ᵥ X‖ * ‖C -ᵥ X‖ * (‖B -ᵥ X‖ * ‖C -ᵥ X‖ + ⟪B -ᵥ X, C -ᵥ X⟫) := by
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hU
  have hu : lineMap B C s -ᵥ X = (1 - s) • (B -ᵥ X) + s • (C -ᵥ X) := by
    rw [lineMap_apply, vadd_vsub_assoc, ← vsub_sub_vsub_cancel_right C B X]
    module
  rw [dist_comm, dist_eq_norm_vsub V, hu]
  rw [EuclideanGeometry.angle, EuclideanGeometry.angle, hu] at hang
  clear hu
  generalize B -ᵥ X = b at *
  generalize C -ᵥ X = c at *
  have hb0 : b ≠ 0 := by rintro rfl; simp at hg
  have hc0 : c ≠ 0 := by rintro rfl; simp at hg
  have hy := norm_pos_iff.2 hb0
  have hz := norm_pos_iff.2 hc0
  have hp := abs_lt.1 (abs_lt_of_sq_lt_sq (by nlinarith) (by positivity) :
    |⟪b, c⟫| < ‖b‖ * ‖c‖)
  have hu2 : ‖(1 - s) • b + s • c‖ ^ 2 =
      (1 - s) ^ 2 * ‖b‖ ^ 2 + 2 * s * (1 - s) * ⟪b, c⟫ + s ^ 2 * ‖c‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_comb]; ring
  have hbu : ⟪b, (1 - s) • b + s • c⟫ = (1 - s) * ‖b‖ ^ 2 + s * ⟪b, c⟫ := by
    have := inner_comb b c 1 0 (1 - s) s; simpa using this
  have hcu : ⟪(1 - s) • b + s • c, c⟫ = (1 - s) * ⟪b, c⟫ + s * ‖c‖ ^ 2 := by
    have := inner_comb b c (1 - s) s 0 1; simpa using this
  have hun : 0 < ‖(1 - s) • b + s • c‖ := by
    have : 0 < ‖(1 - s) • b + s • c‖ ^ 2 := by
      rw [hu2]
      rcases hs0.lt_or_eq with h0 | h0
      · rcases hs1.lt_or_eq with h1 | h1
        · nlinarith [mul_pos (mul_pos h0 (sub_pos.2 h1)) (by linarith : 0 < ‖b‖ * ‖c‖ + ⟪b, c⟫),
            sq_nonneg ((1 - s) * ‖b‖ - s * ‖c‖)]
        · subst h1; nlinarith
      · subst h0; nlinarith
    exact pos_of_mul_pos_left (by nlinarith : 0 < ‖(1 - s) • b + s • c‖ * ‖(1 - s) • b + s • c‖)
      (norm_nonneg _)
  have hc := congrArg Real.cos hang
  rw [InnerProductGeometry.cos_angle, InnerProductGeometry.cos_angle,
    div_eq_div_iff (by positivity) (by positivity), hbu, hcu] at hc
  have h1 : ‖(1 - s) • b + s • c‖ * ((‖b‖ * ‖c‖ - ⟪b, c⟫) * ((1 - s) * ‖b‖ - s * ‖c‖)) = 0 := by
    linear_combination hc
  have h2 := (mul_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hun.ne')).resolve_left
    (by linarith)
  rw [hu2]
  linear_combination (2 * ⟪b, c⟫ * s * ‖b‖ + 2 * ⟪b, c⟫ * s * ‖c‖ - 2 * ⟪b, c⟫ * ‖c‖ -
    s * ‖b‖ ^ 3 - s * ‖b‖ ^ 2 * ‖c‖ - s * ‖b‖ * ‖c‖ ^ 2 - s * ‖c‖ ^ 3 + ‖b‖ ^ 3 +
    2 * ‖b‖ ^ 2 * ‖c‖ - ‖b‖ * ‖c‖ ^ 2) * h2

/-- Barrow's inequality in vector form: `a, b, c` the vectors from `X` to the vertices. -/
lemma barrow_vec {a b c : V} {w0 w1 w2 U V' W : ℝ} (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2)
    (hw : w0 + w1 + w2 = 1) (hsum : w0 • a + w1 • b + w2 • c = 0)
    (hgp : 0 < ‖b‖ ^ 2 * ‖c‖ ^ 2 - ⟪b, c⟫ ^ 2) (hgq : 0 < ‖c‖ ^ 2 * ‖a‖ ^ 2 - ⟪c, a⟫ ^ 2)
    (hgr : 0 < ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2)
    (hU0 : 0 ≤ U) (hV0 : 0 ≤ V') (hW0 : 0 ≤ W)
    (bU : U ^ 2 * (‖b‖ + ‖c‖) ^ 2 = 2 * ‖b‖ * ‖c‖ * (‖b‖ * ‖c‖ + ⟪b, c⟫))
    (bV : V' ^ 2 * (‖c‖ + ‖a‖) ^ 2 = 2 * ‖c‖ * ‖a‖ * (‖c‖ * ‖a‖ + ⟪c, a⟫))
    (bW : W ^ 2 * (‖a‖ + ‖b‖) ^ 2 = 2 * ‖a‖ * ‖b‖ * (‖a‖ * ‖b‖ + ⟪a, b⟫)) :
    2 * (U + V' + W) ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have L : ∀ e : V, w0 * ⟪e, a⟫ + w1 * ⟪e, b⟫ + w2 * ⟪e, c⟫ = 0 := fun e ↦ by
    have := congrArg (fun v ↦ ⟪e, v⟫) hsum
    simpa [inner_add_right, real_inner_smul_right] using this
  have L1 := L a
  have L2 := L b
  have L3 := L c
  rw [real_inner_self_eq_norm_sq] at L1 L2 L3
  have ha0 : a ≠ 0 := by rintro rfl; simp at hgr
  have hb0 : b ≠ 0 := by rintro rfl; simp at hgp
  have hc0 : c ≠ 0 := by rintro rfl; simp at hgq
  have hpq : ∀ {u v : V}, 0 < ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 →
      -(‖u‖ * ‖v‖) < ⟪u, v⟫ ∧ ⟪u, v⟫ < ‖u‖ * ‖v‖ := fun h ↦
    abs_lt.1 (abs_lt_of_sq_lt_sq (by nlinarith) (by positivity))
  have p1 := hpq hgp
  have p2 := hpq hgq
  have p3 := hpq hgr
  refine barrow_scalar (norm_pos_iff.2 ha0) (norm_pos_iff.2 hb0) (norm_pos_iff.2 hc0)
    hw0 hw1 hw2 hw (p := ⟪b, c⟫) (q := ⟪c, a⟫) (r := ⟪a, b⟫) ?_ ?_ ?_
    (by linarith) (by linarith) p3.2.le (by linarith) hU0 hV0 hW0 bU bV bW
  · rw [real_inner_comm c a] at L1; linear_combination L1
  · rw [real_inner_comm a b] at L2; linear_combination L2
  · rw [real_inner_comm b c] at L3; linear_combination L3

/-- `w₀ (A - X) + w₁ (B - X) + w₂ (C - X) = 0` for `X` the affine combination. -/
lemma weighted_vsub_eq_zero (t : Triangle ℝ P) (w : Fin 3 → ℝ) (hw1 : ∑ i, w i = 1) :
    w 0 • (t.points 0 -ᵥ Finset.univ.affineCombination ℝ t.points w) +
      w 1 • (t.points 1 -ᵥ Finset.univ.affineCombination ℝ t.points w) +
      w 2 • (t.points 2 -ᵥ Finset.univ.affineCombination ℝ t.points w) = 0 := by
  have h := Finset.univ.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w t.points
    hw1 (Finset.univ.affineCombination ℝ t.points w)
  have h2 : Finset.univ.weightedVSubOfPoint t.points
      (Finset.univ.affineCombination ℝ t.points w) w = 0 := by
    have := congrArg (fun Y ↦ Y -ᵥ Finset.univ.affineCombination ℝ t.points w) h
    simpa using this.symm
  rw [Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three] at h2
  exact h2

/-- H2.3 (Barrow's inequality): for `X` strictly inside the triangle and `U ∈ [BC]`, `V ∈ [CA]`,
`W ∈ [AB]` on the internal bisectors of `∠BXC`, `∠CXA`, `∠AXB`,
`XA + XB + XC ≥ 2 (XU + XV + XW)`. -/
theorem barrow (t : Triangle ℝ P) (X U V' W : P)
    (hX : ∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
      X = Finset.univ.affineCombination ℝ t.points w)
    (hU : Wbtw ℝ (t.points 1) U (t.points 2)) (hV : Wbtw ℝ (t.points 2) V' (t.points 0))
    (hW : Wbtw ℝ (t.points 0) W (t.points 1))
    (hUa : ∠ (t.points 1) X U = ∠ U X (t.points 2))
    (hVa : ∠ (t.points 2) X V' = ∠ V' X (t.points 0))
    (hWa : ∠ (t.points 0) X W = ∠ W X (t.points 1)) :
    2 * (dist X U + dist X V' + dist X W) ≤
      dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2) := by
  obtain ⟨w, hw0, hw1, hXe⟩ := hX
  have hw : w 0 + w 1 + w 2 = 1 := by rw [← Fin.sum_univ_three]; exact hw1
  have hsum := weighted_vsub_eq_zero t w hw1
  rw [← hXe] at hsum
  have nc : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      ¬ Collinear ℝ ({t.points i, t.points j, t.points k} : Set P) := fun i j k h1 h2 h3 ↦ by
    rw [← affineIndependent_iff_not_collinear_of_ne h1 h2 h3]; exact t.independent
  have gA := gram_pos_of_not_collinear (nc 1 0 2 (by decide) (by decide) (by decide))
  have gB := gram_pos_of_not_collinear (nc 2 1 0 (by decide) (by decide) (by decide))
  have gC := gram_pos_of_not_collinear (nc 0 2 1 (by decide) (by decide) (by decide))
  have eA := affineCombination_vsub_zero t w hw1
  have eB := affineCombination_vsub_one t w hw1
  have eC := affineCombination_vsub_two t w hw1
  rw [← hXe] at eA eB eC
  have fA := gram_frame eA
  have fB := gram_frame eB
  have fC := gram_frame eC
  have hgp : 0 < ‖t.points 1 -ᵥ X‖ ^ 2 * ‖t.points 2 -ᵥ X‖ ^ 2 -
      ⟪t.points 1 -ᵥ X, t.points 2 -ᵥ X⟫ ^ 2 := by
    rw [fA, show 1 - w 1 - w 2 = w 0 by linarith]; have := hw0 0; positivity
  have hgq : 0 < ‖t.points 2 -ᵥ X‖ ^ 2 * ‖t.points 0 -ᵥ X‖ ^ 2 -
      ⟪t.points 2 -ᵥ X, t.points 0 -ᵥ X⟫ ^ 2 := by
    rw [fB, show 1 - w 2 - w 0 = w 1 by linarith]; have := hw0 1; positivity
  have hgr : 0 < ‖t.points 0 -ᵥ X‖ ^ 2 * ‖t.points 1 -ᵥ X‖ ^ 2 -
      ⟪t.points 0 -ᵥ X, t.points 1 -ᵥ X⟫ ^ 2 := by
    rw [fC, show 1 - w 0 - w 1 = w 2 by linarith]; have := hw0 2; positivity
  have bU := bisector_dist hU hUa hgp
  have bV := bisector_dist hV hVa hgq
  have bW := bisector_dist hW hWa hgr
  have hd : ∀ i, dist X (t.points i) = ‖t.points i -ᵥ X‖ := fun i ↦ by
    rw [dist_comm, dist_eq_norm_vsub]
  rw [hd 0, hd 1, hd 2]
  exact barrow_vec (hw0 0) (hw0 1) (hw0 2) hw hsum hgp hgq hgr dist_nonneg dist_nonneg
    dist_nonneg bU bV bW

end ErdosMordell
