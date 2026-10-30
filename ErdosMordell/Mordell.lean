import ErdosMordell.Basic

/-!
# The Erdős–Mordell inequality

The key lemma (Mordell / Kazarinoff): seen from vertex `A`, write `X - A = w₁ (B - A) + w₂ (C - A)`
with `w₁, w₂ ≥ 0`. Then `c · d_C = w₂ √Γ` and `b · d_B = w₁ √Γ` (`Γ` the Gram determinant), and
`a · XA ≥ b · d_C + c · d_B` reduces, after multiplying by `bc` and squaring, to the identity
`a²b²c²|X - A|² - Γ (b² w₂ + c² w₁)² = (b²c² w₁ + b² k w₂ - c² k w₁ - b²c² w₂)²`.
-/

open Affine EuclideanGeometry AffineMap
open scoped RealInnerProductSpace

namespace ErdosMordell

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The squared-slack identity behind the key lemma. -/
lemma key_scalar_sq {a b c R dB dC w1 w2 k : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hdB : 0 ≤ dB) (hdC : 0 ≤ dC) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2)
    (hΓ : 0 ≤ b ^ 2 * c ^ 2 - k ^ 2)
    (hA : a ^ 2 = b ^ 2 + c ^ 2 - 2 * k)
    (hR2 : R ^ 2 = w1 ^ 2 * c ^ 2 + 2 * w1 * w2 * k + w2 ^ 2 * b ^ 2)
    (hC2 : dC ^ 2 * c ^ 2 = w2 ^ 2 * (b ^ 2 * c ^ 2 - k ^ 2))
    (hB2 : dB ^ 2 * b ^ 2 = w1 ^ 2 * (b ^ 2 * c ^ 2 - k ^ 2)) :
    (b * c * (a * R)) ^ 2 - (b * c * (b * dC + c * dB)) ^ 2 =
      (b ^ 2 * c ^ 2 * w1 + b ^ 2 * k * w2 - c ^ 2 * k * w1 - b ^ 2 * c ^ 2 * w2) ^ 2 := by
  have hP : (c * dC) * (b * dB) = w1 * w2 * (b ^ 2 * c ^ 2 - k ^ 2) := by
    have h1 : 0 ≤ (c * dC) * (b * dB) := by positivity
    have h2 : 0 ≤ w1 * w2 * (b ^ 2 * c ^ 2 - k ^ 2) := by positivity
    have : ((c * dC) * (b * dB)) ^ 2 = (w1 * w2 * (b ^ 2 * c ^ 2 - k ^ 2)) ^ 2 := by
      calc ((c * dC) * (b * dB)) ^ 2 = (dC ^ 2 * c ^ 2) * (dB ^ 2 * b ^ 2) := by ring
        _ = _ := by rw [hC2, hB2]; ring
    exact (pow_left_inj₀ h1 h2 two_ne_zero).1 this
  have e1 : (b * c * (b * dC + c * dB)) ^ 2 =
      b ^ 4 * (dC ^ 2 * c ^ 2) + c ^ 4 * (dB ^ 2 * b ^ 2) +
        2 * b ^ 2 * c ^ 2 * ((c * dC) * (b * dB)) := by ring
  have e2 : (b * c * (a * R)) ^ 2 = a ^ 2 * b ^ 2 * c ^ 2 * R ^ 2 := by ring
  rw [e1, e2, hC2, hB2, hP, hA, hR2]
  ring

/-- The scalar core of the key lemma. -/
lemma key_scalar {a b c R dB dC w1 w2 k : ℝ} (hb : 0 < b) (hc : 0 < c) (ha : 0 ≤ a)
    (hR : 0 ≤ R) (hdB : 0 ≤ dB) (hdC : 0 ≤ dC) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2)
    (hΓ : 0 ≤ b ^ 2 * c ^ 2 - k ^ 2)
    (hA : a ^ 2 = b ^ 2 + c ^ 2 - 2 * k)
    (hR2 : R ^ 2 = w1 ^ 2 * c ^ 2 + 2 * w1 * w2 * k + w2 ^ 2 * b ^ 2)
    (hC2 : dC ^ 2 * c ^ 2 = w2 ^ 2 * (b ^ 2 * c ^ 2 - k ^ 2))
    (hB2 : dB ^ 2 * b ^ 2 = w1 ^ 2 * (b ^ 2 * c ^ 2 - k ^ 2)) :
    b * dC + c * dB ≤ a * R := by
  have hsq := key_scalar_sq hb hc hdB hdC hw1 hw2 hΓ hA hR2 hC2 hB2
  have key : (b * c * (b * dC + c * dB)) ^ 2 ≤ (b * c * (a * R)) ^ 2 := by
    nlinarith [sq_nonneg (b ^ 2 * c ^ 2 * w1 + b ^ 2 * k * w2 - c ^ 2 * k * w1 -
      b ^ 2 * c ^ 2 * w2)]
  have hbc : 0 < b * c := mul_pos hb hc
  have := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 key
  exact le_of_mul_le_mul_left this hbc

/-- Equality in the key lemma holds exactly when the square in `key_scalar_sq` vanishes. -/
lemma key_scalar_eq_iff {a b c R dB dC w1 w2 k : ℝ} (hb : 0 < b) (hc : 0 < c) (ha : 0 ≤ a)
    (hR : 0 ≤ R) (hdB : 0 ≤ dB) (hdC : 0 ≤ dC) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2)
    (hΓ : 0 ≤ b ^ 2 * c ^ 2 - k ^ 2)
    (hA : a ^ 2 = b ^ 2 + c ^ 2 - 2 * k)
    (hR2 : R ^ 2 = w1 ^ 2 * c ^ 2 + 2 * w1 * w2 * k + w2 ^ 2 * b ^ 2)
    (hC2 : dC ^ 2 * c ^ 2 = w2 ^ 2 * (b ^ 2 * c ^ 2 - k ^ 2))
    (hB2 : dB ^ 2 * b ^ 2 = w1 ^ 2 * (b ^ 2 * c ^ 2 - k ^ 2)) :
    b * dC + c * dB = a * R ↔
      b ^ 2 * c ^ 2 * w1 + b ^ 2 * k * w2 - c ^ 2 * k * w1 - b ^ 2 * c ^ 2 * w2 = 0 := by
  have hsq := key_scalar_sq hb hc hdB hdC hw1 hw2 hΓ hA hR2 hC2 hB2
  constructor
  · intro h
    rw [h, sub_self] at hsq
    exact pow_eq_zero_iff two_ne_zero |>.1 hsq.symm
  · intro h
    rw [h] at hsq
    have : (b * c * (b * dC + c * dB)) ^ 2 = (b * c * (a * R)) ^ 2 := by linear_combination -hsq
    have := (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 this
    exact mul_left_cancel₀ (mul_pos hb hc).ne' this

/-- The scalar data at a vertex `A`, for `X - A = w₁ (B - A) + w₂ (C - A)`. -/
lemma key_facts {A B C X : P} (hAB : A ≠ B) (hAC : A ≠ C) {w1 w2 : ℝ}
    (hX : X -ᵥ A = w1 • (B -ᵥ A) + w2 • (C -ᵥ A)) :
    dist B C ^ 2 = dist C A ^ 2 + dist A B ^ 2 - 2 * ⟪B -ᵥ A, C -ᵥ A⟫ ∧
    dist X A ^ 2 =
      w1 ^ 2 * dist A B ^ 2 + 2 * w1 * w2 * ⟪B -ᵥ A, C -ᵥ A⟫ + w2 ^ 2 * dist C A ^ 2 ∧
    footDist X A B ^ 2 * dist A B ^ 2 =
      w2 ^ 2 * (dist C A ^ 2 * dist A B ^ 2 - ⟪B -ᵥ A, C -ᵥ A⟫ ^ 2) ∧
    footDist X A C ^ 2 * dist C A ^ 2 =
      w1 ^ 2 * (dist C A ^ 2 * dist A B ^ 2 - ⟪B -ᵥ A, C -ᵥ A⟫ ^ 2) ∧
    0 ≤ dist C A ^ 2 * dist A B ^ 2 - ⟪B -ᵥ A, C -ᵥ A⟫ ^ 2 := by
  have hC2 := footDist_sq_mul (X := X) hAB
  have hB2 := footDist_sq_mul (X := X) hAC
  have hb : dist C A = ‖C -ᵥ A‖ := dist_eq_norm_vsub V C A
  have hc : dist A B = ‖B -ᵥ A‖ := by rw [dist_comm]; exact dist_eq_norm_vsub V B A
  have ha : dist B C = ‖(B -ᵥ A) - (C -ᵥ A)‖ := by
    rw [dist_eq_norm_vsub V, vsub_sub_vsub_cancel_right]
  have hR : dist X A = ‖X -ᵥ A‖ := dist_eq_norm_vsub V X A
  have hcs := real_inner_mul_inner_self_le (B -ᵥ A) (C -ᵥ A)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
  rw [hb, hc, ha, hR]
  rw [hX] at hC2 hB2 ⊢
  generalize B -ᵥ A = p at *
  generalize C -ᵥ A = q at *
  have e1 : ⟪w1 • p + w2 • q, p⟫ = w1 * ‖p‖ ^ 2 + w2 * ⟪p, q⟫ := by
    simpa using inner_comb p q w1 w2 1 0
  have e2 : ⟪w1 • p + w2 • q, q⟫ = w1 * ⟪p, q⟫ + w2 * ‖q‖ ^ 2 := by
    simpa using inner_comb p q w1 w2 0 1
  have e3 : ‖w1 • p + w2 • q‖ ^ 2 =
      w1 ^ 2 * ‖p‖ ^ 2 + 2 * w1 * w2 * ⟪p, q⟫ + w2 ^ 2 * ‖q‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_comb]; ring
  rw [e1, e3] at hC2
  rw [e2, e3] at hB2
  refine ⟨?_, e3, ?_, ?_, ?_⟩
  · rw [norm_sub_sq_real]; ring
  · linear_combination hC2
  · linear_combination hB2
  · nlinarith

/-- The key lemma at a vertex `A`, for `X - A` a nonnegative combination of `B - A`, `C - A`. -/
lemma key_aux {A B C X : P} (hAB : A ≠ B) (hAC : A ≠ C) {w1 w2 : ℝ} (hw1 : 0 ≤ w1)
    (hw2 : 0 ≤ w2) (hX : X -ᵥ A = w1 • (B -ᵥ A) + w2 • (C -ᵥ A)) :
    dist C A * footDist X A B + dist A B * footDist X A C ≤ dist B C * dist X A := by
  obtain ⟨hA, hR, hC, hB, hΓ⟩ := key_facts hAB hAC hX
  exact key_scalar (dist_pos.2 hAC.symm) (dist_pos.2 hAB) dist_nonneg dist_nonneg dist_nonneg
    dist_nonneg hw1 hw2 hΓ hA hR hC hB

/-- H2.2 (key lemma, vertex `A = t.points 0`): `a · XA ≥ b · d_C(X) + c · d_B(X)`. -/
theorem key_lemma_zero (t : Triangle ℝ P) (X : P)
    (hX : ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      X = Finset.univ.affineCombination ℝ t.points w) :
    dist (t.points 2) (t.points 0) *
        dist X (orthogonalProjection line[ℝ, t.points 0, t.points 1] X : P) +
      dist (t.points 0) (t.points 1) *
        dist X (orthogonalProjection line[ℝ, t.points 2, t.points 0] X : P) ≤
      dist (t.points 1) (t.points 2) * dist X (t.points 0) := by
  obtain ⟨w, hw0, hw1, rfl⟩ := hX
  have h := key_aux (points_ne t (by decide : (0 : Fin 3) ≠ 1))
    (points_ne t (by decide : (0 : Fin 3) ≠ 2)) (hw0 1) (hw0 2)
    (affineCombination_vsub_zero t w hw1)
  rw [footDist_comm _ (t.points 0) (t.points 2)] at h
  exact h

/-- H2.2 (key lemma, vertex `B = t.points 1`): `b · XB ≥ c · d_A(X) + a · d_C(X)`. -/
theorem key_lemma_one (t : Triangle ℝ P) (X : P)
    (hX : ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      X = Finset.univ.affineCombination ℝ t.points w) :
    dist (t.points 0) (t.points 1) *
        dist X (orthogonalProjection line[ℝ, t.points 1, t.points 2] X : P) +
      dist (t.points 1) (t.points 2) *
        dist X (orthogonalProjection line[ℝ, t.points 0, t.points 1] X : P) ≤
      dist (t.points 2) (t.points 0) * dist X (t.points 1) := by
  obtain ⟨w, hw0, hw1, rfl⟩ := hX
  have h := key_aux (points_ne t (by decide : (1 : Fin 3) ≠ 2))
    (points_ne t (by decide : (1 : Fin 3) ≠ 0)) (hw0 2) (hw0 0)
    (affineCombination_vsub_one t w hw1)
  rw [footDist_comm _ (t.points 1) (t.points 0)] at h
  exact h

/-- H2.2 (key lemma, vertex `C = t.points 2`): `c · XC ≥ a · d_B(X) + b · d_A(X)`. -/
theorem key_lemma_two (t : Triangle ℝ P) (X : P)
    (hX : ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      X = Finset.univ.affineCombination ℝ t.points w) :
    dist (t.points 1) (t.points 2) *
        dist X (orthogonalProjection line[ℝ, t.points 2, t.points 0] X : P) +
      dist (t.points 2) (t.points 0) *
        dist X (orthogonalProjection line[ℝ, t.points 1, t.points 2] X : P) ≤
      dist (t.points 0) (t.points 1) * dist X (t.points 2) := by
  obtain ⟨w, hw0, hw1, rfl⟩ := hX
  have h := key_aux (points_ne t (by decide : (2 : Fin 3) ≠ 0))
    (points_ne t (by decide : (2 : Fin 3) ≠ 1)) (hw0 0) (hw0 1)
    (affineCombination_vsub_two t w hw1)
  rw [footDist_comm _ (t.points 2) (t.points 1)] at h
  exact h

/-- H2.1 (Erdős–Mordell): for `X` in the closed triangle,
`XA + XB + XC ≥ 2 (d_A(X) + d_B(X) + d_C(X))`. -/
theorem erdos_mordell (t : Triangle ℝ P) (X : P)
    (hX : ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      X = Finset.univ.affineCombination ℝ t.points w) :
    2 * (dist X (orthogonalProjection line[ℝ, t.points 1, t.points 2] X : P) +
        dist X (orthogonalProjection line[ℝ, t.points 2, t.points 0] X : P) +
        dist X (orthogonalProjection line[ℝ, t.points 0, t.points 1] X : P)) ≤
      dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2) := by
  have h0 := key_lemma_zero t X hX
  have h1 := key_lemma_one t X hX
  have h2 := key_lemma_two t X hX
  have ha : 0 < dist (t.points 1) (t.points 2) :=
    dist_pos.2 (points_ne t (by decide : (1 : Fin 3) ≠ 2))
  have hb : 0 < dist (t.points 2) (t.points 0) :=
    dist_pos.2 (points_ne t (by decide : (2 : Fin 3) ≠ 0))
  have hc : 0 < dist (t.points 0) (t.points 1) :=
    dist_pos.2 (points_ne t (by decide : (0 : Fin 3) ≠ 1))
  have hA : 0 ≤ dist X (orthogonalProjection line[ℝ, t.points 1, t.points 2] X : P) := dist_nonneg
  have hB : 0 ≤ dist X (orthogonalProjection line[ℝ, t.points 2, t.points 0] X : P) := dist_nonneg
  have hC : 0 ≤ dist X (orthogonalProjection line[ℝ, t.points 0, t.points 1] X : P) := dist_nonneg
  generalize dist X (orthogonalProjection line[ℝ, t.points 1, t.points 2] X : P) = dA at *
  generalize dist X (orthogonalProjection line[ℝ, t.points 2, t.points 0] X : P) = dB at *
  generalize dist X (orthogonalProjection line[ℝ, t.points 0, t.points 1] X : P) = dC at *
  generalize dist (t.points 1) (t.points 2) = a at *
  generalize dist (t.points 2) (t.points 0) = b at *
  generalize dist (t.points 0) (t.points 1) = c at *
  have habc : 0 < a * b * c := by positivity
  refine le_of_mul_le_mul_left ?_ habc
  nlinarith [mul_le_mul_of_nonneg_left h0 (le_of_lt (mul_pos hb hc)),
    mul_le_mul_of_nonneg_left h1 (le_of_lt (mul_pos ha hc)),
    mul_le_mul_of_nonneg_left h2 (le_of_lt (mul_pos ha hb)),
    mul_nonneg (mul_nonneg hA ha.le) (sq_nonneg (b - c)),
    mul_nonneg (mul_nonneg hB hb.le) (sq_nonneg (c - a)),
    mul_nonneg (mul_nonneg hC hc.le) (sq_nonneg (a - b))]

/-! ### The equality case -/

/-- Combinatorial core of the equality case: with `kᵢ` the vertex dot products
(`a² = k_B + k_C` …), vanishing of the three key-lemma equality expressions and the side
conditions force `w₀ > 0`. -/
lemma eq_pos {kA kB kC w0 w1 w2 a2 : ℝ} (ha0 : 0 < a2)
    (hH : 0 < kA * kB + kB * kC + kC * kA) (hw : w0 + w1 + w2 = 1) (hw0 : 0 ≤ w0)
    (hw1 : 0 ≤ w1) (EB : w2 * a2 * kA = w0 * (kA + kB) * kC)
    (EC : w0 * (kC + kA) * kB = w1 * a2 * kA)
    (s1 : 0 < w1 → kC = kA) (s2 : 0 < w2 → kA = kB) : 0 < w0 := by
  by_contra h
  have h0 : w0 = 0 := le_antisymm (not_lt.1 h) hw0
  subst h0
  have hk : a2 * kA * (w1 + w2) = 0 := by linear_combination EB - EC
  have hkA : kA = 0 := by
    rcases mul_eq_zero.1 hk with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h ha0.ne'
      · exact h
    · linarith
  rcases lt_or_eq_of_le hw1 with h1 | h1
  · have := s1 h1; subst hkA; rw [this] at hH; simp at hH
  · have h2 : 0 < w2 := by linarith
    have := s2 h2; subst hkA; rw [← this] at hH; simp at hH

/-- The scalar form of the Erdős–Mordell equality case. -/
lemma em_eq_scalar {a b c kA kB kC dA dB dC RA RB RC w0 w1 w2 : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hdA : 0 ≤ dA) (hdB : 0 ≤ dB) (hdC : 0 ≤ dC) (hRA : 0 ≤ RA) (hRB : 0 ≤ RB) (hRC : 0 ≤ RC)
    (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hw : w0 + w1 + w2 = 1)
    (hkA : a ^ 2 = b ^ 2 + c ^ 2 - 2 * kA) (hkB : b ^ 2 = c ^ 2 + a ^ 2 - 2 * kB)
    (hkC : c ^ 2 = a ^ 2 + b ^ 2 - 2 * kC) (hH : 0 < b ^ 2 * c ^ 2 - kA ^ 2)
    (hRA2 : RA ^ 2 = w1 ^ 2 * c ^ 2 + 2 * w1 * w2 * kA + w2 ^ 2 * b ^ 2)
    (hCA : dC ^ 2 * c ^ 2 = w2 ^ 2 * (b ^ 2 * c ^ 2 - kA ^ 2))
    (hBA : dB ^ 2 * b ^ 2 = w1 ^ 2 * (b ^ 2 * c ^ 2 - kA ^ 2))
    (hRB2 : RB ^ 2 = w2 ^ 2 * a ^ 2 + 2 * w2 * w0 * kB + w0 ^ 2 * c ^ 2)
    (hAB : dA ^ 2 * a ^ 2 = w0 ^ 2 * (c ^ 2 * a ^ 2 - kB ^ 2))
    (hCB : dC ^ 2 * c ^ 2 = w2 ^ 2 * (c ^ 2 * a ^ 2 - kB ^ 2))
    (hRC2 : RC ^ 2 = w0 ^ 2 * b ^ 2 + 2 * w0 * w1 * kC + w1 ^ 2 * a ^ 2)
    (hBC : dB ^ 2 * b ^ 2 = w1 ^ 2 * (a ^ 2 * b ^ 2 - kC ^ 2))
    (hAC : dA ^ 2 * a ^ 2 = w0 ^ 2 * (a ^ 2 * b ^ 2 - kC ^ 2)) :
    2 * (dA + dB + dC) = RA + RB + RC ↔
      (c = a ∧ a = b) ∧ (w0 = 1 / 3 ∧ w1 = 1 / 3 ∧ w2 = 1 / 3) := by
  have gB : c ^ 2 * a ^ 2 - kB ^ 2 = b ^ 2 * c ^ 2 - kA ^ 2 := by
    have e1 : kA = (b ^ 2 + c ^ 2 - a ^ 2) / 2 := by linarith
    have e2 : kB = (c ^ 2 + a ^ 2 - b ^ 2) / 2 := by linarith
    rw [e1, e2]; ring
  have gC : a ^ 2 * b ^ 2 - kC ^ 2 = b ^ 2 * c ^ 2 - kA ^ 2 := by
    have e1 : kA = (b ^ 2 + c ^ 2 - a ^ 2) / 2 := by linarith
    have e3 : kC = (a ^ 2 + b ^ 2 - c ^ 2) / 2 := by linarith
    rw [e1, e3]; ring
  have hB' : 0 < c ^ 2 * a ^ 2 - kB ^ 2 := gB ▸ hH
  have hC' : 0 < a ^ 2 * b ^ 2 - kC ^ 2 := gC ▸ hH
  -- the three key lemmas and their equality criteria
  have kA' := key_scalar hb hc ha.le hRA hdB hdC hw1 hw2 hH.le hkA hRA2 hCA hBA
  have kB' := key_scalar hc ha hb.le hRB hdC hdA hw2 hw0 hB'.le hkB hRB2 hAB hCB
  have kC' := key_scalar ha hb hc.le hRC hdA hdB hw0 hw1 hC'.le hkC hRC2 hBC hAC
  have eA := key_scalar_eq_iff hb hc ha.le hRA hdB hdC hw1 hw2 hH.le hkA hRA2 hCA hBA
  have eB := key_scalar_eq_iff hc ha hb.le hRB hdC hdA hw2 hw0 hB'.le hkB hRB2 hAB hCB
  have eC := key_scalar_eq_iff ha hb hc.le hRC hdA hdB hw0 hw1 hC'.le hkC hRC2 hBC hAC
  have iden : a * b * c * (RA + RB + RC - 2 * (dA + dB + dC)) =
      b * c * (a * RA - (b * dC + c * dB)) + c * a * (b * RB - (c * dA + a * dC)) +
        a * b * (c * RC - (a * dB + b * dA)) + a * dA * (b - c) ^ 2 + b * dB * (c - a) ^ 2 +
          c * dC * (a - b) ^ 2 := by ring
  have t1 : 0 ≤ b * c * (a * RA - (b * dC + c * dB)) := by
    have := sub_nonneg.2 kA'; positivity
  have t2 : 0 ≤ c * a * (b * RB - (c * dA + a * dC)) := by
    have := sub_nonneg.2 kB'; positivity
  have t3 : 0 ≤ a * b * (c * RC - (a * dB + b * dA)) := by
    have := sub_nonneg.2 kC'; positivity
  have t4 : 0 ≤ a * dA * (b - c) ^ 2 := by positivity
  have t5 : 0 ≤ b * dB * (c - a) ^ 2 := by positivity
  have t6 : 0 ≤ c * dC * (a - b) ^ 2 := by positivity
  constructor
  · intro h
    have z : a * b * c * (RA + RB + RC - 2 * (dA + dB + dC)) = 0 := by rw [← h]; ring
    rw [iden] at z
    have z1 : b * c * (a * RA - (b * dC + c * dB)) = 0 := by linarith
    have z2 : c * a * (b * RB - (c * dA + a * dC)) = 0 := by linarith
    have z3 : a * b * (c * RC - (a * dB + b * dA)) = 0 := by linarith
    have z4 : a * dA * (b - c) ^ 2 = 0 := by linarith
    have z5 : b * dB * (c - a) ^ 2 = 0 := by linarith
    have z6 : c * dC * (a - b) ^ 2 = 0 := by linarith
    have EA := eA.1 (by
      have := (mul_eq_zero.1 z1).resolve_left (mul_pos hb hc).ne'; linarith)
    have EB := eB.1 (by
      have := (mul_eq_zero.1 z2).resolve_left (mul_pos hc ha).ne'; linarith)
    have EC := eC.1 (by
      have := (mul_eq_zero.1 z3).resolve_left (mul_pos ha hb).ne'; linarith)
    -- side conditions: a positive weight makes the corresponding distance positive
    have sd : ∀ {x d w y z G : ℝ}, 0 < x → 0 < G → d ^ 2 * x ^ 2 = w ^ 2 * G →
        x * d * (y - z) ^ 2 = 0 → 0 < w → y = z := by
      intro x d w y z G hx hG hd hz hw
      have hd0 : d ≠ 0 := by
        rintro rfl
        have : w ^ 2 * G = 0 := by rw [← hd]; ring
        rcases mul_eq_zero.1 this with h | h
        · exact hw.ne' (pow_eq_zero_iff two_ne_zero |>.1 h)
        · exact hG.ne' h
      rcases mul_eq_zero.1 hz with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h hx.ne'
        · exact absurd h hd0
      · exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)
    have s0 : 0 < w0 → b = c := sd ha hB' hAB z4
    have s1 : 0 < w1 → c = a := sd hb hH hBA z5
    have s2 : 0 < w2 → a = b := sd hc hH hCA z6
    -- pass to the vertex dot products: `a² = k_B + k_C`, …
    have Hk : 0 < kA * kB + kB * kC + kC * kA := by
      have e1 : kA = (b ^ 2 + c ^ 2 - a ^ 2) / 2 := by linarith
      have e2 : kB = (c ^ 2 + a ^ 2 - b ^ 2) / 2 := by linarith
      have e3 : kC = (a ^ 2 + b ^ 2 - c ^ 2) / 2 := by linarith
      have : kA * kB + kB * kC + kC * kA = b ^ 2 * c ^ 2 - kA ^ 2 := by rw [e1, e2, e3]; ring
      rw [this]; exact hH
    have e1 : kA = (b ^ 2 + c ^ 2 - a ^ 2) / 2 := by linarith
    have e2 : kB = (c ^ 2 + a ^ 2 - b ^ 2) / 2 := by linarith
    have e3 : kC = (a ^ 2 + b ^ 2 - c ^ 2) / 2 := by linarith
    have EA' : w1 * (kA + kB) * kC = w2 * (kC + kA) * kB := by
      rw [e1, e2, e3]; rw [e1] at EA; linear_combination EA
    have EB' : w2 * (kB + kC) * kA = w0 * (kA + kB) * kC := by
      rw [e1, e2, e3]; rw [e2] at EB; linear_combination EB
    have EC' : w0 * (kC + kA) * kB = w1 * (kB + kC) * kA := by
      rw [e1, e2, e3]; rw [e3] at EC; linear_combination EC
    have p0 : 0 < w0 := eq_pos (kA := kA) (kB := kB) (kC := kC) (w0 := w0) (w1 := w1) (w2 := w2)
      (a2 := a ^ 2) (by positivity) Hk
      (by linarith) hw0 hw1 (by rw [show a ^ 2 = kB + kC by rw [e2, e3]; ring]; exact EB')
      (by rw [show a ^ 2 = kB + kC by rw [e2, e3]; ring]; exact EC')
      (fun h ↦ by have := s1 h; rw [e1, e3, this]; ring)
      (fun h ↦ by have := s2 h; rw [e1, e2, this]; ring)
    have p1 : 0 < w1 := eq_pos (kA := kB) (kB := kC) (kC := kA) (w0 := w1) (w1 := w2) (w2 := w0)
      (a2 := b ^ 2) (by positivity) (by linarith)
      (by linarith) hw1 hw2 (by rw [show b ^ 2 = kC + kA by rw [e1, e3]; ring]; exact EC')
      (by rw [show b ^ 2 = kC + kA by rw [e1, e3]; ring]; exact EA')
      (fun h ↦ by have := s2 h; rw [e1, e2, this]; ring)
      (fun h ↦ by have := s0 h; rw [e2, e3, this]; ring)
    have p2 : 0 < w2 := eq_pos (kA := kC) (kB := kA) (kC := kB) (w0 := w2) (w1 := w0) (w2 := w1)
      (a2 := c ^ 2) (by positivity) (by linarith)
      (by linarith) hw2 hw0 (by rw [show c ^ 2 = kA + kB by rw [e1, e2]; ring]; exact EA')
      (by rw [show c ^ 2 = kA + kB by rw [e1, e2]; ring]; exact EB')
      (fun h ↦ by have := s0 h; rw [e2, e3, this]; ring)
      (fun h ↦ by have := s1 h; rw [e1, e3, this]; ring)
    have hca := s1 p1
    have hab := s2 p2
    subst hca
    rw [← hab] at e1 e2 e3
    have hk : 0 < c ^ 2 / 2 := by positivity
    have q1 : w1 = w2 := by
      have : (w1 - w2) * (c ^ 2 * (c ^ 2 / 2)) = 0 := by
        rw [e1, e2, e3] at EA'; linear_combination EA'
      have := (mul_eq_zero.1 this).resolve_right (by positivity)
      linarith
    have q2 : w2 = w0 := by
      have : (w2 - w0) * (c ^ 2 * (c ^ 2 / 2)) = 0 := by
        rw [e1, e2, e3] at EB'; linear_combination EB'
      have := (mul_eq_zero.1 this).resolve_right (by positivity)
      linarith
    refine ⟨⟨rfl, hab⟩, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨⟨hca, hab⟩, h0, h1, h2⟩
    subst hca
    subst hab
    have e1 : kA = c ^ 2 / 2 := by linarith
    have e2 : kB = c ^ 2 / 2 := by linarith
    have e3 : kC = c ^ 2 / 2 := by linarith
    have zA := eA.2 (by rw [h1, h2, e1]; ring)
    have zB := eB.2 (by rw [h2, h0, e2]; ring)
    have zC := eC.2 (by rw [h0, h1, e3]; ring)
    have : c * c * c * (RA + RB + RC - 2 * (dA + dB + dC)) = 0 := by
      rw [iden, zA, zB, zC]; ring
    have := (mul_eq_zero.1 this).resolve_left (by positivity)
    linarith

/-- H2.1, equality case: equality holds in Erdős–Mordell iff the triangle is equilateral and
`X` is its centre (the centroid). -/
theorem erdos_mordell_eq_iff (t : Triangle ℝ P) (X : P)
    (hX : ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      X = Finset.univ.affineCombination ℝ t.points w) :
    2 * (dist X (orthogonalProjection line[ℝ, t.points 1, t.points 2] X : P) +
        dist X (orthogonalProjection line[ℝ, t.points 2, t.points 0] X : P) +
        dist X (orthogonalProjection line[ℝ, t.points 0, t.points 1] X : P)) =
      dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2) ↔
    (dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) ∧
      dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0)) ∧
    X = Finset.univ.centroid ℝ t.points := by
  obtain ⟨w, hw0, hw1, rfl⟩ := hX
  have n01 := points_ne t (by decide : (0 : Fin 3) ≠ 1)
  have n02 := points_ne t (by decide : (0 : Fin 3) ≠ 2)
  have n12 := points_ne t (by decide : (1 : Fin 3) ≠ 2)
  obtain ⟨fA1, fA2, fA3, fA4, -⟩ := key_facts n01 n02 (affineCombination_vsub_zero t w hw1)
  obtain ⟨fB1, fB2, fB3, fB4, -⟩ := key_facts n12 n01.symm (affineCombination_vsub_one t w hw1)
  obtain ⟨fC1, fC2, fC3, fC4, -⟩ := key_facts n02.symm n12.symm
    (affineCombination_vsub_two t w hw1)
  rw [footDist_comm _ (t.points 0) (t.points 2)] at fA4
  rw [footDist_comm _ (t.points 1) (t.points 0)] at fB4
  rw [footDist_comm _ (t.points 2) (t.points 1)] at fC4
  have hc3 : Finset.univ.centroid ℝ t.points =
      Finset.univ.affineCombination ℝ t.points (fun _ ↦ (1 / 3 : ℝ)) := by
    rw [Finset.centroid_def]
    congr 1
    funext i
    rw [Finset.centroidWeights_apply, Finset.card_univ, Fintype.card_fin]
    norm_num
  rw [hc3, t.independent.affineCombination_eq_iff_eq hw1
    (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num)]
  have hw : w 0 + w 1 + w 2 = 1 := by rw [← Fin.sum_univ_three]; exact hw1
  have key := em_eq_scalar (dist_pos.2 n12) (dist_pos.2 n02.symm) (dist_pos.2 n01)
    dist_nonneg dist_nonneg dist_nonneg dist_nonneg dist_nonneg dist_nonneg (hw0 0) (hw0 1) (hw0 2)
    hw fA1 fB1 fC1 (gram_pos t) fA2 fA3 fA4 fB2 fB3 fB4 fC2 fC3 fC4
  rw [key]
  constructor
  · rintro ⟨h, h0, h1, h2⟩
    refine ⟨h, fun i _ ↦ ?_⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · rintro ⟨h, hi⟩
    exact ⟨h, hi 0 (by simp), hi 1 (by simp), hi 2 (by simp)⟩

end ErdosMordell
