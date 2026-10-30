import ErdosMordell.Basic
import ErdosMordell.Mordell
import ErdosMordell.Fermat
import ErdosMordell.Barrow
import ErdosMordell.L14

/-!
# Layer 13: blind restatement (ErdosMordell)

An independent writer, who saw only the plain-English text of the paper and not this library,
formalised its theorem statements in a separate file, `PaperHBlind.lean`
(sha256 begins e257c271479a928f). This file copies that file's `Blind*` definitions verbatim
(inside the namespace `ErdosMordell.Blind`) and each blind statement verbatim as `blindK_stmt`.
For each statement it proves `rb_K` (library theorem → blind statement) and `br_K` (blind
statement → library theorem). Where the paper's statement was split by the blind writer into
several parts, the reverse direction is proved jointly (e.g. `br_456`). The `agree_*` lemmas
identify the blind definitions with the library's. No proof uses a library theorem other than
the one being compared and the definition-level agreement lemmas.
-/

universe u v

namespace ErdosMordell.Blind
open EuclideanGeometry Real

noncomputable section

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Semiperimeter `s = (a+b+c)/2`. -/
def BlindSemiperimeter (t : Affine.Triangle ℝ P) : ℝ :=
  (dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
    dist (t.points 0) (t.points 1)) / 2

/-- Area `Δ = ½ |AB| |AC| sin ∠BAC`. -/
def BlindArea (t : Affine.Triangle ℝ P) : ℝ :=
  1 / 2 * dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
    Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))

/-- Heron's polynomial `Γ(a,b,c) = ¼(2a²b²+2b²c²+2c²a²-a⁴-b⁴-c⁴)` (auxiliary definition). -/
def BlindHeronGamma (a b c : ℝ) : ℝ :=
  1 / 4 * (2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2 - a ^ 4 - b ^ 4 - c ^ 4)

/-- "Equilateral" is `|AB| = |BC| ∧ |BC| = |CA|`. -/
def BlindEquilateral (t : Affine.Triangle ℝ P) : Prop :=
  dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) ∧
    dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0)

/-- `X` is in the closed triangle: `X = w₀A + w₁B + w₂C` with all `wᵢ ≥ 0`, `∑ wᵢ = 1`. -/
def BlindInClosedTriangle (t : Affine.Triangle ℝ P) (X : P) : Prop :=
  ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
    X = Finset.univ.affineCombination ℝ t.points w

/-- `X` is strictly inside the triangle: as above with all `wᵢ > 0`. -/
def BlindStrictlyInside (t : Affine.Triangle ℝ P) (X : P) : Prop :=
  ∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
    X = Finset.univ.affineCombination ℝ t.points w

/-- Distance from `X` to the line `YZ`: `|X π_{YZ}(X)|`, `π_{YZ}` the orthogonal projection. -/
def BlindDistToLine (X Y Z : P) : ℝ :=
  dist X (EuclideanGeometry.orthogonalProjection line[ℝ, Y, Z] X : P)

/-! ### Oriented plane setting (Section "Fermat and Napoleon") -/

section Oriented

variable [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- Orientation sign `σ ∈ {1,-1}` of `t`: `σ = 1` iff `ω(B-A, C-A) > 0`. -/
def BlindOrientationSign (t : Affine.Triangle ℝ P) : ℝ :=
  if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then 1 else -1

/-- Outer apex on `XY`: the image of `Y` under the rotation about `X` by `-σπ/3`. -/
def BlindOuterApex (t : Affine.Triangle ℝ P) (X Y : P) : P :=
  o.rotation ((-(BlindOrientationSign o t * π / 3) : ℝ) : Real.Angle) (Y -ᵥ X) +ᵥ X

/-- `A'`: outer apex on `BC`. -/
def BlindApexA (t : Affine.Triangle ℝ P) : P := BlindOuterApex o t (t.points 1) (t.points 2)
/-- `B'`: outer apex on `CA`. -/
def BlindApexB (t : Affine.Triangle ℝ P) : P := BlindOuterApex o t (t.points 2) (t.points 0)
/-- `C'`: outer apex on `AB`. -/
def BlindApexC (t : Affine.Triangle ℝ P) : P := BlindOuterApex o t (t.points 0) (t.points 1)

/-- `N_A`: centroid of `B C A'`. -/
def BlindNapoleonA (t : Affine.Triangle ℝ P) : P :=
  Finset.univ.centroid ℝ ![t.points 1, t.points 2, BlindApexA o t]
/-- `N_B`: centroid of `C A B'`. -/
def BlindNapoleonB (t : Affine.Triangle ℝ P) : P :=
  Finset.univ.centroid ℝ ![t.points 2, t.points 0, BlindApexB o t]
/-- `N_C`: centroid of `A B C'`. -/
def BlindNapoleonC (t : Affine.Triangle ℝ P) : P :=
  Finset.univ.centroid ℝ ![t.points 0, t.points 1, BlindApexC o t]

end Oriented

end -- noncomputable section

/-! ### Agreement lemmas (Blind ↔ repository) -/

section Agree
variable {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- side-line distance: Blind = repository `footDist` = the projection form used in the theorems -/
theorem agree_distToLine (X Y Z : P) :
    BlindDistToLine X Y Z = ErdosMordell.footDist X Y Z := rfl

theorem agree_distToLine' (X Y Z : P) :
    BlindDistToLine X Y Z =
      dist X (EuclideanGeometry.orthogonalProjection line[ℝ, Y, Z] X : P) := rfl

/-- closed triangle: Blind predicate = repository barycentric hypothesis -/
theorem agree_closed (t : Affine.Triangle ℝ P) (X : P) :
    BlindInClosedTriangle t X ↔ ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      X = Finset.univ.affineCombination ℝ t.points w := Iff.rfl

/-- strictly inside: Blind predicate = repository barycentric hypothesis -/
theorem agree_inside (t : Affine.Triangle ℝ P) (X : P) :
    BlindStrictlyInside t X ↔ ∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
      X = Finset.univ.affineCombination ℝ t.points w := Iff.rfl

/-- equilateral: Blind predicate = the conjunction used in `erdos_mordell_eq_iff` -/
theorem agree_equilateral (t : Affine.Triangle ℝ P) :
    BlindEquilateral t ↔ (dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) ∧
      dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0)) := Iff.rfl

end Agree

open EuclideanGeometry Real

-- verbatim from blind_29
def blind29_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P]
    (t : Affine.Triangle ℝ P) (X : P) (hX : BlindInClosedTriangle t X),
    dist (t.points 2) (t.points 0) * BlindDistToLine X (t.points 0) (t.points 1) +
        dist (t.points 0) (t.points 1) * BlindDistToLine X (t.points 2) (t.points 0) ≤
      dist (t.points 1) (t.points 2) * dist X (t.points 0)

-- verbatim from blind_30
def blind30_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P]
    (t : Affine.Triangle ℝ P) (X : P) (hX : BlindInClosedTriangle t X),
    dist (t.points 0) (t.points 1) * BlindDistToLine X (t.points 1) (t.points 2) +
        dist (t.points 1) (t.points 2) * BlindDistToLine X (t.points 0) (t.points 1) ≤
      dist (t.points 2) (t.points 0) * dist X (t.points 1)

-- verbatim from blind_31
def blind31_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P]
    (t : Affine.Triangle ℝ P) (X : P) (hX : BlindInClosedTriangle t X),
    dist (t.points 1) (t.points 2) * BlindDistToLine X (t.points 2) (t.points 0) +
        dist (t.points 2) (t.points 0) * BlindDistToLine X (t.points 1) (t.points 2) ≤
      dist (t.points 0) (t.points 1) * dist X (t.points 2)

-- verbatim from blind_32
def blind32_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P]
    (t : Affine.Triangle ℝ P) (X : P) (hX : BlindInClosedTriangle t X),
    2 * (BlindDistToLine X (t.points 1) (t.points 2) +
        BlindDistToLine X (t.points 2) (t.points 0) +
        BlindDistToLine X (t.points 0) (t.points 1)) ≤
      dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2)

-- verbatim from blind_33
def blind33_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P]
    (t : Affine.Triangle ℝ P) (X : P) (hX : BlindInClosedTriangle t X),
    2 * (BlindDistToLine X (t.points 1) (t.points 2) +
        BlindDistToLine X (t.points 2) (t.points 0) +
        BlindDistToLine X (t.points 0) (t.points 1)) =
      dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2) ↔
      BlindEquilateral t ∧ X = Finset.univ.centroid ℝ t.points

-- verbatim from blind_34
def blind34_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P]
    (t : Affine.Triangle ℝ P) (X U V' W : P) (hX : BlindStrictlyInside t X)
    (hU : Wbtw ℝ (t.points 1) U (t.points 2)) (hV : Wbtw ℝ (t.points 2) V' (t.points 0))
    (hW : Wbtw ℝ (t.points 0) W (t.points 1))
    (hUa : ∠ (t.points 1) X U = ∠ U X (t.points 2))
    (hVa : ∠ (t.points 2) X V' = ∠ V' X (t.points 0))
    (hWa : ∠ (t.points 0) X W = ∠ W X (t.points 1)),
    2 * (dist X U + dist X V' + dist X W) ≤
      dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2)

-- verbatim from blind_35
def blind35_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P]
    (A B C F : P) (h1 : ∠ A F B = 2 * π / 3) (h2 : ∠ B F C = 2 * π / 3)
    (h3 : ∠ C F A = 2 * π / 3) (X : P),
    dist F A + dist F B + dist F C ≤ dist X A + dist X B + dist X C

-- verbatim from blind_36
def blind36_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P]
    (t : Affine.Triangle ℝ P)
    (hA : ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3)
    (hB : ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3)
    (hC : ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3),
    ∃ F : P, ∠ (t.points 0) F (t.points 1) = 2 * π / 3 ∧
      ∠ (t.points 1) F (t.points 2) = 2 * π / 3 ∧ ∠ (t.points 2) F (t.points 0) = 2 * π / 3 ∧
      ∀ X : P, dist F (t.points 0) + dist F (t.points 1) + dist F (t.points 2) ≤
        dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2)

/-! ### Comparisons -/

-- blind_29 ↔ key_lemma_zero
theorem rb_29 : (type_of% @ErdosMordell.key_lemma_zero.{u, v}) → blind29_stmt.{u, v} := by
  intro h V P _ _ _ _ t X hX
  rw [agree_distToLine', agree_distToLine']
  exact h t X ((agree_closed t X).1 hX)

theorem br_29 : blind29_stmt.{u, v} → (type_of% @ErdosMordell.key_lemma_zero.{u, v}) := by
  intro h V P _ _ _ _ t X hX
  rw [← agree_distToLine', ← agree_distToLine']
  exact h t X ((agree_closed t X).2 hX)

-- blind_30 ↔ key_lemma_one
theorem rb_30 : (type_of% @ErdosMordell.key_lemma_one.{u, v}) → blind30_stmt.{u, v} := by
  intro h V P _ _ _ _ t X hX
  rw [agree_distToLine', agree_distToLine']
  exact h t X ((agree_closed t X).1 hX)

theorem br_30 : blind30_stmt.{u, v} → (type_of% @ErdosMordell.key_lemma_one.{u, v}) := by
  intro h V P _ _ _ _ t X hX
  rw [← agree_distToLine', ← agree_distToLine']
  exact h t X ((agree_closed t X).2 hX)

-- blind_31 ↔ key_lemma_two
theorem rb_31 : (type_of% @ErdosMordell.key_lemma_two.{u, v}) → blind31_stmt.{u, v} := by
  intro h V P _ _ _ _ t X hX
  rw [agree_distToLine', agree_distToLine']
  exact h t X ((agree_closed t X).1 hX)

theorem br_31 : blind31_stmt.{u, v} → (type_of% @ErdosMordell.key_lemma_two.{u, v}) := by
  intro h V P _ _ _ _ t X hX
  rw [← agree_distToLine', ← agree_distToLine']
  exact h t X ((agree_closed t X).2 hX)

-- blind_32 ↔ erdos_mordell
theorem rb_32 : (type_of% @ErdosMordell.erdos_mordell.{u, v}) → blind32_stmt.{u, v} := by
  intro h V P _ _ _ _ t X hX
  rw [agree_distToLine', agree_distToLine', agree_distToLine']
  exact h t X ((agree_closed t X).1 hX)

theorem br_32 : blind32_stmt.{u, v} → (type_of% @ErdosMordell.erdos_mordell.{u, v}) := by
  intro h V P _ _ _ _ t X hX
  rw [← agree_distToLine', ← agree_distToLine', ← agree_distToLine']
  exact h t X ((agree_closed t X).2 hX)

-- blind_33 ↔ erdos_mordell_eq_iff
theorem rb_33 : (type_of% @ErdosMordell.erdos_mordell_eq_iff.{u, v}) → blind33_stmt.{u, v} := by
  intro h V P _ _ _ _ t X hX
  rw [agree_distToLine', agree_distToLine', agree_distToLine', agree_equilateral]
  exact h t X ((agree_closed t X).1 hX)

theorem br_33 : blind33_stmt.{u, v} → (type_of% @ErdosMordell.erdos_mordell_eq_iff.{u, v}) := by
  intro h V P _ _ _ _ t X hX
  rw [← agree_distToLine', ← agree_distToLine', ← agree_distToLine', ← agree_equilateral]
  exact h t X ((agree_closed t X).2 hX)

-- blind_34 ↔ barrow
theorem rb_34 : (type_of% @ErdosMordell.barrow.{u, v}) → blind34_stmt.{u, v} := by
  intro h V P _ _ _ _ t X U V' W hX hU hV hW hUa hVa hWa
  exact h t X U V' W ((agree_inside t X).1 hX) hU hV hW hUa hVa hWa

theorem br_34 : blind34_stmt.{u, v} → (type_of% @ErdosMordell.barrow.{u, v}) := by
  intro h V P _ _ _ _ t X U V' W hX hU hV hW hUa hVa hWa
  exact h t X U V' W ((agree_inside t X).2 hX) hU hV hW hUa hVa hWa

-- blind_35 ↔ fermat_min
theorem rb_35 : (type_of% @ErdosMordell.fermat_min.{u, v}) → blind35_stmt.{u, v} := by
  intro h V P _ _ _ _ A B C F h1 h2 h3 X
  exact h A B C F h1 h2 h3 X

theorem br_35 : blind35_stmt.{u, v} → (type_of% @ErdosMordell.fermat_min.{u, v}) := by
  intro h V P _ _ _ _ A B C F h1 h2 h3 X
  exact h A B C F h1 h2 h3 X

-- blind_36 ↔ fermat_torricelli
theorem rb_36 : (type_of% @ErdosMordell.fermat_torricelli.{u, v}) → blind36_stmt.{u, v} := by
  intro h V P _ _ _ _ t hA hB hC
  exact h t hA hB hC

theorem br_36 : blind36_stmt.{u, v} → (type_of% @ErdosMordell.fermat_torricelli.{u, v}) := by
  intro h V P _ _ _ _ t hA hB hC
  exact h t hA hB hC

-- blind_36 vs fermat_exists (secondary pairing): blind_36 → fermat_exists is mere weakening;
-- fermat_exists → blind_36 would need fermat_min (the minimality claim), not available from the premise.
theorem b36_to_exists : blind36_stmt.{u, v} → (type_of% @ErdosMordell.fermat_exists.{u, v}) := by
  intro h V P _ _ _ _ t hA hB hC
  obtain ⟨F, h1, h2, h3, -⟩ := h t hA hB hC
  exact ⟨F, h1, h2, h3⟩

end ErdosMordell.Blind
