import ErdosMordell.Basic
import ErdosMordell.Mordell
import ErdosMordell.Fermat
import ErdosMordell.Barrow
import ErdosMordell.L14

/-!
# Layer 15: classical statements (ErdosMordell)

An independent writer stated the classical theorems in the textbook form, using only Mathlib
and a few elementary definitions, in a separate file, `PaperHClassical.lean`
(sha256 begins 0ac73f94ec9efdb8). This file copies that file's `Classical*` definitions
verbatim (inside the namespace `ErdosMordell.Classical`) and restates each classical statement with
its verbatim type as `cov_<name>`, proved from the library. Helper lemmas marked NEW PROOF are
arguments that are not in the rest of the library.
-/

open EuclideanGeometry Real

noncomputable section

namespace ErdosMordell.Classical

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! ## Definitions not (directly) in Mathlib -/

/-- Side `a = BC`. -/
def ClassicalSideA (t : Affine.Triangle ℝ P) : ℝ := dist (t.points 1) (t.points 2)
/-- Side `b = CA`. -/
def ClassicalSideB (t : Affine.Triangle ℝ P) : ℝ := dist (t.points 2) (t.points 0)
/-- Side `c = AB`. -/
def ClassicalSideC (t : Affine.Triangle ℝ P) : ℝ := dist (t.points 0) (t.points 1)

/-- Semiperimeter `s = (a+b+c)/2`. -/
def ClassicalSemiperimeter (t : Affine.Triangle ℝ P) : ℝ :=
  (ClassicalSideA t + ClassicalSideB t + ClassicalSideC t) / 2

/-- Area of the triangle with vertices `A B C`: `Δ = ½·AB·AC·sin A`. -/
def ClassicalAreaPts (A B C : P) : ℝ :=
  1 / 2 * dist A B * dist A C * Real.sin (∠ B A C)

/-- Area `Δ` of a triangle. -/
def ClassicalArea (t : Affine.Triangle ℝ P) : ℝ :=
  ClassicalAreaPts (t.points 0) (t.points 1) (t.points 2)

/-- Centroid `G`. -/
def ClassicalCentroid (t : Affine.Triangle ℝ P) : P :=
  Finset.univ.centroid ℝ t.points

/-- Equilateral: `a = b = c`. -/
def ClassicalEquilateral (t : Affine.Triangle ℝ P) : Prop :=
  ClassicalSideA t = ClassicalSideB t ∧ ClassicalSideB t = ClassicalSideC t

/-- Sum of squared sides `a² + b² + c²`. -/
def ClassicalSumSq (t : Affine.Triangle ℝ P) : ℝ :=
  ClassicalSideA t ^ 2 + ClassicalSideB t ^ 2 + ClassicalSideC t ^ 2

/-- `X` lies inside or on the triangle (closed convex hull of the vertices):
all barycentric coordinates nonnegative. -/
def ClassicalInsideOrOn (t : Affine.Triangle ℝ P) (X : P) : Prop :=
  ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
    X = Finset.univ.affineCombination ℝ t.points w

/-- `X` lies strictly inside the triangle: all barycentric coordinates positive
(works in any ambient dimension, i.e. relative interior). -/
def ClassicalStrictlyInside (t : Affine.Triangle ℝ P) (X : P) : Prop :=
  ∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
    X = Finset.univ.affineCombination ℝ t.points w

/-- Distance from `X` to the line through `Y` and `Z`. -/
def ClassicalDistToLine (X Y Z : P) : ℝ :=
  Metric.infDist X (affineSpan ℝ {Y, Z} : Set P)

/-- Fermat point: a point seeing each side under `120°`. -/
def ClassicalIsFermatPoint (t : Affine.Triangle ℝ P) (F : P) : Prop :=
  ∠ (t.points 1) F (t.points 2) = 2 * π / 3 ∧
  ∠ (t.points 2) F (t.points 0) = 2 * π / 3 ∧
  ∠ (t.points 0) F (t.points 1) = 2 * π / 3

/-- All angles of the triangle are less than `120°`. -/
def ClassicalAnglesLt120 (t : Affine.Triangle ℝ P) : Prop :=
  ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3 ∧
  ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3 ∧
  ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3

/-- `X'` is the apex of the equilateral triangle erected outward on side `YZ`
of a triangle whose third vertex is `X`: `X'Y = X'Z = YZ`, and `X'` lies on the
opposite side of line `YZ` from `X`. -/
def ClassicalOutwardEquilateralApex (X Y Z X' : P) : Prop :=
  dist X' Y = dist Y Z ∧ dist X' Z = dist Y Z ∧
  (affineSpan ℝ {Y, Z}).SOppSide X X'

/-- Sum of distances `XA + XB + XC`. -/
def ClassicalDistSum (t : Affine.Triangle ℝ P) (X : P) : ℝ :=
  dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2)

/-- Sum of squared distances `XA² + XB² + XC²`. -/
def ClassicalDistSqSum (t : Affine.Triangle ℝ P) (X : P) : ℝ :=
  dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2

/-- Four distinct points lie "in this order" `A, B, C, D` on a circle or line:
either they are concyclic and the diagonals `AC`, `BD` meet (convex position in
the order `ABCD`), or they are collinear and the pair `{A, C}` separates
`{B, D}` (exactly one of `B, D` lies strictly between `A` and `C`). -/
def ClassicalInOrderOnCircleOrLine (A B C D : P) : Prop :=
  (Concyclic ({A, B, C, D} : Set P) ∧
      ∃ X : P, Wbtw ℝ A X C ∧ Wbtw ℝ B X D) ∨
  (Collinear ℝ ({A, B, C, D} : Set P) ∧ (Sbtw ℝ A B C ↔ ¬ Sbtw ℝ A D C))

/-- M1 (Erdős–Mordell). For X inside or on ABC with distances p, q, r to the side lines
BC, CA, AB: XA + XB + XC ≥ 2(p + q + r). -/
theorem cov_M1a (t : Affine.Triangle ℝ P) (X : P) (hX : ClassicalInsideOrOn t X) :
    2 * (ClassicalDistToLine X (t.points 1) (t.points 2)
        + ClassicalDistToLine X (t.points 2) (t.points 0)
        + ClassicalDistToLine X (t.points 0) (t.points 1)) ≤ ClassicalDistSum t X := by
  unfold ClassicalDistToLine ClassicalDistSum
  rw [← dist_orthogonalProjection_eq_infDist, ← dist_orthogonalProjection_eq_infDist,
    ← dist_orthogonalProjection_eq_infDist]
  exact ErdosMordell.erdos_mordell t X hX

/-- M1 (Erdős–Mordell). … equality iff the triangle is equilateral and X is its centre. -/
theorem cov_M1b (t : Affine.Triangle ℝ P) (X : P) (hX : ClassicalInsideOrOn t X) :
    ClassicalDistSum t X = 2 * (ClassicalDistToLine X (t.points 1) (t.points 2)
        + ClassicalDistToLine X (t.points 2) (t.points 0)
        + ClassicalDistToLine X (t.points 0) (t.points 1)) ↔
      ClassicalEquilateral t ∧ X = ClassicalCentroid t := by
  unfold ClassicalDistToLine ClassicalDistSum ClassicalEquilateral ClassicalSideA ClassicalSideB
    ClassicalSideC ClassicalCentroid
  rw [← dist_orthogonalProjection_eq_infDist, ← dist_orthogonalProjection_eq_infDist,
    ← dist_orthogonalProjection_eq_infDist, eq_comm, ErdosMordell.erdos_mordell_eq_iff t X hX]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h2, (h1.trans h2).symm⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨(h1.trans h2).symm, h1⟩, h3⟩

/-- M2 (Barrow). For X inside ABC, if the internal bisectors of angles BXC, CXA, AXB
meet BC, CA, AB at U, V, W, then XA + XB + XC ≥ 2(XU + XV + XW).
"Internal bisector of ∠BXC meets BC at U" is encoded as: U on segment BC and
∠BXU = ∠UXC. -/
theorem cov_M2 (t : Affine.Triangle ℝ P) (X U V W : P)
    (hX : ClassicalStrictlyInside t X)
    (hU : Wbtw ℝ (t.points 1) U (t.points 2) ∧ ∠ (t.points 1) X U = ∠ U X (t.points 2))
    (hV : Wbtw ℝ (t.points 2) V (t.points 0) ∧ ∠ (t.points 2) X V = ∠ V X (t.points 0))
    (hW : Wbtw ℝ (t.points 0) W (t.points 1) ∧ ∠ (t.points 0) X W = ∠ W X (t.points 1)) :
    2 * (dist X U + dist X V + dist X W) ≤ ClassicalDistSum t X := by
  exact ErdosMordell.barrow t X U V W hX hU.1 hV.1 hW.1 hU.2 hV.2 hW.2

/-- F1 (Fermat–Torricelli). If every angle of ABC is less than 120°, there is a point F
seeing each side under 120°, and F minimises XA + XB + XC over all points X. -/
theorem cov_F1a (t : Affine.Triangle ℝ P) (h : ClassicalAnglesLt120 t) :
    ∃ F : P, ClassicalIsFermatPoint t F ∧
      ∀ X : P, ClassicalDistSum t F ≤ ClassicalDistSum t X := by
  obtain ⟨F, h01, h12, h20, hmin⟩ := ErdosMordell.fermat_torricelli t h.1 h.2.1 h.2.2
  exact ⟨F, ⟨h12, h20, h01⟩, hmin⟩

/-- F1 (Fermat–Torricelli), strengthened reading: any point F seeing each side under 120°
minimises XA + XB + XC.
-- AMBIGUOUS: the textbook phrase "there is a point F … and F minimises" can be read as
-- existence-plus-minimality (F1a) or as "the 120° point is the minimiser" (this form). -/
theorem cov_F1b (t : Affine.Triangle ℝ P) (h : ClassicalAnglesLt120 t) (F : P)
    (hF : ClassicalIsFermatPoint t F) :
    ∀ X : P, ClassicalDistSum t F ≤ ClassicalDistSum t X := by
  intro X
  exact ErdosMordell.fermat_min _ _ _ F hF.2.2 hF.1 hF.2.1 X

end ErdosMordell.Classical
