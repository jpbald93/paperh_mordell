# ErdosMordell — the Erdős–Mordell inequality and the Fermat–Torricelli point in Lean 4 / Mathlib

**Paper:** J. Bald, *Classical triangle inequalities and the Fermat–Napoleon configuration in Lean 4* (2026). Companion repositories: https://github.com/jpbald93/paperh_euler, https://github.com/jpbald93/paperh_fermat.

**Toolchain:** Lean `v4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` (see `lake-manifest.json`).
**Check:** `lake build && bash gate.sh`, then `bash tests/tamper.sh`. **Licence:** Apache-2.0.



**Check:** `lake build && bash gate.sh` prints `PASS (144 declarations, standard axioms only)`;
`bash tests/tamper.sh` prints `ALL TAMPERING TESTS REJECTED`.

Setting: `t : Affine.Triangle ℝ P` in an arbitrary real inner product space (Euclidean affine space
`P` over `V`). **No dimension hypothesis is needed** (no `Fact (finrank ℝ V = 2)`).
Notation: `A, B, C = t.points 0, 1, 2`; `a = dist B C`, `b = dist C A`, `c = dist A B`.
The distance from `X` to a side line is stated literally with Mathlib's orthogonal projection,
e.g. `dist X (orthogonalProjection line[ℝ, t.points 1, t.points 2] X : P)` = `d_A(X)`.
"X in the closed triangle" is stated as
`∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ X = Finset.univ.affineCombination ℝ t.points w`
(with `0 < w i` for "strictly inside" in Barrow).

## Main theorems

| Plain English | Lean name | file:line |
|---|---|---|
| H2.2 For X in the closed triangle: `b·d_C(X) + c·d_B(X) ≤ a·XA` | `ErdosMordell.key_lemma_zero` | `ErdosMordell/Mordell.lean:130` |
| H2.2 analogue at B: `c·d_A(X) + a·d_C(X) ≤ b·XB` | `ErdosMordell.key_lemma_one` | `ErdosMordell/Mordell.lean:146` |
| H2.2 analogue at C: `a·d_B(X) + b·d_A(X) ≤ c·XC` | `ErdosMordell.key_lemma_two` | `ErdosMordell/Mordell.lean:162` |
| H2.1 Erdős–Mordell: for X in the closed triangle, `2(d_A+d_B+d_C) ≤ XA+XB+XC` | `ErdosMordell.erdos_mordell` | `ErdosMordell/Mordell.lean:179` |
| H2.1 equality: equality holds iff `AB = BC = CA` and `X` is the centroid (`Finset.univ.centroid ℝ t.points`) | `ErdosMordell.erdos_mordell_eq_iff` | `ErdosMordell/Mordell.lean:386` |
| H2.3 Barrow: X strictly inside, `U ∈ [BC]`, `V ∈ [CA]`, `W ∈ [AB]` with `∠BXU = ∠UXC` etc. (internal bisectors) ⇒ `2(XU+XV+XW) ≤ XA+XB+XC` | `ErdosMordell.barrow` | `ErdosMordell/Barrow.lean:283` |
| H2.4 minimality: any F with `∠AFB = ∠BFC = ∠CFA = 2π/3` minimises `XA+XB+XC` over all X | `ErdosMordell.fermat_min` | `ErdosMordell/Fermat.lean:44` |
| H2.4 Fermat–Torricelli: if all angles of t are `< 2π/3`, such an F exists and minimises `XA+XB+XC` | `ErdosMordell.fermat_torricelli` | `ErdosMordell/Fermat.lean:291` |

Definition: `ErdosMordell.footDist X Y Z := dist X (orthogonalProjection line[ℝ, Y, Z] X)`
(`ErdosMordell/Basic.lean:20`), used only internally; the main statements spell out the
projection.

## Proof outline
* **H2.2** In the frame `X - A = w₁ (B-A) + w₂ (C-A)` (`affineCombination_vsub_zero`), the
  projection bridge `footDist_sq_mul` gives `(c·d_C)² = w₂² Γ`, `(b·d_B)² = w₁² Γ`
  (`Γ` = Gram determinant), and
  `a²b²c²·XA² − Γ (b² w₂ + c² w₁)² = (b²c² w₁ + b² k w₂ − c² k w₁ − b²c² w₂)²` (`key_scalar_sq`).
* **H2.1** `abc(ΣXA − 2Σd) = Σ bc(a·XA − b·d_C − c·d_B) + Σ a·d_A (b−c)²`.
* **Equality** All six terms vanish; using the vertex dot products the key-lemma equality
  conditions force all weights to be positive (`eq_pos`), hence `a = b = c`, then `w = (⅓,⅓,⅓)`.
* **H2.3** Bisector theorem in squared form (`bisector_dist`) gives `XU ≤ √(XB·XC)·α` with
  `α²` the half-angle cosine squared; `Σ wᵢ (Pᵢ − X) = 0` gives `α²+β²+γ²+2αβγ = 1`
  (`barrow_T`, `barrow_gram`, `barrow_halfangle`); Wolstenholme's inequality is a sum of
  squares (`wolstenholme`).
* **H2.4** Minimality: unit vectors `u, v, w` from F with pairwise inner products `−½` sum to 0, then
  Cauchy–Schwarz. Existence: explicit point
  `F = A + (x_A x_C/T)(B−A) + (x_A x_B/T)(C−A)` with `x_A = G + √3⟪B−A, C−A⟫` (cyclically),
  `G = √Γ`, `T = x_B x_C + x_C x_A + x_A x_B`; the six inner-product identities are
  Gröbner-certified `linear_combination`s (`fermat_alg`); the angle hypotheses give `xᵢ > 0`.

## Layer 13 (blind restatement)

An independent writer, who saw only the plain-English statements of the paper and not this library,
wrote the theorem statements in Lean on their own (`PaperHBlind.lean`, sha256 beginning
`e257c271479a928f`). `ErdosMordell/L13Blind.lean` (namespace `ErdosMordell.Blind`) copies the writer's
definitions and statements 29–36 verbatim. For each one it proves both directions against the library
theorem: `rb_K` (library → blind) and `br_K` (blind → library).

* All 8 blind statements are proved equivalent to the library in both directions (none jointly): the
  three key lemmas, Erdős–Mordell, its equality case, Barrow, and the two Fermat–Torricelli statements.
* `b36_to_exists` records that statement 36 (existence and minimality of the Fermat point) is matched
  by `fermat_torricelli`, while the existence statement `fermat_exists` alone is weaker.
* The agreement lemmas show that the writer's distance to a side line, "in the closed triangle",
  "strictly inside" and "equilateral" are the library's notions by definition.
* No difference in meaning was found.

## Layer 14 (Mathlib-only restatements and witnesses)

`ErdosMordell/L14.lean` restates every main theorem using only Mathlib notions. The distance to a side
line becomes `Metric.infDist`, and the barycentric hypotheses become Mathlib's closed interior and
interior of the triangle (two bridge lemmas). All 9 restatements (`l14_*`) are proved from the library. Five witness
theorems (`l14w_*`) show on explicit triangles that the hypotheses can be satisfied and the
inequalities are strict: the 3-4-5 triangle with an interior point, the equilateral triangle with its
centroid (the equality case), a Barrow configuration with explicit bisector feet, and Fermat-point
configurations with exact 120° angles.

## Layer 15 (classical statements)

An independent writer also stated the classical theorems in textbook form, using only Mathlib and a few
elementary definitions (`PaperHClassical.lean`, sha256 beginning `0ac73f94ec9efdb8`).
`ErdosMordell/L15Classical.lean` (namespace `ErdosMordell.Classical`) copies these definitions
verbatim and restates each assigned classical statement with its verbatim type as `cov_<name>`.

* All 5 classical statements are proved from the library: Erdős–Mordell (M1a) and its equality case
  (M1b), Barrow (M2), and the Fermat–Torricelli point (F1a: existence and minimality; F1b: any point
  seeing the sides at 120° is a minimiser). The library's version of F1b is stronger: it does not need
  the hypothesis that all angles are below 120°.
* NEW PROOFS: none were needed. Every classical statement follows directly from a library theorem.

## Build / gate / tamper
```
lake build
bash gate.sh            # PASS (144 declarations, standard axioms only)
bash tests/tamper.sh    # ALL TAMPERING TESTS REJECTED
```
`gate.sh` rejects `sorry`/`admit`/`native_decide`/`axiom`/`set_option`/syntax extensions, builds
the library, and checks `#print axioms` for every declaration listed in `REQUIRED`.
`tests/tamper.sh` plants seven defects in scratch copies (sorry, two-line axiom, fake `#eval`
output, `macro_rules` override of `#print axioms`, hidden axiom, and two `falsehyp` cases:
weakening `0 ≤ w i` to `w i = w i` in `erdos_mordell`, and dropping `hCA` from `fermat_min`) and
expects each to be rejected.
