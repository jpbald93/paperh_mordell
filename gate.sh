#!/bin/bash
# Gate for the ErdosMordell Lean formalisation. Passes only if all of these hold:
#  * the sources contain no `sorry`, `admit`, `native_decide`, `axiom`, `#eval`, `run_cmd`,
#    `initialize`, `IO`, `set_option`, or syntax-extension commands (which could redefine
#    `#print axioms`);
#  * the library builds without errors;
#  * the gate itself generates the `#print axioms` report for each REQUIRED theorem;
#  * each REQUIRED theorem uses only Lean's standard axioms (propext, Classical.choice, Quot.sound).
# SCAFFOLD=1 skips the forbidden-token check and also tolerates `sorryAx`, so a partially
# finished development can be checked while it still contains `sorry`.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
NS="ErdosMordell"
LIB="ErdosMordell"
REQUIRED="ErdosMordell.footDist ErdosMordell.proj_eq_lineMap ErdosMordell.proj_congr ErdosMordell.footDist_comm ErdosMordell.footDist_sq_mul ErdosMordell.inner_comb ErdosMordell.affineCombination_vsub ErdosMordell.affineCombination_vsub_zero ErdosMordell.affineCombination_vsub_one ErdosMordell.affineCombination_vsub_two ErdosMordell.points_ne ErdosMordell.cos_two_pi_div_three ErdosMordell.arccos_neg_half ErdosMordell.inner_of_angle ErdosMordell.ne_of_angle ErdosMordell.fermat_min ErdosMordell.fermat_alg ErdosMordell.angle_of_alg ErdosMordell.inner_gt_of_angle_lt ErdosMordell.x_pos ErdosMordell.vsub_F_eq ErdosMordell.fermat_exists ErdosMordell.fermat_torricelli ErdosMordell.key_scalar ErdosMordell.key_aux ErdosMordell.key_lemma_zero ErdosMordell.key_lemma_one ErdosMordell.key_lemma_two ErdosMordell.erdos_mordell ErdosMordell.gram_pos ErdosMordell.key_scalar_sq ErdosMordell.key_scalar_eq_iff ErdosMordell.key_facts ErdosMordell.eq_pos ErdosMordell.em_eq_scalar ErdosMordell.erdos_mordell_eq_iff ErdosMordell.wolstenholme ErdosMordell.barrow_T ErdosMordell.barrow_gram ErdosMordell.barrow_halfangle ErdosMordell.barrow_bound ErdosMordell.barrow_scalar ErdosMordell.gram_frame ErdosMordell.gram_pos_of_not_collinear ErdosMordell.bisector_dist ErdosMordell.barrow_vec ErdosMordell.weighted_vsub_eq_zero ErdosMordell.barrow ErdosMordell.l14_of_mem_closedInterior ErdosMordell.l14_of_mem_interior ErdosMordell.l14_key_lemma_zero ErdosMordell.l14_key_lemma_one ErdosMordell.l14_key_lemma_two ErdosMordell.l14_erdos_mordell ErdosMordell.l14_erdos_mordell_eq_iff ErdosMordell.l14_barrow ErdosMordell.l14_fermat_min ErdosMordell.l14_fermat_exists ErdosMordell.l14_fermat_torricelli ErdosMordell.l14_dist_sq ErdosMordell.l14_dist ErdosMordell.l14_not_collinear ErdosMordell.l14_ne ErdosMordell.l14_inner ErdosMordell.l14_mem_line ErdosMordell.l14_ac ErdosMordell.l14_angle_lt ErdosMordell.l14_angle_eq ErdosMordell.l14T ErdosMordell.l14T_sides ErdosMordell.l14T_incenter_mem ErdosMordell.l14w_erdos_mordell ErdosMordell.l14w_erdos_mordell_eq ErdosMordell.l14w_barrow ErdosMordell.l14w_fermat_min ErdosMordell.l14w_fermat_torricelli ErdosMordell.Blind.BlindSemiperimeter ErdosMordell.Blind.BlindArea ErdosMordell.Blind.BlindHeronGamma ErdosMordell.Blind.BlindEquilateral ErdosMordell.Blind.BlindInClosedTriangle ErdosMordell.Blind.BlindStrictlyInside ErdosMordell.Blind.BlindDistToLine ErdosMordell.Blind.BlindOrientationSign ErdosMordell.Blind.BlindOuterApex ErdosMordell.Blind.BlindApexA ErdosMordell.Blind.BlindApexB ErdosMordell.Blind.BlindApexC ErdosMordell.Blind.BlindNapoleonA ErdosMordell.Blind.BlindNapoleonB ErdosMordell.Blind.BlindNapoleonC ErdosMordell.Blind.agree_distToLine ErdosMordell.Blind.agree_distToLine' ErdosMordell.Blind.agree_closed ErdosMordell.Blind.agree_inside ErdosMordell.Blind.agree_equilateral ErdosMordell.Blind.blind29_stmt ErdosMordell.Blind.blind30_stmt ErdosMordell.Blind.blind31_stmt ErdosMordell.Blind.blind32_stmt ErdosMordell.Blind.blind33_stmt ErdosMordell.Blind.blind34_stmt ErdosMordell.Blind.blind35_stmt ErdosMordell.Blind.blind36_stmt ErdosMordell.Blind.rb_29 ErdosMordell.Blind.br_29 ErdosMordell.Blind.rb_30 ErdosMordell.Blind.br_30 ErdosMordell.Blind.rb_31 ErdosMordell.Blind.br_31 ErdosMordell.Blind.rb_32 ErdosMordell.Blind.br_32 ErdosMordell.Blind.rb_33 ErdosMordell.Blind.br_33 ErdosMordell.Blind.rb_34 ErdosMordell.Blind.br_34 ErdosMordell.Blind.rb_35 ErdosMordell.Blind.br_35 ErdosMordell.Blind.rb_36 ErdosMordell.Blind.br_36 ErdosMordell.Blind.b36_to_exists ErdosMordell.Classical.ClassicalSideA ErdosMordell.Classical.ClassicalSideB ErdosMordell.Classical.ClassicalSideC ErdosMordell.Classical.ClassicalSemiperimeter ErdosMordell.Classical.ClassicalAreaPts ErdosMordell.Classical.ClassicalArea ErdosMordell.Classical.ClassicalCentroid ErdosMordell.Classical.ClassicalEquilateral ErdosMordell.Classical.ClassicalSumSq ErdosMordell.Classical.ClassicalInsideOrOn ErdosMordell.Classical.ClassicalStrictlyInside ErdosMordell.Classical.ClassicalDistToLine ErdosMordell.Classical.ClassicalIsFermatPoint ErdosMordell.Classical.ClassicalAnglesLt120 ErdosMordell.Classical.ClassicalOutwardEquilateralApex ErdosMordell.Classical.ClassicalDistSum ErdosMordell.Classical.ClassicalDistSqSum ErdosMordell.Classical.ClassicalInOrderOnCircleOrLine ErdosMordell.Classical.cov_M1a ErdosMordell.Classical.cov_M1b ErdosMordell.Classical.cov_M2 ErdosMordell.Classical.cov_F1a ErdosMordell.Classical.cov_F1b"
SOURCES="ErdosMordell/*.lean ErdosMordell.lean"
[ -e .lake/packages/mathlib ] || { echo "FAIL: Mathlib packages missing (run setup by hand)"; exit 1; }
if [ "${SCAFFOLD:-0}" != "1" ]; then
  if grep -nE "\bsorry\b|\badmit\b|native_decide|\baxiom\b|#eval|\brun_cmd\b|\binitialize\b|\bIO\b|\bdebug\.|\bmacro|\belab|\bsyntax\b|\bnotation\b|\binfix|\bprefix\b|\bpostfix\b|import Lean|open Lean|\bset_option\b" $SOURCES; then
    echo "FAIL: forbidden token"; exit 1; fi
fi
build=$(lake build $LIB 2>&1); bstatus=$?
printf '%s\n' "$build" | tail -3
[ "$bstatus" -eq 0 ] || { printf '%s\n' "$build"; echo "FAIL: build"; exit 1; }
root=$(lake env lean "$LIB.lean" 2>&1) || { printf '%s\n' "$root"; echo "FAIL: build (root file)"; exit 1; }
chk=".gatecheck_$$.lean"
trap 'rm -f "$chk"' EXIT
{ echo "import $LIB"; for t in $REQUIRED; do echo "#print axioms $t"; done; } > "$chk"
out=$(lake env lean "$chk" 2>&1); status=$?
printf '%s\n' "$out"
[ "$status" -eq 0 ] || { echo "FAIL: axiom report"; exit 1; }
echo "$out" | grep -qE "(^|:)[[:space:]]*error" && { echo "FAIL: Lean reported an error"; exit 1; }
flat=$(printf '%s\n' "$out" | awk '/^'"'"'/{if(buf!="")print buf; buf=$0; next} {buf=buf" "$0} END{if(buf!="")print buf}')
reports=$(printf '%s\n' "$flat" | grep -E "depends on axioms|does not depend on any axioms")
n=0
for t in $REQUIRED; do
  te=$(printf '%s' "$t" | sed 's/[.]/\\./g')
  c=$(printf '%s\n' "$reports" | grep -cE "^'$te' (depends on axioms|does not depend)")
  [ "$c" -eq 1 ] || { echo "FAIL: expected one axiom report for $t, found $c"; exit 1; }
  n=$((n+1))
done
[ "$(printf '%s\n' "$reports" | grep -c .)" -eq "$n" ] || { echo "FAIL: unexpected extra reports"; exit 1; }
printf '%s\n' "$reports" | grep "depends on axioms" | grep -qv '\]' && { echo "FAIL: unterminated axiom list"; exit 1; }
if [ "${SCAFFOLD:-0}" = "1" ]; then ALLOW='^(propext|Classical\.choice|Quot\.sound|sorryAx)$'; else ALLOW='^(propext|Classical\.choice|Quot\.sound)$'; fi
bad=$(printf '%s\n' "$reports" | grep "depends on axioms" | sed 's/.*depends on axioms: *\[//; s/\].*//' \
      | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u | grep -vE "$ALLOW")
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
echo "PASS ($n declarations, standard axioms only)"
