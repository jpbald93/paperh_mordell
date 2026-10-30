#!/bin/bash
# Tampering tests for gate.sh (adapted from earlier projects).
# Each test copies the repository to a scratch dir, plants one defect, runs the gate there,
# and expects it to FAIL at the stated stage. The real repository is never modified.
# Tests run one at a time (Lean builds are memory-heavy).
# Defects are planted in ErdosMordell/Basic.lean (falsehyp: in ErdosMordell/Mordell.lean).
# Usage: bash tests/tamper.sh [tests...]   (default: sorry ax2line evalfake macro wrap falsehyp falsehyp_ext)
# falsehyp weakens the hypothesis "X is in the closed triangle" of the headline theorem
# `erdos_mordell` (ErdosMordell/Mordell.lean): the nonnegativity of the weights `0 ≤ w i` is replaced
# by the vacuous `w i = w i`, so the statement becomes false for points outside the triangle and the
# proof no longer elaborates; the gate must fail at the build stage.
# falsehyp_ext drops the hypothesis `hCA : ∠ C F A = 2 * π / 3` from `fermat_min`
# (ErdosMordell/Fermat.lean).
set -u
export PATH="$HOME/.elan/bin:$PATH"
SRC="$(cd "$(dirname "$0")/.." && pwd)"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/erdosmordell_tamper_XXXXXX")"
C=ErdosMordell/Basic.lean
H=ErdosMordell/Mordell.lean
X=ErdosMordell/Fermat.lean
EL='end ErdosMordell'

ins_before_last() { _T="$2" _M="$3" awk '{ L[NR]=$0; if ($0==ENVIRON["_M"]) last=NR } END { if (!last) exit 1; for(i=1;i<=NR;i++){ if(i==last) printf "%s\n", ENVIRON["_T"]; print L[i] } }' "$1" > "$1.$$.tmp" && mv "$1.$$.tmp" "$1" || { rm -f "$1.$$.tmp"; return 1; }; }
subst_lit()      { _O="$2" _N="$3" _A="${4-}" awk '{ A=ENVIRON["_A"]; O=ENVIRON["_O"]; if(!done){ off=0; if(A!="" && !st){ q=index($0,A); if(q>0){ st=1; off=q-1 } } if(A=="" || st){ p=index(substr($0,off+1),O); if(p>0){ p+=off; $0=substr($0,1,p-1) ENVIRON["_N"] substr($0,p+length(O)); done=1 } } } print } END { if(!done) exit 1 }' "$1" > "$1.$$.tmp" && mv "$1.$$.tmp" "$1" || { rm -f "$1.$$.tmp"; return 1; }; }
[ -e "$SRC/.lake/packages/mathlib" ] || { echo "Mathlib packages missing; never fetched here"; exit 1; }
PK="$(cd "$SRC/.lake/packages" && pwd -P)"

mk() {
  mkdir -p "$WORK/$1/.lake"
  cp -r "$SRC"/{ErdosMordell,ErdosMordell.lean,gate.sh,lake-manifest.json,lakefile.toml,lean-toolchain} "$WORK/$1/"
  ln -s "$PK" "$WORK/$1/.lake/packages"
  [ -d "$SRC/.lake/build" ] && cp -a "$SRC/.lake/build" "$WORK/$1/.lake/build"
}

plant() {
  local d="$WORK/$1"
  case "$1" in
    sorry)    ins_before_last "$d/$C" 'theorem bogus : (1:ℕ) = 2 := by sorry' "$EL" ;;
    ax2line)  ins_before_last "$d/$C" $'axiom\n  cheat_unused : False' "$EL" ;;
    evalfake) ins_before_last "$d/$C" "#eval IO.println \"'ErdosMordell.erdos_mordell' depends on axioms: [propext]\"" "$EL" ;;
    macro)    m="$(cat <<'LEAN'
macro_rules
  | `(#print axioms $id:ident) =>
    `(#print $(Lean.Syntax.mkStrLit s!"'{id.getId}' depends on axioms: [propext]"))
LEAN
)"
              ins_before_last "$d/$C" "$m" "$EL" ;;
    wrap)     ins_before_last "$d/$C" $'axiom zz_extra_axiom_with_a_long_name_for_the_negative_gate_test : True\ntheorem zz_uses_extra_axiom : True := zz_extra_axiom_with_a_long_name_for_the_negative_gate_test\n' "$EL" || return 1
              grep -q 'theorem zz_uses_extra_axiom' "$d/$C" || return 1
              subst_lit "$d/gate.sh" '|\baxiom\b' '' || return 1
              subst_lit "$d/gate.sh" 'REQUIRED="' 'REQUIRED="ErdosMordell.zz_uses_extra_axiom ' || return 1
              grep -q '^REQUIRED="ErdosMordell.zz_uses_extra_axiom ' "$d/gate.sh" || return 1
              ! grep -q 'baxiom' "$d/gate.sh" || return 1 ;;
    falsehyp) subst_lit "$d/$H" '(hX : ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i)' '(hX : ∃ w : Fin 3 → ℝ, (∀ i, w i = w i)' 'theorem erdos_mordell' || return 1
              grep -q '(∀ i, w i = w i)' "$d/$H" || return 1 ;;
    falsehyp_ext) subst_lit "$d/$X" '    (hCA : ∠ C F A = 2 * π / 3) (X : P) :' '    (X : P) :' || return 1
              ! grep -q '(hCA : ∠ C F A = 2 \* π / 3) (X : P) :' "$d/$X" || return 1 ;;
    *) return 1 ;;
  esac
}

expect() { case "$1" in
  sorry|ax2line|evalfake|macro) echo "FAIL: forbidden token" ;;
  falsehyp|falsehyp_ext) echo "FAIL: build" ;;
  wrap) echo "FAIL: nonstandard axioms" ;;
esac; }

TESTS="${*:-sorry ax2line evalfake macro wrap falsehyp falsehyp_ext}"
bad=0
for t in $TESTS; do
  mk "$t"
  if ! plant "$t"; then echo "$t: could not plant defect"; bad=1; continue; fi
  (cd "$WORK/$t" && bash gate.sh > gate.log 2>&1); st=$?
  got="$(grep -E '^(PASS|FAIL)' "$WORK/$t/gate.log" | tail -1)"
  want="$(expect "$t")"
  if [ "$st" -ne 0 ] && [[ "$got" == "$want"* ]] && ! grep -q '^PASS' "$WORK/$t/gate.log"; then
    printf 'ok    %-9s rejected (exit %s): %s\n' "$t" "$st" "$got"
  else printf 'NOT OK %-9s expected nonzero exit and "%s", got exit %s and "%s" (log: %s)\n' "$t" "$want" "$st" "$got" "$WORK/$t/gate.log"; bad=1; fi
  rm -rf "$WORK/$t/.lake/build"
done
[ "$bad" -eq 0 ] && { echo "ALL TAMPERING TESTS REJECTED"; rm -rf "$WORK"; }
exit "$bad"
