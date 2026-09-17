#!/bin/sh
# Machine-checked security proofs for IKEv2: build and verification driver.

set -u

HERE=$(cd "$(dirname "$0")" && pwd)
cd "$HERE" || exit 1

SWITCH=${EASYCRYPT_SWITCH:-easycrypt}
if command -v opam >/dev/null 2>&1; then
  eval "$(opam env --switch="$SWITCH" 2>/dev/null)" 2>/dev/null || true
fi

EC=${EASYCRYPT:-easycrypt}
if ! command -v "$EC" >/dev/null 2>&1; then
  echo "error: the easycrypt executable was not found."
  echo "       install EasyCrypt and put it on PATH, or set EASYCRYPT=/path/to/easycrypt."
  exit 127
fi

FILES="IKEv2Core.ec Expansion.ec Segment.ec Compression.ec Cascade.ec Ppk.ec Spks.ec Optimality.ec Qrom.ec Kem.ec Acce.ec Instantiate.ec"

echo "=============================================================="
echo " Machine-checked security proofs for IKEv2"
echo "=============================================================="
echo "EasyCrypt : $(command -v "$EC")"
echo "Provers   : $("$EC" config 2>&1 | sed -n 's/^known provers: //p')"
echo "Directory : $HERE"
echo "--------------------------------------------------------------"

echo "checking that no proof obligation is skipped"
BAD=$(grep -n -E '\b(admit|admitted)\b' $FILES 2>/dev/null)
if [ -n "$BAD" ]; then
  echo "FAILED: an incomplete proof was found"
  echo "$BAD"
  exit 1
fi
echo "  no occurrence of admit or admitted"
echo
echo "assumptions carried by the development"
grep -h -A2 -E '^declare axiom' $FILES 2>/dev/null | sed -n 's/^declare axiom \([A-Za-z_0-9]*\).*/  hypothesis: \1/p' | sort -u
grep -h -E '^(op|type).*as [a-z_0-9]+\.' $FILES 2>/dev/null | sed -n 's/.*as \([a-z_0-9]*\)\..*/  parameter: \1/p' | sort -u
echo "--------------------------------------------------------------"

rm -f ./*.eco
LOG=$(mktemp /tmp/ikev2-ec-XXXXXX)
PASS=0
FAIL=0
START=$(date +%s)

for f in $FILES; do
  if [ ! -f "$f" ]; then
    printf '%-18s %s\n' "$f" "MISSING"
    FAIL=$((FAIL + 1))
    continue
  fi
  T0=$(date +%s)
  "$EC" compile -I . "$f" > "$LOG" 2>&1
  RC=$?
  T1=$(date +%s)
  if [ "$RC" -eq 0 ]; then
    printf '%-18s %s  (%ss)\n' "$f" "verified" "$((T1 - T0))"
    PASS=$((PASS + 1))
  else
    printf '%-18s %s\n' "$f" "FAILED"
    tr '\r' '\n' < "$LOG" | grep -iE 'critical|error' | head -12
    FAIL=$((FAIL + 1))
  fi
done

END=$(date +%s)
rm -f "$LOG"

echo "--------------------------------------------------------------"
echo "verified $PASS file(s), failed $FAIL file(s), $((END - START))s total"
if [ "$FAIL" -eq 0 ]; then
  echo "RESULT: all machine-checked proofs verify"
  exit 0
fi
echo "RESULT: verification failed"
exit 1
