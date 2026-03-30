#!/usr/bin/env bash
set -euo pipefail

# Re-exec with high priority and sleep prevention if not already done.
if [[ -z "${BENCH_PRIORITIZED:-}" ]]; then
  export BENCH_PRIORITIZED=1
  exec sudo nice -n -20 caffeinate -s "$0" "$@"
fi

# --- Configuration ---
# Number of input pairs per limb size to benchmark (max 1000).
PAIRS=4
# Number of times to repeat each benchmark (for benchstat confidence intervals).
COUNT=10
# Estimated time: PAIRS * COUNT * 8 limb sizes * ~3s * 2 configs.
# Default (4 * 10 * 8 * 3 * 2) ≈ 32 min.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
GOROOT="$(cd "${SCRIPT_DIR}/../../../../.." && pwd)"

if [[ ! -x "${GOROOT}/bin/go" ]]; then
  echo "Building toolchain from current checkout: ${GOROOT}"
  (cd "${GOROOT}/src" && ./make.bash)
fi

GO="${GOROOT}/bin/go"
export GOROOT GOTOOLCHAIN=local

# Build the pair filter regex: pair_(0|1|...|N-1)
PAIR_RE=$(seq 0 $((PAIRS - 1)) | tr '\n' '|' | sed 's/|$//')
BENCH_FILTER="BenchmarkExtendedGCD.*/pair_(${PAIR_RE})$"

OUT_DIR="${SCRIPT_DIR}/testdata"
LEGACY_FILE="${OUT_DIR}/bench_legacy.txt"
FIXED_FILE="${OUT_DIR}/bench_fixed.txt"
STATS_FILE="${OUT_DIR}/bench_comparison.txt"

mkdir -p "${OUT_DIR}"

echo "=== Generating inputs (if needed) ==="
"${GO}" test crypto/internal/fips140/bigmod -run=TestGenerateBenchInputs -v

echo ""
echo "=== Running legacy benchmarks (${PAIRS} pairs × count=${COUNT}) ==="
echo "    Filter: ${BENCH_FILTER}"
"${GO}" test crypto/internal/fips140/bigmod \
  -tags=sync_legacy \
  -bench="${BENCH_FILTER}" \
  -run='^$' \
  -count="${COUNT}" \
  | tee "${LEGACY_FILE}"

echo ""
echo "=== Running fixed benchmarks (${PAIRS} pairs × count=${COUNT}) ==="
"${GO}" test crypto/internal/fips140/bigmod \
  -tags=sync_fixed \
  -bench="${BENCH_FILTER}" \
  -run='^$' \
  -count="${COUNT}" \
  | tee "${FIXED_FILE}"

echo ""
echo "=== benchstat comparison ==="
BENCHSTAT="${HOME}/go/bin/benchstat"
if [[ ! -x "${BENCHSTAT}" ]]; then
  echo "Installing benchstat..."
  "${GO}" install golang.org/x/perf/cmd/benchstat@latest
fi
"${BENCHSTAT}" "${LEGACY_FILE}" "${FIXED_FILE}" | tee "${STATS_FILE}"

echo ""
echo "Results written to:"
echo "  ${LEGACY_FILE}"
echo "  ${FIXED_FILE}"
echo "  ${STATS_FILE}"
