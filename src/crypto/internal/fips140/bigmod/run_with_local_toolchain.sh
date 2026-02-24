#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
GOROOT="$(cd "${SCRIPT_DIR}/../../../../.." && pwd)"

if [[ ! -f "${GOROOT}/src/make.bash" ]]; then
  echo "error: could not find src/make.bash under ${GOROOT}" >&2
  echo "run this script from crypto/internal/fips140/bigmod in a Go source checkout" >&2
  exit 1
fi

if [[ ! -x "${GOROOT}/bin/go" ]]; then
  echo "Building toolchain from current checkout: ${GOROOT}"
  (
    cd "${GOROOT}/src"
    ./make.bash
  )
fi

# Run as a stdlib package path so internal imports are allowed.
GOROOT="${GOROOT}" GOTOOLCHAIN=local "${GOROOT}/bin/go" test crypto/internal/fips140/bigmod "$@"
