#!/usr/bin/env bash
# Build a release tarball for the current platform.
#
# Output: dist/seki-<version>-<os>-<arch>.tar.gz
#         containing the `seki` and `seki-lsp` binaries, README, CHANGELOG,
#         LICENSE (if present), stdlib + lib/, and the examples directory.
#
# Usage:
#   ./scripts/release.sh
#
# Requires: Rust + cargo, tar, awk, uname.  No external Rust crates.

set -euo pipefail

cd "$(dirname "$0")/.."

VERSION=$(awk -F\" '/^version =/ {print $2; exit}' Cargo.toml)
OS=$(uname -s | tr '[:upper:]' '[:lower:]')
ARCH=$(uname -m)
case "$ARCH" in
    aarch64) ARCH="arm64" ;;
    *) ;;  # x86_64 etc.
esac

STAGE="seki-${VERSION}-${OS}-${ARCH}"
DIST="dist/${STAGE}"

echo ">> Building release binaries (version ${VERSION}, platform ${OS}-${ARCH})"
cargo build --release --bin seki --bin seki-lsp

echo ">> Verifying binaries"
./target/release/seki --version
./target/release/seki-lsp --help >/dev/null 2>&1 || true

echo ">> Running test gate"
cargo test --release --quiet

echo ">> Smoke-testing every example"
for f in examples/*.seki; do
    [ "$f" = "examples/helpers_mod.seki" ] && continue
    if ! ./target/release/seki "$f" >/dev/null 2>&1; then
        echo "FAIL on example: $f" >&2
        exit 1
    fi
done

echo ">> Smoke-testing seki test suite"
for f in tests/seki/test_*.seki; do
    if ! ./target/release/seki "$f" >/dev/null 2>&1; then
        echo "FAIL on test: $f" >&2
        exit 1
    fi
done

echo ">> Staging into ${DIST}"
rm -rf "dist"
mkdir -p "${DIST}/bin"
cp target/release/seki target/release/seki-lsp "${DIST}/bin/"
# strip if available (smaller binary, no functional impact)
command -v strip >/dev/null && strip "${DIST}/bin/seki" "${DIST}/bin/seki-lsp" || true

cp README.md CHANGELOG.md ROADMAP.md CONTRIBUTING.md SECURITY.md "${DIST}/"
[ -f LICENSE ] && cp LICENSE "${DIST}/" || true
cp -r lib "${DIST}/"
cp -r examples "${DIST}/"
cp -r docs "${DIST}/" 2>/dev/null || true

echo ">> Creating tarball"
( cd dist && tar czf "${STAGE}.tar.gz" "${STAGE}" )
echo ""
echo "Built: dist/${STAGE}.tar.gz"
du -h "dist/${STAGE}.tar.gz"
echo ""
echo "Verify:"
echo "  tar tzf dist/${STAGE}.tar.gz | head"
