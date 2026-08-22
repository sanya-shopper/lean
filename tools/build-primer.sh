#!/usr/bin/env bash
# Build lean-primer.tex -> lean-primer.pdf and UNIT-TEST that the build is clean:
#   - LaTeX exits 0
#   - no undefined references / citations (no "??" in the output)
#   - no missing bibliography entries
# Usage: tools/build-primer.sh   (run from repo root)
# LaTeX aux/log/pdf land in the disposable tree Projects/_buildoutput/lean/
# (safe to rm -rf; recreated on the next build). The final PDF is this repo's
# checked-in product, so it is copied back to the repo root after a clean build.
set -euo pipefail
cd "$(dirname "$0")/.."

DOC=lean-primer
OUT=../_buildoutput/lean
command -v latexmk >/dev/null || { echo "FAIL: latexmk not found"; exit 1; }
command -v biber   >/dev/null || { echo "FAIL: biber not found";   exit 1; }

mkdir -p "$OUT"
echo "== building ${DOC}.pdf (pdflatex + biber via latexmk, outdir $OUT) =="
latexmk -pdf -interaction=nonstopmode -outdir="$OUT" "${DOC}.tex" >/dev/null

fail=0
log="${OUT}/${DOC}.log"

# 1. undefined references / citations
if grep -qE 'LaTeX Warning: (Reference|Citation).*undefined' "$log"; then
  echo "FAIL: undefined references or citations:"
  grep -E 'LaTeX Warning: (Reference|Citation).*undefined' "$log" | sort -u
  fail=1
fi
# 2. rerun-needed left unresolved (labels changed on last pass)
if grep -q 'Rerun to get' "$log"; then
  echo "FAIL: cross-references not converged (rerun needed)"; fail=1
fi
# 3. literal ?? in the produced PDF text (unresolved \ref/\cite)
if command -v pdftotext >/dev/null; then
  if pdftotext "${OUT}/${DOC}.pdf" - 2>/dev/null | grep -q '??'; then
    echo "FAIL: '??' present in PDF (unresolved ref/cite)"; fail=1
  fi
fi
# 4. biber reported missing entries
if [ -f "${OUT}/${DOC}.blg" ] && grep -qiE 'WARN.*cannot find|ERROR' "${OUT}/${DOC}.blg"; then
  echo "FAIL: biber errors / missing entries:"; grep -iE 'WARN|ERROR' "${OUT}/${DOC}.blg"
  fail=1
fi

if [ "$fail" -eq 0 ]; then
  cp "${OUT}/${DOC}.pdf" "${DOC}.pdf"   # the checked-in product (repo T9 exception)
  pages=$(pdfinfo "${DOC}.pdf" 2>/dev/null | awk '/^Pages/{print $2}')
  echo "OK: ${DOC}.pdf built cleanly (${pages:-?} pages), references resolved."
else
  echo "BUILD TEST FAILED"; exit 1
fi
