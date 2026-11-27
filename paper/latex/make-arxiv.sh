#!/usr/bin/env bash
# Build the arXiv upload: main.tex and main.bbl (arXiv does not run BibTeX).
set -euo pipefail
cd "$(dirname "$0")"
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex >/dev/null
if grep -q -e '\[repository URL\]' -e '\[Country\]' main.tex; then
  echo "warning: placeholders remain in main.tex ([repository URL] or [Country])" >&2
fi
rm -rf arxiv
mkdir arxiv
cp main.tex main.bbl arxiv/
tar -czf arxiv-upload.tar.gz -C arxiv .
rm -rf arxiv
echo "wrote $(pwd)/arxiv-upload.tar.gz"
