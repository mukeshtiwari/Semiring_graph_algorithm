#!/usr/bin/env bash
# Generate coqdoc HTML for the whole development into ./docs
#
# Every module of the Semiring and Examples theories is rendered into a single
# directory so that coqdoc cross-links identifiers across both theories.
#
#   docs/index.html      landing page (table of contents)
#   docs/toc.html        table of contents
#   docs/indexpage.html  global index of identifiers
#
# The extraction/*/Extraction.v files are deliberately excluded: they all share
# the module name Extraction and would overwrite one another.

set -euo pipefail

cd "$(dirname "$0")/.."

# coqdoc needs the .v and .glob files, which dune produces under _build.
dune build @all

rm -rf docs
mkdir -p docs

coqdoc --html --toc --toc-depth 2 --interpolate --utf8 --no-lib-name \
  --index indexpage -d docs \
  -R _build/default/algorithm Semiring \
  -R _build/default/examples Examples \
  _build/default/algorithm/*.v \
  _build/default/examples/*.v

# coqdoc emits no index.html once the identifier index is renamed, so use the
# table of contents as the landing page and link the identifier index from it.
sed -e 's|<title>Table of contents</title>|<title>Semiring graph algorithms</title>|' \
    -e 's|<div id="toc">|<h1>Semiring graph algorithms</h1>\n<p><a href="indexpage.html">Index of identifiers</a></p>\n<div id="toc">|' \
    docs/toc.html > docs/index.html

echo "Generated $(ls docs/*.html | wc -l | tr -d ' ') HTML files in docs/"
