#!/usr/bin/env bash
# Build the lean-atlas viewer as a static site under a base path, for GitHub
# Pages. Usage: atlas/build-pages.sh <output-dir> [<base-path>]
#
# The upstream viewer is a Next.js app with two server routes: one reads
# Lean sources, one writes review results back into them. A static site has
# neither, so the routes are dropped and the sources are served as files,
# which the viewer already falls back to. The viewer fetches its data from
# absolute paths, so those are prefixed with the base path.
set -euo pipefail

out=$(realpath -m "$1")
base=${2:-}
here=$(cd "$(dirname "$0")" && pwd)
web="$here/../.lake/packages/lean-atlas/web"
[ -d "$web" ] || { echo "lean-atlas not found; run lake update in atlas/" >&2; exit 1; }

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp -r "$web" "$work/web"
cd "$work/web"
rm -rf node_modules .next out app/api

cat > next.config.ts <<EOF
import type { NextConfig } from "next";

const nextConfig: NextConfig = {
  output: "export",
  basePath: "$base",
  trailingSlash: true,
  images: { unoptimized: true },
};

export default nextConfig;
EOF

# Prefix the viewer's absolute data paths with the base path.
replace() {
  grep -qF "$2" "$1" || { echo "pattern not found in $1: $2" >&2; exit 1; }
  sed -i "s|$2|$3|" "$1"
}
replace hooks/useGraphData.ts '"/data/graph.json"' "\"$base/data/graph.json\""
replace lib/sourceCode.ts '`/lean-source/${filePath}`' "\`$base/lean-source/\${filePath}\`"

mkdir -p public/data public/lean-source
cp "$here/graph.json" public/data/graph.json
cp -rL "$here/LeanGeodesy" "$here/LeanGeodesy.lean" public/lean-source/

pnpm install --frozen-lockfile
pnpm build
rm -rf "$out"
mkdir -p "$(dirname "$out")"
cp -r out "$out"
echo "Static viewer written to $out"
