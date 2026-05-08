#!/usr/bin/env bash
# Boot the Sparkle tutorial container and run the Playwright e2e
# suite against it, then tear the container down.
#
# Usage (from the repo root):
#
#     bash tests/e2e/run.sh            # full cycle, headless
#     SPARKLE_E2E_HEADED=1 bash tests/e2e/run.sh   # show the browser
#
# Prerequisites:
#     - Docker  (we run the existing `sparkle-tutorial:latest` image
#                — build it once with `bash docker/tutorial/build.sh`)
#     - Node + npm  (Playwright itself plus a browser bundle)
#
# Exits non-zero on any failure so CI can gate on it.
set -euo pipefail

PORT="${SPARKLE_E2E_PORT:-18888}"
IMAGE="${SPARKLE_E2E_IMAGE:-sparkle-tutorial:latest}"
CONTAINER="${SPARKLE_E2E_CONTAINER:-sparkle-tutorial-e2e}"

cd "$(dirname "$0")"

# Make sure a previous run isn't still bound to the port.
docker rm -f "$CONTAINER" 2>/dev/null || true

echo ">> docker run --rm -d --name $CONTAINER -p $PORT:8888 $IMAGE"
docker run --rm -d --name "$CONTAINER" -p "$PORT:8888" "$IMAGE"

# Tear the container down on every exit path, even if Playwright
# blows up halfway through.
cleanup() {
  echo ">> docker rm -f $CONTAINER"
  docker rm -f "$CONTAINER" >/dev/null 2>&1 || true
}
trap cleanup EXIT

# Wait for JupyterLab to come up.
echo ">> waiting for http://localhost:$PORT/lab to respond..."
for i in $(seq 1 60); do
  if curl --silent --fail --max-time 2 "http://localhost:$PORT/lab" >/dev/null 2>&1; then
    echo "   ready after ${i}s"
    break
  fi
  if [ "$i" = "60" ]; then
    echo "ERROR: JupyterLab didn't start within 60s" >&2
    docker logs "$CONTAINER" | tail -20
    exit 1
  fi
  sleep 1
done

# Install Playwright deps once per checkout (idempotent).
if [ ! -d node_modules/@playwright/test ]; then
  echo ">> npm install (Playwright)"
  npm install
  npx playwright install chromium
fi

# Playwright's bundled Chromium ships against Ubuntu glibc, so on a
# pure-Nix host (where `libglib-2.0.so.0` isn't on the dynamic
# loader path) it will refuse to start.  Detect that and fall back
# to running Playwright inside its own published docker image, on
# the host network, so the just-started JupyterLab container is
# still reachable on `localhost:$PORT`.
needs_docker_runner=0
if ! npx playwright --version >/dev/null 2>&1; then
  needs_docker_runner=1
elif command -v ldd >/dev/null 2>&1; then
  shell="$(npx playwright install --help 2>&1 | head -1)"
  : # nothing — shell stub
fi

# Quick probe: actually launch Chromium and see if the dynamic
# linker is happy.  Cheap enough and avoids second-guessing.
if [ "$needs_docker_runner" = "0" ]; then
  if ! npx playwright install --dry-run >/dev/null 2>&1; then
    needs_docker_runner=1
  fi
  if [ "$needs_docker_runner" = "0" ]; then
    if ! npx -y -- node -e "(async()=>{const{chromium}=require('@playwright/test');const b=await chromium.launch();await b.close();})().catch(e=>{process.exit(1)})" >/dev/null 2>&1; then
      needs_docker_runner=1
    fi
  fi
fi

if [ "$needs_docker_runner" = "1" ]; then
  echo ">> host-side Chromium failed to launch; using mcr.microsoft.com/playwright"
  exec docker run --rm --network host \
    -v "$(pwd):/work" -w /work \
    -e SPARKLE_E2E_PORT="$PORT" \
    mcr.microsoft.com/playwright:v1.56.0-noble \
    bash -lc 'npm install --no-audit --no-fund && npx playwright test'
fi

if [ -n "${SPARKLE_E2E_HEADED:-}" ]; then
  npx playwright test --headed
else
  npx playwright test
fi
