#!/usr/bin/env bash
# Run the Sparkle tutorial container.  Maps port 8888.
set -euo pipefail

IMAGE_TAG="${IMAGE_TAG:-sparkle-tutorial:latest}"
PORT="${PORT:-8888}"

echo ">> docker run --rm -it -p ${PORT}:8888 ${IMAGE_TAG}"
echo
echo "Once Jupyter starts, open http://localhost:${PORT} in your"
echo "browser.  No token / password required (this image is for"
echo "local development only — don't expose the port publicly)."
echo

exec docker run --rm -it -p "${PORT}:8888" "${IMAGE_TAG}"
