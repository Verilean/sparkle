#!/usr/bin/env bash
# Build the Sparkle tutorial Docker image.
#
# Run from the repo root.  The image tag defaults to
# `sparkle-tutorial:latest`.  Override with `IMAGE_TAG=...`.
set -euo pipefail

IMAGE_TAG="${IMAGE_TAG:-sparkle-tutorial:latest}"
DOCKERFILE="docker/tutorial/Dockerfile"

if [ ! -f "${DOCKERFILE}" ]; then
    echo "Run this script from the Sparkle repo root" >&2
    exit 1
fi

echo ">> docker build -t ${IMAGE_TAG} -f ${DOCKERFILE} ."
docker build -t "${IMAGE_TAG}" -f "${DOCKERFILE}" .

echo
echo "Built image: ${IMAGE_TAG}"
echo "Run with:    bash docker/tutorial/run.sh"
