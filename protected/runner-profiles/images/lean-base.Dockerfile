# Pinned Lean toolchain base image (protected; not candidate-editable).
FROM debian:bookworm-slim@sha256:3783cc01769c7b2b1b83a5c5ad96c815348e28ed7da68e2e3687004faa906251
ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.34.1
ARG ELAN_VERSION=v4.2.4
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl zstd git libc6-dev \
 && rm -rf /var/lib/apt/lists/*
RUN useradd -m -u 10001 -s /bin/sh builder
USER builder
WORKDIR /home/builder
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/${ELAN_VERSION}/elan-init.sh -o /tmp/elan-init.sh \
 && sh /tmp/elan-init.sh -y --no-modify-path --default-toolchain ${LEAN_TOOLCHAIN} \
 && rm /tmp/elan-init.sh
ENV PATH=/home/builder/.elan/bin:/usr/local/bin:/usr/bin:/bin
RUN lean --version && lake --version
