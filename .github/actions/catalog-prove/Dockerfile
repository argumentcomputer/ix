# Prover image for the catalog-prove action: a prebuilt CUDA ix binary plus
# the Lean toolchain it was built with. Build it with build-image.sh, which
# stages `ix` and `lean-toolchain` as the build context.

FROM nvidia/cuda:13.3.1-base-ubuntu26.04

RUN apt-get update \
  && apt-get install --yes --no-install-recommends ca-certificates curl gh git jq unzip \
  && rm -rf /var/lib/apt/lists/*

RUN curl -sSfL -o /tmp/awscli.zip https://awscli.amazonaws.com/awscli-exe-linux-x86_64.zip \
  && unzip -q /tmp/awscli.zip -d /tmp \
  && /tmp/aws/install \
  && rm -rf /tmp/aws /tmp/awscli.zip

ENV ELAN_HOME=/opt/elan
ENV PATH=/opt/elan/bin:$PATH
COPY lean-toolchain /tmp/lean-toolchain
# elan installs a default toolchain lazily on first use, which the image's
# non-root runtime user cannot do, so install it explicitly here.
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain "$(cat /tmp/lean-toolchain)" \
  && elan toolchain install "$(cat /tmp/lean-toolchain)" \
  && lean --version \
  && rm /tmp/lean-toolchain

# Generated device traces with trace-only lookups, the GPU guide's fast path.
# The cell cap and lanes cache keep their defaults; the cache must stay under
# HOME so retained proofs persist between runs.
ENV AIUR_GPU_TRACE=generated AIUR_TRACE_ONLY_LOOKUPS=1 AIUR_MAX_PIECE_LOG_HEIGHT=24

COPY ix /usr/local/bin/ix
RUN ! ldd /usr/local/bin/ix | grep 'not found'
