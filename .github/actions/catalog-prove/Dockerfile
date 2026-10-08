# Prover image for the catalog-prove action: a prebuilt CUDA ix binary plus
# the Lean toolchain it was built with. Build it with build-image.sh, which
# stages `ix` and `lean-toolchain` as the build context.

FROM nvidia/cuda:13.3.1-base-ubuntu26.04

RUN apt-get update \
  && apt-get install --yes --no-install-recommends ca-certificates curl gh git jq \
  && rm -rf /var/lib/apt/lists/*

ENV ELAN_HOME=/opt/elan
ENV PATH=/opt/elan/bin:$PATH
COPY lean-toolchain /tmp/lean-toolchain
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain "$(cat /tmp/lean-toolchain)" \
  && rm /tmp/lean-toolchain

COPY ix /usr/local/bin/ix
RUN ! ldd /usr/local/bin/ix | grep 'not found'
