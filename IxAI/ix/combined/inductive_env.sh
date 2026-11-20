# Source this to run the ix scripts with the build that carries the nested-inductive advice fix
# (fork ~/repos/forks/ix-kernel-inductive, branch kernel-inductive-index-lift). The fix is on the
# prover side only, so the IxVM artifact stays the pinned one (the `ci` profile's digest).
export IX_PROFILE=ci
export IX_CI_CHECKOUT=/home/sam/repos/forks/ix-kernel-inductive
# The fork's CUDA library resolves dlopen through nix's loader, which does not search the system
# driver directory.
export LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libcuda.so.1
