#!/usr/bin/env bash
# build_pr678.sh : build `ix` at the head of ix pull request 678 (worktree ~/repos/ix.ixai-pr678)
# to test its IxVM kernel on this project's constants. Build trees are on the NVMe scratch; the
# Lean package builds (Mathlib and the rest, same manifest) are copied from the kernel-hints
# fork's tree so that only ix's own modules compile. The dev shell is the kernel-hints fork's,
# which avoids evaluating a second flake. Writes build.log and build.done (lake's exit status).
N=/opt/dlami/nvme/ix-ai/pr678
W=/home/sam/repos/ix.ixai-pr678
mkdir -p $N/target
rm -f $N/build.done
if [ ! -d $N/lake ]; then
  mkdir -p $N/lake
  cp -a /opt/dlami/nvme/ix-ai/kernel-hints/lake/packages $N/lake/packages
fi
[ -e $W/.lake ] || ln -s $N/lake $W/.lake
[ -e $W/target ] || ln -s $N/target $W/target
cd $W
IX_CUDA=1 /usr/bin/time -v -o $N/build.time systemd-run --user --scope -q -p MemoryMax=180G -- \
  timeout "${BUILD_CAP:-4500}" nix develop /home/sam/repos/forks/ix-kernel-hints --command lake build ix > $N/build.log 2>&1
echo $? > $N/build.done
exit 0
