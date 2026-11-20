#!/usr/bin/env bash
H=/tmp/claude-30033/-home-sam-repos-ix-ci-merge-tests/1ff7afee-07d4-4f1e-9d25-ce35af5f21a0/scratchpad/hints
S=/home/sam/repos/ix-ai-pipeline/.truthmines/store/mathlib-d13f23b
$H/check.sh $S/env.ixe $H/pilot-multi.log '_private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_1' 'Submodule.basis_of_pid_aux' 'Set.prod_mono_left' 'Int.neg_ediv_of_dvd' 'Finset.union_eq_empty'
$H/check.sh $S/env.ixe $H/pilot-single.log 'Finset.union_eq_empty'
