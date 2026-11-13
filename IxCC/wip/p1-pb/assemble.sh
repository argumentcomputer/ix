#!/usr/bin/env bash
# assemble.sh OUT : the statements file (lead's copy) with PB's proved parts substituted for their sorry.
set -eu
S=/home/jcb/projects/ix-ixcc/IxCC/plans/resource-cert/P1-Statements.lean
D=/home/jcb/projects/ix-ixcc-fix-pb/IxCC/plans/pb/parts
perl -0pe '
  BEGIN { local $/; open F, "<", "'$D'/front_accepted.lean"; $fa = <F>; close F;
          open G, "<", "'$D'/shapeOk_of_run.lean"; $so = <G>; close G; }
  s/(src = Src\.Lazify\.run installed ch\.keys := )sorry\n/$1by\n$fa/;
  s/(theorem shapeOk_of_run \(h : run cfg P c = \.ok a\) : ShapeOk a\.src := )sorry\n/$1by\n$so/;
' $S > "$1"
D2=/home/jcb/projects/ix-ixcc-fix-pb/IxCC/plans/pb/parts
perl -0pi -e '
  BEGIN { local $/; open A, "<", "'$D2'/prefix.lean"; $px = <A>; close A;
          open B, "<", "'$D2'/eval_shielded_prefix.lean"; $sp = <B>; close B;
          open C, "<", "'$D2'/eval_erased_prefix.lean"; $ep = <C>; close C;
          open E, "<", "'$D2'/goesWrong_live.lean"; $gw = <E>; close E;
          open H, "<", "'$D2'/sound_live.lean"; $sl = <H>; close H; }
  s/(\/-- A shielded spine'"'"'s prefix)/$px$1/;
  s/(fv ≠ \.pap h'"'"' ls'"'"' args := )sorry\n/$1by\n$sp/;
  s/(a\.front\.GoesWrong i → a\.front\.GoesWrongLive c\.relevance i := )sorry\n/$1by\n$gw/;
  s/(Lang\.run \(a\.linked D\) i k = \.resource failure\) :=\n  )sorry\n/$1by\n$sl/;
  s/(\(he : eval p k ls ρ f = \.ok fv\) :\n    IgnoresNext ann fv := )sorry\n/$1by\n$ep/;
' "$1"
printf '\n#print axioms IxCC.Recheck.front_accepted\n#print axioms IxCC.Recheck.shapeOk_of_run\n#print axioms IxCC.Src.Relevance.Proof.P1.eval_shielded_prefix\n#print axioms IxCC.Src.Relevance.Proof.P1.eval_erased_prefix\n' >> "$1"
grep -c "sorry" "$1"
