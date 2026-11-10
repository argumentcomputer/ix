import IxCC.Src.Table.Validate
import IxCC.Src.Relevance.Check
import IxCC.Src.Lazify

/-! # The front end's recheck path

What `Recheck.run` (D17) does with a
`Src.Program` before erasure: the table checks re-validate
every unfolding-table entry and the pinned identities (V), the relevance
annotation is installed and checked, tiers S and C (style V) and then
`Relevance.checkCanonical` (V: every irrelevant tag must be justified by the
declaration types, on every program whatever its pinned identities), and
`Lazify` is re-run (P). Ingress, the annotator, `Table.build` and `Admit`
are the producer's and stay off this path. Every step is kernel-evaluable:
`IxCCTests.Lam.KernelK1` evaluates `run` and erasure on real K1
artifacts with `decide +kernel`.

The load pipeline runs the same pieces: `Table.validate` after the table is
built, and `annotation` for each annotation it is given. -/

namespace IxCC.Src.Recheck

/-- Where the recheck path rejected its input. -/
inductive Error where
  | table (message : String)
  | install (message : String)
  | relevance (errs : Array Relevance.RelError)
  deriving Inhabited

/-- The annotation's steps: install the tags, check the annotation (tiers S
and C, `Relevance.check`), refuse any tag the declaration types do not
justify (`Relevance.checkCanonical`, on every program, whatever its pinned
identities), and Lazify the checked runtime terms. -/
def annotation (p : Program) (ann : Relevance.Ann) :
    Except Error (Program × Relevance.Checked) :=
  match Relevance.install p ann with
  | .error msg => .error (.install msg)
  | .ok p =>
    match Relevance.check p ann with
    | .error errs => .error (.relevance errs)
    | .ok checked =>
      let canonErrs := Relevance.checkCanonical p ann checked
      if !canonErrs.isEmpty then .error (.relevance canonErrs.toArray)
      else .ok (Lazify.run p checked.keys, checked)

/-- The front end's recheck path on a program (with its table) and an
annotation. -/
def run (cfg : Table.Config) (p : Program) (ann : Relevance.Ann) :
    Except Error (Program × Relevance.Checked) :=
  match Table.validate cfg p with
  | .error msg => .error (.table msg)
  | .ok () => annotation p ann

end IxCC.Src.Recheck
