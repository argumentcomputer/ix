import Ix.Cert.TableAdmission
import Ix.Cli.TableAdmission

/-! # The kernel's admission of a role table, for the command line

`Ix.Cli.TableAdmission` holds the admission `ix verify` and `ix compress` run on
a claim's role table, and receives it at startup, because the check
(`Ix.Cert.TableAdmission.check`) is outside the module system. This file joins
the two: `checker` is that check, with `explain`, the first of its stages that
refuses, for the refusal's message; `install` hands it to the command line.

`explain` reruns `check`'s stages in `check`'s order (the table's admission, a
string literal's support bound with `String`, the stored seeds, the closure's
order, the committed prelude, the reading (its hints read as `check` reads them), the
fold, then the specifications the fold does not check). It is read only after
`check` refused, and decides nothing. -/

namespace Ix.Cli.TableAdmissionKernel

open Ix.Kernel
open Ix.Cert.TableAdmission

/-- The first stage of `Ix.Cert.TableAdmission.check` that refuses `b` over `E`. -/
def explain (b : Admission.Binding) (E : Ixon.Env) : String :=
  match Admission.admitBinding Address.admissionHash b with
  | .error e => s!"the table's section does not admit: {Admission.Error.binding e}"
  | .ok t =>
    let seeds := seedList t
    if !literalSupportOk t then
      "the table binds String without the rest of a string literal's support \
        (String.ofList, List and its constructors, Char, Char.ofNat)"
    else
    match seeds.find? (!E.consts.contains ·) with
    | some a =>
      s!"the environment lacks {a}, which the table binds or its evidence names"
    | none =>
      let idx := Ix.Cert.artifactRecIndex E
      let (wit, order) := candidate t E idx
      if !(orderedCheck E order && closedCheck t E idx seeds order &&
          reachCheck t E idx seeds wit order) then
        "the closure of the table's constants has no order with each record after the \
          records it references"
      else
        match (Reader.preludeFor t : Except String (Reader.Prelude .anon)) with
        | .error e => s!"the committed prelude does not read under the table: {e}"
        | .ok pre =>
          -- the hints read through a map built once, as `check` reads them (`hintsAt`)
          match Admission.prepareWith Address.admissionHash b pre admissionLimits
              (Ix.Cert.recordsOf E order) (Ix.Cert.blobsOf E order)
              (hintsAt (hintsProjAt E) E) with
          | .error e =>
            let why := toString e
            let record := match e with
              | .read p _ => match order[p]? with
                | some a => s!" (the record {a})"
                | none => ""
              | _ => ""
            if (why.splitOn "without a recursor").length > 1 then
              s!"the reading declines: {why}{record}; the environment must hold the recursor \
                records of every inductive block in the closure, which are not drawn in"
            else s!"the reading declines: {why}{record}"
          | .ok (ev, ds) =>
            match Cached.checkDecls .verified ev (ds.map IxVM.Refinement.thmToOpaqueDefn) with
            | .error (e, p) => s!"the kernel refuses declaration {p}: {e}"
            | .ok envA =>
              if !ds.toList.all (thmInProp envA) then
                "a theorem's statement is not a proposition"
              else if !(userAxiomsOfDecls ds.toList).isEmpty then
                "the closure declares an axiom beyond the standard ones"
              else if !anchorsOk ds.toList then
                "a bound anchor does not have its specification's type"
              else if !eqnsOk t envA ev then
                -- the bound roles `eqnsOk` refuses
                let failing := Role.all.filter fun r =>
                  (t.addressOf? r).isSome && (r.spec (md := .anon)).kind == .eqns &&
                    !isOk (eqnsCheck (fueledOps .verified pureFuel) envA r ev)
                match failing with
                | r :: _ =>
                  s!"the bound role {r.leanName}, specified by equations, does not meet them \
                    ({failing.length} such roles fail)"
                | [] => "a role specified by equations does not meet them"
              else "no stage refuses"

/-- The kernel's admission, as the command line runs it. -/
def checker : Ix.Cli.TableAdmission.Checker where
  check := Ix.Cert.TableAdmission.check
  explain := explain

/-- Hand the kernel's admission to the command line. -/
def install : IO Unit := Ix.Cli.TableAdmission.install checker

end Ix.Cli.TableAdmissionKernel
