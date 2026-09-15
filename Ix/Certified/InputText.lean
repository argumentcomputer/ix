/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.TextCodec

/-! Readable Ixon data values for certified requests and envelopes. The codecs
cover all claim variants, model hints, and selective-revelation fields. Each
constructor is decoded to its existing Lean type before witness search.
-/

namespace Ix.Certified.Text

instance : Codec Ix.DefKind where
  type := ref "Ix.DefKind"
  encode
    | .defn =>
      ref "Ix.DefKind.defn"
    | .opaq =>
      ref "Ix.DefKind.opaq"
    | .thm =>
      ref "Ix.DefKind.thm"
  decode term := do
    let (name, args) ← constructor term
    match name with
    | "Ix.DefKind.defn" => do
      arity name 0 args
      return .defn
    | "Ix.DefKind.opaq" => do
      arity name 0 args
      return .opaq
    | "Ix.DefKind.thm" => do
      arity name 0 args
      return .thm
    | _ => throw "expected a Ix.DefKind constructor"

instance : Codec Ix.DefinitionSafety where
  type := ref "Ix.DefinitionSafety"
  encode
    | .safe =>
      ref "Ix.DefinitionSafety.safe"
    | .unsaf =>
      ref "Ix.DefinitionSafety.unsaf"
    | .part =>
      ref "Ix.DefinitionSafety.part"
  decode term := do
    let (name, args) ← constructor term
    match name with
    | "Ix.DefinitionSafety.safe" => do
      arity name 0 args
      return .safe
    | "Ix.DefinitionSafety.unsaf" => do
      arity name 0 args
      return .unsaf
    | "Ix.DefinitionSafety.part" => do
      arity name 0 args
      return .part
    | _ => throw "expected a Ix.DefinitionSafety constructor"

instance : Codec Ix.QuotKind where
  type := ref "Ix.QuotKind"
  encode
    | .type =>
      ref "Ix.QuotKind.type"
    | .ctor =>
      ref "Ix.QuotKind.ctor"
    | .lift =>
      ref "Ix.QuotKind.lift"
    | .ind =>
      ref "Ix.QuotKind.ind"
  decode term := do
    let (name, args) ← constructor term
    match name with
    | "Ix.QuotKind.type" => do
      arity name 0 args
      return .type
    | "Ix.QuotKind.ctor" => do
      arity name 0 args
      return .ctor
    | "Ix.QuotKind.lift" => do
      arity name 0 args
      return .lift
    | "Ix.QuotKind.ind" => do
      arity name 0 args
      return .ind
    | _ => throw "expected a Ix.QuotKind constructor"

instance : Codec Ix.RevealConstructorInfo where
  type := ref "Ix.RevealConstructorInfo"
  encode value := ctor "Ix.RevealConstructorInfo.mk" #[
    encode value.isUnsafe, encode value.lvls, encode value.cidx, encode value.params,
    encode value.fields, encode value.typ]
  decode term := do
    let args ← arguments "Ix.RevealConstructorInfo.mk" 6 term
    return ⟨
      ← decode args[0]!, ← decode args[1]!, ← decode args[2]!, ← decode args[3]!,
      ← decode args[4]!, ← decode args[5]!⟩

instance : Codec Ix.RevealRecursorRule where
  type := ref "Ix.RevealRecursorRule"
  encode value := ctor "Ix.RevealRecursorRule.mk" #[
    encode value.ruleIdx, encode value.fields, encode value.rhs]
  decode term := do
    let args ← arguments "Ix.RevealRecursorRule.mk" 3 term
    return ⟨
      ← decode args[0]!, ← decode args[1]!, ← decode args[2]!⟩

instance : Codec Ix.RevealMutConstInfo where
  type := ref "Ix.RevealMutConstInfo"
  encode
    | .defn kind safety lvls typ value =>
      ctor "Ix.RevealMutConstInfo.defn" #[
        encode kind, encode safety, encode lvls, encode typ, encode value]
    | .indc isUnsafe lvls params indices typ ctors =>
      ctor "Ix.RevealMutConstInfo.indc" #[
        encode isUnsafe, encode lvls, encode params, encode indices, encode typ, encode ctors]
    | .recr k isUnsafe lvls params indices motives minors typ rules =>
      ctor "Ix.RevealMutConstInfo.recr" #[
        encode k, encode isUnsafe, encode lvls, encode params, encode indices, encode motives,
        encode minors, encode typ, encode rules]
  decode term := do
    let (name, args) ← constructor term
    match name with
    | "Ix.RevealMutConstInfo.defn" => do
      arity name 5 args
      return .defn
        (← decode args[0]!) (← decode args[1]!) (← decode args[2]!) (← decode args[3]!) (← decode args[4]!)
    | "Ix.RevealMutConstInfo.indc" => do
      arity name 6 args
      return .indc
        (← decode args[0]!) (← decode args[1]!) (← decode args[2]!) (← decode args[3]!) (← decode args[4]!) (← decode args[5]!)
    | "Ix.RevealMutConstInfo.recr" => do
      arity name 9 args
      return .recr
        (← decode args[0]!) (← decode args[1]!) (← decode args[2]!) (← decode args[3]!) (← decode args[4]!) (← decode args[5]!) (← decode args[6]!) (← decode args[7]!) (← decode args[8]!)
    | _ => throw "expected a Ix.RevealMutConstInfo constructor"

instance : Codec Ix.RevealConstantInfo where
  type := ref "Ix.RevealConstantInfo"
  encode
    | .defn kind safety lvls typ value =>
      ctor "Ix.RevealConstantInfo.defn" #[
        encode kind, encode safety, encode lvls, encode typ, encode value]
    | .recr k isUnsafe lvls params indices motives minors typ rules =>
      ctor "Ix.RevealConstantInfo.recr" #[
        encode k, encode isUnsafe, encode lvls, encode params, encode indices, encode motives,
        encode minors, encode typ, encode rules]
    | .axio isUnsafe lvls typ =>
      ctor "Ix.RevealConstantInfo.axio" #[
        encode isUnsafe, encode lvls, encode typ]
    | .quot kind lvls typ =>
      ctor "Ix.RevealConstantInfo.quot" #[
        encode kind, encode lvls, encode typ]
    | .cPrj idx cidx block =>
      ctor "Ix.RevealConstantInfo.cPrj" #[
        encode idx, encode cidx, encode block]
    | .rPrj idx block =>
      ctor "Ix.RevealConstantInfo.rPrj" #[
        encode idx, encode block]
    | .iPrj idx block =>
      ctor "Ix.RevealConstantInfo.iPrj" #[
        encode idx, encode block]
    | .dPrj idx block =>
      ctor "Ix.RevealConstantInfo.dPrj" #[
        encode idx, encode block]
    | .muts components =>
      ctor "Ix.RevealConstantInfo.muts" #[
        encode components]
  decode term := do
    let (name, args) ← constructor term
    match name with
    | "Ix.RevealConstantInfo.defn" => do
      arity name 5 args
      return .defn
        (← decode args[0]!) (← decode args[1]!) (← decode args[2]!) (← decode args[3]!) (← decode args[4]!)
    | "Ix.RevealConstantInfo.recr" => do
      arity name 9 args
      return .recr
        (← decode args[0]!) (← decode args[1]!) (← decode args[2]!) (← decode args[3]!) (← decode args[4]!) (← decode args[5]!) (← decode args[6]!) (← decode args[7]!) (← decode args[8]!)
    | "Ix.RevealConstantInfo.axio" => do
      arity name 3 args
      return .axio
        (← decode args[0]!) (← decode args[1]!) (← decode args[2]!)
    | "Ix.RevealConstantInfo.quot" => do
      arity name 3 args
      return .quot
        (← decode args[0]!) (← decode args[1]!) (← decode args[2]!)
    | "Ix.RevealConstantInfo.cPrj" => do
      arity name 3 args
      return .cPrj
        (← decode args[0]!) (← decode args[1]!) (← decode args[2]!)
    | "Ix.RevealConstantInfo.rPrj" => do
      arity name 2 args
      return .rPrj
        (← decode args[0]!) (← decode args[1]!)
    | "Ix.RevealConstantInfo.iPrj" => do
      arity name 2 args
      return .iPrj
        (← decode args[0]!) (← decode args[1]!)
    | "Ix.RevealConstantInfo.dPrj" => do
      arity name 2 args
      return .dPrj
        (← decode args[0]!) (← decode args[1]!)
    | "Ix.RevealConstantInfo.muts" => do
      arity name 1 args
      return .muts
        (← decode args[0]!)
    | _ => throw "expected a Ix.RevealConstantInfo constructor"

instance : Codec Ix.Claim where
  type := ref "Ix.Claim"
  encode
    | .eval input output assumptions =>
      ctor "Ix.Claim.eval" #[
        encode input, encode output, encode assumptions]
    | .check const assumptions =>
      ctor "Ix.Claim.check" #[
        encode const, encode assumptions]
    | .checkEnv root assumptions =>
      ctor "Ix.Claim.checkEnv" #[
        encode root, encode assumptions]
    | .reveal comm info =>
      ctor "Ix.Claim.reveal" #[
        encode comm, encode info]
    | .contains tree const =>
      ctor "Ix.Claim.contains" #[
        encode tree, encode const]
    | .catalog members content assumptions =>
      ctor "Ix.Claim.catalog" #[
        encode members, encode content, encode assumptions]
  decode term := do
    let (name, args) ← constructor term
    match name with
    | "Ix.Claim.eval" => do
      arity name 3 args
      return .eval
        (← decode args[0]!) (← decode args[1]!) (← decode args[2]!)
    | "Ix.Claim.check" => do
      arity name 2 args
      return .check
        (← decode args[0]!) (← decode args[1]!)
    | "Ix.Claim.checkEnv" => do
      arity name 2 args
      return .checkEnv
        (← decode args[0]!) (← decode args[1]!)
    | "Ix.Claim.reveal" => do
      arity name 2 args
      return .reveal
        (← decode args[0]!) (← decode args[1]!)
    | "Ix.Claim.contains" => do
      arity name 2 args
      return .contains
        (← decode args[0]!) (← decode args[1]!)
    | "Ix.Claim.catalog" => do
      arity name 3 args
      return .catalog
        (← decode args[0]!) (← decode args[1]!) (← decode args[2]!)
    | _ => throw "expected a Ix.Claim constructor"

instance : Codec Ix.Certified.Profile where
  type := ref "Ix.Certified.Profile"
  encode value := ctor "Ix.Certified.Profile.mk" #[
    encode value.falseType, encode value.falseElim, encode value.natType]
  decode term := do
    let args ← arguments "Ix.Certified.Profile.mk" 3 term
    return ⟨
      ← decode args[0]!, ← decode args[1]!, ← decode args[2]!⟩

instance : Codec Ix.Certified.Protocol where
  type := ref "Ix.Certified.Protocol"
  encode value := ctor "Ix.Certified.Protocol.mk" #[
    encode value.format, encode value.codec, encode value.checker, encode value.policy,
    encode value.aggregation]
  decode term := do
    let args ← arguments "Ix.Certified.Protocol.mk" 5 term
    return ⟨
      ← decode args[0]!, ← decode args[1]!, ← decode args[2]!, ← decode args[3]!,
      ← decode args[4]!⟩

instance : Codec Ix.Certified.Envelope where
  type := ref "Ix.Certified.Envelope"
  encode value := ctor "Ix.Certified.Envelope.mk" #[
    encode value.protocol, encode value.profile, encode value.claim, encode value.logicalAxioms]
  decode term := do
    let args ← arguments "Ix.Certified.Envelope.mk" 4 term
    return ⟨
      ← decode args[0]!, ← decode args[1]!, ← decode args[2]!, ← decode args[3]!⟩

instance : Codec Ix.Certified.InputSelection where
  type := ref "Ix.Certified.InputSelection"
  encode value := ctor "Ix.Certified.InputSelection.mk" #[
    encode value.objects, encode value.naturals]
  decode term := do
    let args ← arguments "Ix.Certified.InputSelection.mk" 2 term
    return ⟨
      ← decode args[0]!, ← decode args[1]!⟩

instance : Codec Ix.Certified.ModelProofHint where
  type := ref "Ix.Certified.ModelProofHint"
  encode value := ctor "Ix.Certified.ModelProofHint.mk" #[
    encode value.equality, encode value.reflexivity, encode value.eliminator, encode value.proof]
  decode term := do
    let args ← arguments "Ix.Certified.ModelProofHint.mk" 4 term
    return ⟨
      ← decode args[0]!, ← decode args[1]!, ← decode args[2]!, ← decode args[3]!⟩

instance : Codec Ix.Certified.ModelRuleHints where
  type := ref "Ix.Certified.ModelRuleHints"
  encode value := ctor "Ix.Certified.ModelRuleHints.mk" #[
    encode value.owner, encode value.proofs]
  decode term := do
    let args ← arguments "Ix.Certified.ModelRuleHints.mk" 2 term
    return ⟨
      ← decode args[0]!, ← decode args[1]!⟩

instance : Codec Ix.Certified.ModelHint where
  type := ref "Ix.Certified.ModelHint"
  encode value := ctor "Ix.Certified.ModelHint.mk" #[
    encode value.source, encode value.recursors, encode value.targets, encode value.proofs]
  decode term := do
    let args ← arguments "Ix.Certified.ModelHint.mk" 4 term
    return ⟨
      ← decode args[0]!, ← decode args[1]!, ← decode args[2]!, ← decode args[3]!⟩

instance : Codec Ix.Certified.Command.Request where
  type := ref "Ix.Certified.Command.Request"
  encode value := ctor "Ix.Certified.Command.Request.mk" #[
    encode value.profile, encode value.target, encode value.subjects, encode value.selection,
    encode value.models]
  decode term := do
    let args ← arguments "Ix.Certified.Command.Request.mk" 5 term
    return ⟨
      ← decode args[0]!, ← decode args[1]!, ← decode args[2]!, ← decode args[3]!,
      ← decode args[4]!⟩

instance : Codec Ix.Certified.LeafHint where
  type := ref "Ix.Certified.LeafHint"
  encode value := ctor "Ix.Certified.LeafHint.mk" #[
    encode value.claim, encode value.subjects, encode value.frontierTree]
  decode term := do
    let args ← arguments "Ix.Certified.LeafHint.mk" 3 term
    return ⟨
      ← decode args[0]!, ← decode args[1]!, ← decode args[2]!⟩

instance : Codec Ix.Certified.LogicalHint where
  type := ref "Ix.Certified.LogicalHint"
  encode value := ctor "Ix.Certified.LogicalHint.mk" #[
    encode value.selection, encode value.leaves, encode value.subjects, encode value.members,
    encode value.frontierTree, encode value.axiomTree, encode value.models]
  decode term := do
    let args ← arguments "Ix.Certified.LogicalHint.mk" 7 term
    return ⟨
      ← decode args[0]!, ← decode args[1]!, ← decode args[2]!, ← decode args[3]!,
      ← decode args[4]!, ← decode args[5]!, ← decode args[6]!⟩

instance : Codec Ixon.Comm where
  type := ref "Ixon.Comm"
  encode value := ctor "Ixon.Comm.mk" #[
    encode value.secret, encode value.payload]
  decode term := do
    let args ← arguments "Ixon.Comm.mk" 2 term
    return ⟨
      ← decode args[0]!, ← decode args[1]!⟩

instance : Codec Ix.Certified.RevealWitness where
  type := ref "Ix.Certified.RevealWitness"
  encode value := ctor "Ix.Certified.RevealWitness.mk" #[
    encode value.opening]
  decode term := do
    let args ← arguments "Ix.Certified.RevealWitness.mk" 1 term
    return ⟨
      ← decode args[0]!⟩

instance : Codec Ix.Certified.ClaimCommand.Hint where
  type := ref "Ix.Certified.ClaimCommand.Hint"
  encode
    | .logical hint =>
      ctor "Ix.Certified.ClaimCommand.Hint.logical" #[
        encode hint]
    | .contains tree =>
      ctor "Ix.Certified.ClaimCommand.Hint.contains" #[
        encode tree]
    | .reveal witness =>
      ctor "Ix.Certified.ClaimCommand.Hint.reveal" #[
        encode witness]
  decode term := do
    let (name, args) ← constructor term
    match name with
    | "Ix.Certified.ClaimCommand.Hint.logical" => do
      arity name 1 args
      return .logical
        (← decode args[0]!)
    | "Ix.Certified.ClaimCommand.Hint.contains" => do
      arity name 1 args
      return .contains
        (← decode args[0]!)
    | "Ix.Certified.ClaimCommand.Hint.reveal" => do
      arity name 1 args
      return .reveal
        (← decode args[0]!)
    | _ => throw "expected a Ix.Certified.ClaimCommand.Hint constructor"

instance : Codec Ix.Certified.ClaimCommand.Request where
  type := ref "Ix.Certified.ClaimCommand.Request"
  encode value := ctor "Ix.Certified.ClaimCommand.Request.mk" #[
    encode value.address, encode value.hint]
  decode term := do
    let args ← arguments "Ix.Certified.ClaimCommand.Request.mk" 2 term
    return ⟨
      ← decode args[0]!, ← decode args[1]!⟩

end Ix.Certified.Text

namespace Ix.Certified

def Command.Request.toText (request : Command.Request) : String := Text.write "request" request

def Command.Request.ofText (text : String) : Except String Command.Request := Text.read text

def ClaimCommand.Request.toText (request : ClaimCommand.Request) : String := Text.write "request" request

def ClaimCommand.Request.ofText (text : String) : Except String ClaimCommand.Request := Text.read text

def Envelope.toText (envelope : Envelope) : String := Text.write "envelope" envelope

def Envelope.ofText (text : String) : Except String Envelope := Text.read text

end Ix.Certified

