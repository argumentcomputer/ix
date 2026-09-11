import Ix.Compiler.IxIR2.CreditRefinement

/-!
# Full-credit regression gate

These independently written CFGs exercise combinations beyond the existing
single-candidate optimizer fixtures. Every accepted program runs through the
actual policy runners; comparisons check the whole trace, result shape,
exact costs, and complete reclamation. Guards execute during library builds.
-/

namespace Ix.Compiler.IxIR2.CreditRefinement.Examples

open Eval
open Ix.Compiler.Ixon (Address Owned)

private def blockAddress : Address := Address.replicate 0xb1
private def layout : LayoutId := Address.replicate 0xb2
private def pairLayout : LayoutId := Address.replicate 0xb3
private def fieldLayout : LayoutId := Address.replicate 0xb4
private def helperAddress : Address := Address.replicate 0xb5
private def nestedAddress : Address := Address.replicate 0xb6
private def leaf : CtorId := ⟨blockAddress, 0, 0⟩
private def pair : CtorId := ⟨blockAddress, 0, 1⟩
private def field : CtorId := ⟨blockAddress, 0, 2⟩

private def schemas (world : Owned) (cid : CtorId) : Option CtorSchema :=
  if cid == leaf then some ⟨layout, #[]⟩
  else if cid == pair then some ⟨pairLayout, #[world, world]⟩
  else if cid == field then some ⟨fieldLayout, #[world]⟩
  else none

private def signature (world : Owned := .unique) : Signature := ⟨#[], world, false⟩
private def validation : Validate.Context := { schemas }

private def accepts (policy : CreditPolicy) (program : Program) : Bool :=
  (Validate.validateWithPolicy policy Validate.defaultLimits validation program).isOk

private def rejects (policy : CreditPolicy) (kind : Validate.Violation) (program : Program) : Bool :=
  match Validate.validateWithPolicy policy Validate.defaultLimits validation program with
  | .error (.invalid _ actual _) => actual == kind
  | _ => false

private def run (policy : CreditPolicy) (interpretation : Interpretation) (program : Program)
    (control : Nat := 3000) (heap : Nat := 2000) : Except Error Result :=
  Policy.runMain policy (Context.ofProgram program schemas) interpretation program control heap

private def laws (logical physical : Store) (credits : Nat) : Bool :=
  decide (CounterLaw logical.snapshot physical.snapshot credits) &&
    logical.peakLiveNodes == physical.peakLiveNodes &&
    physical.live + physical.heap.frees + credits == physical.heap.allocs

private def reclaimed (world : Owned) (result : Result) : Bool :=
  match reclaim world 2000 result.store result.value with
  | .ok (store, _) => store.live == 0 && store.heap.allocs == store.heap.frees
  | _ => false

private def trace : Nat → CreditPolicy → Context → Machine → Machine → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, policy, context, logical, physical =>
      laws logical.store physical.store physical.presentCredits &&
        match logical.control, physical.control with
        | .halted _, .halted _ => true
        | .running .., .running .. =>
            match Policy.step policy context .logical logical,
                Policy.step policy context .physical physical with
            | .ok left, .ok right => trace fuel policy context left right
            | _, _ => false
        | _, _ => false

private def traceMatches (policy : CreditPolicy) (program : Program) : Bool :=
  trace 3000 policy (Context.ofProgram program schemas)
    (initialMachine program.main #[] 2000) (initialMachine program.main #[] 2000)

private def leafAt (store : Store) (value : RVal) : Bool :=
  match value with
  | .loc location => match store.get? location with
    | some ⟨.unique, 1, .ctorN cid fields⟩ => cid == leaf && fields.isEmpty
    | _ => false
  | _ => false

private def pairResult (result : Result) : Bool :=
  match result.value with
  | .loc location => match result.store.get? location with
    | some ⟨.unique, 1, .ctorN cid #[left, right]⟩ =>
        cid == pair && left != right && leafAt result.store left && leafAt result.store right
    | _ => false
  | _ => false

private def fieldResult (world : Owned) (value : Nat) (result : Result) : Bool :=
  match result.value with
  | .loc location => match result.store.get? location with
    | some ⟨actualWorld, 1, .ctorN cid #[.lit (.nat actual)]⟩ =>
        actualWorld == world && cid == field && actual == value
    | _ => false
  | _ => false

/-! Two live reservations cross a back edge in reverse order. Nested callees
allocate while those slots remain owned by a suspended caller. -/

private def nested : Function :=
  { signature := signature
    blocks := #[
      { valueParams := #[], creditParams := #[]
        instructions := #[.alloc .unique leaf #[], .dropUnique (.reg 0)]
        terminator := .ret (.lit (.nat 17)) }] }

private def helper : Function :=
  { signature := signature
    blocks := #[
      { valueParams := #[], creditParams := #[]
        instructions := #[.alloc .unique leaf #[], .dropUnique (.reg 0), .call nestedAddress #[]]
        terminator := .ret (.reg 1) }] }

private def pairedLoop (iterations : Nat) (calls : Bool) : Program :=
  { declarations := [(helperAddress, .fn helper), (nestedAddress, .fn nested)]
    main :=
      { signature := signature
        blocks := #[
          { valueParams := #[], creditParams := #[]
            instructions := #[.alloc .unique leaf #[], .alloc .unique leaf #[],
              .takeUnique (.reg 0) leaf, .takeUnique (.reg 1) leaf]
            terminator := .jump { target := 1, values := #[.lit (.nat iterations)], credits := #[0, 1] } },
          { valueParams := #[.scalar], creditParams := #[.required layout, .required layout]
            instructions := #[]
            terminator := .switchValue (.reg 0) #[] (some
              { zero := { target := 3, values := #[], credits := #[0, 1] }
                succ := { target := 2, values := #[], credits := #[0, 1] } }) },
          { valueParams := #[.scalar], creditParams := #[.required layout, .required layout]
            instructions := if calls then #[.call helperAddress #[], .dropUnique (.reg 1)] else #[]
            terminator := .jump { target := 1, values := #[.reg 0], credits := #[1, 0] } },
          { valueParams := #[], creditParams := #[.required layout, .required layout]
            instructions := #[.allocWith 0 .unique leaf #[], .allocWith 1 .unique leaf #[],
              .alloc .unique pair #[.reg 0, .reg 1]]
            terminator := .ret (.reg 2) }] } }

private def pairedCheck (policy : CreditPolicy) (iterations : Nat) (calls : Bool) : Bool :=
  let program := pairedLoop iterations calls
  accepts policy program && traceMatches policy program &&
    match run policy .logical program, run policy .physical program 3100 2100 with
    | .ok logical, .ok physical =>
        let extra := if calls then 2 * iterations else 0
        pairResult logical && pairResult physical && laws logical.store physical.store 0 &&
          logical.store.heap.allocs == 5 + extra && logical.store.heap.frees == 2 + extra &&
          physical.store.heap.allocs == 3 + extra && physical.store.heap.frees == extra &&
          physical.store.heap.reuses == 2 && physical.store.heap.rcops == 0 &&
          physical.store.peakLiveNodes == 3 && reclaimed .unique logical && reclaimed .unique physical
    | _, _ => false

#guard [0, 1, 2, 3, 16, 64].all fun count =>
  pairedCheck .callLocalV0 count false && pairedCheck .suspendedCallsV1 count false &&
    pairedCheck .suspendedCallsV1 count true
#guard rejects .callLocalV0 .credit (pairedLoop 2 true)

private def advance (policy : CreditPolicy) (program : Program) (interpretation : Interpretation)
    (count : Nat) : Except Error Machine :=
  count.fold (fun _ _ state => state.bind (Policy.step policy (Context.ofProgram program schemas) interpretation))
    (.ok (initialMachine program.main #[] 2000))

/-! At step 11 the nested callee is active, with two caller reservations and
two continuation frames. Fresh allocation uses the next slot after both
reservations; it cannot occupy either one. -/
#guard match advance .suspendedCallsV1 (pairedLoop 1 true) .logical 11,
    advance .suspendedCallsV1 (pairedLoop 1 true) .physical 11 with
  | .ok logical, .ok physical =>
      physical.presentCredits == 2 && physical.reservations == [0, 1] &&
        (match physical.store.heap.nodes[0]? with | some none => true | _ => false) &&
        (match physical.store.heap.nodes[1]? with | some none => true | _ => false) &&
        physical.store.heap.nodes.size == 4 && physical.store.live == 1 &&
        laws logical.store physical.store 2 &&
        match physical.control with
        | .running _ stack => stack.length == 2
        | _ => false
  | _, _ => false

/-! Required unique, present optional shared, and absent optional shared
credits coexist. The cold reset's old shared alias survives until released. -/

private def mixed : Program :=
  { declarations := []
    main :=
      { signature := signature
        blocks := #[
          { valueParams := #[], creditParams := #[]
            instructions := #[
              .alloc .unique field #[.lit (.nat 11)],
              .alloc .shared field #[.lit (.nat 22)],
              .alloc .shared field #[.lit (.nat 33)], .retainShared (.reg 2),
              .takeUnique (.reg 0) field, .resetShared (.reg 1) field, .resetShared (.reg 2) field,
              .allocWith 0 .unique field #[.reg 4], .allocWith 1 .shared field #[.reg 5],
              .allocWith 2 .shared field #[.reg 6],
              .releaseShared (.reg 3), .releaseShared (.reg 8), .releaseShared (.reg 9)]
            terminator := .ret (.reg 7) }] } }

private def mixedCheck (policy : CreditPolicy) : Bool :=
  accepts policy mixed && traceMatches policy mixed &&
    match run policy .logical mixed, run policy .physical mixed 3100 2100 with
    | .ok logical, .ok physical =>
        fieldResult .unique 11 logical && fieldResult .unique 11 physical &&
          laws logical.store physical.store 0 &&
          logical.store.heap.allocs == 6 && logical.store.heap.frees == 5 &&
          physical.store.heap.allocs == 4 && physical.store.heap.frees == 3 &&
          physical.store.heap.reuses == 2 && physical.store.heap.rcops == 5 &&
          physical.store.resetAttempts == 2 && physical.store.hotResets == 1 &&
          physical.store.coldResets == 1 && physical.store.reusedPayloadUnits == 2 &&
          physical.store.peakLiveNodes == 4 && reclaimed .unique logical && reclaimed .unique physical
    | _, _ => false

#guard mixedCheck .callLocalV0 && mixedCheck .suspendedCallsV1
#guard match advance .suspendedCallsV1 mixed .logical 7, advance .suspendedCallsV1 mixed .physical 7 with
  | .ok logical, .ok physical =>
      laws logical.store physical.store 2 && physical.presentCredits == 2 &&
        match physical.control with
        | .running frame [] => frame.credits.size == 3 &&
            frame.credits[2]? == some (some { layout := fieldLayout, presence := .absent })
        | _ => false
  | _, _ => false

/-! Both optional-credit branches reach the same join. One slot is reused,
while another present or absent credit is explicitly discarded. -/

private def diamond (cold : Bool) : Program :=
  { declarations := []
    main :=
      { signature := signature .shared
        blocks := #[
          { valueParams := #[], creditParams := #[]
            instructions := #[.alloc .shared field #[.lit (.nat 41)]] ++
              (if cold then #[.retainShared (.reg 0)] else #[]) ++
              #[.resetShared (.reg 0) field]
            terminator := .branchCredit 0
              { target := 1, values := if cold then #[.reg 1, .reg 2] else #[.lit (.nat 0), .reg 1], credits := #[0] }
              { target := 2, values := if cold then #[.reg 1, .reg 2] else #[.lit (.nat 0), .reg 1], credits := #[0] } },
          { valueParams := #[.owned .shared, .owned .shared], creditParams := #[.required fieldLayout]
            instructions := #[]
            terminator := .jump { target := 3, values := #[.reg 0, .reg 1], credits := #[0] } },
          { valueParams := #[.owned .shared, .owned .shared], creditParams := #[.optional fieldLayout]
            instructions := #[]
            terminator := .jump { target := 3, values := #[.reg 0, .reg 1], credits := #[0] } },
          { valueParams := #[.owned .shared, .owned .shared], creditParams := #[.optional fieldLayout]
            instructions := #[.allocWith 0 .shared field #[.reg 1], .releaseShared (.reg 0),
              .alloc .shared leaf #[]] ++
              (if cold then #[.retainShared (.reg 3)] else #[]) ++
              #[.resetShared (.reg 3) leaf, .discardCredit 1] ++
              (if cold then #[.releaseShared (.reg 4)] else #[])
            terminator := .ret (.reg 2) }] } }

#guard [CreditPolicy.callLocalV0, .suspendedCallsV1].all fun policy =>
  [false, true].all fun cold =>
    let program := diamond cold
    accepts policy program && traceMatches policy program &&
      match run policy .logical program, run policy .physical program with
      | .ok logical, .ok physical =>
          fieldResult .shared 41 logical && fieldResult .shared 41 physical &&
            laws logical.store physical.store 0 && physical.store.heap.reuses == (if cold then 0 else 1) &&
            reclaimed .shared logical && reclaimed .shared physical
      | _, _ => false

/-! A borrowed parameter is read while the caller retains its owner and a
separate reservation. The caller subsequently reuses that reservation. -/

private def borrowed : Function :=
  { signature := ⟨#[⟨.unique, .borrowed⟩], .unique, false⟩
    blocks := #[
      { valueParams := #[.borrowed .unique .caller], creditParams := #[]
        instructions := #[.fetch (.reg 0) field 0]
        terminator := .ret (.lit (.nat 17)) }] }

private def borrowCall : Program :=
  { declarations := [(helperAddress, .fn borrowed)]
    main :=
      { signature := signature
        blocks := #[
          { valueParams := #[], creditParams := #[]
            instructions := #[.alloc .unique field #[.lit (.nat 51)], .alloc .unique leaf #[],
              .takeUnique (.reg 1) leaf, .call helperAddress #[.reg 0], .dropUnique (.reg 2),
              .allocWith 0 .unique leaf #[], .dropUnique (.reg 3)]
            terminator := .ret (.reg 0) }] } }

#guard accepts .suspendedCallsV1 borrowCall && traceMatches .suspendedCallsV1 borrowCall
#guard rejects .callLocalV0 .credit borrowCall
#guard match run .suspendedCallsV1 .logical borrowCall, run .suspendedCallsV1 .physical borrowCall with
  | .ok logical, .ok physical =>
      fieldResult .unique 51 logical && fieldResult .unique 51 physical &&
        physical.store.heap.rcops == 0 && physical.store.heap.reuses == 1 &&
        reclaimed .unique logical && reclaimed .unique physical
  | _, _ => false

/-! Malformed artifacts keep their existing rejection boundary. -/

private def replaceBlock (program : Program) (id : Nat) (update : Block → Block) : Program :=
  { program with main := { program.main with blocks := program.main.blocks.modify id update } }

#guard rejects .suspendedCallsV1 .credit (replaceBlock (pairedLoop 1 false) 2 fun block =>
  { block with terminator := .jump { target := 1, values := #[.reg 0], credits := #[0, 0] } })
#guard rejects .suspendedCallsV1 .credit (replaceBlock (pairedLoop 1 false) 3 fun block =>
  { block with
    instructions := #[.allocWith 0 .unique field #[.lit (.nat 0)], .discardCredit 1]
    terminator := .ret (.reg 0) })
#guard rejects .suspendedCallsV1 .credit (replaceBlock (pairedLoop 1 false) 3 fun block =>
  { block with
    instructions := #[.discardCredit 0, .discardCredit 0, .discardCredit 1]
    terminator := .ret (.lit (.nat 0)) })
#guard rejects .suspendedCallsV1 .resources (replaceBlock (pairedLoop 1 false) 3 fun block =>
  { block with instructions := #[], terminator := .ret (.lit (.nat 0)) })
#guard rejects .suspendedCallsV1 .credit (replaceBlock (pairedLoop 1 true) 2 fun block =>
  { block with instructions := #[], terminator := .tailCall helperAddress #[] })
#guard [Instr.papp helperAddress #[], .apply .erased #[], .extern helperAddress #[]].all fun instruction =>
  rejects .suspendedCallsV1 .credit (replaceBlock (pairedLoop 1 true) 2 fun block =>
    { block with instructions := #[instruction] })
#guard rejects .suspendedCallsV1 .borrow (replaceBlock borrowCall 0 fun block =>
  { block with
    instructions := #[.alloc .unique field #[.lit (.nat 51)], .fetch (.reg 0) field 0,
      .dropUnique (.reg 0)]
    terminator := .ret (.reg 1) })

/-! Runner fuel is a budget, not a claim of divergence or semantic failure. -/
#guard match run .suspendedCallsV1 .logical (pairedLoop 1 true) 0 100 with
  | .error .controlFuel => true
  | _ => false
#guard match run .suspendedCallsV1 .physical (pairedLoop 1 true) 100 0 with
  | .error .heapFuel => true
  | _ => false

end Ix.Compiler.IxIR2.CreditRefinement.Examples
