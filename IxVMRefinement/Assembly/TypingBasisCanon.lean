import IxVMRefinement.Assembly.TypingBasisLoads
import IxVMRefinement.StatementRel.LoadedReadsCanonRec
import IxVMRefinement.StatementRel.LoadedReadsCanonCtor
import IxVMRefinement.StatementRel.LoadedReadsCanonInd
import IxVMRefinement.StatementRel.LoadedReadsCanonQuot

/-! # The pins reload: the load facts at the stored keys of the basis

Every load at a stored key of the environment of the pins returns a constant that represents
the pin stored there, for every store of the basis records: the reload theorems of
`LoadedReadsCanon*` (`reloadsAs_ind`, `reloadsAs_ctor`, `reloadsAs_recr`, `reloadsAs_axio`)
give it for the canonical annotated constant of each record, and the canonical constant is
the pin, by evaluation.

* `canonAnnC`: `LoadedReads.canonAnn` with the binder tree computed (`buildTree`, which
  `Ingress.BinderTreeBuilt` accepts: `buildTree_built`) and the binder plan by structural
  recursion with fuel (`needsF`, `planStepF`, `rootPlanF`; the originals are well-founded and
  do not evaluate in the kernel), so that it evaluates; every value it returns is the
  original's (`canonAnn_of_C`, `canonRules_of_C`, `canonRec_of_C`).
* `indReload?`, `ctorReload?`, `recReload?`, `axioReload?`: proof-returning checks of one row.
  Each reads the record's expressions with the row reader, checks well-scopedness, computes the
  canonical constant and compares it with the pin; on success it returns the reload of the pin
  for every store of the basis records (`PinReload`).
* A recursor's pin differs from its canonical constant in the rule fields the install computes
  (`fire`, the rescue bits); the loaded value constrains only each rule's field count and
  right-hand side, and the K bit and constructor parameters of a K rule
  (`Core.CIRep.recr`), so the reload transfers (`reloadsAs_recr_transfer`).
* `basis_rowReloads`: every row that is not a block and not a quotient record passes
  (evaluated). `basis_reloads`: the pin of every basis role other than the four quotient roles
  reloads.
* `basis_getCI_of_quot`: the `getCI` field of the load contract at the environment of the pins,
  given the reload of the four quotient pins (for which no reload theorem exists: the
  quotient arm of `Ingress::get_ci` has no traced conversion).
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.TableInhabit (basisEnv)
open Ix.Kernel (ConstantInfo ConstantVal RecRule Key Role)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## A computable binder tree -/

/-- Adjacent pairing of binder-tree entries, by structural recursion with the pending first
element of a pair. -/
def pairsAux : Option Ingress.BinderTreeEntryData → List Ingress.BinderTreeEntryData →
    List Ingress.BinderTreeEntryData
  | none, [] => []
  | some e, [] => [e]
  | none, e :: rest => pairsAux (some e) rest
  | some f, s :: rest => (f.1, .node s.1 f.2 s.2) :: pairsAux none rest

theorem pairsAux_eq : ∀ es : List Ingress.BinderTreeEntryData,
    pairsAux none es = Ingress.binderPairsData es
  | [] => by simp [pairsAux, Ingress.binderPairsData]
  | [_] => by simp [pairsAux, Ingress.binderPairsData]
  | _ :: _ :: rest => by
    simp only [pairsAux, Ingress.binderPairsData, pairsAux_eq rest]

theorem pairsAux_length : ∀ es : List Ingress.BinderTreeEntryData,
    (pairsAux none es).length = (es.length + 1) / 2
  | [] => by simp [pairsAux]
  | [_] => by simp [pairsAux]
  | _ :: _ :: rest => by
    simp only [pairsAux, List.length_cons, pairsAux_length rest]
    omega

/-- The binder tree of a list of entries by repeated adjacent pairing, with fuel. -/
def buildTree (n : Nat) (es : List Ingress.BinderTreeEntryData) : Ingress.BinderTreeData :=
  match es with
  | [] => .empty
  | [e] => e.2
  | e₁ :: e₂ :: rest =>
    match n with
    | 0 => .empty
    | n + 1 => buildTree n (pairsAux none (e₁ :: e₂ :: rest))

theorem buildTree_built : ∀ (n : Nat) (es : List Ingress.BinderTreeEntryData), es.length ≤ n + 1 →
    Ingress.BinderTreeBuilt es (buildTree n es)
  | _, [], _ => by
    unfold buildTree
    exact .empty
  | _, [e], _ => by
    unfold buildTree
    exact .single e
  | 0, _ :: _ :: _, h => by
    simp only [List.length_cons] at h
    omega
  | n + 1, e₁ :: e₂ :: rest, h => by
    unfold buildTree
    refine .pair ?_
    rw [← pairsAux_eq]
    refine buildTree_built n _ ?_
    rw [pairsAux_length]
    simp only [List.length_cons] at h ⊢
    omega

/-- The binder tree of a record's binder blocks, computed. -/
def treeOf (c : Ixon.Constant) : Ingress.BinderTreeData :=
  buildTree (Ingress.binderLeavesData c.binders.toList).length (Ingress.binderLeavesData c.binders.toList)

theorem treeOf_built (c : Ixon.Constant) :
    Ingress.BinderTreeBuilt (Ingress.binderLeavesData c.binders.toList) (treeOf c) :=
  buildTree_built _ _ (Nat.le_succ _)

/-! ## The binder plan with fuel

`Ingress.needsBinderAt` and `Ingress.binderPlanStep` are defined by well-founded recursion, which the
kernel does not evaluate. `needsF` and `planStepF` compute the same by structural recursion on
a fuel argument, and return `none` when the fuel runs out or at a node kind no basis record
has (`prj`, `letE`); every `some` they return is the original function's
(`needsF_sound`, `planStepF_sound`, `rootPlanF_sound`). -/

def needsF : Nat → List Ixon.Expr → Nat → Ixon.Expr → Option Bool
  | 0, _, _, _ => none
  | _ + 1, _, _, .lam _ _ => some true
  | _ + 1, _, _, .all _ _ => some true
  | fuel + 1, sharing, bound, .app func arg =>
    (needsF fuel sharing bound func).bind fun a =>
      (needsF fuel sharing bound arg).map fun b => a || b
  | fuel + 1, sharing, bound, .share index =>
    if index.toNat < bound then
      match sharing[index.toNat]? with
      | some entry => needsF fuel sharing index.toNat entry
      | none => some false
    else some false
  | _ + 1, _, _, .prj _ _ _ => none
  | _ + 1, _, _, .letE _ _ _ _ _ => none
  | _ + 1, _, _, .sort _ => some false
  | _ + 1, _, _, .var _ => some false
  | _ + 1, _, _, .ref _ _ => some false
  | _ + 1, _, _, .recur _ _ => some false
  | _ + 1, _, _, .str _ => some false
  | _ + 1, _, _, .nat _ => some false

theorem needsF_sound : ∀ (fuel : Nat) (sharing : List Ixon.Expr) (bound : Nat)
    (expr : Ixon.Expr) (v : Bool), needsF fuel sharing bound expr = some v →
      Ingress.needsBinderAt sharing bound expr = v
  | 0, _, _, _, _, h => by simp [needsF] at h
  | _ + 1, _, _, .lam _ _, v, h => by
    simp only [needsF, Option.some.injEq] at h
    subst h
    simp [Ingress.needsBinderAt]
  | _ + 1, _, _, .all _ _, v, h => by
    simp only [needsF, Option.some.injEq] at h
    subst h
    simp [Ingress.needsBinderAt]
  | fuel + 1, sharing, bound, .app func arg, v, h => by
    simp only [needsF] at h
    cases h1 : needsF fuel sharing bound func with
    | none => simp [h1] at h
    | some a =>
      cases h2 : needsF fuel sharing bound arg with
      | none => simp [h1, h2] at h
      | some b =>
        simp only [h1, h2, Option.bind, Option.map, Option.some.injEq] at h
        subst h
        simp only [Ingress.needsBinderAt, needsF_sound fuel _ _ _ _ h1, needsF_sound fuel _ _ _ _ h2]
  | fuel + 1, sharing, bound, .share index, v, h => by
    simp only [needsF] at h
    by_cases hidx : index.toNat < bound
    · simp only [hidx, ↓reduceIte] at h
      cases hb : sharing[index.toNat]? with
      | none =>
        simp only [hb, Option.some.injEq] at h
        subst h
        simp [Ingress.needsBinderAt, hidx, hb]
      | some entry =>
        simp only [hb] at h
        have e : Ingress.needsBinderAt sharing bound (.share index) =
            Ingress.needsBinderAt sharing index.toNat entry := by
          simp [Ingress.needsBinderAt, hidx, hb]
        rw [e]
        exact needsF_sound fuel _ _ _ _ h
    · simp only [hidx, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp [Ingress.needsBinderAt, hidx]
  | _ + 1, _, _, .prj _ _ _, _, h => by simp [needsF] at h
  | _ + 1, _, _, .letE _ _ _ _ _, _, h => by simp [needsF] at h
  | _ + 1, _, _, .sort _, v, h => by
    simp only [needsF, Option.some.injEq] at h
    subst h
    simp [Ingress.needsBinderAt]
  | _ + 1, _, _, .var _, v, h => by
    simp only [needsF, Option.some.injEq] at h
    subst h
    simp [Ingress.needsBinderAt]
  | _ + 1, _, _, .ref _ _, v, h => by
    simp only [needsF, Option.some.injEq] at h
    subst h
    simp [Ingress.needsBinderAt]
  | _ + 1, _, _, .recur _ _, v, h => by
    simp only [needsF, Option.some.injEq] at h
    subst h
    simp [Ingress.needsBinderAt]
  | _ + 1, _, _, .str _, v, h => by
    simp only [needsF, Option.some.injEq] at h
    subst h
    simp [Ingress.needsBinderAt]
  | _ + 1, _, _, .nat _, v, h => by
    simp only [needsF, Option.some.injEq] at h
    subst h
    simp [Ingress.needsBinderAt]

/-- A child's step, when it needs a binder plan. -/
def condF (needs : Option Bool) (step : Option (List Core.KLevel × List Ixon.BinderNode))
    (ns : List Ixon.BinderNode) : Option (List Core.KLevel × List Ixon.BinderNode) :=
  match needs with
  | some true => step
  | some false => some ([], ns)
  | none => none

theorem condF_sound {tree : Ingress.BinderTreeData} {sharing : List Ixon.Expr} {bound : Nat}
    {e : Ixon.Expr} {ns : List Ixon.BinderNode} {needs : Option Bool}
    {step : Option (List Core.KLevel × List Ixon.BinderNode)}
    {r : List Core.KLevel × List Ixon.BinderNode}
    (hn : ∀ v, needs = some v → Ingress.needsBinderAt sharing bound e = v)
    (hs : step = some r → Ingress.binderPlanStep tree sharing bound e ns = some r)
    (h : condF needs step ns = some r) :
    (if Ingress.needsBinderAt sharing bound e then Ingress.binderPlanStep tree sharing bound e ns
      else some ([], ns)) = some r := by
  cases needs with
  | none => simp [condF] at h
  | some v =>
    rw [hn v rfl]
    cases v with
    | true =>
      simp only [condF] at h
      simpa using hs h
    | false =>
      simp only [condF] at h
      simpa using h

def planStepF : Nat → Ingress.BinderTreeData → List Ixon.Expr → Nat → Ixon.Expr →
    List Ixon.BinderNode → Option (List Core.KLevel × List Ixon.BinderNode)
  | 0, _, _, _, _, _ => none
  | fuel + 1, tree, sharing, bound, .lam dom body, node :: rest =>
    (condF (needsF fuel sharing bound dom) (planStepF fuel tree sharing bound dom rest) rest).bind
      fun p => (condF (needsF fuel sharing bound body) (planStepF fuel tree sharing bound body p.2)
        p.2).bind fun q => some (Ingress.binderLevel node :: (p.1 ++ q.1), q.2)
  | fuel + 1, tree, sharing, bound, .all dom body, node :: rest =>
    (condF (needsF fuel sharing bound dom) (planStepF fuel tree sharing bound dom rest) rest).bind
      fun p => (condF (needsF fuel sharing bound body) (planStepF fuel tree sharing bound body p.2)
        p.2).bind fun q => some (Ingress.binderLevel node :: (p.1 ++ q.1), q.2)
  | fuel + 1, tree, sharing, bound, .app func arg, nodes =>
    (condF (needsF fuel sharing bound func) (planStepF fuel tree sharing bound func nodes)
      nodes).bind fun p => (condF (needsF fuel sharing bound arg)
        (planStepF fuel tree sharing bound arg p.2) p.2).bind fun q => some (p.1 ++ q.1, q.2)
  | fuel + 1, tree, sharing, bound, .share index, .share variant :: rest =>
    if index.toNat < bound then
      (sharing[index.toNat]?).bind fun body =>
        (tree.lookup (1, (index.toNat : F), (variant.toNat : F))).bind fun entryNodes =>
          match planStepF fuel tree sharing index.toNat body entryNodes with
          | some (plan, []) => some (plan, rest)
          | _ => none
    else none
  | _ + 1, _, _, _, _, _ => none

theorem planStepF_sound : ∀ (fuel : Nat) (tree : Ingress.BinderTreeData) (sharing : List Ixon.Expr)
    (bound : Nat) (expr : Ixon.Expr) (nodes : List Ixon.BinderNode)
    (r : List Core.KLevel × List Ixon.BinderNode),
    planStepF fuel tree sharing bound expr nodes = some r →
      Ingress.binderPlanStep tree sharing bound expr nodes = some r := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ h; simp [planStepF] at h
  | succ fuel ih =>
    intro tree sharing bound expr nodes r h
    have hc : ∀ (e : Ixon.Expr) (ns : List Ixon.BinderNode)
        (q : List Core.KLevel × List Ixon.BinderNode),
        condF (needsF fuel sharing bound e) (planStepF fuel tree sharing bound e ns) ns = some q →
        (if Ingress.needsBinderAt sharing bound e then Ingress.binderPlanStep tree sharing bound e ns
          else some ([], ns)) = some q :=
      fun e ns q hq => condF_sound (fun v hv => needsF_sound fuel _ _ _ _ hv)
        (ih tree sharing bound e ns q) hq
    match expr, nodes, h with
    | .lam dom body, node :: rest, h =>
      cases h1 : condF (needsF fuel sharing bound dom) (planStepF fuel tree sharing bound dom rest)
          rest with
      | none =>
        have h' : planStepF (fuel + 1) tree sharing bound (.lam dom body) (node :: rest) = none := by
          simp only [planStepF, h1, Option.bind]
        rw [h'] at h
        cases h
      | some p =>
        obtain ⟨domPlan, middle⟩ := p
        cases h2 : condF (needsF fuel sharing bound body)
            (planStepF fuel tree sharing bound body middle) middle with
        | none =>
          have h' : planStepF (fuel + 1) tree sharing bound (.lam dom body) (node :: rest) = none := by
            simp only [planStepF, h1, h2, Option.bind]
          rw [h'] at h
          cases h
        | some q =>
          obtain ⟨bodyPlan, after⟩ := q
          have h' : planStepF (fuel + 1) tree sharing bound (.lam dom body) (node :: rest) =
              some (Ingress.binderLevel node :: (domPlan ++ bodyPlan), after) := by
            simp only [planStepF, h1, h2, Option.bind]
          rw [h'] at h
          cases h
          exact Ingress.binderPlanStep_lam (hc _ _ _ h1) (hc _ _ _ h2)
    | .all dom body, node :: rest, h =>
      cases h1 : condF (needsF fuel sharing bound dom) (planStepF fuel tree sharing bound dom rest)
          rest with
      | none =>
        have h' : planStepF (fuel + 1) tree sharing bound (.all dom body) (node :: rest) = none := by
          simp only [planStepF, h1, Option.bind]
        rw [h'] at h
        cases h
      | some p =>
        obtain ⟨domPlan, middle⟩ := p
        cases h2 : condF (needsF fuel sharing bound body)
            (planStepF fuel tree sharing bound body middle) middle with
        | none =>
          have h' : planStepF (fuel + 1) tree sharing bound (.all dom body) (node :: rest) = none := by
            simp only [planStepF, h1, h2, Option.bind]
          rw [h'] at h
          cases h
        | some q =>
          obtain ⟨bodyPlan, after⟩ := q
          have h' : planStepF (fuel + 1) tree sharing bound (.all dom body) (node :: rest) =
              some (Ingress.binderLevel node :: (domPlan ++ bodyPlan), after) := by
            simp only [planStepF, h1, h2, Option.bind]
          rw [h'] at h
          cases h
          exact Ingress.binderPlanStep_all (hc _ _ _ h1) (hc _ _ _ h2)
    | .app func arg, nodes, h =>
      cases h1 : condF (needsF fuel sharing bound func) (planStepF fuel tree sharing bound func nodes)
          nodes with
      | none =>
        have h' : planStepF (fuel + 1) tree sharing bound (.app func arg) nodes = none := by
          simp only [planStepF, h1, Option.bind]
        rw [h'] at h
        cases h
      | some p =>
        obtain ⟨funcPlan, middle⟩ := p
        cases h2 : condF (needsF fuel sharing bound arg)
            (planStepF fuel tree sharing bound arg middle) middle with
        | none =>
          have h' : planStepF (fuel + 1) tree sharing bound (.app func arg) nodes = none := by
            simp only [planStepF, h1, h2, Option.bind]
          rw [h'] at h
          cases h
        | some q =>
          obtain ⟨argPlan, after⟩ := q
          have h' : planStepF (fuel + 1) tree sharing bound (.app func arg) nodes =
              some (funcPlan ++ argPlan, after) := by
            simp only [planStepF, h1, h2, Option.bind]
          rw [h'] at h
          cases h
          exact Ingress.binderPlanStep_app (hc _ _ _ h1) (hc _ _ _ h2)
    | .share index, .share variant :: rest, h =>
      by_cases hidx : index.toNat < bound
      · cases hb : sharing[index.toNat]? with
        | none =>
          have h' : planStepF (fuel + 1) tree sharing bound (.share index)
              (.share variant :: rest) = none := by
            simp only [planStepF, hidx, ↓reduceIte, hb, Option.bind]
          rw [h'] at h
          cases h
        | some body =>
          cases hl : tree.lookup (1, (index.toNat : F), (variant.toNat : F)) with
          | none =>
            have h' : planStepF (fuel + 1) tree sharing bound (.share index)
                (.share variant :: rest) = none := by
              simp only [planStepF, hidx, ↓reduceIte, hb, hl, Option.bind]
            rw [h'] at h
            cases h
          | some entryNodes =>
            cases hp : planStepF fuel tree sharing index.toNat body entryNodes with
            | none =>
              have h' : planStepF (fuel + 1) tree sharing bound (.share index)
                  (.share variant :: rest) = none := by
                simp only [planStepF, hidx, ↓reduceIte, hb, hl, hp, Option.bind]
              rw [h'] at h
              cases h
            | some pr =>
              obtain ⟨plan, after⟩ := pr
              cases after with
              | cons _ _ =>
                have h' : planStepF (fuel + 1) tree sharing bound (.share index)
                    (.share variant :: rest) = none := by
                  simp only [planStepF, hidx, ↓reduceIte, hb, hl, hp, Option.bind]
                rw [h'] at h
                cases h
              | nil =>
                have h' : planStepF (fuel + 1) tree sharing bound (.share index)
                    (.share variant :: rest) = some (plan, rest) := by
                  simp only [planStepF, hidx, ↓reduceIte, hb, hl, hp, Option.bind]
                rw [h'] at h
                cases h
                have hrec := ih tree sharing index.toNat body entryNodes (plan, []) hp
                simp [Ingress.binderPlanStep, hidx, hb, hl, hrec]
      · have h' : planStepF (fuel + 1) tree sharing bound (.share index)
            (.share variant :: rest) = none := by
          simp only [planStepF, hidx, ↓reduceIte]
        rw [h'] at h
        cases h
    | .lam _ _, [], h => simp [planStepF] at h
    | .all _ _, [], h => simp [planStepF] at h
    | .share _, [], h => simp [planStepF] at h
    | .share _, .never _ :: _, h => simp [planStepF] at h
    | .share _, .zero _ :: _, h => simp [planStepF] at h
    | .share _, .ifAllZero _ _ :: _, h => simp [planStepF] at h
    | .share _, .undecided _ :: _, h => simp [planStepF] at h
    | .sort _, _, h => simp [planStepF] at h
    | .var _, _, h => simp [planStepF] at h
    | .ref _ _, _, h => simp [planStepF] at h
    | .recur _ _, _, h => simp [planStepF] at h
    | .prj _ _ _, _, h => simp [planStepF] at h
    | .str _, _, h => simp [planStepF] at h
    | .nat _, _, h => simp [planStepF] at h
    | .letE _ _ _ _ _, _, h => simp [planStepF] at h

/-- `Ingress.binderRootPlan` with fuel. -/
def rootPlanF (fuel : Nat) (tree : Ingress.BinderTreeData) (sharing : List Ixon.Expr) (root : F)
    (expr : Ixon.Expr) : Option (List Core.KLevel) :=
  match needsF fuel sharing 4294967295 expr with
  | some true =>
    (tree.lookup (0, root, 0)).bind fun nodes =>
      match planStepF fuel tree sharing 4294967295 expr nodes with
      | some (plan, []) => some plan
      | _ => none
  | some false => some []
  | none => none

theorem rootPlanF_sound {fuel : Nat} {tree : Ingress.BinderTreeData} {sharing : List Ixon.Expr}
    {root : F} {expr : Ixon.Expr} {plan : List Core.KLevel}
    (h : rootPlanF fuel tree sharing root expr = some plan) :
    Ingress.binderRootPlan tree sharing root expr = some plan := by
  unfold rootPlanF at h
  cases hn : needsF fuel sharing 4294967295 expr with
  | none => simp [hn] at h
  | some v =>
    have hv := needsF_sound fuel _ _ _ _ hn
    cases v with
    | false =>
      simp only [hn, Option.some.injEq] at h
      subst h
      simp [Ingress.binderRootPlan, hv]
    | true =>
      simp only [hn] at h
      cases hl : tree.lookup (0, root, 0) with
      | none => simp [hl] at h
      | some nodes =>
        simp only [hl, Option.bind] at h
        cases hp : planStepF fuel tree sharing 4294967295 expr nodes with
        | none => simp [hp] at h
        | some pr =>
          obtain ⟨pl, after⟩ := pr
          cases after with
          | cons _ _ => simp [hp] at h
          | nil =>
            simp only [hp, Option.some.injEq] at h
            subst h
            have hs := planStepF_sound fuel _ _ _ _ _ _ hp
            simp [Ingress.binderRootPlan, hv, hl, hs]

/-- The fuel the basis records need, with room. -/
def planFuel : Nat := 512

/-- `LoadedReads.canonAnn` with the computed binder tree and the plan with fuel. -/
def canonAnnC (src : Ixon.Constant) (ps : List Ix.Kernel.LevelParam) (root : F)
    (e : Ixon.Expr) (E_rd : Ix.Kernel.Expr .anon) : Option (Ix.Kernel.Expr .anon) :=
  (rootPlanF planFuel (treeOf src) src.sharing.toList root e).bind fun plan =>
    (Ingress.applyBinderTrace (fun level => Core.bmeta (Ingress.invPosLevel ps level)) E_rd plan).map
      Prod.fst

theorem canonAnn_of_C {src : Ixon.Constant} {ps : List Ix.Kernel.LevelParam} {root : F}
    {e : Ixon.Expr} {E_rd x : Ix.Kernel.Expr .anon} (h : canonAnnC src ps root e E_rd = some x) :
    LoadedReads.canonAnn src ps root e E_rd = some x := by
  unfold canonAnnC at h
  unfold LoadedReads.canonAnn
  rw [LoadedReads.canonTree_eq (treeOf_built src)]
  cases hp : rootPlanF planFuel (treeOf src) src.sharing.toList root e with
  | none => simp [hp] at h
  | some plan =>
    rw [hp] at h
    rw [rootPlanF_sound hp]
    exact h

/-- `LoadedReads.canonRules` with the computed binder tree. -/
def canonRulesC (src : Ixon.Constant) (ps : List Ix.Kernel.LevelParam) (kFlag : Bool)
    (cParams : Nat) : F → List Ixon.RecursorRule → List (RecRule .anon) →
      Option (List (RecRule .anon))
  | _, [], [] => some []
  | root, ru :: rus, rl :: rls =>
    (canonAnnC src ps root ru.rhs rl.rhs).bind fun rhs' =>
      (canonRulesC src ps kFlag cParams (root + 1) rus rls).map fun rest =>
        { rl with rhs := rhs', k := kFlag, ctorParams := cParams } :: rest
  | _, [], _ :: _ => none
  | _, _ :: _, [] => none

theorem canonRules_of_C (src : Ixon.Constant) (ps : List Ix.Kernel.LevelParam) (kFlag : Bool)
    (cParams : Nat) : ∀ (root : F) (rus : List Ixon.RecursorRule) (rls : List (RecRule .anon))
    (out : List (RecRule .anon)), canonRulesC src ps kFlag cParams root rus rls = some out →
      LoadedReads.canonRules src ps kFlag cParams root rus rls = some out
  | _, [], [], out, h => by simpa [canonRulesC, LoadedReads.canonRules] using h
  | root, ru :: rus, rl :: rls, out, h => by
    simp only [canonRulesC] at h
    cases ha : canonAnnC src ps root ru.rhs rl.rhs with
    | none => simp [ha] at h
    | some rhs' =>
      cases hr : canonRulesC src ps kFlag cParams (root + 1) rus rls with
      | none => simp [ha, hr] at h
      | some rest =>
        simp only [ha, hr, Option.bind, Option.map, Option.some.injEq] at h
        subst h
        simp [LoadedReads.canonRules, canonAnn_of_C ha,
          canonRules_of_C src ps kFlag cParams (root + 1) rus rls rest hr]
  | _, [], _ :: _, _, h => by simp [canonRulesC] at h
  | _, _ :: _, [], _, h => by simp [canonRulesC] at h

/-- `LoadedReads.canonRec` with the computed binder tree. -/
def canonRecC (key : Key .anon) (src : Ixon.Constant) (base : F) (rc : Ixon.Recursor)
    (ps : List Ix.Kernel.LevelParam) (ty₀ : Ix.Kernel.Expr .anon)
    (rules₀ : List (RecRule .anon)) : Option (ConstantInfo .anon) :=
  (canonAnnC src ps base rc.typ ty₀).bind fun ty' =>
    (canonRulesC src ps rc.k rc.params.toNat (base + 1) rc.rules.toList rules₀).map
      fun rules' => .recInfo ⟨key, ps, ty'⟩
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules'

theorem canonRec_of_C {key : Key .anon} {src : Ixon.Constant} {base : F} {rc : Ixon.Recursor}
    {ps : List Ix.Kernel.LevelParam} {ty₀ : Ix.Kernel.Expr .anon}
    {rules₀ : List (RecRule .anon)} {cn : ConstantInfo .anon}
    (h : canonRecC key src base rc ps ty₀ rules₀ = some cn) :
    LoadedReads.canonRec key src base rc ps ty₀ rules₀ = some cn := by
  unfold canonRecC at h
  cases ha : canonAnnC src ps base rc.typ ty₀ with
  | none => simp [ha] at h
  | some ty' =>
    cases hr : canonRulesC src ps rc.k rc.params.toNat (base + 1) rc.rules.toList rules₀ with
    | none => simp [ha, hr] at h
    | some rls =>
      simp only [ha, hr, Option.bind, Option.map, Option.some.injEq] at h
      subst h
      exact LoadedReads.canonRec_eq (canonAnn_of_C ha) (canonRules_of_C _ _ _ _ _ _ _ _ hr)

/-! ## A recursor's reload transfers across the install-computed rule fields -/

/-- What a loaded rule list fixes of a rule: its field count, its right-hand side, its K bit
and its constructor's parameter count. -/
def ruleData (r : RecRule .anon) : Nat × Ix.Kernel.Expr .anon × Bool × Nat :=
  (r.nfields, r.rhs, r.k, r.ctorParams)

theorem rulesRep_transfer {κ : _root_.Address → Core.KKey} {h : Heap F}
    {ps : List Ix.Kernel.LevelParam} {j : Nat} {p : SourceValue F} {rls : List (RecRule .anon)}
    (hr : Core.RulesRep κ h ps j p rls) :
    ∀ {rls' : List (RecRule .anon)}, rls'.map ruleData = rls.map ruleData →
      Core.RulesRep κ h ps j p rls' := by
  induction hr with
  | nil cell =>
    intro rls' he
    cases rls' with
    | nil => exact .nil cell
    | cons _ _ => simp at he
  | cons cell hr _ ih =>
    intro rls' he
    cases rls' with
    | nil => simp at he
    | cons rl' rest' =>
      simp only [List.map_cons, List.cons.injEq] at he
      obtain ⟨h1, h2⟩ := he
      simp only [ruleData, Prod.mk.injEq] at h1
      obtain ⟨hnf, hrhs, -, -⟩ := h1
      obtain ⟨rhs, hv, hlt, htm⟩ := hr
      exact .cons cell ⟨rhs, by rw [hnf]; exact hv, by rw [hnf]; exact hlt,
        by rw [hrhs]; exact htm⟩ (ih h2)

theorem ciRep_recr_transfer {κ : _root_.Address → Core.KKey} {h : Heap F} {v : SourceValue F}
    {cv : ConstantVal .anon} {mI rP : Nat} {rls rls' : List (RecRule .anon)}
    (hrep : Core.CIRep κ h v (.recInfo cv mI rP rls))
    (he : rls'.map ruleData = rls.map ruleData) :
    Core.CIRep κ h v (.recInfo cv mI rP rls') := by
  cases hrep with
  | quot hv hk =>
    refine .quot hv ?_
    rcases hk with ⟨hk, _, _, he'⟩ | ⟨hk, _, _, _, he'⟩ | ⟨hk, _, _, _, _, he'⟩ |
      ⟨hk, _, _, _, _, he'⟩
    · cases he'
    · cases he'
    · exact Or.inr (Or.inr (Or.inl ⟨hk, cv, mI, rP, rls', rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hk, cv, mI, rP, rls', rfl⟩))
  | recr hv hnp hni hnm hnmi hrP hmI hcounts hrules hk hkey =>
    refine .recr hv hnp hni hnm hnmi hrP hmI hcounts (rulesRep_transfer hrules he) ?_ hkey
    intro hk1
    obtain ⟨rl, hrl, hrlk, hrlp⟩ := hk hk1
    subst hrl
    cases rls' with
    | nil => simp at he
    | cons rl' rest =>
      simp only [List.map_cons, List.cons.injEq] at he
      obtain ⟨h1, hrest⟩ := he
      simp only [ruleData, Prod.mk.injEq] at h1
      obtain ⟨-, -, hk', hp'⟩ := h1
      have hnil : rest = [] := by
        cases rest with
        | nil => rfl
        | cons _ _ => simp at hrest
      subst hnil
      exact ⟨rl', rfl, hk'.trans hrlk, hp'.trans hrlp⟩

theorem reloadsAs_recr_transfer {E : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {env : Ix.Kernel.Env .anon} {cv : ConstantVal .anon} {mI rP : Nat}
    {rls rls' : List (RecRule .anon)} (h : Decl.ReloadsAs E t env (.recInfo cv mI rP rls))
    (he : rls'.map ruleData = rls.map ruleData) :
    Decl.ReloadsAs E t env (.recInfo cv mI rP rls') := by
  intro addr ptr h₁ h₂ cs a ev hg ha hk
  obtain ⟨v, hld, hrep⟩ := h addr ptr h₁ h₂ cs a ev hg ha hk
  exact ⟨v, hld, ciRep_recr_transfer hrep he⟩

/-! ## Facts about the rows -/

/-- The basis store, as a store of rows. -/
abbrev basisS : RowReader.RowStore ctab := BasisReads.basisRowStore

/-- **A row's record is what every store of the basis records holds at its address**, exact
decoding. -/
theorem recordOf_of_row {E : Ixon.Env} (hE : RecordsFor StoreInhabit.basisStore E)
    {a : _root_.Address} {c : Ixon.Constant} (h : (a, c) ∈ StoreInhabit.basisRows) :
    IxVM.Consistency.recordOf E a = some c := by
  have h1 : Ix.Cert.recordAt E a = some c := hE.2.1 a c (StoreInhabit.store_record_of_mem h)
  have h1' : (E.consts.get? a).bind (·.get?) = some c := h1
  unfold IxVM.Consistency.recordOf
  cases hg : E.consts.get? a with
  | none =>
    rw [hg] at h1'
    exact absurd h1' (by simp)
  | some lc =>
    rw [hg] at h1'
    have hlc : lc.get? = some c := h1'
    obtain ⟨c', hget, hex⟩ := hE.1 a lc hg
    rw [hlc] at hget
    have e : c = c' := Option.some.inj hget
    show (Ixon.deConstantExact lc.rawBytes).toOption = some c
    rw [hex, e]
    rfl

/-- Every reference a row uses has its key stored (decided). -/
theorem basis_refsStored :
    StoreInhabit.basisRows.all (fun e => (IxVM.Consistency.usedRefIdxs e.2).all fun i =>
      (e.2.refs.toList[i]?).all fun x => (basisEnv.find? (Core.keyOf ctab x)).isSome) = true := by
  decide +kernel

theorem row_usedRefs {a : _root_.Address} {c : Ixon.Constant}
    (h : (a, c) ∈ StoreInhabit.basisRows) : Decl.UsedRefsStored ctab basisEnv c := by
  intro i hi x hx
  have h1 := List.all_eq_true.mp basis_refsStored (a, c) h
  simp only [List.all_eq_true] at h1
  have h2 := h1 i hi
  rw [hx] at h2
  exact Option.isSome_iff_exists.mp h2

/-- The members of a block of the basis store are stored. -/
theorem row_blockStored {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hB : (B, cb) ∈ StoreInhabit.basisRows) (hms : cb.info = .muts ms) :
    LoadedReads.BlockStored ctab basisEnv B ms := by
  refine LoadedReads.blockStored_of_members fun k m hm => ?_
  have hp := RowReader.mem_expected hB hms hm _ List.mem_cons_self
  have hnm : StoreInhabit.isMutsInfo (IxVM.Consistency.memberProjection B k m).info = false := by
    cases m <;> rfl
  have h := proj_stored (x := IxVM.Consistency.memberAddr B k m) hp hnm rfl
  rw [← LoadedReads.keyOf_eq] at h
  exact Option.isSome_iff_exists.mp h

/-- A reading over the basis store's blobs is a reading over every store of the basis
records. -/
theorem read_mono {E : Ixon.Env} (hE : RecordsFor StoreInhabit.basisStore E)
    {src : Ixon.Constant} {param : Nat → Ix.Kernel.LevelParam}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Key .anon))} {e : Ixon.Expr}
    {v : Ix.Kernel.Expr .anon}
    (h : (Ix.Kernel.Reader.MemberReader.mk'
      (IxVM.Consistency.readCtx ctab (fun x => StoreInhabit.basisStore.blobs.get? x)) src param
        self).read e = .ok v) :
    (IxVM.Consistency.exprReader ctab (fun x => E.blobs.get? x) src param self).read e = .ok v :=
  ReaderReads.exprReader_mono hE.2.2.1 h

/-! ## The checks of one row -/

/-- **The reload of the pin at a row's key**, for every store of the basis records. -/
def PinReload (a : _root_.Address) : Prop :=
  ∀ E, RecordsFor StoreInhabit.basisStore E → ∀ pin,
    basisEnv.find? (Core.keyOf ctab a) = some pin → Decl.ReloadsAs E ctab basisEnv pin

/-- The check of an inductive type's projection row. -/
def indReload? (a : _root_.Address) (c : Ixon.Constant)
    (hrow : (a, c) ∈ StoreInhabit.basisRows) : Option (PLift (PinReload a)) :=
  match hinfo : c.info with
  | .iPrj p =>
    match hb : RowReader.blockOf StoreInhabit.basisRows p.block with
    | none => none
    | some eb =>
      match hms : eb.2.info with
      | .muts ms =>
        match hm : ms[p.idx.toNat]? with
        | some (.indc ind) =>
          match ExprReader.sharesCheck (RowReader.blockOracle basisS (RowReader.blockOf_mem hb) hms)
              eb.2.sharing.toList with
          | none => none
          | some sh =>
            match ExprReader.readCheck (RowReader.blockOracle basisS (RowReader.blockOf_mem hb) hms)
                sh ind.typ with
            | none => none
            | some ty =>
              if h1 : ty.1.looseBVarsBounded 0 = true ∧
                  ty.1.allLevelParamsDefined (List.range ind.lvls.toNat) = true then
                match hp : basisEnv.find? (Core.keyOf ctab a) with
                | some (ConstantInfo.indInfo cv caps) =>
                  if h3 : canonAnnC eb.2 (List.range ind.lvls.toNat)
                      ((Ingress.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) ind.typ ty.1 =
                        some cv.type ∧
                      cv = ⟨Core.keyOf ctab a, List.range ind.lvls.toNat, cv.type⟩ then
                    some ⟨fun E hE pin hpin => by
                      rw [hp] at hpin
                      cases hpin
                      have e : (⟨IxVM.Consistency.keyOf ctab a, List.range ind.lvls.toNat,
                          cv.type⟩ : ConstantVal .anon) = cv := h3.2.symm
                      have hcn : LoadedReads.canonInd (IxVM.Consistency.keyOf ctab a) eb.2
                          ((Ingress.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) ind ty.1 caps =
                            some (.indInfo cv caps) := by
                        rw [LoadedReads.canonInd_eq (canonAnn_of_C h3.1), e]
                      exact LoadedReads.reloadsAs_ind RoleVal.committedDefaultRoleTable_check
                        (recordOf_of_row hE hrow) hinfo
                        (recordOf_of_row hE (RowReader.blockOf_mem hb)) hms hm
                        (read_mono hE ty.2) h1.1 h1.2 (row_usedRefs (RowReader.blockOf_mem hb))
                        (row_blockStored (RowReader.blockOf_mem hb) hms) hcn⟩
                  else none
                | _ => none
              else none
        | _ => none
      | _ => none
  | _ => none

/-- The check of a constructor's projection row. -/
def ctorReload? (a : _root_.Address) (c : Ixon.Constant)
    (hrow : (a, c) ∈ StoreInhabit.basisRows) : Option (PLift (PinReload a)) :=
  match hinfo : c.info with
  | .cPrj p =>
    match hb : RowReader.blockOf StoreInhabit.basisRows p.block with
    | none => none
    | some eb =>
      match hms : eb.2.info with
      | .muts ms =>
        match hm : ms[p.idx.toNat]? with
        | some (.indc ind) =>
          match hct : ind.ctors[p.cidx.toNat]? with
          | none => none
          | some ct =>
            if hcx : ct.cidx.toNat = p.cidx.toNat then
              match ExprReader.sharesCheck (RowReader.blockOracle basisS (RowReader.blockOf_mem hb) hms)
                  eb.2.sharing.toList with
              | none => none
              | some sh =>
                match ExprReader.readCheck (RowReader.blockOracle basisS (RowReader.blockOf_mem hb) hms)
                    sh ct.typ with
                | none => none
                | some ty =>
                  if h1 : ty.1.looseBVarsBounded 0 = true ∧
                      ty.1.allLevelParamsDefined (List.range ct.lvls.toNat) = true then
                    match hp : basisEnv.find? (Core.keyOf ctab a) with
                    | some (ConstantInfo.ctorInfo cv nP nF) =>
                      if h3 : canonAnnC eb.2 (List.range ct.lvls.toNat)
                          (((Ingress.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) + 1 +
                            ((p.cidx.toNat : Nat) : F)) ct.typ ty.1 = some cv.type ∧
                          cv = ⟨Core.keyOf ctab a, List.range ct.lvls.toNat, cv.type⟩ ∧
                          nP = ct.params.toNat ∧ nF = ct.fields.toNat then
                        some ⟨fun E hE pin hpin => by
                          rw [hp] at hpin
                          cases hpin
                          obtain ⟨hT, hcv, hnP, hnF⟩ := h3
                          have e : (⟨IxVM.Consistency.keyOf ctab a, List.range ct.lvls.toNat,
                              cv.type⟩ : ConstantVal .anon) = cv := hcv.symm
                          have hcn : LoadedReads.canonCtor (IxVM.Consistency.keyOf ctab a) eb.2
                              (((Ingress.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) + 1 +
                                ((p.cidx.toNat : Nat) : F)) ct ty.1 =
                                some (.ctorInfo cv nP nF) := by
                            rw [LoadedReads.canonCtor_eq (canonAnn_of_C hT), e,
                              hnP, hnF]
                          exact LoadedReads.reloadsAs_ctor RoleVal.committedDefaultRoleTable_check
                            (recordOf_of_row hE hrow) hinfo
                            (recordOf_of_row hE (RowReader.blockOf_mem hb)) hms hm hct hcx
                            (read_mono hE ty.2) h1.1 h1.2
                            (row_usedRefs (RowReader.blockOf_mem hb))
                            (row_blockStored (RowReader.blockOf_mem hb) hms) ⟨_, hp⟩ hcn⟩
                      else none
                    | _ => none
                  else none
            else none
        | _ => none
      | _ => none
  | _ => none

/-- The rules of a recursor record read one for one, with the proof. The constructor key of
each rule is a placeholder: the reload reads only the field count and the right-hand side. -/
def rulesRead {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {param : Nat → Ix.Kernel.LevelParam}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Key .anon))}
    (o : ExprReader.Oracle
      (⟨cx, src, src.univs.map (Ix.Kernel.Reader.convUniv param), self⟩ :
        Ix.Kernel.Reader.ECx .anon))
    (sh : { ws : Array (Ix.Kernel.Reader.CExpr .anon) //
      ExprReader.ShareOk ⟨cx, src, src.univs.map (Ix.Kernel.Reader.convUniv param), self⟩
        src.sharing.toList ws })
    (ps : List Ix.Kernel.LevelParam) :
    (rus : List Ixon.RecursorRule) →
      Option { rules₀ : List (RecRule .anon) // List.Forall₂ (fun ru rl₀ =>
        rl₀.nfields = ru.fields.toNat ∧
        (Ix.Kernel.Reader.MemberReader.mk' cx src param self).read ru.rhs = .ok rl₀.rhs ∧
        rl₀.rhs.looseBVarsBounded 0 = true ∧ rl₀.rhs.allLevelParamsDefined ps = true)
        rus rules₀ }
  | [] => some ⟨[], .nil⟩
  | ru :: rus =>
    match ExprReader.readCheck o sh ru.rhs, rulesRead o sh ps rus with
    | some rhs, some rest =>
      if h : rhs.1.looseBVarsBounded 0 = true ∧ rhs.1.allLevelParamsDefined ps = true then
        some ⟨RecRule.mk (Key.role .nat) ru.fields.toNat 0 .inert rhs.1 false false false :: rest.1,
          .cons ⟨rfl, rhs.2, h.1, h.2⟩ rest.2⟩
      else none
    | _, _ => none

/-- The check of a standalone recursor row. -/
def recReload? (a : _root_.Address) (c : Ixon.Constant)
    (hrow : (a, c) ∈ StoreInhabit.basisRows) : Option (PLift (PinReload a)) :=
  match hinfo : c.info with
  | .recr rc =>
    match hp : basisEnv.find? (Core.keyOf ctab a) with
    | some (ConstantInfo.recInfo cvP mIP rPP rlsP) =>
      if hps : cvP.levelParams.length = rc.lvls.toNat ∧
          cvP.levelParams.Perm (List.range cvP.levelParams.length) then
        match ExprReader.sharesCheck
            (RowReader.soloOracle basisS a c (Ix.Kernel.Reader.recParam cvP.levelParams))
            c.sharing.toList with
        | none => none
        | some sh =>
          match ExprReader.readCheck
              (RowReader.soloOracle basisS a c (Ix.Kernel.Reader.recParam cvP.levelParams)) sh
              rc.typ with
          | none => none
          | some ty =>
            match rulesRead
                (RowReader.soloOracle basisS a c (Ix.Kernel.Reader.recParam cvP.levelParams)) sh
                cvP.levelParams rc.rules.toList with
            | none => none
            | some rules₀ =>
              if h1 : ty.1.looseBVarsBounded 0 = true ∧
                  ty.1.allLevelParamsDefined cvP.levelParams = true ∧
                  (rc.k = true → rc.rules.size = 1) then
                match hcn : canonRecC (Core.keyOf ctab a) c 0 rc cvP.levelParams ty.1 rules₀.1 with
                | some (ConstantInfo.recInfo cv mI rP rls) =>
                  if h3 : cv = cvP ∧ mI = mIP ∧ rP = rPP ∧
                      rlsP.map ruleData = rls.map ruleData then
                    some ⟨fun E hE pin hpin => by
                      rw [hp] at hpin
                      cases hpin
                      obtain ⟨hcv, hmI, hrP, hrl⟩ := h3
                      subst hcv
                      subst hmI
                      subst hrP
                      have hcn' : LoadedReads.canonRec (IxVM.Consistency.keyOf ctab a) c 0 rc
                          cv.levelParams ty.1 rules₀.1 = some (.recInfo cv mI rP rls) :=
                        canonRec_of_C hcn
                      have hre := LoadedReads.reloadsAs_recr (E' := E) (env := basisEnv)
                        RoleVal.committedDefaultRoleTable_check (recordOf_of_row hE hrow) hinfo
                        hps.1 hps.2 (read_mono hE ty.2) h1.1 h1.2.1
                        (rules₀.2.imp fun _ _ hr => ⟨hr.1, read_mono hE hr.2.1, hr.2.2.1,
                          hr.2.2.2⟩)
                        h1.2.2 (row_usedRefs hrow) ⟨_, hp⟩ hcn'
                      exact reloadsAs_recr_transfer hre hrl⟩
                  else none
                | _ => none
              else none
      else none
    | _ => none
  | _ => none

/-- The check of an axiom row. -/
def axioReload? (a : _root_.Address) (c : Ixon.Constant)
    (hrow : (a, c) ∈ StoreInhabit.basisRows) : Option (PLift (PinReload a)) :=
  match hinfo : c.info with
  | .axio ax =>
    match ExprReader.sharesCheck (RowReader.plainOracle basisS c) c.sharing.toList with
    | none => none
    | some sh =>
      match ExprReader.readCheck (RowReader.plainOracle basisS c) sh ax.typ with
      | none => none
      | some ty =>
        if h1 : ty.1.looseBVarsBounded 0 = true ∧
            ty.1.allLevelParamsDefined (List.range ax.lvls.toNat) = true then
          match hcn : canonAnnC c (List.range ax.lvls.toNat) 0 ax.typ ty.1 with
          | none => none
          | some ty' =>
            if h3 : basisEnv.find? (Core.keyOf ctab a) =
                some (.axiomInfo ⟨Core.keyOf ctab a, List.range ax.lvls.toNat, ty'⟩) then
              some ⟨fun E hE pin hpin => by
                rw [h3] at hpin
                cases hpin
                exact LoadedReads.reloadsAs_axio RoleVal.committedDefaultRoleTable_check
                  (recordOf_of_row hE hrow) hinfo (read_mono hE ty.2) h1.1 h1.2
                  (row_usedRefs hrow) (canonAnn_of_C hcn)⟩
            else none
        else none
  | _ => none

/-- The check of a row, by its kind. -/
def rowReload? (a : _root_.Address) (c : Ixon.Constant)
    (hrow : (a, c) ∈ StoreInhabit.basisRows) : Option (PLift (PinReload a)) :=
  match indReload? a c hrow with
  | some r => some r
  | none =>
    match ctorReload? a c hrow with
    | some r => some r
    | none =>
      match recReload? a c hrow with
      | some r => some r
      | none => axioReload? a c hrow

/-! ## Every pin but the quotient pins reloads -/

/-- The four quotient roles whose records are quotient records. -/
def quotRoles : List Role := [.quot, .quotMk, .quotLift, .quotInd]

/-- A key is one of the four quotient roles'. -/
def isQuotKey : Key .anon → Bool
  | .role r => decide (r ∈ quotRoles)
  | _ => false

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Every row passes its check**, except the blocks (at no role's key) and the four
quotient records (decided: the readings computed, the canonical constants computed and
compared with the pins). -/
theorem basis_rowReloads :
    StoreInhabit.basisRows.attach.all (fun x =>
      (StoreInhabit.isMutsInfo x.1.2.info && !StoreInhabit.isBasisKey (Core.keyOf ctab x.1.1)) ||
      isQuotKey (Core.keyOf ctab x.1.1) ||
      (rowReload? x.1.1 x.1.2 x.2).isSome) = true := by
  decide +kernel

/-- **The pin of every basis role other than the quotient roles reloads**, for every store
of the basis records. -/
theorem basis_reloads {E : Ixon.Env} (hE : RecordsFor StoreInhabit.basisStore E) {r : Role}
    (hr : r ∈ TableInhabit.basisRoleOrder) (hq : r ∉ quotRoles) {pin : ConstantInfo .anon}
    (hpin : basisEnv.find? (Key.role r) = some pin) : Decl.ReloadsAs E ctab basisEnv pin := by
  have h0 := List.all_eq_true.mp basisRoles_rows r hr
  cases ha : ctab.addressOf? r with
  | none =>
    rw [ha] at h0
    cases h0
  | some a =>
    have hk : Core.keyOf ctab a = Key.role r := Core.keyOf_of_addressOf committedTable_wf ha
    obtain ⟨c, hmem, -⟩ := basis_role_record hE hr hk
    have h1 := List.all_eq_true.mp basis_rowReloads ⟨(a, c), hmem⟩ (List.mem_attach _ _)
    have hb : StoreInhabit.isBasisKey (Key.role r) = true := List.elem_eq_true_of_mem hr
    have hqk : isQuotKey (Key.role r) = false := by
      simp [isQuotKey, hq]
    simp only [hk, hb, hqk, Bool.not_true, Bool.and_false, Bool.false_or] at h1
    obtain ⟨⟨hrl⟩, -⟩ := Option.isSome_iff_exists.mp h1
    exact hrl E hE pin (by rw [hk]; exact hpin)

/-! ## The `getCI` field -/

section
open IxVM.Refinement.Core

/-- **The `getCI` field of the load contract at the environment of the pins**, given the
reload of the four quotient pins: a load at a stored key represents the pin stored there. -/
theorem basis_getCI_of_quot {E : Ixon.Env} (hE : RecordsFor StoreInhabit.basisStore E)
    (lim : Option Nat)
    (hq : ∀ r ∈ quotRoles, ∀ pin, basisEnv.find? (Key.role r) = some pin →
      Decl.ReloadsAs E ctab basisEnv pin) :
    ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs →
      (bctx E lim).stored.allowedTop "Ingress::get_ci" [addr] h →
      (bctx E lim).stored.κ (ixAddr a) ≠ unresolvedKey → CoreGood (bctx E lim).stored cs →
    Bytes.RepAddressRef addrTy h a addr →
      ∃ ci, (bctx E lim).stored.env.find? ((bctx E lim).stored.κ (ixAddr a)) = some ci ∧
        CIPtrRep (bctx E lim).stored.κ h' ptr ci := by
  intro addr ptr h h' cs a ev _ hres hg ha
  obtain ⟨ci, hci⟩ := Ctx.stored_key_ne hres (ixAddr_not_marker a)
  obtain ⟨r, hr, hk⟩ := basisEnv_find_role hci
  have hci' : basisEnv.find? (Key.role r) = some ci := by
    rw [← hk]
    exact hci
  have hrl : Decl.ReloadsAs E ctab basisEnv ci := by
    by_cases hqr : r ∈ quotRoles
    · exact hq r hqr ci hci'
    · exact basis_reloads hE hr hqr hci'
  have e : (bctx E lim).stored.κ (ixAddr a) = keyOf ctab (ixAddr a) :=
    (bctx E lim).stored.key_eq hres
  refine ⟨ci, by rw [e]; exact hci, ?_⟩
  have hname : keyOf ctab (ixAddr a) = ci.name := (WhnfAux.name_of_find hci).symm
  exact hrl addr ptr h h' cs a ev hg.raw ha hname

end

/-! ## The quotient pins reload -/

/-- The check of a quotient row (`LoadedReads.reloadsAs_quot`). -/
def quotReload? (a : _root_.Address) (c : Ixon.Constant)
    (hrow : (a, c) ∈ StoreInhabit.basisRows) : Option (PLift (PinReload a)) :=
  match hinfo : c.info with
  | .quot q =>
    match ExprReader.sharesCheck (RowReader.plainOracle basisS c) c.sharing.toList with
    | none => none
    | some sh =>
      match ExprReader.readCheck (RowReader.plainOracle basisS c) sh q.typ with
      | none => none
      | some ty =>
        if h1 : ty.1.looseBVarsBounded 0 = true ∧
            ty.1.allLevelParamsDefined (List.range q.lvls.toNat) = true then
          match hcn : canonAnnC c (List.range q.lvls.toNat) 0 q.typ ty.1 with
          | none => none
          | some ty' =>
            match hp : basisEnv.find? (Core.keyOf ctab a) with
            | none => none
            | some ci =>
              if h3 : ci.toConstantVal = ⟨Core.keyOf ctab a, List.range q.lvls.toNat, ty'⟩ ∧
                  LoadedReads.quotKindOk q.kind ci = true then
                some ⟨fun E hE pin hpin => by
                  rw [hp] at hpin
                  cases hpin
                  exact LoadedReads.reloadsAs_quot RoleVal.committedDefaultRoleTable_check
                    (recordOf_of_row hE hrow) hinfo (read_mono hE ty.2) h1.1 h1.2
                    (row_usedRefs hrow) (canonAnn_of_C hcn) h3.1 h3.2⟩
              else none
        else none
  | _ => none

/-- The check of a row, by its kind, the quotient records included. -/
def rowReloadAll? (a : _root_.Address) (c : Ixon.Constant)
    (hrow : (a, c) ∈ StoreInhabit.basisRows) : Option (PLift (PinReload a)) :=
  match rowReload? a c hrow with
  | some r => some r
  | none => quotReload? a c hrow

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Every row that is not a block passes its check** (decided). -/
theorem basis_rowReloadsAll :
    StoreInhabit.basisRows.attach.all (fun x =>
      (StoreInhabit.isMutsInfo x.1.2.info && !StoreInhabit.isBasisKey (Core.keyOf ctab x.1.1)) ||
      (rowReloadAll? x.1.1 x.1.2 x.2).isSome) = true := by
  decide +kernel

/-- **The pin of every basis role reloads**, for every store of the basis records. -/
theorem basis_reloadsAll {E : Ixon.Env} (hE : RecordsFor StoreInhabit.basisStore E) {r : Role}
    (hr : r ∈ TableInhabit.basisRoleOrder) {pin : ConstantInfo .anon}
    (hpin : basisEnv.find? (Key.role r) = some pin) : Decl.ReloadsAs E ctab basisEnv pin := by
  have h0 := List.all_eq_true.mp basisRoles_rows r hr
  cases ha : ctab.addressOf? r with
  | none =>
    rw [ha] at h0
    cases h0
  | some a =>
    have hk : Core.keyOf ctab a = Key.role r := Core.keyOf_of_addressOf committedTable_wf ha
    obtain ⟨c, hmem, -⟩ := basis_role_record hE hr hk
    have h1 := List.all_eq_true.mp basis_rowReloadsAll ⟨(a, c), hmem⟩ (List.mem_attach _ _)
    have hb : StoreInhabit.isBasisKey (Key.role r) = true := List.elem_eq_true_of_mem hr
    simp only [hk, hb, Bool.not_true, Bool.and_false, Bool.false_or] at h1
    obtain ⟨⟨hrl⟩, -⟩ := Option.isSome_iff_exists.mp h1
    exact hrl E hE pin (by rw [hk]; exact hpin)

theorem quotRoles_basis : ∀ r ∈ quotRoles, r ∈ TableInhabit.basisRoleOrder := by decide

section
open IxVM.Refinement.Core

/-- **The `getCI` field of the load contract at the environment of the pins**: a load at a
stored key represents the pin stored there. -/
theorem basis_getCI {E : Ixon.Env} (hE : RecordsFor StoreInhabit.basisStore E)
    (lim : Option Nat) :
    ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs →
      (bctx E lim).stored.allowedTop "Ingress::get_ci" [addr] h →
      (bctx E lim).stored.κ (ixAddr a) ≠ unresolvedKey → CoreGood (bctx E lim).stored cs →
    Bytes.RepAddressRef addrTy h a addr →
      ∃ ci, (bctx E lim).stored.env.find? ((bctx E lim).stored.κ (ixAddr a)) = some ci ∧
        CIPtrRep (bctx E lim).stored.κ h' ptr ci :=
  basis_getCI_of_quot hE lim fun r hr _ hpin =>
    basis_reloadsAll hE (quotRoles_basis r hr) hpin

end

end IxVM.Refinement.Typing
