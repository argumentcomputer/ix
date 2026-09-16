import Compilatrix.Ixon.V3.Env

namespace Compilatrix.Ixon.V3.Tc

/-! Consumer limits apply before converting an untrusted constant to kernel
nodes. They restrict admission without changing its committed identity. -/

def checkCount (label : String) (value : UInt64) : Except String Unit :=
  if value ≤ 4096 then .ok () else .error s!"typing: {label} exceeds 4096"

def checkExprCounts : Expr → Except String Unit
  | .var i => checkCount "bound variable index" i
  | .prj _ field value => do
      checkCount "projection field" field
      checkExprCounts value
  | .app f a => checkExprCounts f *> checkExprCounts a
  | .lam _ t b | .all _ _ t b => checkExprCounts t *> checkExprCounts b
  | .letE _ t v b => checkExprCounts t *> checkExprCounts v *> checkExprCounts b
  | _ => .ok ()

def checkDefinitionCounts (d : Definition) : Except String Unit :=
  checkCount "universe parameters" d.lvls

def checkRecursorCounts (r : Recursor) : Except String Unit := do
  for n in #[r.lvls, r.params, r.indices, r.motives, r.minors] do
    checkCount "recursor count" n
  for rule in r.rules do checkCount "recursor rule fields" rule.fields

def checkInductiveCounts (i : Inductive) : Except String Unit := do
  for n in #[i.lvls, i.params, i.indices] do checkCount "inductive count" n
  for c in i.ctors do
    for n in #[c.lvls, c.cidx, c.params, c.fields] do checkCount "constructor count" n

def checkConstantCounts (c : Constant) : Except String Unit := do
  match c.info with
  | .defn d => checkDefinitionCounts d
  | .recr r => checkRecursorCounts r
  | .axio a => checkCount "universe parameters" a.lvls
  | .quot q => checkCount "universe parameters" q.lvls
  | .muts ms =>
    if ms.isEmpty then throw "typing: empty mutual block"
    for m in ms do
      match m with
      | .defn d => checkDefinitionCounts d
      | .recr r => checkRecursorCounts r
      | .indc i => checkInductiveCounts i
  | _ => pure ()
  for e in c.info.exprs ++ c.sharing.toList do checkExprCounts e

end Compilatrix.Ixon.V3.Tc
