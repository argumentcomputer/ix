import IxCC.Cfg.Rc.Prefix
import IxCC.Cfg.Lower
import IxCC.Own.Plain.Owned

set_option autoImplicit false
namespace IxCC.Cfg.Rc


mutual
def actionCount : Own.Plain.Code → Nat
  | .act _ k | .dropSlot _ k => 1 + actionCount k
  | .bind _ _ k | .reset _ _ _ _ _ k | .reuse _ _ _ _ _ k => actionCount k
  | .jp _ _ _ _ b k => actionCount k + actionCount b
  | .case _ alts d => actionCountAlts alts + actionCountOpt d
  | .jmp .. | .ret .. | .tcall .. | .trap => 0
def actionCountAlts : List Own.Plain.Alt → Nat
  | [] => 0
  | .mk _ b :: rest => actionCount b + actionCountAlts rest
def actionCountOpt : Option Own.Plain.Code → Nat
  | none => 0
  | some c => actionCount c
end

def markerRhs (limit : Nat) : Action → Own.Rhs
  | .inc x n => .fir (.call limit [.var x, .lit (.nat n)])
  | .dec x => .fir (.call (limit + 1) [.var x])

def heapCtorIndex (ctors : List Lam.CtorInfo) (key : Key.CtorKey) : Nat :=
  (((ctors.filter (fun c => c.arity > 0)).zipIdx.find? fun p => p.1.key == key).map (·.2)).getD 0

mutual
def skeleton (limit first : Nat) (c : Own.Plain.Code)
    (ctors : List Lam.CtorInfo := []) (slotBase : Nat := first) : Own.Code :=
  match c with
  | .act a k => .bind first (markerRhs limit a) (skeleton limit (first + 1) k ctors slotBase)
  | .bind x r k => .bind x (Own.immRhs r) (skeleton limit first k ctors slotBase)
  | .reset s x ctor fields uniq k =>
    let ci := heapCtorIndex ctors ctor.key
    let mask := Own.Plain.fieldsMask fields
    .bind (slotBase + s) (.fir (.call (limit + 2)
      [.var x, .lit (.nat ci), .lit (.nat mask), .lit (.nat (if uniq then 1 else 0))]))
      (skeleton limit first k ctors slotBase)
  | .reuse x s ctor args uniq k =>
    let ci := heapCtorIndex ctors ctor.key
    .bind x (.fir (.call (limit + 3)
      (.var (slotBase + s) :: .lit (.nat ci) :: .lit (.nat (if uniq then 1 else 0)) :: args)))
      (skeleton limit first k ctors slotBase)
  | .dropSlot s k =>
    .bind first (markerRhs limit (.dec (slotBase + s))) (skeleton limit (first + 1) k ctors slotBase)
  | .jp j ps captured rec b k =>
    .jp j (ps.map (·, Own.PSig.plain .tobj)) (captured.map (·, 1)) rec
      (skeleton limit (first + actionCount k) b ctors slotBase)
      (skeleton limit first k ctors slotBase)
  | .case x alts d => .case x (skeletonAlts limit first alts ctors slotBase)
      (skeletonOpt limit (first + actionCountAlts alts) d ctors slotBase)
  | .jmp j args => .jmp j args
  | .ret a => .ret a
  | .tcall f args => .tcall f args
  | .trap => .trap
def skeletonAlts (limit first : Nat) (alts : List Own.Plain.Alt)
    (ctors : List Lam.CtorInfo := []) (slotBase : Nat := first) : List Own.Alt :=
  match alts with
  | [] => []
  | .mk key b :: rest => .mk key (skeleton limit first b ctors slotBase) ::
      skeletonAlts limit (first + actionCount b) rest ctors slotBase
def skeletonOpt (limit first : Nat) (d : Option Own.Plain.Code)
    (ctors : List Lam.CtorInfo := []) (slotBase : Nat := first) : Option Own.Code :=
  match d with
  | none => none
  | some c => some (skeleton limit first c ctors slotBase)
end

def instructions (f : Cfg.Fun) : List Instr := f.blocks.flatMap (·.body)

def lowerFunction (limit f : Nat) (fd : Fir.Fun) (body : Own.Plain.Code)
    (ctors : List Lam.CtorInfo := []) : Cfg.Fun :=
  let first := fd.vars + Own.Plain.slotBound body
  Cfg.Lower.function f { Own.immFun fd with
    body := skeleton limit first body ctors fd.vars
    vars := first + actionCount body }

/-- The candidate instruction table is checked against the actual emitted
blocks; it is neither trusted metadata nor silently regenerated on execution. -/
def checkFunction (limit : Nat) (first : Nat) (fd : Cfg.Fun) (table : ActionTable) : Bool :=
  checkMarkers limit first (instructions fd) table

end IxCC.Cfg.Rc
