import IxCC.Cfg.Rc.Prefix
import IxCC.Cfg.Lower
import IxCC.Own.Plain.Owned

set_option autoImplicit false
namespace IxCC.Cfg.Rc


mutual
def actionCount : Own.Plain.Code → Nat
  | .act _ k => 1 + actionCount k
  | .bind _ _ k => actionCount k
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

mutual
def skeleton (limit first : Nat) : Own.Plain.Code → Own.Code
  | .act a k => .bind first (markerRhs limit a) (skeleton limit (first + 1) k)
  | .bind x r k => .bind x (Own.immRhs r) (skeleton limit first k)
  | .jp j ps captured rec b k =>
    .jp j (ps.map (·, Own.PSig.plain .tobj)) (captured.map (·, 1)) rec
      (skeleton limit (first + actionCount k) b) (skeleton limit first k)
  | .case x alts d => .case x (skeletonAlts limit first alts)
      (skeletonOpt limit (first + actionCountAlts alts) d)
  | .jmp j args => .jmp j args
  | .ret a => .ret a
  | .tcall f args => .tcall f args
  | .trap => .trap
def skeletonAlts (limit first : Nat) : List Own.Plain.Alt → List Own.Alt
  | [] => []
  | .mk key b :: rest => .mk key (skeleton limit first b) ::
      skeletonAlts limit (first + actionCount b) rest
def skeletonOpt (limit first : Nat) : Option Own.Plain.Code → Option Own.Code
  | none => none
  | some c => some (skeleton limit first c)
end

def instructions (f : Cfg.Fun) : List Instr := f.blocks.flatMap (·.body)

def lowerFunction (limit f : Nat) (fd : Fir.Fun) (body : Own.Plain.Code) : Cfg.Fun :=
  Cfg.Lower.function f { Own.immFun fd with
    body := skeleton limit fd.vars body
    vars := fd.vars + actionCount body }

/-- The candidate instruction table is checked against the actual emitted
blocks; it is neither trusted metadata nor silently regenerated on execution. -/
def checkFunction (limit : Nat) (first : Nat) (fd : Cfg.Fun) (table : ActionTable) : Bool :=
  checkMarkers limit first (instructions fd) table

end IxCC.Cfg.Rc
