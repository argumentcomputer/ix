import IxCC.Cfg.Rc.Native
import IxCC.Lir.Proof.Steps
import IxCC.Rt.Proof.Mem
import IxCC.Rt.Proof.Words

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Lir
open IxCC.Rt.Proof

def fieldAddress (address : Word) (i : Nat) : Word := address + UInt64.ofNat (8 * (i + 1))

def fieldStore (pointer i : Nat) : Lir.Stmt :=
  .store .w64 {base := some (.v pointer), disp := Int.ofNat (8 * (i + 1))} (.v i)

def publishFields (mem : X86.Memory) (address : Word) (words : Nat → Word) (indices : List Nat) : X86.Memory :=
  indices.foldl (fun m i => m.write .w64 (fieldAddress address i) (words i)) mem

/-- Permissions, actual pointer and field register lookups suffice for all
publishing stores. No successful store or procedure simulation is assumed. -/
theorem publish_exec (indices : List Nat) (pointer : Nat) (env : Lir.Env)
    (address : Word) (words : Nat → Word) (ctx : Word)
    (pointerValue : env[pointer]? = some address)
    (fields : ∀ i ∈ indices, env[i]? = some (words i))
    (mem : X86.Memory)
    (writable : ∀ i ∈ indices, ∀ byte < 8,
      mem.writable (fieldAddress address i + UInt64.ofNat byte) = true) :
    Lir.execList env mem ctx (indices.map (fieldStore pointer)) =
      some (env, publishFields mem address words indices) := by
  induction indices generalizing mem with
  | nil => rfl
  | cons i indices ih =>
    have write := write?_ok (w := .w64) (v := words i)
      (a := fieldAddress address i) (writable i (by simp))
    have store : (fieldStore pointer i).exec env mem ctx =
        some (env, mem.write .w64 (fieldAddress address i) (words i)) := by
      simp only [fieldStore, Lir.Stmt.exec, Lir.Addr.eval, Lir.Arg.eval, pointerValue,
        fields i (by simp)]
      change (match mem.write? .w64
        (address + 0 + Lir.dispWord ((8 * (i + 1) : Nat) : Int)) (words i) with
        | .ok after => some (env, after)
        | .error _ => none) = _
      rw [UInt64.add_zero, Lir.dispWord_ofNat]
      change (match mem.write? .w64 (fieldAddress address i) (words i) with
        | .ok after => some (env, after)
        | .error _ => none) = _
      rw [write]
    rw [List.map_cons, Lir.execList, store]
    apply ih (fun j hj => fields j (by simp [hj]))
    intro j hj byte bound
    simpa [X86.Memory.write] using writable j (by simp [hj]) byte bound

/-- The actual native publishing wrapper reaches its return only after every
payload field has been stored. The allocator result register is fresh relative
to all input field registers; the wrapper's caller frame is preserved. -/
theorem allocation_publish {p : Lir.Program} {g allocator fields : Nat}
    {env : Lir.Env} {address : Word} {words : Nat → Word} {rest : List Lir.Frame}
    {mem : X86.Memory} {ctx : Word}
    (function : p.funcs[g]? = some (allocationWrapper allocator fields))
    (values : ∀ i < fields, env[i]? = some (words i))
    (writable : ∀ i < fields, ∀ byte < 8,
      mem.writable (fieldAddress address i + UInt64.ofNat byte) = true) :
    Sem.Star (Lir.semStep p)
      {mem, ctx, stack := {fn := g, label := 0, pos := 1, env := env.insert fields address} :: rest} 0
      {mem := publishFields mem address words (List.range fields), ctx,
        stack := {fn := g, label := 0, pos := 1 + fields, env := env.insert fields address} :: rest} := by
  have exec := publish_exec (List.range fields) fields (env.insert fields address)
    address words ctx (by simp) (by
      intro i hi
      have bound := List.mem_range.mp hi
      rw [Lir.env_insert_ne _ address (by omega)]
      exact values i bound) mem (by
      intro i hi byte hb
      exact writable i (List.mem_range.mp hi) byte hb)
  have trace := Lir.star_stmts (p := p) (ctx := ctx) (rest := rest) (dsts := []) function
    (show (allocationWrapper allocator fields).blocks[0]? = some {
      body := (Lir.Stmt.call [fields] allocator [] :: (List.range fields).map (fieldStore fields)).toArray
      term := .ret [.v fields]} from rfl)
    (pre := [.call [fields] allocator []]) (ss := (List.range fields).map (fieldStore fields))
    (post := []) (by simp) (by
      intro stmt member
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
      rfl) exec
  simpa using trace



end IxCC.Cfg.Rc.Native
