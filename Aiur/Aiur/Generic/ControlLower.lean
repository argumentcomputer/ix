import Aiur.Generic.PatternLowering
import Aiur.Generic.Consts

/-! Eliminate lexical exits after source evaluation's semantic boundary.
Continuations are compiler syntax records, never Aiur function values. Every binder
is renamed before a continuation is placed beneath it, so an exiting scope
cannot capture a variable used after its target block. -/

namespace Aiur.Generic.ControlLower

def hasControl : Expr α → Bool
  | .control _ _ => true
  | .literal _ | .var _ | .global _ _ => false
  | .builtin _ xs | .update _ xs | .record _ xs | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs | .call _ _ xs =>
      (xs.map hasControl).any id
  | .member x _ | .repeat x _ | .index x _ | .slice x _ _ | .project x _ | .store x | .load x | .hint _ x channel | .neg x => hasControl x
  | .letValue _ x b | .binary _ x b => hasControl x || hasControl b
  | .matchValue x arms => hasControl x || (arms.map fun arm => hasControl arm.2).any id
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

def names : Expr α → List String
  | .literal _ | .global _ _ => []
  | .var name => [name]
  | .builtin _ xs | .update _ xs | .record _ xs | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs | .call _ _ xs => xs.flatMap names
  | .member x _ | .control _ x | .repeat x _ | .index x _ | .slice x _ _ | .project x _ | .store x | .load x | .hint _ x channel | .neg x => names x
  | .letValue pat x b => pat.bindingNames ++ names x ++ names b
  | .binary _ x b => names x ++ names b
  | .matchValue x arms => names x ++ arms.flatMap (fun arm => arm.1.bindingNames ++ names arm.2)
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

abbrev Renaming := List (String × String)

def rename (env : Renaming) (name : String) : String := (env.lookup name).getD name

def renamePattern (env : Renaming) : Pattern α → Pattern α
  | .literal x => .literal x
  | .wildcard => .wildcard
  | .bind name => .bind (rename env name)
  | .global name type => .global name type
  | .orElse left right names => .orElse (renamePattern env left) (renamePattern env right) { names with names := names.names.map (rename env) }
  | .load p => .load (renamePattern env p)
  | .record head ps => .record head (ps.map (renamePattern env))
  | .tuple ps => .tuple (ps.map (renamePattern env))
  | .array ps => .array (ps.map (renamePattern env))
  | .repeat p n => .repeat (renamePattern env p) n
  | .construct t c ps => .construct t c (ps.map (renamePattern env))
  | .constructAs params t c ps => .constructAs params t c (ps.map (renamePattern env))
termination_by pat => sizeOf pat

/-- A continuation has one value parameter. Keeping it as syntax makes
freshness a finite check, including when it is copied into several arms. -/
structure Continuation (α : Type) where
  arg : String
  body : Expr α

abbrev Handlers (α : Type) := List (ExitTarget × Continuation α)

def Continuation.names (next : Continuation α) : List String := next.arg :: ControlLower.names next.body

def Continuation.apply (next : Continuation α) (value : Expr α) : Expr α :=
  .letValue (.bind next.arg) value next.body

def reserved (env : Renaming) (next : Continuation α) (handlers : Handlers α) : List String :=
  env.map Prod.snd ++ next.names ++ handlers.flatMap (fun h => h.2.names)

def fresh (used : List String) : Except String String :=
  let name := PatternLowering.freshPrefix used ++ "control"
  if name ∈ used then .error "control temporary is not fresh" else .ok name

def bindings (pat : Pattern α) (used : List String) : Except String Renaming :=
  let stem := PatternLowering.freshPrefix used ++ "control:"
  let result := pat.bindingNames.eraseDups.zipIdx.map fun (name, i) => (name, stem ++ toString i)
  if !(Consts.dependencies pat).isEmpty then .error "expand const patterns before control lowering"
  else if !(result.map Prod.snd).Nodup then .error "duplicate control temporary"
  else if !(result.all fun entry => !(used.contains entry.2)) then .error "control temporary captures a variable"
  else .ok result

def projects (name : String) (length : Nat) : List (Expr α) :=
  (List.range length).map (fun i => .project (.var name) i)

mutual
  def expression : Nat → Renaming → Expr α → Continuation α → Handlers α → Except String (Expr α)
    | 0, _, _, _, _ => throw "control lowering depth exceeded"
    | fuel + 1, env, expr, next, handlers => do
        let used := reserved env next handlers
        match expr with
        | .control (.block label) body =>
            expression fuel env body next ((.block label, next) :: handlers)
        | .control (.exit target) value =>
            let some handler := handlers.lookup target | throw s!"unbound control target {repr target}"
            expression fuel env value handler handlers
        | .literal value => return next.apply (.literal value)
        | .var name =>
            let some renamed := env.lookup name | throw s!"unbound variable '{name}' during control lowering"
            return next.apply (.var renamed)
        | .global _ _ => throw "expand const expressions before control lowering"
        | .tuple xs | .array xs => arguments fuel env xs next handlers
        | .builtin op xs =>
            let input ← fresh (reserved env next handlers)
            arguments fuel env xs ⟨input, next.apply (.builtin op (projects input xs.length))⟩ handlers
        | .update paths xs =>
            let input ← fresh (reserved env next handlers)
            arguments fuel env xs ⟨input, next.apply (.update paths (projects input xs.length))⟩ handlers
        | .record head xs =>
            let input ← fresh used
            arguments fuel env xs ⟨input, next.apply (.record head (projects input xs.length))⟩ handlers
        | .construct name types ctor xs =>
            let input ← fresh used
            arguments fuel env xs ⟨input, next.apply (.construct name types ctor (projects input xs.length))⟩ handlers
        | .constructAs params t ctor xs =>
            let input ← fresh used
            arguments fuel env xs ⟨input, next.apply (.constructAs params t ctor (projects input xs.length))⟩ handlers
        | .call name types xs =>
            let input ← fresh used
            arguments fuel env xs ⟨input, next.apply (.call name types (projects input xs.length))⟩ handlers
        | .repeat x n =>
            let input ← fresh used
            expression fuel env x ⟨input, next.apply (.repeat (.var input) n)⟩ handlers
        | .index x i =>
            let input ← fresh used
            expression fuel env x ⟨input, next.apply (.index (.var input) i)⟩ handlers
        | .slice x start stop =>
            let input ← fresh used
            expression fuel env x ⟨input, next.apply (.slice (.var input) start stop)⟩ handlers
        | .member x field =>
            let input ← fresh used
            expression fuel env x ⟨input, next.apply (.member (.var input) field)⟩ handlers
        | .project x i =>
            let input ← fresh used
            expression fuel env x ⟨input, next.apply (.project (.var input) i)⟩ handlers
        | .store x =>
            let input ← fresh used
            expression fuel env x ⟨input, next.apply (.store (.var input))⟩ handlers
        | .load x =>
            let input ← fresh used
            expression fuel env x ⟨input, next.apply (.load (.var input))⟩ handlers
        | .hint t x channel =>
            let input ← fresh used
            expression fuel env x ⟨input, next.apply (.hint t (.var input) channel)⟩ handlers
        | .neg x =>
            let input ← fresh used
            expression fuel env x ⟨input, next.apply (.neg (.var input))⟩ handlers
        | .binary op x y =>
            let left ← fresh used
            let right ← fresh (left :: used)
            let rest ← expression fuel env y
              ⟨right, next.apply (.binary op (.var left) (.var right))⟩ handlers
            expression fuel env x ⟨left, rest⟩ handlers
        | .letValue pat x body =>
            let bound ← bindings pat used
            let input ← fresh ((bound.map Prod.snd) ++ used)
            let rest ← expression fuel (bound ++ env) body next handlers
            expression fuel env x ⟨input, .letValue (renamePattern bound pat) (.var input) rest⟩ handlers
        | .matchValue x arms =>
            let input ← fresh used
            let arms ← arms.mapM fun (pat, body) => do
              let bound ← bindings pat used
              return (renamePattern bound pat, ← expression fuel (bound ++ env) body next handlers)
            expression fuel env x ⟨input, .matchValue (.var input) arms⟩ handlers

  def arguments : Nat → Renaming → List (Expr α) → Continuation α → Handlers α → Except String (Expr α)
    | 0, _, _, _, _ => throw "control lowering depth exceeded"
    | _ + 1, _, [], next, _ => return next.apply (.tuple [])
    | fuel + 1, env, first :: rest, next, handlers => do
        let used := reserved env next handlers
        let head ← fresh used
        let tail ← fresh (head :: used)
        let remaining ← arguments fuel env rest
          ⟨tail, next.apply (.tuple (.var head :: projects tail rest.length))⟩ handlers
        expression fuel env first ⟨head, remaining⟩ handlers
end

def function (expr : Expr α) (parameters : List String) : Except String (Expr α) := do
  if !hasControl expr then return expr
  let name ← fresh (parameters ++ names expr)
  let next : Continuation α := ⟨name, .var name⟩
  expression 4096 (parameters.map fun name => (name, name)) expr next [(.function, next)]

end Aiur.Generic.ControlLower
