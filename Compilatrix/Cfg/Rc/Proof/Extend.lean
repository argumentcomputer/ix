import Compilatrix.Cfg.Rc.Proof.State

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc

theorem EnvSub.trans {a b c : Own.Env} (ab : EnvSub a b) (bc : EnvSub b c) : EnvSub a c :=
  fun x v h => bc x v (ab x v h)

theorem Joins.extend {limit self lo : Nat} {B : Cfg.Proof.Blocks} {ρ target : Own.Env}
    {scope : Cfg.Lower.JScope} {saved : List Own.Plain.JEntry}
    (h : Joins limit B self ρ lo scope saved) (sub : EnvSub ρ target) :
    Joins limit B self target lo scope saved := by
  induction h with
  | nil => exact .nil
  | cons tail bound params charge layout env below lower boundBody upper scopedNames ih =>
    exact .cons ih bound params charge layout (env.trans sub) below lower boundBody upper scopedNames

theorem At.extend {F : Fir.Program} {P : Program} {fr : Frame} {ρ target : Own.Env}
    {saved : List Own.Plain.JEntry} {code : Own.Plain.Code}
    (h : At F P fr ρ saved code) (sub : EnvSub fr.env target) :
    At F P { fr with env := target } ρ saved code := by
  obtain ⟨fd, scope, params, acc, next, first, lo, lookup, range, layout, cursor,
    env, below, scopedNames, joins⟩ := h
  exact ⟨fd, scope, params, acc, next, first, lo, lookup, range, layout, cursor,
    env.trans sub, below, scopedNames, joins.extend sub⟩


end Compilatrix.Cfg.Rc
