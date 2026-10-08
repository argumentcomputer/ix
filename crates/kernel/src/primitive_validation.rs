//! Admission of primitive rules from declarations, independent of Lean releases.
//!
//! Required literal rules validate their construction interfaces. Optional Nat
//! folds validate defining recurrences with all optional shortcuts disabled.
//! Declarations without an admitted shortcut retain ordinary kernel reduction.

use ix_common::address::Address;
use ix_common::env::{BinderInfo, DefinitionSafety, Name, QuotKind};
use ixon::constant::DefKind;

use crate::constant::KConst;
use crate::env::KEnv;
use crate::error::TcError;
use crate::expr::KExpr;
use crate::id::KId;
use crate::level::KUniv;
use crate::mode::KernelMode;
use crate::tc::TypeChecker;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Rule {
  Nat,
  String,
  Bool,
  Pred,
  Add,
  Sub,
  Mul,
  Pow,
  Beq,
  Ble,
  QuotLift,
  QuotInd,
  Div,
  Mod,
  Gcd,
  Land,
  Lor,
  Xor,
  ShiftLeft,
  ShiftRight,
}

fn cnst<M: KernelMode>(id: &KId<M>) -> KExpr<M> {
  KExpr::cnst(id.clone(), Box::new([]))
}

fn arrow<M: KernelMode>(a: KExpr<M>, b: KExpr<M>) -> KExpr<M> {
  KExpr::all(
    M::meta_field(Name::anon()),
    M::meta_field(BinderInfo::Default),
    a,
    b,
  )
}

impl<M: KernelMode> TypeChecker<'_, M> {
  pub(super) fn trusted_primitives(&self) -> bool {
    self.prims.trusted && !self.primitive_validation
  }

  /// Separate environments prevent conversion caches from certifying a rule
  /// using results produced by that same rule. Lazy workers fault only the
  /// declarations the validation actually needs.
  fn validate_primitive(&mut self, rule: Rule) -> Result<bool, TcError<M>> {
    let mut env =
      KEnv::new_with_recursor_aux_order(self.env.recursor_aux_order);
    if self.lazy_ixon.is_none() && self.lazy_anon.is_none() {
      for (id, c) in self.env.iter() {
        env.insert(id, c);
      }
      env.blocks = self.env.blocks.clone();
    }
    let _ = env.set_prims(self.prims.clone());
    let mut tc = TypeChecker::new(&mut env);
    tc.lazy_ixon = self.lazy_ixon.clone();
    tc.lazy_anon = self.lazy_anon.clone();
    if let Some(lazy) = &mut tc.lazy_ixon {
      lazy.faulted_addrs.clear();
    }
    if let Some(lazy) = &mut tc.lazy_anon {
      lazy.faulted_addrs.clear();
    }
    tc.ixon_ingress = self.ixon_ingress;
    tc.primitive_validation = true;
    tc.validating_primitive_rules =
      self.validating_primitive_rules | (1 << rule as u32);
    // Failure to establish an optional optimization within this budget leaves
    // the ordinary reducer available. It does not change declaration validity.
    tc.rec_fuel = tc.rec_fuel.min(100_000);
    tc.validate_rule(rule)
  }

  pub(super) fn require_primitive(
    &mut self,
    rule: Rule,
  ) -> Result<(), TcError<M>> {
    if self.trusted_primitives() {
      return Ok(());
    }
    let key = (self.prims.binding_key.clone(), rule);
    if self.env.primitive_admission.get(&key) == Some(&true) {
      return Ok(());
    }
    if self.validating_primitive_rules & (1 << rule as u32) != 0 {
      return Err(TcError::Other(format!(
        "circular primitive contract: {rule:?}"
      )));
    }
    // Literal contracts use syntax and ordinary inference, never optional
    // native operations. They are also required in the validation checker.
    let valid = match rule {
      Rule::Nat | Rule::Bool => self.validate_rule(rule)?,
      _ => self.validate_primitive(rule)?,
    };
    if valid {
      self.env.primitive_admission.insert(key, true);
      Ok(())
    } else {
      Err(TcError::Other(format!(
        "unsupported primitive binding: {rule:?} construction contract"
      )))
    }
  }

  pub(super) fn admit_nat_operation(&mut self, addr: &Address) -> bool {
    if self.trusted_primitives() {
      return true;
    }
    if self.primitive_validation {
      return false;
    }
    let p = &self.prims;
    let rule = if *addr == p.nat_pred.addr {
      Rule::Pred
    } else if *addr == p.nat_add.addr {
      Rule::Add
    } else if *addr == p.nat_sub.addr {
      Rule::Sub
    } else if *addr == p.nat_mul.addr {
      Rule::Mul
    } else if *addr == p.nat_pow.addr {
      Rule::Pow
    } else if *addr == p.nat_beq.addr {
      Rule::Beq
    } else if *addr == p.nat_ble.addr {
      Rule::Ble
    } else if *addr == p.nat_div.addr {
      Rule::Div
    } else if *addr == p.nat_mod.addr {
      Rule::Mod
    } else if *addr == p.nat_gcd.addr {
      Rule::Gcd
    } else if *addr == p.nat_land.addr {
      Rule::Land
    } else if *addr == p.nat_lor.addr {
      Rule::Lor
    } else if *addr == p.nat_xor.addr {
      Rule::Xor
    } else if *addr == p.nat_shift_left.addr {
      Rule::ShiftLeft
    } else if *addr == p.nat_shift_right.addr {
      Rule::ShiftRight
    } else {
      return false;
    };
    if p.native.ambiguous_nat_ops & (1 << (rule as u32)) != 0 {
      return false;
    }
    if p.native.nat_ops & (1 << (rule as u32)) != 0 {
      return true;
    }
    if matches!(
      rule,
      Rule::Div
        | Rule::Mod
        | Rule::Gcd
        | Rule::Land
        | Rule::Lor
        | Rule::Xor
        | Rule::ShiftLeft
        | Rule::ShiftRight
    ) {
      return false;
    }
    let key = (p.binding_key.clone(), rule);
    if let Some(result) = self.env.primitive_admission.get(&key) {
      return *result;
    }
    let deps: &[Rule] = match rule {
      Rule::Sub => &[Rule::Pred],
      Rule::Mul => &[Rule::Add],
      Rule::Pow => &[Rule::Add, Rule::Mul],
      _ => &[],
    };
    let admitted = deps.iter().all(|dep| {
      let addr = self.nat_rule_id(*dep).addr;
      self.admit_nat_operation(&addr)
    }) && self.validate_primitive(rule).unwrap_or(false);
    self.env.primitive_admission.insert(key, admitted);
    admitted
  }

  fn nat_rule_id(&self, rule: Rule) -> KId<M> {
    let p = &self.prims;
    match rule {
      Rule::Pred => &p.nat_pred,
      Rule::Add => &p.nat_add,
      Rule::Sub => &p.nat_sub,
      Rule::Mul => &p.nat_mul,
      Rule::Pow => &p.nat_pow,
      Rule::Beq => &p.nat_beq,
      Rule::Ble => &p.nat_ble,
      _ => unreachable!(),
    }
    .clone()
  }

  fn validate_rule(&mut self, rule: Rule) -> Result<bool, TcError<M>> {
    match rule {
      Rule::Nat => self.validate_nat(),
      Rule::Bool => self.validate_bool(),
      Rule::String => self.validate_string(),
      Rule::QuotLift | Rule::QuotInd => self.validate_quot(rule),
      _ => self.validate_nat_equations(rule),
    }
  }

  fn validate_nat(&mut self) -> Result<bool, TcError<M>> {
    let p = self.prims.clone();
    let nat = cnst(&p.nat);
    if !matches!(self.get_const(&p.nat)?,
      KConst::Indc { lvls: 0, params: 0, indices: 0, is_unsafe: false, ty, ctors, .. }
      if ty == KExpr::sort(KUniv::succ(KUniv::zero())) && ctors == [p.nat_zero.clone(), p.nat_succ.clone()])
    {
      return Ok(false);
    }
    for (id, index, fields, expected) in [
      (p.nat_zero, 0, 0, nat.clone()),
      (p.nat_succ, 1, 1, arrow(nat.clone(), nat)),
    ] {
      if !matches!(self.get_const(&id)?,
        KConst::Ctor { lvls: 0, params: 0, is_unsafe: false, induct, cidx, fields: n, ty, .. }
        if induct == p.nat && cidx == index && n == fields && ty == expected)
      {
        return Ok(false);
      }
    }
    Ok(true)
  }

  fn validate_bool(&mut self) -> Result<bool, TcError<M>> {
    let p = self.prims.clone();
    if !matches!(self.get_const(&p.bool_type)?,
      KConst::Indc { lvls: 0, params: 0, indices: 0, is_unsafe: false, ty, ctors, .. }
      if ty == KExpr::sort(KUniv::succ(KUniv::zero())) && ctors == [p.bool_false.clone(), p.bool_true.clone()])
    {
      return Ok(false);
    }
    for (id, index) in [(p.bool_false, 0), (p.bool_true, 1)] {
      if !matches!(self.get_const(&id)?,
        KConst::Ctor { lvls: 0, params: 0, fields: 0, is_unsafe: false, induct, cidx, ty, .. }
        if induct == p.bool_type && cidx == index && ty == cnst(&p.bool_type))
      {
        return Ok(false);
      }
    }
    Ok(true)
  }

  fn validate_string(&mut self) -> Result<bool, TcError<M>> {
    self.require_primitive(Rule::Nat)?;
    let p = self.prims.clone();
    let char_ty = cnst(&p.char_type);
    let string_ty = cnst(&p.string);
    let list = |id: &KId<M>| {
      KExpr::app(
        KExpr::cnst(id.clone(), Box::new([KUniv::zero()])),
        char_ty.clone(),
      )
    };
    let list_ty = list(&p.list);
    for (term, expected) in [
      (char_ty.clone(), KExpr::sort(KUniv::succ(KUniv::zero()))),
      (string_ty.clone(), KExpr::sort(KUniv::succ(KUniv::zero()))),
      (list_ty.clone(), KExpr::sort(KUniv::succ(KUniv::zero()))),
      (list(&p.list_nil), list_ty.clone()),
      (
        list(&p.list_cons),
        arrow(char_ty.clone(), arrow(list_ty.clone(), list_ty.clone())),
      ),
      (cnst(&p.char_of_nat), arrow(cnst(&p.nat), char_ty.clone())),
      (cnst(&p.string_of_list), arrow(list_ty, string_ty)),
    ] {
      let actual = self.infer(&term)?;
      if !self.is_def_eq(&actual, &expected)? {
        return Ok(false);
      }
    }
    Ok(true)
  }

  fn validate_quot(&mut self, rule: Rule) -> Result<bool, TcError<M>> {
    let p = self.prims.clone();
    let eliminator =
      if rule == Rule::QuotLift { p.quot_lift } else { p.quot_ind };
    let kind =
      if rule == Rule::QuotLift { QuotKind::Lift } else { QuotKind::Ind };
    if rule == Rule::QuotLift {
      self.get_const(&p.eq)?;
      self.get_const(&p.eq_refl)?;
    }
    for (id, expected) in [
      (p.quot_type, QuotKind::Type),
      (p.quot_ctor, QuotKind::Ctor),
      (eliminator, kind),
    ] {
      let KConst::Quot { kind, lvls, ty, .. } = self.get_const(&id)? else {
        return Ok(false);
      };
      if kind != expected {
        return Ok(false);
      }
      self.check_quot(&id, kind, lvls, &ty)?;
    }
    Ok(true)
  }

  fn validate_nat_equations(&mut self, rule: Rule) -> Result<bool, TcError<M>> {
    self.require_primitive(Rule::Nat)?;
    let p = self.prims.clone();
    let id = self.nat_rule_id(rule);
    let nat = cnst(&p.nat);
    let is_bool = matches!(rule, Rule::Beq | Rule::Ble);
    if is_bool {
      self.require_primitive(Rule::Bool)?;
    }
    let cod = if is_bool { cnst(&p.bool_type) } else { nat.clone() };
    let expected = if rule == Rule::Pred {
      arrow(nat.clone(), cod)
    } else {
      arrow(nat.clone(), arrow(nat.clone(), cod))
    };
    let KConst::Defn {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      ty,
      val,
      ..
    } = self.get_const(&id)?
    else {
      return Ok(false);
    };
    if !self.is_def_eq(&ty, &expected)? {
      return Ok(false);
    }
    let val_ty = self.infer(&val)?;
    if !self.is_def_eq(&val_ty, &ty)? {
      return Ok(false);
    }
    self.push_local(nat.clone());
    self.push_local(nat);
    let x = KExpr::var(1, M::meta_field(Name::anon()));
    let y = KExpr::var(0, M::meta_field(Name::anon()));
    let z = cnst(&p.nat_zero);
    let succ = |x| KExpr::app(cnst(&p.nat_succ), x);
    let ap = |id: &KId<M>, a, b| KExpr::app(KExpr::app(cnst(id), a), b);
    let own = |a, b| ap(&id, a, b);
    let unary = |a| KExpr::app(cnst(&id), a);
    let t = cnst(&p.bool_true);
    let f = cnst(&p.bool_false);
    let equations = match rule {
      Rule::Pred => vec![(unary(z.clone()), z), (unary(succ(x.clone())), x)],
      Rule::Add => vec![
        (own(x.clone(), z), x.clone()),
        (own(x.clone(), succ(y.clone())), succ(own(x, y))),
      ],
      Rule::Sub => vec![
        (own(x.clone(), z), x.clone()),
        (
          own(x.clone(), succ(y.clone())),
          KExpr::app(cnst(&p.nat_pred), own(x, y)),
        ),
      ],
      Rule::Mul => vec![
        (own(x.clone(), z.clone()), z),
        (own(x.clone(), succ(y.clone())), ap(&p.nat_add, own(x.clone(), y), x)),
      ],
      Rule::Pow => vec![
        (own(x.clone(), z.clone()), succ(z)),
        (own(x.clone(), succ(y.clone())), ap(&p.nat_mul, own(x.clone(), y), x)),
      ],
      Rule::Beq => vec![
        (own(z.clone(), z.clone()), t),
        (own(z.clone(), succ(y.clone())), f.clone()),
        (own(succ(x.clone()), z), f),
        (own(succ(x.clone()), succ(y.clone())), own(x, y)),
      ],
      Rule::Ble => vec![
        (own(z.clone(), y.clone()), t),
        (own(succ(x.clone()), z), f),
        (own(succ(x.clone()), succ(y.clone())), own(x, y)),
      ],
      _ => unreachable!(),
    };
    for (a, b) in equations {
      if !self.is_def_eq(&a, &b)? {
        return Ok(false);
      }
    }
    Ok(true)
  }
}

#[cfg(test)]
mod tests;
