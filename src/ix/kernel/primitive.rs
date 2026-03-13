//! Primitive type and operation validation.
//!
//! Validates that known primitive types (Bool, Nat) and operations
//! (Nat.add, Nat.sub, etc.) have the expected shapes.
//!
//! Ported from Ix/Kernel2/Primitive.lean.

use crate::ix::address::Address;
use crate::ix::env::Name;

use super::error::TcError;
use super::tc::{TcResult, TypeChecker};
use super::types::{KConstantInfo, KExpr, KLevel, MetaMode, *};

impl<M: MetaMode> TypeChecker<'_, M> {
  // =====================================================================
  // Expression builders
  // =====================================================================

  fn nat_const(&self) -> Option<KExpr<M>> {
    Some(KExpr::cnst(
      self.prims.nat.clone()?,
      Vec::new(),
    ))
  }

  fn bool_const(&self) -> Option<KExpr<M>> {
    Some(KExpr::cnst(
      self.prims.bool_type.clone()?,
      Vec::new(),
    ))
  }

  fn true_const(&self) -> Option<KExpr<M>> {
    Some(KExpr::cnst(
      self.prims.bool_true.clone()?,
      Vec::new(),
    ))
  }

  fn false_const(&self) -> Option<KExpr<M>> {
    Some(KExpr::cnst(
      self.prims.bool_false.clone()?,
      Vec::new(),
    ))
  }

  fn zero_const(&self) -> Option<KExpr<M>> {
    Some(KExpr::cnst(
      self.prims.nat_zero.clone()?,
      Vec::new(),
    ))
  }

  fn char_const(&self) -> Option<KExpr<M>> {
    Some(KExpr::cnst(
      self.prims.char_type.clone()?,
      Vec::new(),
    ))
  }

  fn string_const(&self) -> Option<KExpr<M>> {
    Some(KExpr::cnst(
      self.prims.string.clone()?,
      Vec::new(),
    ))
  }

  fn list_char_const(&self) -> Option<KExpr<M>> {
    let list_id = self.prims.list.clone()?;
    let char_e = self.char_const()?;
    Some(KExpr::app(
      KExpr::cnst(
        list_id,
        vec![KLevel::zero()],
      ),
      char_e,
    ))
  }

  fn succ_app(&self, e: KExpr<M>) -> Option<KExpr<M>> {
    Some(KExpr::app(
      KExpr::cnst(
        self.prims.nat_succ.clone()?,
        Vec::new(),
      ),
      e,
    ))
  }

  fn pred_app(&self, e: KExpr<M>) -> Option<KExpr<M>> {
    Some(KExpr::app(
      KExpr::cnst(
        self.prims.nat_pred.clone()?,
        Vec::new(),
      ),
      e,
    ))
  }

  fn bin_app(
    &self,
    id: &MetaId<M>,
    a: KExpr<M>,
    b: KExpr<M>,
  ) -> KExpr<M> {
    KExpr::app(
      KExpr::app(
        KExpr::cnst(
          id.clone(),
          Vec::new(),
        ),
        a,
      ),
      b,
    )
  }

  fn add_app(&self, a: KExpr<M>, b: KExpr<M>) -> Option<KExpr<M>> {
    Some(self.bin_app(self.prims.nat_add.as_ref()?, a, b))
  }

  fn mul_app(&self, a: KExpr<M>, b: KExpr<M>) -> Option<KExpr<M>> {
    Some(self.bin_app(self.prims.nat_mul.as_ref()?, a, b))
  }

  fn div_app(&self, a: KExpr<M>, b: KExpr<M>) -> Option<KExpr<M>> {
    Some(self.bin_app(self.prims.nat_div.as_ref()?, a, b))
  }

  fn nat_bin_type(&self) -> Option<KExpr<M>> {
    let nat = self.nat_const()?;
    Some(KExpr::mk_arrow(
      nat.clone(),
      KExpr::mk_arrow(nat.clone(), nat),
    ))
  }

  fn nat_unary_type(&self) -> Option<KExpr<M>> {
    let nat = self.nat_const()?;
    Some(KExpr::mk_arrow(nat.clone(), nat))
  }

  fn nat_bin_bool_type(&self) -> Option<KExpr<M>> {
    let nat = self.nat_const()?;
    let bool_e = self.bool_const()?;
    Some(KExpr::mk_arrow(
      nat.clone(),
      KExpr::mk_arrow(nat, bool_e),
    ))
  }

  /// Wrap in one lambda over Nat and check isDefEq.
  fn defeq1(
    &mut self,
    a: KExpr<M>,
    b: KExpr<M>,
  ) -> TcResult<bool, M> {
    let nat = self
      .nat_const()
      .ok_or_else(|| self.prim_err("Nat not found"))?;
    let lam_a = KExpr::lam(
      nat.clone(),
      a,
      M::Field::<Name>::default(),
      M::Field::<BinderInfo>::default(),
    );
    let lam_b = KExpr::lam(
      nat,
      b,
      M::Field::<Name>::default(),
      M::Field::<BinderInfo>::default(),
    );
    let va = self.eval_in_ctx(&lam_a)?;
    let vb = self.eval_in_ctx(&lam_b)?;
    self.is_def_eq(&va, &vb)
  }

  /// Wrap in two lambdas over Nat and check isDefEq.
  fn defeq2(
    &mut self,
    a: KExpr<M>,
    b: KExpr<M>,
  ) -> TcResult<bool, M> {
    let nat = self
      .nat_const()
      .ok_or_else(|| self.prim_err("Nat not found"))?;
    let lam_a = KExpr::lam(
      nat.clone(),
      KExpr::lam(
        nat.clone(),
        a,
        M::Field::<Name>::default(),
        M::Field::<BinderInfo>::default(),
      ),
      M::Field::<Name>::default(),
      M::Field::<BinderInfo>::default(),
    );
    let lam_b = KExpr::lam(
      nat.clone(),
      KExpr::lam(
        nat,
        b,
        M::Field::<Name>::default(),
        M::Field::<BinderInfo>::default(),
      ),
      M::Field::<Name>::default(),
      M::Field::<BinderInfo>::default(),
    );
    let va = self.eval_in_ctx(&lam_a)?;
    let vb = self.eval_in_ctx(&lam_b)?;
    self.is_def_eq(&va, &vb)
  }

  fn prim_err(&self, msg: &str) -> TcError<M> {
    TcError::KernelException {
      msg: format!("primitive validation: {}", msg),
    }
  }

  fn prim_in_env(&self, p: &Option<MetaId<M>>) -> bool {
    p.as_ref().map_or(false, |id| self.env.contains_key(id))
  }

  fn check_defeq_expr(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> TcResult<bool, M> {
    let va = self.eval_in_ctx(a)?;
    let vb = self.eval_in_ctx(b)?;
    self.is_def_eq(&va, &vb)
  }

  // =====================================================================
  // Top-level dispatch
  // =====================================================================

  /// Validate a primitive type or operation, if applicable.
  pub fn validate_primitive(
    &mut self,
    addr: &Address,
  ) -> TcResult<(), M> {
    // Check if this is a known primitive inductive
    if Primitives::<M>::addr_matches(&self.prims.nat, addr)
      || Primitives::<M>::addr_matches(&self.prims.bool_type, addr)
    {
      return self.check_primitive_inductive(addr);
    }

    // Check if this is a known primitive definition
    self.check_primitive_def(addr)?;

    Ok(())
  }

  /// Validate quotient types (Eq, Quot, etc.).
  pub fn validate_quotient(&mut self) -> TcResult<(), M> {
    self.check_eq_type()?;
    self.check_quot_types()?;
    Ok(())
  }

  // =====================================================================
  // Primitive inductive validation (Bool, Nat)
  // =====================================================================

  fn check_primitive_inductive(
    &mut self,
    addr: &Address,
  ) -> TcResult<(), M> {
    let addr_id = self.env.get_id_by_addr(addr)
      .ok_or_else(|| self.prim_err("primitive inductive not found in environment"))?
      .clone();
    let ci = self.deref_const(&addr_id)?.clone();
    let iv = match &ci {
      KConstantInfo::Inductive(v) => v,
      _ => return Ok(()),
    };
    if iv.is_unsafe || iv.cv.num_levels != 0 || iv.num_params != 0 {
      return Ok(());
    }
    // Type should be Sort 1
    let sort1 = KExpr::sort(KLevel::succ(KLevel::zero()));
    if !self.check_defeq_expr(&iv.cv.typ, &sort1)? {
      return Ok(());
    }

    if Primitives::<M>::addr_matches(&self.prims.bool_type, addr) {
      if iv.ctors.len() != 2 {
        return Err(self
          .prim_err("Bool must have exactly 2 constructors"));
      }
      let bool_e = self
        .bool_const()
        .ok_or_else(|| self.prim_err("Bool not found"))?;
      for ctor_id in &iv.ctors {
        let ctor = self.deref_const(ctor_id)?.clone();
        if !self.check_defeq_expr(ctor.typ(), &bool_e)? {
          return Err(self
            .prim_err("Bool constructor has unexpected type"));
        }
      }
    }

    if Primitives::<M>::addr_matches(&self.prims.nat, addr) {
      if iv.ctors.len() != 2 {
        return Err(
          self.prim_err("Nat must have exactly 2 constructors")
        );
      }
      let nat_e = self
        .nat_const()
        .ok_or_else(|| self.prim_err("Nat not found"))?;
      let nat_unary = self
        .nat_unary_type()
        .ok_or_else(|| self.prim_err("can't build Nat→Nat"))?;
      for ctor_id in &iv.ctors {
        let ctor = self.deref_const(ctor_id)?.clone();
        if Primitives::<M>::addr_matches(&self.prims.nat_zero, &ctor_id.addr) {
          if !self.check_defeq_expr(ctor.typ(), &nat_e)? {
            return Err(
              self.prim_err("Nat.zero has unexpected type")
            );
          }
        } else if Primitives::<M>::addr_matches(&self.prims.nat_succ, &ctor_id.addr) {
          if !self.check_defeq_expr(ctor.typ(), &nat_unary)? {
            return Err(
              self.prim_err("Nat.succ has unexpected type")
            );
          }
        } else {
          return Err(self.prim_err("unexpected Nat constructor"));
        }
      }
    }

    Ok(())
  }

  // =====================================================================
  // Primitive definition validation
  // =====================================================================

  fn check_primitive_def(
    &mut self,
    addr: &Address,
  ) -> TcResult<(), M> {
    let addr_id = self.env.get_id_by_addr(addr)
      .ok_or_else(|| self.prim_err("primitive def not found in environment"))?
      .clone();
    let ci = self.deref_const(&addr_id)?.clone();
    let v = match &ci {
      KConstantInfo::Definition(d) => d,
      _ => return Ok(()),
    };

    // Check if this is a known primitive address
    let p = self.prims;
    let is_prim = [
      &p.nat_add,
      &p.nat_pred,
      &p.nat_sub,
      &p.nat_mul,
      &p.nat_pow,
      &p.nat_beq,
      &p.nat_ble,
      &p.nat_shift_left,
      &p.nat_shift_right,
      &p.nat_land,
      &p.nat_lor,
      &p.nat_xor,
      &p.nat_bitwise,
      &p.nat_mod,
      &p.nat_div,
      &p.nat_gcd,
      &p.char_mk,
    ]
    .iter()
    .any(|p| Primitives::<M>::addr_matches(p, addr));

    // String.ofList is prim only if distinct from String.mk
    let is_string_of_list = Primitives::<M>::addr_matches(&p.string_of_list, addr)
      && p.string_of_list.as_ref().map(|id| &id.addr) != p.string_mk.as_ref().map(|id| &id.addr);

    if !is_prim && !is_string_of_list {
      return Ok(());
    }

    let x = KExpr::bvar(0, M::Field::<Name>::default());
    let y = KExpr::bvar(1, M::Field::<Name>::default());

    // Nat.add
    if Primitives::<M>::addr_matches(&self.prims.nat_add, addr) {
      if !self.prim_in_env(&self.prims.nat) || v.cv.num_levels != 0 {
        return Err(self.prim_err("natAdd: missing Nat or bad numLevels"));
      }
      let expected = self.nat_bin_type().ok_or_else(|| self.prim_err("can't build type"))?;
      if !self.check_defeq_expr(&v.cv.typ, &expected)? {
        return Err(self.prim_err("natAdd: type mismatch"));
      }
      // Use the constant so try_reduce_nat_val step-case fires
      let add_const = KExpr::cnst(self.prims.nat_add.as_ref().unwrap().clone(), Vec::new());
      let add_v = |a: KExpr<M>, b: KExpr<M>| -> KExpr<M> {
        KExpr::app(KExpr::app(add_const.clone(), a), b)
      };
      let zero = self.zero_const().ok_or_else(|| self.prim_err("zero"))?;
      let succ_x = self.succ_app(x.clone()).ok_or_else(|| self.prim_err("succ"))?;
      let add_y_x = (self.add_app(y.clone(), x.clone())).ok_or_else(|| self.prim_err("add"))?;
      let succ_add = self.succ_app(add_y_x).ok_or_else(|| self.prim_err("succ"))?;
      if !self.defeq1(add_v(x.clone(), zero), x.clone())? {
        return Err(self.prim_err("natAdd: add x 0 ≠ x"));
      }
      if !self.defeq2(add_v(y.clone(), succ_x), succ_add)? {
        return Err(self.prim_err("natAdd: step check failed"));
      }
      return Ok(());
    }

    // Nat.pred
    if Primitives::<M>::addr_matches(&self.prims.nat_pred, addr) {
      if !self.prim_in_env(&self.prims.nat) || v.cv.num_levels != 0 {
        return Err(self.prim_err("natPred: missing Nat or bad numLevels"));
      }
      let expected = self.nat_unary_type().ok_or_else(|| self.prim_err("can't build type"))?;
      if !self.check_defeq_expr(&v.cv.typ, &expected)? {
        return Err(self.prim_err("natPred: type mismatch"));
      }
      // Use the constant so try_reduce_nat_val step-case fires
      let pred_const = KExpr::cnst(self.prims.nat_pred.as_ref().unwrap().clone(), Vec::new());
      let pred_v = |a: KExpr<M>| -> KExpr<M> {
        KExpr::app(pred_const.clone(), a)
      };
      let zero = self.zero_const().ok_or_else(|| self.prim_err("zero"))?;
      let succ_x = self.succ_app(x.clone()).ok_or_else(|| self.prim_err("succ"))?;
      if !self.check_defeq_expr(&pred_v(zero.clone()), &zero)? {
        return Err(self.prim_err("natPred: pred 0 ≠ 0"));
      }
      if !self.defeq1(pred_v(succ_x), x.clone())? {
        return Err(self.prim_err("natPred: pred (succ x) ≠ x"));
      }
      return Ok(());
    }

    // Nat.sub
    if Primitives::<M>::addr_matches(&self.prims.nat_sub, addr) {
      if !self.prim_in_env(&self.prims.nat_pred) || v.cv.num_levels != 0 {
        return Err(self.prim_err("natSub: missing natPred or bad numLevels"));
      }
      let expected = self.nat_bin_type().ok_or_else(|| self.prim_err("can't build type"))?;
      if !self.check_defeq_expr(&v.cv.typ, &expected)? {
        return Err(self.prim_err("natSub: type mismatch"));
      }
      // Use the constant so try_reduce_nat_val step-case fires
      let sub_const = KExpr::cnst(self.prims.nat_sub.as_ref().unwrap().clone(), Vec::new());
      let sub_v = |a: KExpr<M>, b: KExpr<M>| -> KExpr<M> {
        KExpr::app(KExpr::app(sub_const.clone(), a), b)
      };
      let zero = self.zero_const().ok_or_else(|| self.prim_err("zero"))?;
      let succ_x = self.succ_app(x.clone()).ok_or_else(|| self.prim_err("succ"))?;
      let sub_y_x = sub_v(y.clone(), x.clone());
      let pred_sub = self.pred_app(sub_y_x).ok_or_else(|| self.prim_err("pred"))?;
      if !self.defeq1(sub_v(x.clone(), zero), x.clone())? {
        return Err(self.prim_err("natSub: sub x 0 ≠ x"));
      }
      if !self.defeq2(sub_v(y.clone(), succ_x), pred_sub)? {
        return Err(self.prim_err("natSub: step check failed"));
      }
      return Ok(());
    }

    // Nat.mul
    if Primitives::<M>::addr_matches(&self.prims.nat_mul, addr) {
      if !self.prim_in_env(&self.prims.nat_add) || v.cv.num_levels != 0 {
        return Err(self.prim_err("natMul: missing natAdd or bad numLevels"));
      }
      let expected = self.nat_bin_type().ok_or_else(|| self.prim_err("can't build type"))?;
      if !self.check_defeq_expr(&v.cv.typ, &expected)? {
        return Err(self.prim_err("natMul: type mismatch"));
      }
      // Use the constant so try_reduce_nat_val step-case fires
      let mul_const = KExpr::cnst(self.prims.nat_mul.as_ref().unwrap().clone(), Vec::new());
      let mul_v = |a: KExpr<M>, b: KExpr<M>| -> KExpr<M> {
        KExpr::app(KExpr::app(mul_const.clone(), a), b)
      };
      let zero = self.zero_const().ok_or_else(|| self.prim_err("zero"))?;
      let succ_x = self.succ_app(x.clone()).ok_or_else(|| self.prim_err("succ"))?;
      let mul_y_x = mul_v(y.clone(), x.clone());
      let add_result = self.add_app(mul_y_x, y.clone()).ok_or_else(|| self.prim_err("add"))?;
      if !self.defeq1(mul_v(x.clone(), zero.clone()), zero)? {
        return Err(self.prim_err("natMul: mul x 0 ≠ 0"));
      }
      if !self.defeq2(mul_v(y.clone(), succ_x), add_result)? {
        return Err(self.prim_err("natMul: step check failed"));
      }
      return Ok(());
    }

    // Nat.pow
    if Primitives::<M>::addr_matches(&self.prims.nat_pow, addr) {
      if !self.prim_in_env(&self.prims.nat_mul) || v.cv.num_levels != 0 {
        return Err(self.prim_err("natPow: missing natMul or bad numLevels"));
      }
      let expected = self.nat_bin_type().ok_or_else(|| self.prim_err("can't build type"))?;
      if !self.check_defeq_expr(&v.cv.typ, &expected)? {
        return Err(self.prim_err("natPow: type mismatch"));
      }
      // Use the constant so try_reduce_nat_val step-case fires
      let pow_const = KExpr::cnst(self.prims.nat_pow.as_ref().unwrap().clone(), Vec::new());
      let pow_v = |a: KExpr<M>, b: KExpr<M>| -> KExpr<M> {
        KExpr::app(KExpr::app(pow_const.clone(), a), b)
      };
      let zero = self.zero_const().ok_or_else(|| self.prim_err("zero"))?;
      let one = self.succ_app(zero.clone()).ok_or_else(|| self.prim_err("succ"))?;
      let succ_x = self.succ_app(x.clone()).ok_or_else(|| self.prim_err("succ"))?;
      let pow_y_x = pow_v(y.clone(), x.clone());
      let mul_result = self.mul_app(pow_y_x, y.clone()).ok_or_else(|| self.prim_err("mul"))?;
      if !self.defeq1(pow_v(x.clone(), zero), one)? {
        return Err(self.prim_err("natPow: pow x 0 ≠ 1"));
      }
      if !self.defeq2(pow_v(y.clone(), succ_x), mul_result)? {
        return Err(self.prim_err("natPow: step check failed"));
      }
      return Ok(());
    }

    // Nat.beq
    if Primitives::<M>::addr_matches(&self.prims.nat_beq, addr) {
      if v.cv.num_levels != 0 {
        return Err(self.prim_err("natBeq: bad numLevels"));
      }
      let expected = self.nat_bin_bool_type().ok_or_else(|| self.prim_err("can't build type"))?;
      if !self.check_defeq_expr(&v.cv.typ, &expected)? {
        return Err(self.prim_err("natBeq: type mismatch"));
      }
      // Use the constant so try_reduce_nat_val step-case fires
      let beq_const = KExpr::cnst(self.prims.nat_beq.as_ref().unwrap().clone(), Vec::new());
      let beq_v = |a: KExpr<M>, b: KExpr<M>| -> KExpr<M> {
        KExpr::app(KExpr::app(beq_const.clone(), a), b)
      };
      let zero = self.zero_const().ok_or_else(|| self.prim_err("zero"))?;
      let tru = self.true_const().ok_or_else(|| self.prim_err("true"))?;
      let fal = self.false_const().ok_or_else(|| self.prim_err("false"))?;
      let succ_x = self.succ_app(x.clone()).ok_or_else(|| self.prim_err("succ"))?;
      let succ_y = self.succ_app(y.clone()).ok_or_else(|| self.prim_err("succ"))?;
      if !self.check_defeq_expr(&beq_v(zero.clone(), zero.clone()), &tru)? {
        return Err(self.prim_err("natBeq: beq 0 0 ≠ true"));
      }
      if !self.defeq1(beq_v(zero.clone(), succ_x.clone()), fal.clone())? {
        return Err(self.prim_err("natBeq: beq 0 (succ x) ≠ false"));
      }
      if !self.defeq1(beq_v(succ_x.clone(), zero.clone()), fal)? {
        return Err(self.prim_err("natBeq: beq (succ x) 0 ≠ false"));
      }
      if !self.defeq2(beq_v(succ_y, succ_x), beq_v(y.clone(), x.clone()))? {
        return Err(self.prim_err("natBeq: step check failed"));
      }
      return Ok(());
    }

    // Nat.ble
    if Primitives::<M>::addr_matches(&self.prims.nat_ble, addr) {
      if v.cv.num_levels != 0 {
        return Err(self.prim_err("natBle: bad numLevels"));
      }
      let expected = self.nat_bin_bool_type().ok_or_else(|| self.prim_err("can't build type"))?;
      if !self.check_defeq_expr(&v.cv.typ, &expected)? {
        return Err(self.prim_err("natBle: type mismatch"));
      }
      // Use the constant so try_reduce_nat_val step-case fires
      let ble_const = KExpr::cnst(self.prims.nat_ble.as_ref().unwrap().clone(), Vec::new());
      let ble_v = |a: KExpr<M>, b: KExpr<M>| -> KExpr<M> {
        KExpr::app(KExpr::app(ble_const.clone(), a), b)
      };
      let zero = self.zero_const().ok_or_else(|| self.prim_err("zero"))?;
      let tru = self.true_const().ok_or_else(|| self.prim_err("true"))?;
      let fal = self.false_const().ok_or_else(|| self.prim_err("false"))?;
      let succ_x = self.succ_app(x.clone()).ok_or_else(|| self.prim_err("succ"))?;
      let succ_y = self.succ_app(y.clone()).ok_or_else(|| self.prim_err("succ"))?;
      if !self.check_defeq_expr(&ble_v(zero.clone(), zero.clone()), &tru)? {
        return Err(self.prim_err("natBle: ble 0 0 ≠ true"));
      }
      if !self.defeq1(ble_v(zero.clone(), succ_x.clone()), tru.clone())? {
        return Err(self.prim_err("natBle: ble 0 (succ x) ≠ true"));
      }
      if !self.defeq1(ble_v(succ_x.clone(), zero.clone()), fal)? {
        return Err(self.prim_err("natBle: ble (succ x) 0 ≠ false"));
      }
      if !self.defeq2(ble_v(succ_y, succ_x), ble_v(y.clone(), x.clone()))? {
        return Err(self.prim_err("natBle: step check failed"));
      }
      return Ok(());
    }

    // Nat.shiftLeft
    if Primitives::<M>::addr_matches(&self.prims.nat_shift_left, addr) {
      if !self.prim_in_env(&self.prims.nat_mul) || v.cv.num_levels != 0 {
        return Err(self.prim_err("natShiftLeft: missing natMul or bad numLevels"));
      }
      let expected = self.nat_bin_type().ok_or_else(|| self.prim_err("can't build type"))?;
      if !self.check_defeq_expr(&v.cv.typ, &expected)? {
        return Err(self.prim_err("natShiftLeft: type mismatch"));
      }
      // Use the constant (not v.value) so try_reduce_nat_val step-case fires
      let shl_const = KExpr::cnst(self.prims.nat_shift_left.as_ref().unwrap().clone(), Vec::new());
      let shl_v = |a: KExpr<M>, b: KExpr<M>| -> KExpr<M> {
        KExpr::app(KExpr::app(shl_const.clone(), a), b)
      };
      let zero = self.zero_const().ok_or_else(|| self.prim_err("zero"))?;
      let one = self.succ_app(zero.clone()).ok_or_else(|| self.prim_err("succ"))?;
      let two = self.succ_app(one).ok_or_else(|| self.prim_err("succ"))?;
      let succ_y = self.succ_app(y.clone()).ok_or_else(|| self.prim_err("succ"))?;
      let mul_2_x = self.mul_app(two, x.clone()).ok_or_else(|| self.prim_err("mul"))?;
      if !self.defeq1(shl_v(x.clone(), zero), x.clone())? {
        return Err(self.prim_err("natShiftLeft: shl x 0 ≠ x"));
      }
      if !self.defeq2(shl_v(x.clone(), succ_y), shl_v(mul_2_x, y.clone()))? {
        return Err(self.prim_err("natShiftLeft: step check failed"));
      }
      return Ok(());
    }

    // Nat.shiftRight
    if Primitives::<M>::addr_matches(&self.prims.nat_shift_right, addr) {
      if !self.prim_in_env(&self.prims.nat_div) || v.cv.num_levels != 0 {
        return Err(self.prim_err("natShiftRight: missing natDiv or bad numLevels"));
      }
      let expected = self.nat_bin_type().ok_or_else(|| self.prim_err("can't build type"))?;
      if !self.check_defeq_expr(&v.cv.typ, &expected)? {
        return Err(self.prim_err("natShiftRight: type mismatch"));
      }
      // Use the constant (not v.value) so try_reduce_nat_val step-case fires
      let shr_const = KExpr::cnst(self.prims.nat_shift_right.as_ref().unwrap().clone(), Vec::new());
      let shr_v = |a: KExpr<M>, b: KExpr<M>| -> KExpr<M> {
        KExpr::app(KExpr::app(shr_const.clone(), a), b)
      };
      let zero = self.zero_const().ok_or_else(|| self.prim_err("zero"))?;
      let one = self.succ_app(zero.clone()).ok_or_else(|| self.prim_err("succ"))?;
      let two = self.succ_app(one).ok_or_else(|| self.prim_err("succ"))?;
      let succ_y = self.succ_app(y.clone()).ok_or_else(|| self.prim_err("succ"))?;
      let shr_x_y = shr_v(x.clone(), y.clone());
      let div_result = self.div_app(shr_x_y, two).ok_or_else(|| self.prim_err("div"))?;
      if !self.defeq1(shr_v(x.clone(), zero), x.clone())? {
        return Err(self.prim_err("natShiftRight: shr x 0 ≠ x"));
      }
      if !self.defeq2(shr_v(x.clone(), succ_y), div_result)? {
        return Err(self.prim_err("natShiftRight: step check failed"));
      }
      return Ok(());
    }

    // Nat.land
    if Primitives::<M>::addr_matches(&self.prims.nat_land, addr) {
      if !self.prim_in_env(&self.prims.nat_bitwise) || v.cv.num_levels != 0 {
        return Err(self.prim_err("natLand: missing natBitwise or bad numLevels"));
      }
      let expected = self.nat_bin_type().ok_or_else(|| self.prim_err("can't build type"))?;
      if !self.check_defeq_expr(&v.cv.typ, &expected)? {
        return Err(self.prim_err("natLand: type mismatch"));
      }
      // v.value must be (Nat.bitwise f)
      let (fn_head, fn_args) = v.value.get_app_args();
      if fn_args.len() != 1
        || !self.prims.nat_bitwise.as_ref().map_or(false, |id| fn_head.is_const_of(&id.addr))
      {
        return Err(self.prim_err("natLand: value must be Nat.bitwise applied to a function"));
      }
      let f = fn_args[0].clone();
      let and_f = |a: KExpr<M>, b: KExpr<M>| -> KExpr<M> {
        KExpr::app(KExpr::app(f.clone(), a), b)
      };
      let fal = self.false_const().ok_or_else(|| self.prim_err("false"))?;
      let tru = self.true_const().ok_or_else(|| self.prim_err("true"))?;
      if !self.defeq1(and_f(fal.clone(), x.clone()), fal.clone())? {
        return Err(self.prim_err("natLand: and false x ≠ false"));
      }
      if !self.defeq1(and_f(tru, x.clone()), x.clone())? {
        return Err(self.prim_err("natLand: and true x ≠ x"));
      }
      return Ok(());
    }

    // Nat.lor
    if Primitives::<M>::addr_matches(&self.prims.nat_lor, addr) {
      if !self.prim_in_env(&self.prims.nat_bitwise) || v.cv.num_levels != 0 {
        return Err(self.prim_err("natLor: missing natBitwise or bad numLevels"));
      }
      let expected = self.nat_bin_type().ok_or_else(|| self.prim_err("can't build type"))?;
      if !self.check_defeq_expr(&v.cv.typ, &expected)? {
        return Err(self.prim_err("natLor: type mismatch"));
      }
      let (fn_head, fn_args) = v.value.get_app_args();
      if fn_args.len() != 1
        || !self.prims.nat_bitwise.as_ref().map_or(false, |id| fn_head.is_const_of(&id.addr))
      {
        return Err(self.prim_err("natLor: value must be Nat.bitwise applied to a function"));
      }
      let f = fn_args[0].clone();
      let or_f = |a: KExpr<M>, b: KExpr<M>| -> KExpr<M> {
        KExpr::app(KExpr::app(f.clone(), a), b)
      };
      let fal = self.false_const().ok_or_else(|| self.prim_err("false"))?;
      let tru = self.true_const().ok_or_else(|| self.prim_err("true"))?;
      if !self.defeq1(or_f(fal, x.clone()), x.clone())? {
        return Err(self.prim_err("natLor: or false x ≠ x"));
      }
      if !self.defeq1(or_f(tru.clone(), x.clone()), tru)? {
        return Err(self.prim_err("natLor: or true x ≠ true"));
      }
      return Ok(());
    }

    // Nat.xor
    if Primitives::<M>::addr_matches(&self.prims.nat_xor, addr) {
      if !self.prim_in_env(&self.prims.nat_bitwise) || v.cv.num_levels != 0 {
        return Err(self.prim_err("natXor: missing natBitwise or bad numLevels"));
      }
      let expected = self.nat_bin_type().ok_or_else(|| self.prim_err("can't build type"))?;
      if !self.check_defeq_expr(&v.cv.typ, &expected)? {
        return Err(self.prim_err("natXor: type mismatch"));
      }
      let (fn_head, fn_args) = v.value.get_app_args();
      if fn_args.len() != 1
        || !self.prims.nat_bitwise.as_ref().map_or(false, |id| fn_head.is_const_of(&id.addr))
      {
        return Err(self.prim_err("natXor: value must be Nat.bitwise applied to a function"));
      }
      let f = fn_args[0].clone();
      let xor_f = |a: KExpr<M>, b: KExpr<M>| -> KExpr<M> {
        KExpr::app(KExpr::app(f.clone(), a), b)
      };
      let fal = self.false_const().ok_or_else(|| self.prim_err("false"))?;
      let tru = self.true_const().ok_or_else(|| self.prim_err("true"))?;
      if !self.check_defeq_expr(&xor_f(fal.clone(), fal.clone()), &fal)? {
        return Err(self.prim_err("natXor: xor false false ≠ false"));
      }
      if !self.check_defeq_expr(&xor_f(tru.clone(), fal.clone()), &tru)? {
        return Err(self.prim_err("natXor: xor true false ≠ true"));
      }
      if !self.check_defeq_expr(&xor_f(fal.clone(), tru.clone()), &tru)? {
        return Err(self.prim_err("natXor: xor false true ≠ true"));
      }
      if !self.check_defeq_expr(&xor_f(tru.clone(), tru), &fal)? {
        return Err(self.prim_err("natXor: xor true true ≠ false"));
      }
      return Ok(());
    }

    // Nat.mod
    if Primitives::<M>::addr_matches(&self.prims.nat_mod, addr) {
      if !self.prim_in_env(&self.prims.nat_sub) || v.cv.num_levels != 0 {
        return Err(self.prim_err("natMod: missing natSub or bad numLevels"));
      }
      let expected = self.nat_bin_type().ok_or_else(|| self.prim_err("can't build type"))?;
      if !self.check_defeq_expr(&v.cv.typ, &expected)? {
        return Err(self.prim_err("natMod: type mismatch"));
      }
      return Ok(());
    }

    // Nat.div
    if Primitives::<M>::addr_matches(&self.prims.nat_div, addr) {
      if !self.prim_in_env(&self.prims.nat_sub) || v.cv.num_levels != 0 {
        return Err(self.prim_err("natDiv: missing natSub or bad numLevels"));
      }
      let expected = self.nat_bin_type().ok_or_else(|| self.prim_err("can't build type"))?;
      if !self.check_defeq_expr(&v.cv.typ, &expected)? {
        return Err(self.prim_err("natDiv: type mismatch"));
      }
      return Ok(());
    }

    // Nat.gcd
    if Primitives::<M>::addr_matches(&self.prims.nat_gcd, addr) {
      if !self.prim_in_env(&self.prims.nat_mod) || v.cv.num_levels != 0 {
        return Err(self.prim_err("natGcd: missing natMod or bad numLevels"));
      }
      let expected = self.nat_bin_type().ok_or_else(|| self.prim_err("can't build type"))?;
      if !self.check_defeq_expr(&v.cv.typ, &expected)? {
        return Err(self.prim_err("natGcd: type mismatch"));
      }
      return Ok(());
    }

    // Nat.bitwise - just check type
    if Primitives::<M>::addr_matches(&self.prims.nat_bitwise, addr) {
      return Ok(());
    }

    // Char.mk
    if Primitives::<M>::addr_matches(&self.prims.char_mk, addr) {
      if v.cv.num_levels != 0 {
        return Err(self.prim_err("charMk: bad numLevels"));
      }
      let nat = self.nat_const().ok_or_else(|| self.prim_err("Nat not found"))?;
      let char_e = self.char_const().ok_or_else(|| self.prim_err("Char not found"))?;
      let expected = KExpr::mk_arrow(nat, char_e);
      if !self.check_defeq_expr(&v.cv.typ, &expected)? {
        return Err(self.prim_err("charMk: type mismatch"));
      }
      return Ok(());
    }

    // String.ofList
    if is_string_of_list {
      if v.cv.num_levels != 0 {
        return Err(self.prim_err("stringOfList: bad numLevels"));
      }
      let list_char = self.list_char_const().ok_or_else(|| self.prim_err("List Char not found"))?;
      let string_e = self.string_const().ok_or_else(|| self.prim_err("String not found"))?;
      let expected = KExpr::mk_arrow(list_char.clone(), string_e);
      if !self.check_defeq_expr(&v.cv.typ, &expected)? {
        return Err(self.prim_err("stringOfList: type mismatch"));
      }
      // Validate List.nil Char and List.cons Char types
      let char_e = self.char_const().ok_or_else(|| self.prim_err("Char"))?;
      let nil_char = KExpr::app(
        KExpr::cnst(
          self.prims.list_nil.clone().ok_or_else(|| self.prim_err("List.nil"))?,
          vec![KLevel::zero()],
        ),
        char_e.clone(),
      );
      let (_, nil_type) = self.infer(&nil_char)?;
      let nil_type_expr = self.quote(&nil_type, self.depth())?;
      if !self.check_defeq_expr(&nil_type_expr, &list_char)? {
        return Err(self.prim_err("stringOfList: List.nil Char type mismatch"));
      }
      let cons_char = KExpr::app(
        KExpr::cnst(
          self.prims.list_cons.clone().ok_or_else(|| self.prim_err("List.cons"))?,
          vec![KLevel::zero()],
        ),
        char_e.clone(),
      );
      let (_, cons_type) = self.infer(&cons_char)?;
      let cons_type_expr = self.quote(&cons_type, self.depth())?;
      let expected_cons_type = KExpr::mk_arrow(
        char_e,
        KExpr::mk_arrow(list_char.clone(), list_char),
      );
      if !self.check_defeq_expr(&cons_type_expr, &expected_cons_type)? {
        return Err(self.prim_err("stringOfList: List.cons Char type mismatch"));
      }
      return Ok(());
    }

    Ok(())
  }

  // =====================================================================
  // Quotient validation (Eq, Quot, Quot.mk, Quot.lift, Quot.ind)
  // =====================================================================

  fn check_eq_type(&mut self) -> TcResult<(), M> {
    let eq_id = self
      .prims
      .eq
      .as_ref()
      .ok_or_else(|| self.prim_err("Eq type not found"))?
      .clone();
    if !self.env.contains_key(&eq_id) {
      return Err(self.prim_err("Eq type not found in environment"));
    }
    let ci = self.deref_const(&eq_id)?.clone();
    let iv = match &ci {
      KConstantInfo::Inductive(v) => v,
      _ => return Err(self.prim_err("Eq is not an inductive")),
    };
    if iv.cv.num_levels != 1 {
      return Err(self.prim_err("Eq must have exactly 1 universe parameter"));
    }
    if iv.ctors.len() != 1 {
      return Err(self.prim_err("Eq must have exactly 1 constructor"));
    }
    // Expected: ∀ {α : Sort u}, α → α → Prop
    let u = KLevel::param(0, M::Field::<Name>::default());
    let sort_u = KExpr::sort(u.clone());
    let expected_eq_type = KExpr::forall_e(
      sort_u,
      KExpr::forall_e(
        KExpr::bvar(0, M::Field::<Name>::default()),
        KExpr::forall_e(
          KExpr::bvar(1, M::Field::<Name>::default()),
          KExpr::prop(),
          M::Field::<Name>::default(),
          M::Field::<BinderInfo>::default(),
        ),
        M::Field::<Name>::default(),
        M::Field::<BinderInfo>::default(),
      ),
      M::Field::<Name>::default(),
      M::Field::<BinderInfo>::default(),
    );
    if !self.check_defeq_expr(&ci.typ().clone(), &expected_eq_type)? {
      return Err(self.prim_err("Eq has unexpected type"));
    }

    // Validate Eq.refl
    let refl_id = self
      .prims
      .eq_refl
      .as_ref()
      .ok_or_else(|| self.prim_err("Eq.refl not found"))?
      .clone();
    if !self.env.contains_key(&refl_id) {
      return Err(self.prim_err("Eq.refl not found in environment"));
    }
    let refl = self.deref_const(&refl_id)?.clone();
    if refl.cv().num_levels != 1 {
      return Err(self.prim_err("Eq.refl must have exactly 1 universe parameter"));
    }
    let u = KLevel::param(0, M::Field::<Name>::default());
    let sort_u = KExpr::sort(u.clone());
    let eq_const = KExpr::cnst(
      eq_id,
      vec![u],
    );
    // Expected: ∀ {α : Sort u} (a : α), @Eq α a a
    let expected_refl_type = KExpr::forall_e(
      sort_u,
      KExpr::forall_e(
        KExpr::bvar(0, M::Field::<Name>::default()),
        KExpr::app(
          KExpr::app(
            KExpr::app(
              eq_const,
              KExpr::bvar(1, M::Field::<Name>::default()),
            ),
            KExpr::bvar(0, M::Field::<Name>::default()),
          ),
          KExpr::bvar(0, M::Field::<Name>::default()),
        ),
        M::Field::<Name>::default(),
        M::Field::<BinderInfo>::default(),
      ),
      M::Field::<Name>::default(),
      M::Field::<BinderInfo>::default(),
    );
    if !self.check_defeq_expr(&refl.typ().clone(), &expected_refl_type)? {
      return Err(self.prim_err("Eq.refl has unexpected type"));
    }

    Ok(())
  }

  fn check_quot_types(&mut self) -> TcResult<(), M> {
    let u = KLevel::param(0, M::Field::<Name>::default());
    let sort_u = KExpr::sort(u.clone());
    let d = M::Field::<Name>::default();
    let bi = M::Field::<BinderInfo>::default();
    let bv = |n: usize| KExpr::bvar(n, d.clone());

    // relType depth = ∀ (_ : bvar(depth)), ∀ (_ : bvar(depth+1)), Prop
    let rel_type = |depth: usize| -> KExpr<M> {
      KExpr::forall_e(
        bv(depth),
        KExpr::forall_e(bv(depth + 1), KExpr::prop(), d.clone(), bi.clone()),
        d.clone(),
        bi.clone(),
      )
    };

    // Quot
    if let Some(qt_id) = self.prims.quot_type.clone() {
      let ci = self.deref_const(&qt_id)?.clone();
      // Expected: ∀ {α : Sort u} (r : α → α → Prop), Sort u
      let expected = KExpr::forall_e(
        sort_u.clone(),
        KExpr::forall_e(
          rel_type(0),
          KExpr::sort(u.clone()),
          d.clone(),
          bi.clone(),
        ),
        d.clone(),
        bi.clone(),
      );
      if !self.check_defeq_expr(ci.typ(), &expected)? {
        return Err(self.prim_err("Quot type signature mismatch"));
      }
    }

    // Quot.mk
    if let Some(qc_id) = self.prims.quot_ctor.clone() {
      let ci = self.deref_const(&qc_id)?.clone();
      let qt_id = self.prims.quot_type.clone()
        .ok_or_else(|| self.prim_err("Quot type not found"))?;
      // Quot applied to bvar(2) and bvar(1)
      let quot_app = KExpr::app(
        KExpr::app(
          KExpr::cnst(qt_id, vec![u.clone()]),
          bv(2),
        ),
        bv(1),
      );
      // Expected: ∀ {α : Sort u} (r : α→α→Prop) (a : α), Quot r
      let expected = KExpr::forall_e(
        sort_u.clone(),
        KExpr::forall_e(
          rel_type(0),
          KExpr::forall_e(bv(1), quot_app, d.clone(), bi.clone()),
          d.clone(),
          bi.clone(),
        ),
        d.clone(),
        bi.clone(),
      );
      if !self.check_defeq_expr(ci.typ(), &expected)? {
        return Err(self.prim_err("Quot.mk type signature mismatch"));
      }
    }

    // Quot.lift
    if let Some(ql_id) = self.prims.quot_lift.clone() {
      let ci = self.deref_const(&ql_id)?.clone();
      if ci.cv().num_levels != 2 {
        return Err(self.prim_err("Quot.lift must have exactly 2 universe parameters"));
      }
      let v = KLevel::param(1, d.clone());
      let sort_v = KExpr::sort(v.clone());
      let qt_id = self.prims.quot_type.clone()
        .ok_or_else(|| self.prim_err("Quot type not found"))?;
      let eq_id = self.prims.eq.clone()
        .ok_or_else(|| self.prim_err("Eq type not found"))?;

      // f : α → β  (at depth where α = bvar(2), β = bvar(1))
      let f_type = KExpr::forall_e(bv(2), bv(1), d.clone(), bi.clone());
      // h : ∀ a b, r a b → f a = f b
      let h_type = KExpr::forall_e(
        bv(3),
        KExpr::forall_e(
          bv(4),
          KExpr::forall_e(
            KExpr::app(KExpr::app(bv(4), bv(1)), bv(0)),
            KExpr::app(
              KExpr::app(
                KExpr::app(
                  KExpr::cnst(eq_id, vec![v.clone()]),
                  bv(4),
                ),
                KExpr::app(bv(3), bv(2)),
              ),
              KExpr::app(bv(3), bv(1)),
            ),
            d.clone(),
            bi.clone(),
          ),
          d.clone(),
          bi.clone(),
        ),
        d.clone(),
        bi.clone(),
      );
      let q_type = KExpr::app(
        KExpr::app(
          KExpr::cnst(qt_id, vec![u.clone()]),
          bv(4),
        ),
        bv(3),
      );
      let expected = KExpr::forall_e(
        sort_u.clone(),
        KExpr::forall_e(
          rel_type(0),
          KExpr::forall_e(
            sort_v,
            KExpr::forall_e(
              f_type,
              KExpr::forall_e(
                h_type,
                KExpr::forall_e(q_type, bv(3), d.clone(), bi.clone()),
                d.clone(),
                bi.clone(),
              ),
              d.clone(),
              bi.clone(),
            ),
            d.clone(),
            bi.clone(),
          ),
          d.clone(),
          bi.clone(),
        ),
        d.clone(),
        bi.clone(),
      );
      if !self.check_defeq_expr(ci.typ(), &expected)? {
        return Err(self.prim_err("Quot.lift type signature mismatch"));
      }
    }

    // Quot.ind
    if let Some(qi_id) = self.prims.quot_ind.clone() {
      let ci = self.deref_const(&qi_id)?.clone();
      if ci.cv().num_levels != 1 {
        return Err(self.prim_err("Quot.ind must have exactly 1 universe parameter"));
      }
      let qt_id = self.prims.quot_type.clone()
        .ok_or_else(|| self.prim_err("Quot type not found"))?;
      let qc_id = self.prims.quot_ctor.clone()
        .ok_or_else(|| self.prim_err("Quot.mk not found"))?;

      let quot_at_depth2 = KExpr::app(
        KExpr::app(
          KExpr::cnst(qt_id.clone(), vec![u.clone()]),
          bv(1),
        ),
        bv(0),
      );
      let beta_type = KExpr::forall_e(
        quot_at_depth2.clone(),
        KExpr::prop(),
        d.clone(),
        bi.clone(),
      );
      // Quot.mk applied: Quot.mk α r a
      let quot_mk_a = KExpr::app(
        KExpr::app(
          KExpr::app(
            KExpr::cnst(qc_id, vec![u.clone()]),
            bv(3),
          ),
          bv(2),
        ),
        bv(0),
      );
      let h_type = KExpr::forall_e(
        bv(2),
        KExpr::app(bv(1), quot_mk_a),
        d.clone(),
        bi.clone(),
      );
      let q_type = KExpr::app(
        KExpr::app(
          KExpr::cnst(qt_id, vec![u.clone()]),
          bv(3),
        ),
        bv(2),
      );
      let expected = KExpr::forall_e(
        sort_u,
        KExpr::forall_e(
          rel_type(0),
          KExpr::forall_e(
            beta_type,
            KExpr::forall_e(
              h_type,
              KExpr::forall_e(
                q_type,
                KExpr::app(bv(2), bv(0)),
                d.clone(),
                bi.clone(),
              ),
              d.clone(),
              bi.clone(),
            ),
            d.clone(),
            bi.clone(),
          ),
          d.clone(),
          bi.clone(),
        ),
        d.clone(),
        bi.clone(),
      );
      if !self.check_defeq_expr(ci.typ(), &expected)? {
        return Err(self.prim_err("Quot.ind type signature mismatch"));
      }
    }

    Ok(())
  }
}
