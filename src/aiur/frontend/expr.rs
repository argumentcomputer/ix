//! Aiur's frontend, which uses named references for variables and functions.

use std::fmt::Debug;

use rustc_hash::FxHashMap;

use crate::aiur::{
    execute::FxIndexMap,
    ir::{Block, Ctrl, FuncIdx, Function, Name, Op, Prim, SelIdx, Toplevel, ValIdx},
    layout::func_layout,
};

/// The type for variable references
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct Var {
    pub name: Ident,
    pub size: u32,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum Ident {
    User(&'static str),
    Internal(usize),
}

impl Var {
    pub fn atom(name: &'static str) -> Self {
        Self {
            name: Ident::User(name),
            size: 1,
        }
    }
}

impl std::fmt::Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.size == 1 {
            write!(f, "{}", self.name)
        } else {
            write!(f, "{}: [{}]", self.name, self.size)
        }
    }
}

impl std::fmt::Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ident::User(n) => write!(f, "{}", n),
            Ident::Internal(n) => write!(f, "${}", n),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VarVec(Vec<Var>);

impl VarVec {
    #[inline]
    pub fn total_size(&self) -> u32 {
        self.0.iter().map(|var| var.size).sum()
    }

    #[inline]
    pub fn as_slice(&self) -> &[Var] {
        &self.0
    }

    #[inline]
    pub fn iter(&self) -> core::slice::Iter<'_, Var> {
        self.as_slice().iter()
    }

    fn var_list_str(&self) -> String {
        self.iter()
            .map(|v| format!("{v}"))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

impl std::fmt::Display for VarVec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self.var_list_str();
        if self.as_slice().len() == 1 {
            write!(f, "{}", s)
        } else {
            write!(f, "({})", s)
        }
    }
}

impl<const N: usize> From<[Var; N]> for VarVec {
    fn from(value: [Var; N]) -> Self {
        Self(value.into())
    }
}

impl From<Vec<Var>> for VarVec {
    fn from(value: Vec<Var>) -> Self {
        Self(value)
    }
}

/// Interface for basic Aiur operations
#[allow(clippy::type_complexity)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OpE {
    Prim(Var, u64),
    Add(Var, Var, Var),
    Sub(Var, Var, Var),
    Mul(Var, Var, Var),
    Store(Var, VarVec),
    Load(VarVec, Var),
    Call(VarVec, Name, VarVec),
}

/// A "code block" containing a sequence of operators and a control node to be
/// executed afterwards
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BlockE {
    pub ops: Vec<OpE>,
    pub ctrl: CtrlE,
}

impl BlockE {
    #[inline]
    pub fn no_op(ctrl: CtrlE) -> Self {
        Self {
            ops: [].into(),
            ctrl,
        }
    }
}

/// Encodes the logical flow of a Aiur program
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CtrlE {
    If(Var, Box<BlockE>, Box<BlockE>),
    Return(VarVec),
}

impl CtrlE {
    #[inline]
    pub fn return_vars<const N: usize>(vars: [Var; N]) -> Self {
        Self::Return(vars.into())
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum CaseType {
    Constrained,
    Unconstrained,
}

/// Represents the cases for `CtrlE::Match`, containing the branches for successful
/// matches and an optional default case in case there's no match. Each code path
/// is encoded as its own block
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CasesE<K, B> {
    pub branches: Vec<(K, B)>,
    pub default: Option<Box<B>>,
}

impl<K, B> CasesE<K, B> {
    #[inline]
    pub fn no_default(branches: Vec<(K, B)>) -> Self {
        Self {
            branches,
            default: None,
        }
    }
}

/// Abstraction for a Aiur function, which has a name, the input variables, the
/// size (arity) of the output and, of course, its body (encoded as a block).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionE {
    pub name: Name,
    pub invertible: bool,
    pub partial: bool,
    pub input_params: VarVec,
    pub output_size: u32,
    pub body: BlockE,
}

impl OpE {
    pub fn pretty(&self) -> String {
        match self {
            OpE::Prim(x, c) => {
                format!("let {x} = {:?};", c)
            }
            OpE::Add(x, y, z) => {
                format!("let {x} = add({y}, {z});")
            }
            OpE::Sub(x, y, z) => {
                format!("let {x} = sub({y}, {z});")
            }
            OpE::Mul(x, y, z) => {
                format!("let {x} = mul({y}, {z});")
            }
            OpE::Call(xs, n, ys) => {
                format!("let {xs} = call({n}, {});", ys.var_list_str())
            }
            OpE::Store(x, ys) => {
                format!("let {x} = store({});", ys.var_list_str())
            }
            OpE::Load(xs, y) => {
                format!("let {xs} = load({y});")
            }
        }
    }
}

pub(crate) struct FuncInfo {
    input_size: u32,
    output_size: u32,
    partial: bool,
}

pub fn toplevel_from_funcs(func_exprs: &[FunctionE]) -> Toplevel {
    let info_map = func_exprs
        .iter()
        .map(|func| {
            let func_info = FuncInfo {
                input_size: func.input_params.total_size(),
                output_size: func.output_size,
                partial: func.partial,
            };
            (func.name, func_info)
        })
        .collect();
    let functions: Vec<_> = func_exprs
        .iter()
        .map(|func| {
            func.check(&info_map);
            func.compile(&info_map)
        })
        .collect();
    let mut mem_sizes = Vec::new();
    let layouts = functions
        .iter()
        .map(|f| func_layout(f, &mut mem_sizes))
        .collect();
    Toplevel {
        functions,
        layouts,
        mem_sizes,
    }
}

/// A map from `Var` its block identifier. Variables in this map are always bound
type BindMap = FxHashMap<Var, usize>;

/// A map that tells whether a `Var`, from a certain block, has been used or not
type UsedMap = FxHashMap<(Var, usize), bool>;

/// A map from `Var` to its compiled indices
type LinkMap = FxHashMap<Var, Vec<ValIdx>>;

impl Var {
    fn check_unused_var(&self, used: bool) {
        let Ident::User(name) = self.name else {
            unreachable!()
        };
        let ch = name.chars().next().expect("Empty var name");
        assert!(
            used || ch == '_',
            "Variable {self} not used. If intended, please prefix it with \"_\""
        );
    }
}

#[inline]
/// Binds a new variable. If a variable of the same name, in the same block, is shadowed,
/// then it ensures the variable has been used at least once or starts with '_'
fn bind_var(var: &Var, ctx: &mut CheckCtx<'_>) {
    ctx.bind_map.insert(*var, ctx.block_ident);
    if let Some(used) = ctx.used_map.insert((*var, ctx.block_ident), false) {
        var.check_unused_var(used)
    }
}

#[inline]
/// Marks a variable as used
fn use_var(var: &Var, ctx: &mut CheckCtx<'_>) {
    let block_idx = ctx
        .bind_map
        .get(var)
        .unwrap_or_else(|| panic!("Variable {var} is unbound."));
    let used = ctx
        .used_map
        .get_mut(&(*var, *block_idx))
        .expect("Data should have been inserted when binding");
    *used = true;
}

#[inline]
/// Links a variable name to a list of fresh indices
fn link_new(var: &Var, ctx: &mut LinkCtx<'_>) {
    let idxs = (0..var.size).map(|_| ctx.new_var()).collect();
    link(var, idxs, ctx);
}

#[inline]
/// Links a variable name to a given list of indices
fn link(var: &Var, idxs: Vec<ValIdx>, ctx: &mut LinkCtx<'_>) {
    ctx.link_map.insert(*var, idxs);
}

#[inline]
/// Retrieves the indices of a given variable
fn get_var<'a>(var: &Var, ctx: &'a mut LinkCtx<'_>) -> &'a [ValIdx] {
    ctx.link_map
        .get(var)
        .unwrap_or_else(|| panic!("Variable {var} is unbound."))
}

/// Context struct of `check`
struct CheckCtx<'a> {
    block_ident: usize,
    return_size: u32,
    partial: bool,
    bind_map: BindMap,
    used_map: UsedMap,
    info_map: &'a FxIndexMap<Name, FuncInfo>,
}

/// Context struct of `compile`
struct LinkCtx<'a> {
    var_index: ValIdx,
    return_ident: SelIdx,
    return_idents: Vec<SelIdx>,
    link_map: LinkMap,
    info_map: &'a FxIndexMap<Name, FuncInfo>,
}

impl CheckCtx<'_> {
    fn save_state(&mut self) -> BindMap {
        self.bind_map.clone()
    }

    fn restore_state(&mut self, bind_map: BindMap) {
        self.bind_map = bind_map;
    }
}

impl LinkCtx<'_> {
    fn save_state(&mut self) -> (ValIdx, LinkMap) {
        (self.var_index, self.link_map.clone())
    }

    fn restore_state(&mut self, (index, link_map): (ValIdx, LinkMap)) {
        self.var_index = index;
        self.link_map = link_map;
    }

    fn new_var(&mut self) -> ValIdx {
        let var = self.var_index;
        self.var_index.0 += 1;
        var
    }
}

impl FunctionE {
    /// Checks that a Aiur function is well formed
    fn check(&self, info_map: &FxIndexMap<Name, FuncInfo>) {
        let ctx = &mut CheckCtx {
            block_ident: 0,
            return_size: self.output_size,
            partial: self.partial,
            bind_map: FxHashMap::default(),
            used_map: FxHashMap::default(),
            info_map,
        };
        self.input_params.iter().for_each(|var| {
            bind_var(var, ctx);
        });
        self.body.check(ctx);
        for ((var, _), used) in ctx.used_map.iter() {
            var.check_unused_var(*used)
        }
    }

    /// Compile a Aiur function into bytecode
    fn compile(&self, info_map: &FxIndexMap<Name, FuncInfo>) -> Function {
        let ctx = &mut LinkCtx {
            var_index: ValIdx(0),
            return_ident: SelIdx(0),
            return_idents: vec![],
            link_map: FxHashMap::default(),
            info_map,
        };
        self.input_params.iter().for_each(|var| {
            link_new(var, ctx);
        });
        let body = self.body.compile(ctx);
        let input_size = self.input_params.total_size();
        let output_size = self.output_size;
        Function {
            name: self.name,
            body,
            input_size,
            output_size,
        }
    }
}

impl BlockE {
    fn check(&self, ctx: &mut CheckCtx<'_>) {
        self.ops.iter().for_each(|op| op.check(ctx));
        self.ctrl.check(ctx);
    }

    fn compile(&self, ctx: &mut LinkCtx<'_>) -> Block {
        let mut ops = vec![];
        self.ops.iter().for_each(|op| op.compile(&mut ops, ctx));
        let saved_return_idents = std::mem::take(&mut ctx.return_idents);
        let ctrl = self.ctrl.compile(ctx).into();
        let block_return_idents = std::mem::take(&mut ctx.return_idents);
        // sanity check
        assert!(
            !block_return_idents.is_empty(),
            "A block must have at least one return ident"
        );
        ctx.return_idents = saved_return_idents;
        ctx.return_idents.extend(&block_return_idents);
        Block {
            ops,
            ctrl,
            return_idents: block_return_idents,
        }
    }
}

impl CtrlE {
    fn check(&self, ctx: &mut CheckCtx<'_>) {
        match &self {
            CtrlE::Return(return_vars) => {
                let total_size = return_vars.total_size();
                assert_eq!(
                    total_size, ctx.return_size,
                    "Return size {} different from expected size of return {}",
                    total_size, ctx.return_size
                );
                return_vars.iter().for_each(|arg| use_var(arg, ctx));
            }
            CtrlE::If(b, true_block, false_block) => {
                use_var(b, ctx);

                let state = ctx.save_state();
                ctx.block_ident += 1;
                true_block.check(ctx);
                ctx.restore_state(state);

                let state = ctx.save_state();
                ctx.block_ident += 1;
                false_block.check(ctx);
                ctx.restore_state(state);
            }
        }
    }

    fn compile(&self, ctx: &mut LinkCtx<'_>) -> Ctrl {
        match &self {
            CtrlE::Return(return_vars) => {
                let return_vec = return_vars
                    .iter()
                    .flat_map(|arg| get_var(arg, ctx).to_vec())
                    .collect();
                let ctrl = Ctrl::Return(ctx.return_ident, return_vec);
                ctx.return_idents.push(ctx.return_ident);
                ctx.return_ident.0 += 1;
                ctrl
            }
            CtrlE::If(b, t, f) => {
                let b = get_var(b, ctx)[0];
                let state = ctx.save_state();
                let t = t.compile(ctx);
                ctx.restore_state(state);
                let state = ctx.save_state();
                let f = f.compile(ctx);
                ctx.restore_state(state);
                Ctrl::If(b, t, f)
            }
        }
    }
}

impl OpE {
    fn check(&self, ctx: &mut CheckCtx<'_>) {
        match self {
            OpE::Prim(tgt, _) => {
                assert_eq!(tgt.size, 1, "Var mismatch on `{}`", self.pretty());
                bind_var(tgt, ctx);
            }
            OpE::Add(tgt, a, b) | OpE::Mul(tgt, a, b) | OpE::Sub(tgt, a, b) => {
                assert_eq!(a.size, 1, "Var mismatch on `{}`", self.pretty());
                assert_eq!(b.size, 1, "Var mismatch on `{}`", self.pretty());
                assert_eq!(tgt.size, 1, "Var mismatch on `{}`", self.pretty());
                use_var(a, ctx);
                use_var(b, ctx);
                bind_var(tgt, ctx);
            }
            OpE::Call(out, name, inp) => {
                let info = ctx
                    .info_map
                    .get(name)
                    .unwrap_or_else(|| panic!("Unknown function {name}"));
                let FuncInfo {
                    input_size,
                    output_size,
                    partial,
                } = *info;
                if partial {
                    assert!(ctx.partial);
                }
                assert_eq!(
                    inp.total_size(),
                    input_size,
                    "Input mismatch on `{}`",
                    self.pretty()
                );
                assert_eq!(
                    out.total_size(),
                    output_size,
                    "Output mismatch on `{}`",
                    self.pretty()
                );
                inp.iter().for_each(|a| use_var(a, ctx));
                out.iter().for_each(|t| bind_var(t, ctx));
            }
            OpE::Store(ptr, vals) => {
                assert_eq!(ptr.size, 1, "Var mismatch on `{}`", self.pretty());
                vals.iter().for_each(|a| use_var(a, ctx));
                bind_var(ptr, ctx);
            }
            OpE::Load(vals, ptr) => {
                assert_eq!(ptr.size, 1, "Var mismatch on `{}`", self.pretty());
                use_var(ptr, ctx);
                vals.iter().for_each(|val| bind_var(val, ctx));
            }
        }
    }

    fn compile(&self, ops: &mut Vec<Op>, ctx: &mut LinkCtx<'_>) {
        match self {
            OpE::Prim(tgt, f) => {
                ops.push(Op::Prim(Prim::U64(*f)));
                link_new(tgt, ctx);
            }
            OpE::Add(tgt, a, b) => {
                let a = get_var(a, ctx)[0];
                let b = get_var(b, ctx)[0];
                ops.push(Op::Add(a, b));
                link_new(tgt, ctx);
            }
            OpE::Mul(tgt, a, b) => {
                let a = get_var(a, ctx)[0];
                let b = get_var(b, ctx)[0];
                ops.push(Op::Mul(a, b));
                link_new(tgt, ctx);
            }
            OpE::Sub(tgt, a, b) => {
                let a = get_var(a, ctx)[0];
                let b = get_var(b, ctx)[0];
                ops.push(Op::Sub(a, b));
                link_new(tgt, ctx);
            }
            OpE::Call(out, name, inp) => {
                let (idx, _, info) = ctx
                    .info_map
                    .get_full(name)
                    .unwrap_or_else(|| panic!("Unknown function {name}"));
                let name_idx = FuncIdx(idx.try_into().expect("Too many functions"));
                let inp = inp.iter().flat_map(|a| get_var(a, ctx).to_vec()).collect();
                ops.push(Op::Call(name_idx, inp, info.output_size));
                out.iter().for_each(|t| link_new(t, ctx));
            }
            OpE::Store(ptr, vals) => {
                let vals = vals.iter().flat_map(|a| get_var(a, ctx).to_vec()).collect();
                ops.push(Op::Store(vals));
                link_new(ptr, ctx);
            }
            OpE::Load(vals, ptr) => {
                let ptr = get_var(ptr, ctx)[0];
                ops.push(Op::Load(vals.total_size(), ptr));
                vals.iter().for_each(|val| link_new(val, ctx));
            }
        }
    }
}
