use indexmap::IndexSet;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};
use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
    sync::{Arc, Mutex},
};

use crate::{
    cons_list::ConsList,
    ixon::{
        self, Axiom, DataValue, DefKind, Definition, Ixon, Metadata, Metadatum, Preresolved,
        Quotient, Recursor, Serialize, SourceInfo, Substring, Syntax,
        address::{Address, MetaAddress},
    },
    lean::nat::Nat,
    lean_env::{
        AxiomVal, ConstMap, ConstantInfo, ConstantVal, ConstructorVal, DataValue as LeanDataValue,
        DefinitionSafety, DefinitionVal, Expr, InductiveVal, Level, Literal, Name, OpaqueVal,
        QuotVal, RecursorRule, RecursorVal, ReducibilityHints, SourceInfo as LeanSourceInfo,
        Substring as LeanSubstring, Syntax as LeanSyntax, SyntaxPreresolved, TheoremVal,
        ref_graph::{NameSet, RefMap},
    },
};

/// The size of the SCC chunks in which parallel compilation will occur.
/// This constant regulates the maximum recursion depth that can happen
/// in the worst-case scenario when there's a linear dependency between SCCs.
const PAR_CHUNK_SIZE: usize = 1024;

pub fn compile(
    sccs: &RefMap,
    out_refs: &RefMap,
    const_map: &ConstMap,
) -> Result<FxHashMap<Arc<Name>, MetaAddress>, CompileError> {
    // The compilation process involves:
    // 1. Finding root SCCs (those with no external dependencies)
    // 2. Building a dependency DAG and sequencing it
    // 3. Compiling SCCs in parallel chunks from leaves to roots
    // 4. Collecting and validating the resulting data

    // Internal macro for safe access to SCC and dependency data.
    macro_rules! get {
        (SCC, $name:expr) => {
            sccs.get($name).expect("Missing SCC")
        };
        (DEPS, $name:expr) => {
            out_refs.get($name).expect("Missing dependencies")
        };
    }

    // Find root SCCs - those that no other SCC depends on.
    let mut roots: FxHashSet<_> = sccs.values().map(NameSetWrap).collect();
    for (name, deps) in out_refs {
        for dep in deps {
            let dep_scc = get!(SCC, dep);
            // Don't remove SCCs due to circular dependencies within the same SCC.
            if !dep_scc.contains(name) {
                roots.remove(&NameSetWrap(dep_scc));
            }
        }
    }

    // Build a sequenced DAG of SCCs with roots on the left and transitive
    // dependencies to the right, reached via DFS.
    let mut dag = IndexSet::with_capacity_and_hasher(sccs.len(), FxBuildHasher);
    for scc_wrap in roots {
        if dag.contains(&scc_wrap) {
            continue;
        }
        dag.insert(scc_wrap.clone());

        // Initiate the stack with the immediate children of the current SCC.
        let mut scc_stack = vec![];
        for name in scc_wrap.0 {
            for dep in get!(DEPS, name) {
                let dep_scc = get!(SCC, dep);
                if !dag.contains(&NameSetWrap(dep_scc)) {
                    scc_stack.push(dep_scc);
                }
            }
        }

        // Pop the last SCC from the stack, add it to the sequenced DAG and push
        // its unvisited children to the stack.
        while let Some(popped_scc) = scc_stack.pop() {
            dag.insert(NameSetWrap(popped_scc));
            for name in popped_scc {
                for dep in get!(DEPS, name) {
                    let dep_scc = get!(SCC, dep);
                    if !dag.contains(&NameSetWrap(dep_scc)) {
                        scc_stack.push(dep_scc);
                    }
                }
            }
        }
    }

    // Reverse the DAG so we process from leaves to roots.
    // This order enables efficient compilation with caching while avoiding the
    // recursion depth limit.
    let dag_rev: Vec<_> = dag.into_iter().rev().collect();

    // Pre-populate hash storage with mutexes for thread-safe updates.
    let mut hashes = HashMap::with_capacity_and_hasher(dag_rev.len(), FxBuildHasher);
    for scc in &dag_rev {
        hashes.insert(scc, Mutex::new(None));
    }

    // Compile SCCs in parallel chunks.
    dag_rev.chunks(PAR_CHUNK_SIZE).for_each(|sccs_chunk| {
        sccs_chunk.par_iter().for_each(|scc_wrap| {
            let _ = compile_scc(scc_wrap, sccs, const_map, &hashes);
        });
    });

    // Collect results and validate disjoint SCCs.
    let mut map = FxHashMap::default();
    for mutex in hashes.values() {
        let mutex_lock = mutex.lock().unwrap();
        let compile_result = mutex_lock.as_ref().expect("Missing computed hash");
        match compile_result {
            Err(err) => return Err(err.clone()),
            Ok(scc_hashes) => {
                for (name, hash) in scc_hashes.as_ref() {
                    // SCCs are disjoint so there should be no duplicates.
                    assert!(map.insert(name.clone(), hash.clone()).is_none());
                }
            }
        }
    }

    // Verify that we computed hashes for all nodes in the dependency graph.
    assert_eq!(map.len(), out_refs.len());
    Ok(map)
}

/// Wrapper for [`NameSet`] to provide concrete [`Hash`] and [`Eq`] implementations.
#[derive(PartialEq, Eq, Clone)]
struct NameSetWrap<'a>(&'a NameSet);

impl Hash for NameSetWrap<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for name in self.0 {
            name.get_hash().hash(state);
        }
    }
}

/// Thread-safe storage for computed hashes of SCCs.
///
/// This is a specialized hashmap where each value is protected by a mutex,
/// allowing concurrent access to different SCCs without contention.
type HashedEntries<'a> = FxHashMap<&'a NameSetWrap<'a>, Mutex<Option<CompileResult>>>;

type CompileResult = Result<Arc<FxHashMap<Arc<Name>, MetaAddress>>, CompileError>;

#[derive(Clone)]
pub struct CompileError;

fn compile_scc(
    scc_wrap: &NameSetWrap<'_>,
    sccs: &RefMap,
    const_map: &ConstMap,
    hashes: &HashedEntries<'_>,
) -> CompileResult {
    let mutex = hashes.get(scc_wrap).expect("Missing SCC");
    let scc = scc_wrap.0;

    // Lock the entire SCC.
    let mut mutex_lock = mutex.lock().unwrap();

    // Return cached result if already computed.
    if let Some(scc_hashes) = mutex_lock.as_ref() {
        return scc_hashes.clone();
    }

    let mut stt = CompileState::default();
    let mut hashes_map = HashMap::with_capacity_and_hasher(scc.len(), FxBuildHasher);
    let mut delayed_ctors = Vec::new();
    for constant_name in scc {
        let const_info = const_map.get(constant_name).expect("Missing constant");
        match const_info {
            ConstantInfo::DefnInfo(val) => {
                let base_def = BaseDef::mk_defn(val);
                let mut_const = LeanMutConst::Def(base_def);
                let (data_ixon, meta_ixon) =
                    compile_mutual(mut_const, scc, sccs, const_map, hashes, &mut stt)?;
                let data = store_ixon(&data_ixon);
                let meta = store_ixon(&meta_ixon);
                let addr = MetaAddress { data, meta };
                hashes_map.insert(constant_name.clone(), addr);
            }
            ConstantInfo::ThmInfo(val) => {
                let base_def = BaseDef::mk_theo(val);
                let mut_const = LeanMutConst::Def(base_def);
                let (data_ixon, meta_ixon) =
                    compile_mutual(mut_const, scc, sccs, const_map, hashes, &mut stt)?;
                let data = store_ixon(&data_ixon);
                let meta = store_ixon(&meta_ixon);
                let addr = MetaAddress { data, meta };
                hashes_map.insert(constant_name.clone(), addr);
            }
            ConstantInfo::OpaqueInfo(val) => {
                let base_def = BaseDef::mk_opaq(val);
                let mut_const = LeanMutConst::Def(base_def);
                let (data_ixon, meta_ixon) =
                    compile_mutual(mut_const, scc, sccs, const_map, hashes, &mut stt)?;
                let data = store_ixon(&data_ixon);
                let meta = store_ixon(&meta_ixon);
                let addr = MetaAddress { data, meta };
                hashes_map.insert(constant_name.clone(), addr);
            }
            ConstantInfo::InductInfo(val) => {
                let base_ind = BaseInd::mk(val, const_map)?;
                let mut_const = LeanMutConst::Ind(base_ind);
                let (data_ixon, meta_ixon) =
                    compile_mutual(mut_const, scc, sccs, const_map, hashes, &mut stt)?;
                let data = store_ixon(&data_ixon);
                let meta = store_ixon(&meta_ixon);
                let addr = MetaAddress { data, meta };
                hashes_map.insert(constant_name.clone(), addr);
            }
            ConstantInfo::RecInfo(val) => {
                let mut_const = LeanMutConst::Rec(val);
                let (data_ixon, meta_ixon) =
                    compile_mutual(mut_const, scc, sccs, const_map, hashes, &mut stt)?;
                let data = store_ixon(&data_ixon);
                let meta = store_ixon(&meta_ixon);
                let addr = MetaAddress { data, meta };
                hashes_map.insert(constant_name.clone(), addr);
            }
            ConstantInfo::CtorInfo(val) => delayed_ctors.push(val.constant_val.name.clone()),
            ConstantInfo::AxiomInfo(val) => {
                let AxiomVal {
                    constant_val,
                    is_unsafe,
                } = val;
                let ConstantVal {
                    name,
                    level_params,
                    typ,
                } = constant_val;
                let univ_ctx = ConsList::from_iterator(level_params.iter().cloned());
                let n = compile_name(name.clone(), &mut stt);
                let ls = level_params
                    .iter()
                    .map(|n| compile_name(n.clone(), &mut stt))
                    .collect();
                let MetaAddress {
                    data: data_t,
                    meta: meta_t,
                } = compile_expr(
                    typ,
                    univ_ctx,
                    ConsList::Nil,
                    sccs,
                    const_map,
                    hashes,
                    &mut stt,
                )?;
                let axiom = Axiom {
                    is_unsafe: *is_unsafe,
                    lvls: Nat::from_le_bytes(&level_params.len().to_le_bytes()),
                    typ: data_t,
                };
                let nodes = vec![
                    Metadatum::Link(n),
                    Metadatum::Links(ls),
                    Metadatum::Link(meta_t),
                ];
                let data_ixon = Ixon::Axio(axiom);
                let meta_ixon = Ixon::Meta(Metadata { nodes });
                let data = store_ixon(&data_ixon);
                let meta = store_ixon(&meta_ixon);
                let addr = MetaAddress { data, meta };
                hashes_map.insert(constant_name.clone(), addr);
            }
            ConstantInfo::QuotInfo(val) => {
                let QuotVal { constant_val, kind } = val;
                let ConstantVal {
                    name,
                    level_params,
                    typ,
                } = constant_val;
                let univ_ctx = ConsList::from_iterator(level_params.iter().cloned());
                let n = compile_name(name.clone(), &mut stt);
                let ls = level_params
                    .iter()
                    .map(|n| compile_name(n.clone(), &mut stt))
                    .collect();
                let MetaAddress {
                    data: data_t,
                    meta: meta_t,
                } = compile_expr(
                    typ,
                    univ_ctx,
                    ConsList::Nil,
                    sccs,
                    const_map,
                    hashes,
                    &mut stt,
                )?;
                let quot = Quotient {
                    kind: *kind,
                    lvls: Nat::from_le_bytes(&level_params.len().to_le_bytes()),
                    typ: data_t,
                };
                let nodes = vec![
                    Metadatum::Link(n),
                    Metadatum::Links(ls),
                    Metadatum::Link(meta_t),
                ];
                let data_ixon = Ixon::Quot(quot);
                let meta_ixon = Ixon::Meta(Metadata { nodes });
                let data = store_ixon(&data_ixon);
                let meta = store_ixon(&meta_ixon);
                let addr = MetaAddress { data, meta };
                hashes_map.insert(constant_name.clone(), addr);
            }
        }
    }

    for delayed_ctor in delayed_ctors {
        let addr = stt
            .ctors
            .remove(&delayed_ctor)
            .expect("Missing compiled ctor");
        hashes_map.insert(delayed_ctor, addr);
    }

    let hashes_arc = Arc::new(hashes_map);
    let compile_result = Ok(hashes_arc);

    // Cache and return the result
    *mutex_lock = Some(compile_result.clone());
    compile_result
}

fn compile_mutual<'a>(
    mutual: LeanMutConst<'a>,
    all: &NameSet,
    sccs: &RefMap,
    const_map: &ConstMap,
    hashes: &HashedEntries<'_>,
    stt: &mut CompileState,
) -> Result<(Ixon, Ixon), CompileError> {
    if all.len() == 1 && matches!(&mutual, LeanMutConst::Def(_) | LeanMutConst::Rec(_)) {
        match mutual {
            LeanMutConst::Def(base_def) => {
                let muts_ctx = ConsList::Nil.cons((base_def.name.clone(), Nat::ZERO));
                let (data, meta) =
                    compile_base_def(base_def, muts_ctx, sccs, const_map, hashes, stt)?;
                Ok((Ixon::Defn(data), Ixon::Meta(meta)))
            }
            LeanMutConst::Rec(rec) => {
                let muts_ctx = ConsList::Nil.cons((rec.constant_val.name.clone(), Nat::ZERO));
                let (data, meta) = compile_rec(rec, &muts_ctx, sccs, const_map, hashes, stt)?;
                Ok((Ixon::Recr(data), Ixon::Meta(meta)))
            }
            _ => unreachable!(),
        }
    } else {
        let mut consts = Vec::new();
        for name in all {
            let Some(const_info) = const_map.get(name) else {
                return Err(CompileError);
            };
            let mut_const = match const_info {
                ConstantInfo::InductInfo(val) => {
                    let base_ind = BaseInd::mk(val, const_map)?;
                    LeanMutConst::Ind(base_ind)
                }
                ConstantInfo::DefnInfo(val) => {
                    let base_def = BaseDef::mk_defn(val);
                    LeanMutConst::Def(base_def)
                }
                ConstantInfo::OpaqueInfo(val) => {
                    let base_def = BaseDef::mk_opaq(val);
                    LeanMutConst::Def(base_def)
                }
                ConstantInfo::ThmInfo(val) => {
                    let base_def = BaseDef::mk_theo(val);
                    LeanMutConst::Def(base_def)
                }
                ConstantInfo::RecInfo(val) => LeanMutConst::Rec(val),
                _ => continue,
            };
            consts.push(mut_const);
        }
        let consts_sorted = sort_consts(&consts);
        let mut_meta = consts_sorted
            .iter()
            .map(|m| m.iter().map(|c| compile_name(c.name(), stt)).collect())
            .collect();

        let muts_ctx: ConsList<(Arc<Name>, Nat)> = ConsList::Nil; // TODO

        let ctx = muts_ctx
            .iter()
            .map(|(n, i)| (compile_name(n.clone(), stt), store_nat(i)))
            .collect();

        let (data, metas) = compile_mut_consts(consts_sorted, muts_ctx)?;

        let metas_vec = metas.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
        let nodes = vec![
            Metadatum::Muts(mut_meta),
            Metadatum::Map(ctx),
            Metadatum::Map(metas_vec),
        ];

        #[expect(unused_variables)]
        let block_addr = MetaAddress {
            data: store_ixon(&data),
            meta: store_serialize(&Metadata { nodes }),
        };

        todo!()
    }
}

fn compile_mut_consts(
    _mut_consts: Vec<Vec<LeanMutConst<'_>>>,
    _muts_ctx: ConsList<(Arc<Name>, Nat)>,
) -> Result<(Ixon, FxHashMap<Address, Address>), CompileError> {
    todo!()
}

fn sort_consts<'a>(_consts: &[LeanMutConst<'_>]) -> Vec<Vec<LeanMutConst<'a>>> {
    todo!()
}

fn compile_base_def(
    base_def: BaseDef<'_>,
    muts_ctx: ConsList<(Arc<Name>, Nat)>,
    sccs: &RefMap,
    const_map: &ConstMap,
    hashes: &HashedEntries<'_>,
    stt: &mut CompileState,
) -> Result<(Definition, Metadata), CompileError> {
    let BaseDef {
        name,
        level_params,
        typ,
        kind,
        value,
        hints,
        safety,
        all,
    } = base_def;
    let univ_ctx = ConsList::from_iterator(level_params.iter().cloned());
    let n = compile_name(name.clone(), stt);
    let ls = level_params
        .iter()
        .map(|n| compile_name(n.clone(), stt))
        .collect();
    let MetaAddress {
        data: data_t,
        meta: meta_t,
    } = compile_expr(
        typ,
        univ_ctx.clone(),
        muts_ctx.clone(),
        sccs,
        const_map,
        hashes,
        stt,
    )?;
    let MetaAddress {
        data: data_v,
        meta: meta_v,
    } = compile_expr(value, univ_ctx, muts_ctx, sccs, const_map, hashes, stt)?;
    let all = all.iter().map(|n| compile_name(n.clone(), stt)).collect();
    let lvls = Nat::from_le_bytes(&level_params.len().to_le_bytes());
    let data = Definition {
        kind,
        safety,
        lvls,
        typ: data_t,
        value: data_v,
    };
    let nodes = vec![
        Metadatum::Link(n),
        Metadatum::Links(ls),
        Metadatum::Hints(hints),
        Metadatum::Link(meta_t),
        Metadatum::Link(meta_v),
        Metadatum::Links(all),
    ];
    Ok((data, Metadata { nodes }))
}

fn compile_rec(
    base_rec: BaseRec<'_>,
    muts_ctx: &ConsList<(Arc<Name>, Nat)>,
    sccs: &RefMap,
    const_map: &ConstMap,
    hashes: &HashedEntries<'_>,
    stt: &mut CompileState,
) -> Result<(Recursor, Metadata), CompileError> {
    let RecursorVal {
        constant_val,
        all,
        num_params,
        num_indices,
        num_motives,
        num_minors,
        rules,
        k,
        is_unsafe,
    } = base_rec;
    let ConstantVal {
        name,
        level_params,
        typ,
    } = constant_val;
    let univ_ctx = ConsList::from_iterator(level_params.iter().cloned());
    let n = compile_name(name.clone(), stt);
    let ls = level_params
        .iter()
        .map(|n| compile_name(n.clone(), stt))
        .collect();
    let MetaAddress {
        data: data_t,
        meta: meta_t,
    } = compile_expr(
        typ,
        univ_ctx.clone(),
        muts_ctx.clone(),
        sccs,
        const_map,
        hashes,
        stt,
    )?;
    let mut rules_ixon = Vec::with_capacity(rules.len());
    let mut rules_map = Vec::with_capacity(rules.len());
    for rule in rules {
        let (rule_ixon, pair) = compile_rule(
            rule,
            univ_ctx.clone(),
            muts_ctx.clone(),
            sccs,
            const_map,
            hashes,
            stt,
        )?;
        rules_ixon.push(rule_ixon);
        rules_map.push(pair);
    }
    let all = all.iter().map(|n| compile_name(n.clone(), stt)).collect();
    let lvls = Nat::from_le_bytes(&level_params.len().to_le_bytes());
    let data = Recursor {
        k: *k,
        is_unsafe: *is_unsafe,
        lvls,
        params: num_params.clone(),
        indices: num_indices.clone(),
        motives: num_motives.clone(),
        minors: num_minors.clone(),
        typ: data_t,
        rules: rules_ixon,
    };
    let nodes = vec![
        Metadatum::Link(n),
        Metadatum::Links(ls),
        Metadatum::Link(meta_t),
        Metadatum::Map(rules_map),
        Metadatum::Links(all),
    ];
    Ok((data, Metadata { nodes }))
}

fn compile_rule(
    rule: &RecursorRule,
    univ_ctx: ConsList<Arc<Name>>,
    muts_ctx: ConsList<(Arc<Name>, Nat)>,
    sccs: &RefMap,
    const_map: &ConstMap,
    hashes: &HashedEntries<'_>,
    stt: &mut CompileState,
) -> Result<(ixon::RecursorRule, (Address, Address)), CompileError> {
    let RecursorRule {
        ctor,
        n_fields,
        rhs,
    } = rule;
    let n = compile_name(ctor.clone(), stt);
    let MetaAddress {
        data: data_rhs,
        meta: meta_rhs,
    } = compile_expr(rhs, univ_ctx, muts_ctx, sccs, const_map, hashes, stt)?;
    let data = ixon::RecursorRule {
        fields: n_fields.clone(),
        rhs: data_rhs,
    };
    Ok((data, (n, meta_rhs)))
}

enum LeanMutConst<'a> {
    Def(BaseDef<'a>),
    Ind(BaseInd<'a>),
    Rec(BaseRec<'a>),
}

impl<'a> LeanMutConst<'a> {
    fn name(&self) -> Arc<Name> {
        match self {
            Self::Def(x) => x.name.clone(),
            Self::Ind(x) => x.ind.constant_val.name.clone(),
            Self::Rec(x) => x.constant_val.name.clone(),
        }
    }
}

struct BaseDef<'a> {
    name: &'a Arc<Name>,
    level_params: &'a [Arc<Name>],
    typ: &'a Arc<Expr>,
    kind: DefKind,
    value: &'a Arc<Expr>,
    hints: ReducibilityHints,
    safety: DefinitionSafety,
    all: &'a [Arc<Name>],
}

impl<'a> BaseDef<'a> {
    fn mk_defn(val: &'a DefinitionVal) -> Self {
        let DefinitionVal {
            constant_val,
            value,
            hints,
            safety,
            all,
        } = val;
        Self {
            name: &constant_val.name,
            level_params: &constant_val.level_params,
            typ: &constant_val.typ,
            kind: DefKind::Definition,
            value,
            hints: *hints,
            safety: *safety,
            all,
        }
    }
    fn mk_theo(val: &'a TheoremVal) -> Self {
        let TheoremVal {
            constant_val,
            value,
            all,
        } = val;
        Self {
            name: &constant_val.name,
            level_params: &constant_val.level_params,
            typ: &constant_val.typ,
            kind: DefKind::Theorem,
            value,
            hints: ReducibilityHints::Opaque,
            safety: DefinitionSafety::Safe,
            all,
        }
    }
    fn mk_opaq(val: &'a OpaqueVal) -> Self {
        let OpaqueVal {
            constant_val,
            value,
            is_unsafe,
            all,
        } = val;
        Self {
            name: &constant_val.name,
            level_params: &constant_val.level_params,
            typ: &constant_val.typ,
            kind: DefKind::Opaque,
            value,
            hints: ReducibilityHints::Opaque,
            safety: if *is_unsafe {
                DefinitionSafety::Unsafe
            } else {
                DefinitionSafety::Safe
            },
            all,
        }
    }
}

#[expect(dead_code)]
struct BaseInd<'a> {
    ind: &'a InductiveVal,
    ctors: Vec<&'a ConstructorVal>,
}

impl<'a> BaseInd<'a> {
    fn mk(val: &'a InductiveVal, const_map: &'a ConstMap) -> Result<Self, CompileError> {
        let mut ctors = Vec::with_capacity(val.ctors.len());
        for ctor_name in &val.ctors {
            let Some(ConstantInfo::CtorInfo(c)) = const_map.get(ctor_name) else {
                return Err(CompileError);
            };
            ctors.push(c);
        }
        Ok(BaseInd { ind: val, ctors })
    }
}

type BaseRec<'a> = &'a RecursorVal;

#[derive(Default)]
#[allow(clippy::type_complexity)]
struct CompileState {
    expr_cache:
        FxHashMap<(ConsList<Arc<Name>>, ConsList<(Arc<Name>, Nat)>, Arc<Expr>), MetaAddress>,
    univ_cache: FxHashMap<(ConsList<Arc<Name>>, Arc<Level>), MetaAddress>,
    name_cache: FxHashMap<Arc<Name>, Address>,
    ctors: FxHashMap<Arc<Name>, MetaAddress>,
}

fn compile_expr(
    expr: &Arc<Expr>,
    univ_ctx: ConsList<Arc<Name>>,
    muts_ctx: ConsList<(Arc<Name>, Nat)>,
    sccs: &RefMap,
    const_map: &ConstMap,
    hashes: &HashedEntries<'_>,
    stt: &mut CompileState,
) -> Result<MetaAddress, CompileError> {
    let key = (univ_ctx.clone(), muts_ctx.clone(), expr.clone());
    if let Some(cached) = stt.expr_cache.get(&key) {
        return Ok(cached.clone());
    }

    #[expect(clippy::too_many_arguments)]
    fn go(
        kvs: &ConsList<Vec<(Arc<Name>, LeanDataValue)>>,
        expr: &Arc<Expr>,
        univ_ctx: ConsList<Arc<Name>>,
        muts_ctx: ConsList<(Arc<Name>, Nat)>,
        sccs: &RefMap,
        const_map: &ConstMap,
        hashes: &HashedEntries<'_>,
        stt: &mut CompileState,
    ) -> Result<(Ixon, Ixon), CompileError> {
        match expr.as_ref() {
            Expr::Mdata(kv, x, _) => go(
                &kvs.cons(kv.clone()),
                x,
                univ_ctx,
                muts_ctx,
                sccs,
                const_map,
                hashes,
                stt,
            ),
            Expr::Bvar(idx, _) => {
                let data = Ixon::EVar(idx.clone());
                let md = compile_kv_maps(kvs, stt);
                let nodes = vec![Metadatum::Link(md)];
                let meta = Ixon::Meta(Metadata { nodes });
                Ok((data, meta))
            }
            Expr::Sort(univ, _) => {
                let md = compile_kv_maps(kvs, stt);
                let MetaAddress {
                    data: udata,
                    meta: umeta,
                } = compile_level(univ, univ_ctx, stt)?;
                let data = Ixon::ESort(udata);
                let nodes = vec![Metadatum::Link(md), Metadatum::Link(umeta)];
                let meta = Ixon::Meta(Metadata { nodes });
                Ok((data, meta))
            }
            Expr::Const(name, lvls, _) => {
                let md = compile_kv_maps(kvs, stt);
                let n = compile_name(name.clone(), stt);
                let mut us_data = Vec::with_capacity(lvls.len());
                let mut us_meta = Vec::with_capacity(lvls.len());
                for u in lvls {
                    let MetaAddress { data, meta } = compile_level(u, univ_ctx.clone(), stt)?;
                    us_data.push(data);
                    us_meta.push(meta);
                }
                let mut mut_idx = None;
                for (mut_name, idx) in muts_ctx.iter() {
                    if name == mut_name {
                        mut_idx = Some(idx.clone());
                        break;
                    }
                }
                if let Some(idx) = mut_idx {
                    let data = Ixon::ERec(idx, us_data);
                    let nodes = vec![
                        Metadatum::Link(md),
                        Metadatum::Link(n),
                        Metadatum::Links(us_meta),
                    ];
                    let meta = Ixon::Meta(Metadata { nodes });
                    Ok((data, meta))
                } else {
                    let scc = sccs.get(name).expect("Missing SCC");
                    let scc_wrap = NameSetWrap(scc);
                    let scc_hashes = compile_scc(&scc_wrap, sccs, const_map, hashes)?;
                    let MetaAddress { data, meta } = scc_hashes.get(name).expect("Incomplete SCC");
                    let data = Ixon::ERef(data.clone(), us_data);
                    let nodes = vec![
                        Metadatum::Link(md),
                        Metadatum::Link(n),
                        Metadatum::Link(meta.clone()),
                        Metadatum::Links(us_meta),
                    ];
                    let meta = Ixon::Meta(Metadata { nodes });
                    Ok((data, meta))
                }
            }
            Expr::App(f, a, _) => {
                let md = compile_kv_maps(kvs, stt);
                let MetaAddress {
                    data: data_f,
                    meta: meta_f,
                } = compile_expr(
                    f,
                    univ_ctx.clone(),
                    muts_ctx.clone(),
                    sccs,
                    const_map,
                    hashes,
                    stt,
                )?;
                let MetaAddress {
                    data: data_a,
                    meta: meta_a,
                } = compile_expr(a, univ_ctx, muts_ctx, sccs, const_map, hashes, stt)?;
                let data = Ixon::EApp(data_f, data_a);
                let nodes = vec![
                    Metadatum::Link(md),
                    Metadatum::Link(meta_f),
                    Metadatum::Link(meta_a),
                ];
                Ok((data, Ixon::Meta(Metadata { nodes })))
            }
            Expr::Lam(n, t, b, i, _) => {
                let md = compile_kv_maps(kvs, stt);
                let n = compile_name(n.clone(), stt);
                let MetaAddress {
                    data: data_t,
                    meta: meta_t,
                } = compile_expr(
                    t,
                    univ_ctx.clone(),
                    muts_ctx.clone(),
                    sccs,
                    const_map,
                    hashes,
                    stt,
                )?;
                let MetaAddress {
                    data: data_b,
                    meta: meta_b,
                } = compile_expr(b, univ_ctx, muts_ctx, sccs, const_map, hashes, stt)?;
                let data = Ixon::ELam(data_t, data_b);
                let nodes = vec![
                    Metadatum::Link(md),
                    Metadatum::Link(n),
                    Metadatum::Info(i.clone()),
                    Metadatum::Link(meta_t),
                    Metadatum::Link(meta_b),
                ];
                Ok((data, Ixon::Meta(Metadata { nodes })))
            }
            Expr::ForallE(n, t, b, i, _) => {
                let md = compile_kv_maps(kvs, stt);
                let n = compile_name(n.clone(), stt);
                let MetaAddress {
                    data: data_t,
                    meta: meta_t,
                } = compile_expr(
                    t,
                    univ_ctx.clone(),
                    muts_ctx.clone(),
                    sccs,
                    const_map,
                    hashes,
                    stt,
                )?;
                let MetaAddress {
                    data: data_b,
                    meta: meta_b,
                } = compile_expr(b, univ_ctx, muts_ctx, sccs, const_map, hashes, stt)?;
                let data = Ixon::EAll(data_t, data_b);
                let nodes = vec![
                    Metadatum::Link(md),
                    Metadatum::Link(n),
                    Metadatum::Info(i.clone()),
                    Metadatum::Link(meta_t),
                    Metadatum::Link(meta_b),
                ];
                Ok((data, Ixon::Meta(Metadata { nodes })))
            }
            Expr::LetE(n, t, v, b, nd, _) => {
                let md = compile_kv_maps(kvs, stt);
                let n = compile_name(n.clone(), stt);
                let MetaAddress {
                    data: data_t,
                    meta: meta_t,
                } = compile_expr(
                    t,
                    univ_ctx.clone(),
                    muts_ctx.clone(),
                    sccs,
                    const_map,
                    hashes,
                    stt,
                )?;
                let MetaAddress {
                    data: data_v,
                    meta: meta_v,
                } = compile_expr(
                    v,
                    univ_ctx.clone(),
                    muts_ctx.clone(),
                    sccs,
                    const_map,
                    hashes,
                    stt,
                )?;
                let MetaAddress {
                    data: data_b,
                    meta: meta_b,
                } = compile_expr(b, univ_ctx, muts_ctx, sccs, const_map, hashes, stt)?;
                let data = Ixon::ELet(*nd, data_t, data_v, data_b);
                let nodes = vec![
                    Metadatum::Link(md),
                    Metadatum::Link(n),
                    Metadatum::Link(meta_t),
                    Metadatum::Link(meta_v),
                    Metadatum::Link(meta_b),
                ];
                Ok((data, Ixon::Meta(Metadata { nodes })))
            }
            Expr::Lit(Literal::NatVal(n), _) => {
                let md = compile_kv_maps(kvs, stt);
                let nodes = vec![Metadatum::Link(md)];
                Ok((Ixon::ENat(store_nat(n)), Ixon::Meta(Metadata { nodes })))
            }
            Expr::Lit(Literal::StrVal(s), _) => {
                let md = compile_kv_maps(kvs, stt);
                let nodes = vec![Metadatum::Link(md)];
                Ok((Ixon::ENat(store_string(s)), Ixon::Meta(Metadata { nodes })))
            }
            Expr::Proj(n, i, s, _) => {
                let md = compile_kv_maps(kvs, stt);
                let scc = sccs.get(n).expect("Missing SCC");
                let scc_wrap = NameSetWrap(scc);
                let scc_hashes = compile_scc(&scc_wrap, sccs, const_map, hashes)?;
                let MetaAddress {
                    data: data_t,
                    meta: meta_t,
                } = scc_hashes.get(n).expect("Incomplete SCC");
                let n = compile_name(n.clone(), stt);
                let MetaAddress {
                    data: data_s,
                    meta: meta_s,
                } = compile_expr(s, univ_ctx, muts_ctx, sccs, const_map, hashes, stt)?;
                let data = Ixon::EPrj(data_t.clone(), i.clone(), data_s);
                let nodes = vec![
                    Metadatum::Link(md),
                    Metadatum::Link(n),
                    Metadatum::Link(meta_t.clone()),
                    Metadatum::Link(meta_s),
                ];
                Ok((data, Ixon::Meta(Metadata { nodes })))
            }
            Expr::Fvar(..) | Expr::Mvar(..) => Err(CompileError),
        }
    }

    let (data_ixon, meta_ixon) = go(
        &ConsList::Nil,
        expr,
        univ_ctx,
        muts_ctx,
        sccs,
        const_map,
        hashes,
        stt,
    )?;
    let data = store_ixon(&data_ixon);
    let meta = store_ixon(&meta_ixon);
    let meta_address = MetaAddress { data, meta };
    stt.expr_cache.insert(key, meta_address.clone());
    Ok(meta_address)
}

fn compile_level(
    level: &Arc<Level>,
    univs: ConsList<Arc<Name>>,
    stt: &mut CompileState,
) -> Result<MetaAddress, CompileError> {
    let key = (univs.clone(), level.clone());
    if let Some(cached) = stt.univ_cache.get(&key) {
        return Ok(cached.clone());
    }

    fn go(
        level: &Level,
        univs: ConsList<Arc<Name>>,
        stt: &mut CompileState,
    ) -> Result<(Ixon, Ixon), CompileError> {
        match level {
            Level::Zero => Ok((Ixon::UZero, Ixon::Meta(Metadata::default()))),
            Level::Succ(x) => {
                let MetaAddress { data, meta } = compile_level(x, univs, stt)?;
                let nodes = vec![Metadatum::Link(meta)];
                Ok((Ixon::USucc(data), Ixon::Meta(Metadata { nodes })))
            }
            Level::Max(x, y) => {
                let MetaAddress {
                    data: data_x,
                    meta: meta_x,
                } = compile_level(x, univs.clone(), stt)?;
                let MetaAddress {
                    data: data_y,
                    meta: meta_y,
                } = compile_level(y, univs, stt)?;
                let nodes = vec![Metadatum::Link(meta_x), Metadatum::Link(meta_y)];
                Ok((Ixon::UMax(data_x, data_y), Ixon::Meta(Metadata { nodes })))
            }
            Level::Imax(x, y) => {
                let MetaAddress {
                    data: data_x,
                    meta: meta_x,
                } = compile_level(x, univs.clone(), stt)?;
                let MetaAddress {
                    data: data_y,
                    meta: meta_y,
                } = compile_level(y, univs, stt)?;
                let nodes = vec![Metadatum::Link(meta_x), Metadatum::Link(meta_y)];
                Ok((Ixon::UIMax(data_x, data_y), Ixon::Meta(Metadata { nodes })))
            }
            Level::Param(n) => match univs.index_of(n) {
                Some(i) => {
                    let data = Ixon::UVar(Nat::from_le_bytes(&i.to_le_bytes()));
                    let n_addr = compile_name(n.clone(), stt);
                    let nodes = vec![Metadatum::Link(n_addr)];
                    Ok((data, Ixon::Meta(Metadata { nodes })))
                }
                None => Err(CompileError),
            },
            Level::Mvar(_) => Err(CompileError),
        }
    }

    let (data_ixon, meta_ixon) = go(level, univs, stt)?;
    let data = store_ixon(&data_ixon);
    let meta = store_ixon(&meta_ixon);
    let meta_address = MetaAddress { data, meta };
    stt.univ_cache.insert(key, meta_address.clone());
    Ok(meta_address)
}

fn compile_kv_maps(
    maps: &ConsList<Vec<(Arc<Name>, LeanDataValue)>>,
    stt: &mut CompileState,
) -> Address {
    let nodes = maps
        .iter()
        .map(|kv_map| {
            let mut kv = Vec::with_capacity(kv_map.len());
            for (name, data_value) in kv_map {
                let n = compile_name(name.clone(), stt);
                let d = compile_data_value(data_value, stt);
                kv.push((n, d));
            }
            Metadatum::KVMap(kv)
        })
        .collect();
    store_ixon(&Ixon::Meta(Metadata { nodes }))
}

fn compile_data_value(data_value: &LeanDataValue, stt: &mut CompileState) -> DataValue {
    match data_value {
        LeanDataValue::OfString(s) => DataValue::OfString(store_string(s)),
        LeanDataValue::OfBool(b) => DataValue::OfBool(*b),
        LeanDataValue::OfName(n) => DataValue::OfName(compile_name(n.clone(), stt)),
        LeanDataValue::OfNat(i) => DataValue::OfNat(store_nat(i)),
        LeanDataValue::OfInt(i) => DataValue::OfInt(store_serialize(i)),
        LeanDataValue::OfSyntax(s) => DataValue::OfSyntax(store_serialize(&compile_syntax(s, stt))),
    }
}

fn compile_name(name: Arc<Name>, stt: &mut CompileState) -> Address {
    if let Some(cached) = stt.name_cache.get(&name) {
        return cached.clone();
    }

    let addr = match name.as_ref() {
        Name::Anonymous => store_ixon(&Ixon::NAnon),
        Name::Str(n, s, _) => {
            let n_ = compile_name(n.clone(), stt);
            let s_ = store_string(s);
            store_ixon(&Ixon::NStr(n_, s_))
        }
        Name::Num(n, i, _) => {
            let n_ = compile_name(n.clone(), stt);
            let s_ = store_nat(i);
            store_ixon(&Ixon::NNum(n_, s_))
        }
    };

    stt.name_cache.insert(name, addr.clone());
    addr
}

fn compile_syntax(syn: &LeanSyntax, stt: &mut CompileState) -> Syntax {
    match syn {
        LeanSyntax::Missing => Syntax::Missing,
        LeanSyntax::Node(info, kind, args) => {
            let info = compile_source_info(info);
            let kind = compile_name(kind.clone(), stt);
            let args = args
                .iter()
                .map(|s| store_serialize(&compile_syntax(s, stt)))
                .collect();
            Syntax::Node(info, kind, args)
        }
        LeanSyntax::Atom(info, val) => {
            let info = compile_source_info(info);
            let val = store_string(val);
            Syntax::Atom(info, val)
        }
        LeanSyntax::Ident(info, raw_val, val, preresolved) => {
            let info = compile_source_info(info);
            let raw_val = compile_substring(raw_val);
            let val = compile_name(val.clone(), stt);
            let preresolved = preresolved
                .iter()
                .map(|pre| compile_preresolved(pre, stt))
                .collect();
            Syntax::Ident(info, raw_val, val, preresolved)
        }
    }
}

fn compile_substring(substring: &LeanSubstring) -> Substring {
    let LeanSubstring {
        str,
        start_pos,
        stop_pos,
    } = substring;
    let str = store_string(str);
    Substring {
        str,
        start_pos: start_pos.clone(),
        stop_pos: stop_pos.clone(),
    }
}

fn compile_preresolved(preresolved: &SyntaxPreresolved, stt: &mut CompileState) -> Preresolved {
    match preresolved {
        SyntaxPreresolved::Namespace(ns) => Preresolved::Namespace(compile_name(ns.clone(), stt)),
        SyntaxPreresolved::Decl(n, fs) => {
            let fs = fs.iter().map(|s| store_string(s)).collect();
            Preresolved::Decl(compile_name(n.clone(), stt), fs)
        }
    }
}

fn compile_source_info(info: &LeanSourceInfo) -> SourceInfo {
    match info {
        LeanSourceInfo::Original(l, p, t, e) => {
            let l = compile_substring(l);
            let t = compile_substring(t);
            SourceInfo::Original(l, p.clone(), t, e.clone())
        }
        LeanSourceInfo::Synthetic(p, e, c) => SourceInfo::Synthetic(p.clone(), e.clone(), *c),
        LeanSourceInfo::None => SourceInfo::None,
    }
}

fn store_ixon(ixon: &Ixon) -> Address {
    let mut bytes = Vec::new();
    ixon.put(&mut bytes);
    let hash = blake3::hash(&bytes);
    Address { hash }
}

fn store_string(str: &str) -> Address {
    let hash = blake3::hash(str.as_bytes());
    Address { hash }
}

fn store_nat(nat: &Nat) -> Address {
    let hash = blake3::hash(&nat.to_le_bytes());
    Address { hash }
}

fn store_serialize<A: Serialize>(a: &A) -> Address {
    let mut bytes = Vec::new();
    a.put(&mut bytes);
    let hash = blake3::hash(&bytes);
    Address { hash }
}
