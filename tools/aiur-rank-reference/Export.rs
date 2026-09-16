//! Optional oracle, compiled inside the unchanged pinned Aiur module tree.
use crate::{G, FxIndexMap, bytecode::{Toplevel, Function, FunctionLayout, Block, Ctrl, Op,
    Circuit, CallComponent}, gadgets::{AiurGadget, bytes2::Bytes2}};
use multi_stark::{expr::{Expr, RowOffset, Source}, lookup::Lookup,
    p3_field::{PrimeField64, PrimeCharacteristicRing}, p3_matrix::Matrix};
use serde_json::{Value, json};
use std::{fs, path::Path};

fn expression(expr: &Expr<G>) -> Value {
    match expr {
        Expr::Const(value) => json!(["constant", value.as_canonical_u64().to_string()]),
        Expr::Var(column) => json!([match (column.source, column.offset) {
            (Source::Main, RowOffset::Current) => "main",
            (Source::Main, RowOffset::Next) => "next",
            (Source::Preprocessed, RowOffset::Current) => "preprocessed",
            _ => panic!("unexpected variable source in rank fixture"),
        }, column.index]),
        Expr::IsTransition => json!(["transition"]),
        Expr::Add(left, right) => json!(["add", expression(left), expression(right)]),
        Expr::Sub(left, right) => json!(["sub", expression(left), expression(right)]),
        Expr::Mul(left, right) => json!(["mul", expression(left), expression(right)]),
        Expr::Neg(value) => json!(["neg", expression(value)]),
        _ => panic!("unexpected rank expression"),
    }
}

fn lookup(item: &Lookup<Expr<G>>) -> Value {
    json!({"multiplicity": expression(&item.multiplicity),
        "arguments": item.args.iter().map(expression).collect::<Vec<_>>()})
}

fn fixture(name: &str, parent_ranked: bool, child_ranked: bool, ordered: bool,
    legacy: bool, gated: bool) -> Value {
    let extras = if ordered { 3 } else if child_ranked { 1 } else { 0 };
    let parent_layout = FunctionLayout { input_size: 1, selectors: 1,
        auxiliaries: 2 + if parent_ranked { 3 } else { 0 } + extras,
        lookups: 2 + if parent_ranked { 3 } else { 0 } + if ordered { 3 } else { 0 } };
    let child_layout = FunctionLayout { input_size: 1, selectors: 1,
        auxiliaries: 1 + if child_ranked { 3 } else { 0 },
        lookups: 1 + if child_ranked { 3 } else { 0 } };
    let mut body = Block { ops: vec![Op::Call(1, vec![0], 1, false)],
        ctrl: Ctrl::Return(0, vec![1]) };
    if gated {
        let mut cases = FxIndexMap::default();
        cases.insert(G::ZERO, body);
        body = Block { ops: vec![], ctrl: Ctrl::Match(0, cases, None) };
    }
    let toplevel = Toplevel {
        functions: vec![
            Function { body, layout: parent_layout, entry: true, constrained: true },
            Function { body: Block { ops: vec![], ctrl: Ctrl::Return(0, vec![0]) },
                layout: child_layout, entry: false, constrained: true }],
        memory_sizes: vec![],
        circuits: vec![Circuit { members: vec![0], layout: parent_layout },
            Circuit { members: vec![1], layout: child_layout }],
        call_components: if legacy { vec![] } else { vec![
            CallComponent { order: 0, ranked: parent_ranked },
            CallComponent { order: if ordered { 0 } else { 1 }, ranked: child_ranked }] },
    };
    // Apply the same admission checks that precede AiurSystem construction.
    toplevel.checked_claim_shapes().unwrap();
    toplevel.validate_call_components().unwrap();
    toplevel.validate_row_counts().unwrap();
    let circuits: Vec<_> = (0..2).map(|index| {
        let (constraints, lookups) = toplevel.build_constraints(index);
        json!({"width": constraints.width,
            "selectors": [constraints.selectors.start, constraints.selectors.end],
            "zeros": constraints.zeros.iter().map(expression).collect::<Vec<_>>(),
            "lookups": lookups.iter().map(lookup).collect::<Vec<_>>()})
    }).collect();
    json!({"name": name, "circuits": circuits})
}

pub fn run(output: &Path) {
    fs::create_dir_all(output).unwrap();
    let table = Bytes2.preprocessed().unwrap();
    assert_eq!(table.width(), 11);
    assert_eq!(table.height(), 65536);
    let projection: Vec<u8> = table.values.chunks_exact(11).flat_map(|row|
        [u8::try_from(row[0].as_canonical_u64()).unwrap(),
         u8::try_from(row[1].as_canonical_u64()).unwrap()]).collect();
    fs::write(output.join("range-columns.bin"), projection).unwrap();
    let report = json!({
        "schema": "aiur-rank-air/1",
        "ix_revision": "a8c4d2d21eaf45ee9160bdd103dfbcefe31f7f03",
        "multi_stark_revision": "9a90612286625b6cec59516532d4501677cf468c",
        "range": {"main_width": Bytes2.main_width(), "preprocessed_width": table.width(),
            "height": table.height(), "projection_columns": [0, 1],
            "pull": lookup(&Bytes2.lookups()[7])},
        "fixtures": [
            fixture("legacy-ordered", true, true, true, true, false),
            fixture("ordered", true, true, true, false, false),
            fixture("bound", true, true, false, false, false),
            fixture("bound-unranked-parent", false, true, false, false, false),
            fixture("zero", true, false, false, false, false),
            fixture("gated-ordered", true, true, true, false, true),
        ]});
    fs::write(output.join("expected.json"), serde_json::to_string_pretty(&report).unwrap() + "\n").unwrap();
}
