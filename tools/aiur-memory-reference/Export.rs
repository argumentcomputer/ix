//! Optional independent oracle: call the pinned Rust builder directly.
use aiur::{G, memory::Memory};
use multi_stark::{expr::{Expr, RowOffset, Source}, p3_field::PrimeField64};
use serde_json::{Value, json};

fn expression(expr: &Expr<G>) -> Value {
    match expr {
        Expr::Const(value) => json!(["constant", value.as_canonical_u64().to_string()]),
        Expr::Var(column) => {
            assert_eq!(column.source, Source::Main, "unexpected memory column source");
            json!([match column.offset { RowOffset::Current => "main", RowOffset::Next => "next" }, column.index])
        }
        Expr::IsTransition => json!(["transition"]),
        Expr::Add(left, right) => json!(["add", expression(left), expression(right)]),
        Expr::Sub(left, right) => json!(["sub", expression(left), expression(right)]),
        Expr::Mul(left, right) => json!(["mul", expression(left), expression(right)]),
        Expr::Neg(value) => json!(["neg", expression(value)]),
        _ => panic!("unexpected expression in the pinned memory builder"),
    }
}

fn main() {
    let circuits: Vec<Value> = [0_usize, 1, 2, 7, 256].into_iter().map(|bucket| {
        let (_, zeros, lookups) = Memory::build(bucket);
        json!({
            "bucket": bucket,
            "zeros": zeros.iter().map(expression).collect::<Vec<_>>(),
            "lookups": lookups.iter().map(|lookup| json!({
                "multiplicity": expression(&lookup.multiplicity),
                "arguments": lookup.args.iter().map(expression).collect::<Vec<_>>()
            })).collect::<Vec<_>>()
        })
    }).collect();
    println!("{}", serde_json::to_string_pretty(&json!({
        "schema": "aiur-memory-air/1",
        "ix_revision": "a8c4d2d21eaf45ee9160bdd103dfbcefe31f7f03",
        "multi_stark_revision": "9a90612286625b6cec59516532d4501677cf468c",
        "circuits": circuits
    })).unwrap());
}
