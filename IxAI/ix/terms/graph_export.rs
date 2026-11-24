//! Turn a term dump (`env_terms` output) into one graph shared by every
//! theorem statement, in which a bound variable carries its binder's type.
//!
//! ```text
//! graph_export DUMP-DIR OUT-DIR [--nary] [--all]
//! ```
//!
//! With `--all` the type of every constant is added, not only the statements
//! of theorems, so a definition's type can be encoded like a statement.
//!
//! Two occurrences are one node exactly when the sub-terms are equal and the
//! binders of their free variables have the same type node, so a node's
//! vector can be computed once and reused by every statement containing it.
//! Nodes are numbered in creation order: a node's children, and a variable's
//! binder type, always have smaller numbers.
//!
//! Files (little-endian):
//! * `gnodes.bin`: five `u32` per node, `tag x y z level`. Tags are those of
//!   the dump. A variable is `1 index binder-type-node 0`; an application
//!   `7 function argument 0`; a lambda or forall `8|9 domain body 0`; a let
//!   `10 type value body`; a projection `4 constant field value`; the other
//!   leaves keep the dump's fields. `level` is 0 for a leaf, one more than
//!   its binder type's for a variable, and one more than the largest child
//!   level otherwise. `u32::MAX` marks a missing node.
//!   With `--nary` an application and all its arguments are one node,
//!   `7 head first-argument-slot argument-count`, and `args.bin` holds the
//!   argument nodes of every application, in order, as `u32`. A partial
//!   application is a node of its own only where a term uses it as a value.
//! * `roots.bin`: one `u32` per constant of the dump, the node of a
//!   theorem's statement (with `--all`, of any constant's type) or `u32::MAX`.
//! * `stmt_ptr.bin` (`u64`, one more than the constants) and
//!   `stmt_nodes.bin` (`u32`): for each constant, the ascending list of the
//!   nodes its statement contains.
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::io::{BufRead, BufReader, BufWriter, Write};

#[derive(Default)]
struct Fx(u64);
impl Fx {
    fn add(&mut self, w: u64) {
        self.0 = (self.0.rotate_left(5) ^ w).wrapping_mul(0x517cc1b727220a95);
    }
}
impl Hasher for Fx {
    fn finish(&self) -> u64 { self.0 }
    fn write(&mut self, bytes: &[u8]) { for b in bytes { self.add(*b as u64); } }
    fn write_u32(&mut self, i: u32) { self.add(i as u64); }
    fn write_u64(&mut self, i: u64) { self.add(i); }
    fn write_usize(&mut self, i: usize) { self.add(i as u64); }
}
type Map<K, V> = HashMap<K, V, BuildHasherDefault<Fx>>;
const NONE: u32 = u32::MAX;

#[derive(Default)]
struct Graph {
    ids: Map<[u32; 4], u32>,
    nodes: Vec<[u32; 5]>,
    /// Applications with their arguments, keyed by head followed by arguments.
    apps: Map<Vec<u32>, u32>,
    args: Vec<u32>,
}
impl Graph {
    fn node(&mut self, key: [u32; 4], level: u32) -> u32 {
        if let Some(&id) = self.ids.get(&key) { return id; }
        let id = self.nodes.len() as u32;
        self.ids.insert(key, id);
        self.nodes.push([key[0], key[1], key[2], key[3], level]);
        id
    }
    fn level(&self, id: u32) -> u32 { if id == NONE { 0 } else { self.nodes[id as usize][4] } }
    fn app(&mut self, key: Vec<u32>) -> u32 {
        if let Some(&id) = self.apps.get(&key) { return id; }
        let level = 1 + key.iter().map(|x| self.level(*x)).max().unwrap_or(0);
        let id = self.nodes.len() as u32;
        self.nodes.push([7, key[0], self.args.len() as u32, key.len() as u32 - 1, level]);
        self.args.extend_from_slice(&key[1..]);
        self.apps.insert(key, id);
        id
    }
}

/// One statement being added to the graph.
struct Walk<'a> {
    local: &'a [[u32; 4]],
    /// Loose bound variable range of each local node.
    lbr: Vec<u32>,
    /// Graph node of a local node under the binder types its free variables see.
    memo: Map<(u32, u64), u32>,
    graph: &'a mut Graph,
    /// Type nodes of the enclosing binders, outermost first.
    env: Vec<u32>,
    nary: bool,
}
impl Walk<'_> {
    fn signature(&self, n: u32) -> u64 {
        let seen = (self.lbr[n as usize] as usize).min(self.env.len());
        if seen == 0 { return 0; }
        let mut h = Fx::default();
        for x in &self.env[self.env.len() - seen..] { h.add(*x as u64); }
        h.add(seen as u64);
        h.0 | 1
    }
    fn go(&mut self, n: u32) -> u32 {
        let key = (n, self.signature(n));
        if let Some(&id) = self.memo.get(&key) { return id; }
        let [t, a, b, c] = self.local[n as usize];
        let id = match t {
            1 => {
                let ty = if (a as usize) < self.env.len() { self.env[self.env.len() - 1 - a as usize] } else { NONE };
                let level = if ty == NONE { 0 } else { self.graph.level(ty) + 1 };
                self.graph.node([1, a, ty, 0], level)
            }
            7 if self.nary => {
                let mut spine = vec![b];
                let mut head = a;
                while self.local[head as usize][0] == 7 {
                    spine.push(self.local[head as usize][2]);
                    head = self.local[head as usize][1];
                }
                let mut key = vec![self.go(head)];
                for x in spine.into_iter().rev() { key.push(self.go(x)); }
                self.graph.app(key)
            }
            7 => {
                let (f, x) = (self.go(a), self.go(b));
                let level = 1 + self.graph.level(f).max(self.graph.level(x));
                self.graph.node([7, f, x, 0], level)
            }
            8 | 9 => {
                let dom = self.go(a);
                self.env.push(dom);
                let body = self.go(b);
                self.env.pop();
                let level = 1 + self.graph.level(dom).max(self.graph.level(body));
                self.graph.node([t, dom, body, 0], level)
            }
            10 => {
                let (ty, value) = (self.go(a), self.go(b));
                self.env.push(ty);
                let body = self.go(c);
                self.env.pop();
                let level = 1 + self.graph.level(ty).max(self.graph.level(value)).max(self.graph.level(body));
                self.graph.node([10, ty, value, body], level)
            }
            4 => {
                let value = self.go(c);
                let level = 1 + self.graph.level(value);
                self.graph.node([4, a, b, value], level)
            }
            _ => self.graph.node([t, a, b, c], 0),
        };
        self.memo.insert(key, id);
        id
    }
}

fn run() -> std::io::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    let (dir, out) = (&args[1], &args[2]);
    let nary = args.iter().any(|a| a == "--nary");
    let all = args.iter().any(|a| a == "--all");
    std::fs::create_dir_all(out)?;
    let bytes = std::fs::read(format!("{dir}/nodes.bin"))?;
    let word = |i: usize| u32::from_le_bytes([bytes[4 * i], bytes[4 * i + 1], bytes[4 * i + 2], bytes[4 * i + 3]]);
    let mut graph = Graph::default();
    let mut roots: Vec<u32> = Vec::new();
    let mut ptr: Vec<u64> = vec![0];
    let mut stmt = BufWriter::new(std::fs::File::create(format!("{out}/stmt_nodes.bin"))?);
    let mut written = 0u64;
    for line in BufReader::new(std::fs::File::open(format!("{dir}/consts.tsv"))?).lines() {
        let line = line?;
        let f: Vec<&str> = line.split('\t').collect();
        let count: usize = f[9].parse().unwrap();
        if (f[2] != "thm" && !all) || count == 0 || f[10].starts_with('-') {
            roots.push(NONE);
            ptr.push(written);
            continue;
        }
        let start: usize = f[8].parse().unwrap();
        let root: u32 = f[10].parse().unwrap();
        let local: Vec<[u32; 4]> = (0..count)
            .map(|i| [word(4 * (start + i)), word(4 * (start + i) + 1), word(4 * (start + i) + 2), word(4 * (start + i) + 3)])
            .collect();
        let mut lbr: Vec<u32> = Vec::with_capacity(count);
        for &[t, a, b, c] in &local {
            let l = |x: u32| lbr[x as usize];
            lbr.push(match t {
                1 => a + 1,
                7 => l(a).max(l(b)),
                8 | 9 => l(a).max(l(b).saturating_sub(1)),
                10 => l(a).max(l(b)).max(l(c).saturating_sub(1)),
                4 => l(c),
                _ => 0,
            });
        }
        let mut walk = Walk { local: &local, lbr, memo: Map::default(), graph: &mut graph, env: Vec::new(), nary };
        roots.push(walk.go(root));
        let mut used: Vec<u32> = walk.memo.values().copied().collect();
        used.sort_unstable();
        used.dedup();
        for id in &used { stmt.write_all(&id.to_le_bytes())?; }
        written += used.len() as u64;
        ptr.push(written);
    }
    stmt.flush()?;
    let mut w = BufWriter::new(std::fs::File::create(format!("{out}/gnodes.bin"))?);
    for node in &graph.nodes { for x in node { w.write_all(&x.to_le_bytes())?; } }
    w.flush()?;
    if nary {
        let mut w = BufWriter::new(std::fs::File::create(format!("{out}/args.bin"))?);
        for x in &graph.args { w.write_all(&x.to_le_bytes())?; }
        w.flush()?;
    }
    let mut w = BufWriter::new(std::fs::File::create(format!("{out}/roots.bin"))?);
    for x in &roots { w.write_all(&x.to_le_bytes())?; }
    w.flush()?;
    let mut w = BufWriter::new(std::fs::File::create(format!("{out}/stmt_ptr.bin"))?);
    for x in &ptr { w.write_all(&x.to_le_bytes())?; }
    w.flush()?;
    let levels = graph.nodes.iter().map(|n| n[4]).max().unwrap_or(0);
    eprintln!("constants {}  graph nodes {}  statement entries {}  levels {}", roots.len(), graph.nodes.len(), written, levels + 1);
    if nary {
        let mut hist = [0u64; 12];
        for n in &graph.nodes { if n[0] == 7 { hist[(n[3] as usize).min(11)] += 1; } }
        eprintln!("applications {}  argument slots {}  by argument count (1..10, 11+): {:?}", graph.apps.len(), graph.args.len(), &hist[1..]);
        let mut by = vec![0u64; levels as usize + 1];
        for n in &graph.nodes { by[n[4] as usize] += 1; }
        let total = graph.nodes.len() as u64; let mut cum = 0u64;
        for (lv, c) in by.iter().enumerate() { cum += c; if cum * 100 >= total * 99 { eprintln!("99% of nodes within {} levels", lv + 1); break; } }
    }
    Ok(())
}

fn main() {
    std::thread::Builder::new().stack_size(4 << 30).spawn(run).unwrap().join().unwrap().unwrap();
}
