//! Native single-constant check, mirroring the Zisk guest's reuse-mode path
//! (`zisk/guest/src/main.rs`): resolve a Lean NAME through the env's `named`
//! metadata to its ingress block, then `check_const` exactly that work item
//! with the lazy-anon TypeChecker. Exists so the kernel's `IX_*`
//! instrumentation (inert inside zkVM guests — see `src/lib.rs::env_var_os`)
//! can be pointed at one expensive constant without re-checking a whole env.
//!
//!   IX_PERF_COUNTERS=1 cargo run --release --example check_one -- \
//!     ~/ix/init.ixe '_private.Init.Data.Range.Polymorphic.SInt.0.Int16.instRxcHasSize_eq'

use std::env;
use std::fs;
use std::time::Instant;

use ix_kernel::anon_work::build_anon_work;
use ix_kernel::env::KEnv;
use ix_kernel::id::KId;
use ix_kernel::mode::Anon;
use ix_kernel::tc::TypeChecker;
use ixon::constant::ConstantInfo as CI;
use ixon::env::Env as IxonEnv;

fn main() {
  env_logger::builder()
    .filter_level(log::LevelFilter::Info)
    .format_timestamp(None)
    .init();
  let path = env::args().nth(1).expect("usage: check_one <ixe> <name>");
  let name = env::args().nth(2).expect("usage: check_one <ixe> <name>");
  let bytes = fs::read(&path).expect("read ixe");

  let t_parse = Instant::now();
  let env = IxonEnv::get(&mut &bytes[..]).expect("decode env");
  eprintln!("[check_one] parse:   {:>8.2?}", t_parse.elapsed());

  // Name → constant address → ingress block (mirrors zisk-host
  // `block_of_addr`): a projection's `block`, else the address itself.
  let addr = env
    .named
    .iter()
    .find(|e| e.key().pretty() == name || e.key().to_string() == name)
    .map_or_else(
      || panic!("no constant named {name:?} in {path}"),
      |e| e.value().addr.clone(),
    );
  let block = match env.get_const(&addr).map(|c| c.info.clone()) {
    Some(CI::IPrj(p)) => p.block,
    Some(CI::CPrj(p)) => p.block,
    Some(CI::RPrj(p)) => p.block,
    Some(CI::DPrj(p)) => p.block,
    _ => addr.clone(),
  };

  let work = build_anon_work(&env).expect("build_anon_work");
  let item =
    work.iter().find(|it| *it.primary() == block).expect("work item for block");

  let mut kenv = KEnv::<Anon>::new();
  let mut tc = TypeChecker::<Anon>::new_with_lazy_anon(&mut kenv, &env);
  let kid = KId::<Anon>::new(item.primary().clone(), ());
  let t_check = Instant::now();
  let result = tc.check_const(&kid);
  eprintln!(
    "[check_one] check:   {:>8.2?}  result: {:?}",
    t_check.elapsed(),
    result.is_ok()
  );
  if let Err(e) = result {
    eprintln!("[check_one] error: {e:?}");
    std::process::exit(1);
  }
}
