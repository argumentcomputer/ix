// The Zisk memory-layout linker script (`zisk.ld`, vendored verbatim from
// 0xPolygonHermez/rust `compiler/rustc_target/src/spec/targets/
// riscv64ima_zisk_zkvm_elf_linker_script.ld`) defines `_global_pointer`,
// `_init_stack_top`, and the `_kernel_heap_*` symbols that `ziskos::_start`
// and its allocators reference. The zisk-1.0.0 toolchain release dropped the
// script embedded in the target spec, so the guest passes it explicitly;
// drop this (and `zisk.ld`) once a pinned toolchain ships it again.
fn main() {
  if std::env::var("TARGET").as_deref() == Ok("riscv64ima-zisk-zkvm-elf") {
    println!(
      "cargo:rustc-link-arg=-T{}/zisk.ld",
      std::env::var("CARGO_MANIFEST_DIR").unwrap()
    );
  }
  println!("cargo:rerun-if-changed=zisk.ld");
}
