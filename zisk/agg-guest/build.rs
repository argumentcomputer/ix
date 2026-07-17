// Same explicit linker script as the main guest — `ziskos::_start` needs the
// Zisk memory-layout symbols and the zisk-1.0.0 toolchain doesn't embed the
// script. Shares `zisk/guest/zisk.ld` so the layout can't drift between the
// two guests; see that guest's build.rs for details.
fn main() {
  if std::env::var("TARGET").as_deref() == Ok("riscv64ima-zisk-zkvm-elf") {
    println!(
      "cargo:rustc-link-arg=-T{}/../guest/zisk.ld",
      std::env::var("CARGO_MANIFEST_DIR").unwrap()
    );
  }
  println!("cargo:rerun-if-changed=../guest/zisk.ld");
}
