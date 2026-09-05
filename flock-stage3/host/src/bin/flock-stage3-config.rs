use flock_stage3_host::{
  FLOCK_UPSTREAM_REVISION, FlockConfigV1, STAGE3_TRANSCRIPT_DOMAIN,
};

fn main() {
  println!("flock_revision={FLOCK_UPSTREAM_REVISION}");
  println!("field=f128");
  println!("profile=fast128");
  println!("merkle_hash=blake3");
  println!("transcript=chained-blake3");
  println!(
    "transcript_domain={}",
    String::from_utf8_lossy(STAGE3_TRANSCRIPT_DOMAIN)
  );
  println!(
    "config_digest={}",
    blake3::Hash::from_bytes(FlockConfigV1.digest()).to_hex()
  );
}
