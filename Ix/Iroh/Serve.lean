namespace Iroh.Serve

-- TODO: Calling the Rust directly works, but on error the error message get cut off and only the second half of it prints
@[never_extract, extern "rs_iroh_serve"]
private opaque serve' : Unit → Except String Unit

def serve : IO Unit :=
  match serve' () with
  | .ok () => return
  | .error e => throw (IO.userError e)

end Iroh.Serve
