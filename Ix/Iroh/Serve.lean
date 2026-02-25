module

public section

namespace Iroh.Serve

@[never_extract, extern "c_rs_iroh_serve"]
private opaque serve' : Unit → Except String Unit

def serve : IO Unit :=
  match serve' () with
  | .ok () => return
  | .error e => throw (IO.userError e)

end Iroh.Serve

end
