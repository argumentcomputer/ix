import MultiStark.Export.TilingExport2

/-! The `tiling_export2` executable; the exporter is `Aiur.Tiling.TilingExport2.main`. -/

def main (args : List String) : IO UInt32 := Aiur.Tiling.TilingExport2.main args
