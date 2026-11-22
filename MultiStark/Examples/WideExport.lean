import MultiStark.Export.WideExport

/-! The `wide_export` executable; the exporter is `Aiur.Tiling.WideExport.main`. -/

def main (args : List String) : IO UInt32 := Aiur.Tiling.WideExport.main args
