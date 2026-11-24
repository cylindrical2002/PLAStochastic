import PLAStochastic.Index.GEP.DirectTerm.DiscInterpolation
import PLAStochastic.Index.GEP.DirectTerm.OfRawDisc
import PLAStochastic.Index.GEP.RawDisc.OfSurvivalBound

/-!
# WP4 leaf `DirectTerm` from the survival bound

`discInterp` (`GEPDirectInterp`), `directTerm_of_rawDisc` (`GEPDirectReduction`) and
`rawDisc_of_survivalBound` (`GEPRawAssembly`) reduce the leaf `DirectTerm` to the fixed-disc
survival bound `SurvivalBound` (`GEPRawDefs`).
-/

namespace PGM

/-- **`DirectTerm` from the survival bound.** -/
theorem directTerm_of_survivalBound (hS : SurvivalBound) : DirectTerm :=
  directTerm_of_rawDisc discInterp (rawDisc_of_survivalBound hS)

end PGM
