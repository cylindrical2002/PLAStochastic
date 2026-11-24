import PLAStochastic.Index.GEP.StrongApprox.Main
import PLAStochastic.Index.GEP.Universality.BrownianSide

/-! # WP5: the one-layer universality rate without auxiliary proof assumptions -/

namespace PGM

/-- The original one-layer universality specification, with its class-uniform
constants and rate `β = 17/32`. Strong approximation and the canonical
Brownian lifetime comparison are both proved in the main library. -/
theorem universality : GEPUniversality :=
  universality_of_SA strongApproxClass

end PGM
