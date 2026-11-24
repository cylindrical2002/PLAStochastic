import PLAStochastic.Index.CEPS.Canonical.MorseChart
import PLAStochastic.Index.CEPS.Canonical.LineSeparation
import PLAStochastic.Index.CEPS.Canonical.DomainExists
import PLAStochastic.Index.CEPS.Canonical.Factor
import PLAStochastic.Index.CEPS.Canonical.TransportLog
import PLAStochastic.Index.CEPS.Canonical.TransportL
import PLAStochastic.Index.CEPS.Canonical.TransportIdentity
import PLAStochastic.Index.CEPS.Canonical.LineDecay
import PLAStochastic.Index.CEPS.Canonical.TransportSobolev
import PLAStochastic.Index.CEPS.Canonical.MuJet
import PLAStochastic.Index.CEPS.Canonical.MuRegularity
import PLAStochastic.ForMathlib.Analysis.Complex.PartialDeriv
import PLAStochastic.ForMathlib.Analysis.Complex.LineIntegralHolo
import PLAStochastic.Index.CEPS.Canonical.MixedBounds

/-!
# CEPS WP3: canonical factor (aggregator)

Imports the WP3 modules (blueprint `research/2026-10-02-lean-ceps/blueprint-CS.md` §4.2,
lemmas C-1 … C-4). Progress and open items: `research/2026-10-02-lean-ceps/track-WP3.md`.
-/
