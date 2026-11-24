import PLAStochastic.Index.CEPS.BrownianCoeff.Completion
import PLAStochastic.Index.CEPS.BrownianCoeff.Main
import PLAStochastic.Index.CEPS.Band.Main
import PLAStochastic.Index.CEPS.Band.ClassicalMain
import PLAStochastic.Index.CEPS.BandDisc.Main
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Esscher.Main
import PLAStochastic.Index.CEPS.Inversion.Main
import PLAStochastic.Index.CEPS.AssemblyOfInputs
import PLAStochastic.Index.CEPS.Leading.Limit
import PLAStochastic.Index.CEPS.Fluctuation.Basic
import PLAStochastic.Index.CEPS.Family.Reduction
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Main
import PLAStochastic.Index.CEPS.Output.Sobolev
import PLAStochastic.Index.CEPS.Canonical.Main
import PLAStochastic.Index.CEPS.Ident.Main
import PLAStochastic.Index.CEPS.Actual.Main
import PLAStochastic.Index.CEPS.Assembly.OneLayer
import PLAStochastic.Index.CEPS.Tails.Main
import PLAStochastic.Index.CEPS.Normal.Main
import PLAStochastic.Index.CEPS.Normal.ActualMain
import PLAStochastic.Index.CEPS.Scaled.Main
import PLAStochastic.Index.CEPS.Reward.Main
import PLAStochastic.Index.CEPS.Glue.Main
import PLAStochastic.Index.CEPS.ZeroOrder.Main
import PLAStochastic.Index.CEPS.Jets.Main
import PLAStochastic.Index.CEPS.Total.Main
import PLAStochastic.Index.CEPS.StripError.Main
import PLAStochastic.Index.CEPS.Contour.Main
import PLAStochastic.Index.CEPS.Final.Main
import PLAStochastic.Index.CEPS.Final.KernelJetFinal

/-!
# P-CEPS support modules: import aggregator

Every P-CEPS support module is imported here so that the package import closure stays
complete. The final theorem `PGM.gepC_asymptoticExpansion` is in `Final.Unconditional`
(public entry `PLAStochastic.Results.CEPS`); see `research/2026-10-02-lean-ceps/`.
-/
