import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LargeDeviation
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LineShift
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.ExpRenewal

/-!
# Fluctuation theory of iid real random walks: Wiener–Hopf library

Aggregator of the `WienerHopf` subtree: ladder epochs and transforms (`Defs`), splitting and
time reversal of the iid path (`Markov`), coefficient identities (`Renewal`) and the
Wiener–Hopf factorization (`Factorization`, `Series`), exponential masses of ladder
heights (`LadderMass`), the factorization on a strip (`Strip`) with
holomorphy of the factors (`Holomorphic`), and ladder height laws and
densities with exponential envelopes (`LadderHeight`), a unit-interval bound for the pre-ladder
occupation measure (`Occupation`), with constants uniform over the gap-law class (`Uniform`) and
the centred step class (`StepClass`); discount `s = e^{-q}` and drifted steps (`Discount`);
fixed-drift large deviations (`LargeDeviation`); analytic tools for the complex renewal theorem
(`LineShift`, `Plancherel`, `ConvPow`, `RenewalSeries`, `LaplaceAnalytic`,
`LineInversion`) and the complex renewal theorem with an exponential remainder (`ExpRenewal`).
-/
