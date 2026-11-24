import PLAStochastic.Index.KEP.Additive.OfReferenceCountTail
import PLAStochastic.Index.KEP.ReferenceScale.Recurrence
import PLAStochastic.Index.KEP.FiniteWindow.CountOutput
import PLAStochastic.ForMathlib.Probability.Hellinger.Censoring
import PLAStochastic.ForMathlib.Probability.Hellinger.StoppedChain
import PLAStochastic.Index.KEP.ReferenceScale.LawOrbit
import PLAStochastic.ForMathlib.Probability.Hellinger.DerivativeInterpolation
import PLAStochastic.Index.KEP.ReferenceScale.KernelSecond
import PLAStochastic.Index.KEP.ReferenceScale.GammaWeighted
import PLAStochastic.Index.KEP.ReferenceScale.KernelSlope
import PLAStochastic.Index.KEP.ReferenceScale.KernelWard
import PLAStochastic.Index.KEP.ReferenceScale.ActualBridgeSecond
import PLAStochastic.Index.KEP.ReferenceScale.ActualGraphSecondTransfer
import PLAStochastic.Index.KEP.ReferenceScale.ActualLongKernelSecond
import PLAStochastic.Index.KEP.ReferenceScale.ActualLongKernelSeries
import PLAStochastic.Index.KEP.ReferenceScale.KernelFirstDecay
import PLAStochastic.Index.KEP.ReferenceScale.ActualLongKernelQuantitative
import PLAStochastic.Index.KEP.ReferenceScale.ActualMixedFirstSeries
import PLAStochastic.Index.KEP.ReferenceScale.ActualMixedFirstDoubleSeries
import PLAStochastic.Index.KEP.ReferenceScale.ActualBoundaryMixedFirst
import PLAStochastic.Index.KEP.ReferenceScale.ActualScaleCriterion
import PLAStochastic.Index.KEP.ReferenceScale.ActualRecurrenceCriterion
import PLAStochastic.Index.KEP.ReferenceScale.OutputConvolutionSeries
import PLAStochastic.Index.KEP.ReferenceScale.SurvivingCore
import PLAStochastic.Index.KEP.ReferenceScale.CertificateCoefficients
import PLAStochastic.Index.KEP.ReferenceScale.ActualBridgeBudgets
import PLAStochastic.Index.KEP.ReferenceScale.TailPairFluxKilledBounds
import PLAStochastic.Index.KEP.ReferenceScale.LongSecondGraphKernel
import PLAStochastic.Index.KEP.ReferenceScale.SurvivingCoreBudget
import PLAStochastic.Index.KEP.ReferenceScale.MellinDerivativeBudget
import PLAStochastic.Index.KEP.ReferenceScale.CertificateRadial
import PLAStochastic.Index.KEP.ReferenceScale.InsertedNegativeMoments
import PLAStochastic.Index.KEP.ReferenceScale.RadialProductDerivatives
import PLAStochastic.Index.KEP.ReferenceScale.RadialPhysicalTransfer
import PLAStochastic.Index.KEP.ReferenceScale.InsertedChernoff
import PLAStochastic.Index.KEP.ReferenceScale.RarePathGeometry
import PLAStochastic.Index.KEP.ReferenceScale.RareNegativeBudget
import PLAStochastic.Index.KEP.ReferenceScale.ActualWeightedConeTransfer
import PLAStochastic.Index.KEP.ReferenceScale.InsertionVectorMomentBudget
import PLAStochastic.Index.KEP.CountRoute.ReferenceCount
import PLAStochastic.Index.KEP.CountRoute.WindowTail
import PLAStochastic.Index.KEP.CountRoute.WindowChoice

import PLAStochastic.Index.KEP.ReferenceScale.BoundedRareCertificateSeries
import PLAStochastic.Index.KEP.ReferenceScale.BoundedStoppedPrefixBudget
import PLAStochastic.Index.KEP.ReferenceScale.FixedScaleRareCertificateSeries
import PLAStochastic.Index.KEP.ReferenceScale.PhysicalOutputTests

import PLAStochastic.Index.KEP.ReferenceScale.GammaFourthRegularity
import PLAStochastic.Index.KEP.ReferenceScale.UnconditionalScale

import PLAStochastic.Index.KEP.Poisson.SuccessiveRestarts
import PLAStochastic.Index.KEP.Poisson.ChildScale
import PLAStochastic.Index.KEP.Poisson.ModelKCoordinates
import PLAStochastic.Index.KEP.CountRoute.LocalWindowChoice
import PLAStochastic.ForMathlib.Probability.Hellinger.KernelIterations
import PLAStochastic.Index.KEP.Poisson.ParentOutput
import PLAStochastic.Index.KEP.Poisson.ParentFiniteness
import PLAStochastic.Index.KEP.Poisson.WindowProbability
import PLAStochastic.Index.KEP.Additive.GeneralDensity

/-!
# Proved dependencies and unconditional general-density additive KEP theorem

This entry collects the actual-height count/tail reduction, Hellinger comparison
tools, uniform binomial--Poisson comparison through arbitrary Markov kernels,
actual exponential mean-scale budgets and positive Laplace smoothing calculus.
The actual positive reference layers also have finite classical derivative
norms at one fixed exponential weight and a polynomial first-layer budget.
Endpoint slope averages and the actual one-step slope derivatives are proved.
All finite killed bridges have proved translation and slope Ward identities,
with explicit internal pin sums. Their mixed and second slope identities apply
to the actual reference densities without additional analytic inputs.
Exterior tails include their terminal Dirac pin. Their weak transport and both
finite two-tail graph transfers are proved, including the full integrated pin
sum and identically vanishing ineffective pins. The complete finite graph and
original long surviving-core length series have uniform polynomial budgets.
The actual smooth reference density has layer-independent killed-band class data;
its long second-derivative kernel bound discharges the BV decomposition.
Its compact physical-slope average pays the first norm, bounded by a square root
of the second norm, while retaining the geometric remainder decay. The actual
long-kernel series has a quantitative polynomial epsilon budget under every fixed polynomial length weight at
one fixed positive physical exponent, chosen before epsilon and the layer.
Direct first derivatives also retain the killed spectral decay. The long first
derivative has a derivative-free regular part; mixed first-factor series retain
a square-root input second norm and an exponentially small linear remainder.
Both length indices of these three-step factors have a polynomial total budget;
a genuine one-step endpoint factor paired with a long factor has the same type
of bound, including both residual orientations and zero-tail boundary factors.
Weighted first-derivative interpolation and actual logarithmic derivative norms
give the measure-level two-thirds scale criterion in terms of the actual
weighted second norm, without additional analytic premises. These kernel
series now bound the entire original long surviving core; the complementary
rare paths and free cutoff are also paid by the full output assembly below.
The actual next reference law has an exact cutoff series of surviving and
stopped convolution prefixes, with absolute integral summability for every
bounded measurable test. Stopping integrability, independent insertion and
Fubini inputs are discharged. The original surviving certificate now has an exact
second graph transfer with a proved fixed smooth cutoff, and surviving prefixes
split into the long bridge graphs and their explicit complement. All positive
bridge lengths have actual first-derivative slope budgets retaining full killed
decay. All original core certificate pairs and prefix lengths are summed under
one fixed positive exponential weight. Actual Mellin insertions, radial cutoff
derivatives and inserted-coordinate negative moments have proved uniform costs.
Actual inserted proportion deviations and their second negative moments retain
exponential length decay. The physical second transfer now applies to the exact
multivariate iid law with the original rare cutoff and both true derivatives,
and discharges integrability and coordinate-face boundary inputs. The full original rare certificate series and short stopped prefix budgets are
proved at a stopping-scale exponential weight chosen before the input norm weight.
Actual inverse moments also pay tests through the origin and genuine bounded
convolution increments. The actual fixed-weight output recurrence is proved from these complete budgets,
using compact-test duality and the actual second-density integration by parts.
It closes a layer-uniform polynomial norm and two-thirds Hellinger scale budget,
including the exponential base layer, without analytical premises.
The count route reduces the actual layer-count input to the finite-sample window
quantile condition `KepWindowQuantile` at the reference scale, by window trials and
a deterministic suffix-window contraction on the sorted sample; the actual
early-termination tail input reduces to the window tail condition `KepWindowTail`
on the anchored canonical model, so the two window conditions alone give the
additive height for general Model K. The window bridge identifies the law of the
sorted-sample window configuration as a binomial count composed with the sorted
window kernel, compares it with the Poisson window model at Hellinger cost `p`, and
reads the censored block and span events on the finite sample, so both window
conditions follow from an exponential Poisson block tail `KepPoissonExpTail` and a
Poisson span quantile `KepPoissonSpanQuantile` on the Poisson window model alone.
The actual nonhomogeneous Poisson arrival transform, base Hellinger budget and
fixed exponential moment are proved uniformly in the anchor. The original layer
laws are measurable state kernels. Completed endpoint ranks preserve infinity,
and their natural stopping and fresh-innovation restart identities are proved.
Leading-block finiteness implies finiteness of every successive completed pivot.
The original intensity ratio pays the child scale error, and the exact kernel
Hellinger chain identity allows active-state and physical-moment budgets. A local
Poisson exponential tail, restricted to the comparison cutoff, suffices for the
existing height reduction. The original absorbing-prefix laws are identified with their state-kernel iterations.
Conditional child exponential moments pay all integer path moments. Actual window
survival bounds propagate through true completed restarts to geometric parent
stopping tails and parent leading-pivot finiteness. Active second moments are paid
by fourth moments and geometric block sums. The full stopped-path comparison and
its exact normalized parent-output readout are proved under these child moment
and window inputs. Their joint induction now pays a fixed exponential moment,
leading-block finiteness and a layer-uniform two-thirds comparison budget.
The actual arrival-window law, original finite-height readout, exponential
window tail and positive span quantile are proved. The imported general-density
theorem assembles these results at the original Model K signature, with no
remaining analytic or probabilistic premises.
-/
