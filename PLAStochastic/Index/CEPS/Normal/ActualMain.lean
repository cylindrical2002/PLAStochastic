import PLAStochastic.Index.CEPS.Normal.ActualHalfDiscHolomorphy
import PLAStochastic.Index.CEPS.Normal.ActualBridgeBound
import PLAStochastic.Index.CEPS.Normal.ActualEntranceBound
import PLAStochastic.Index.CEPS.Normal.ActualHalfLineIdentity
import PLAStochastic.Index.CEPS.Normal.NegativeDiscountOriginal
import PLAStochastic.Index.CEPS.Normal.ZeroMarkedPrimitiveLimit
import PLAStochastic.Index.CEPS.Normal.BottomDiscount

/-! # Canonical local normal forms for the actual step law

The original root-zone normal data, with `canonL`, have holomorphic regular
entrance and bridge throughout the radial interior of the discount half-disc.
A uniform class Delta lower bound is paid on the closed half-disc. Both simultaneous root and marker
collisions are handled by genuine divided differences. The large-width budget
is an explicit class constant. A uniform regular bridge bound retains the
root-merging inverse-width gain; the regular entrance has a quadratic
width bound for small markers with nonnegative real part. Both bounds
include all root/marker collisions. Actual marked and fixed-discount
half-line transport discharge the root and factor differential inputs
under the Sobolev class, away from merger and zero discount. A common negative-real extension of size C / l^2 is paid for the regular
forms. On a smaller strip all discount derivatives have explicit class
Cauchy bounds. The analytic extension includes negative square-root branch
cuts and all root/marker collisions. At positive drift, the actual marked
and unmarked half-line primitives have the same finite zero-discount limit
after removing their common simple pole. The derivative of that endpoint
is the actual regular half-line occupation pair under the Sobolev class.
The lower-end unmarked occupation entrance also has a genuine divided-
difference extension, a quadratic width bound and all discount derivative
bounds on the same common negative strip, including mergers and cuts.
-/
