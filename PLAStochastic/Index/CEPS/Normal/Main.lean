import PLAStochastic.Index.CEPS.Normal.PassageSystem
import PLAStochastic.Index.CEPS.Normal.WidthDerivative
import PLAStochastic.Index.CEPS.Normal.HalfLineTransport
import PLAStochastic.Index.CEPS.Normal.DiscountInvariant
import PLAStochastic.Index.CEPS.Normal.RootCompatibility
import PLAStochastic.Index.CEPS.Normal.DenominatorBound
import PLAStochastic.Index.CEPS.Normal.Removable
import PLAStochastic.Index.CEPS.Normal.SquaredHolomorphy

/-!
# X5: strip normal forms over an abstract factor

The package proves the normal two-passage system, width and difference
identities, root exchange, simultaneous divided-difference cancellation,
and local holomorphic extensions in the squared root coordinate. The latter
are derived from joint analytic factor/quotient data and a strict width budget.
The half-line total derivative follows from actual root equations, joint
factor differentials and transport on its nonzero root-slope/discount domain.

The factor is always an argument. There is no dependency on the unfinished
canonical-factor construction. Uniform actual Morse-quotient instantiation,
full-domain coarse bounds, and zero-discount endpoints of the half-line
transport theorem remain separate targets; see the X5 progress record.
-/
