import PLAStochastic.Affine.Moments.Anchored.Recurrence
import PLAStochastic.Affine.Moments.Optimal.AllOrders.Moments
import PLAStochastic.Affine.Moments.Optimal.FirstFourMoments

/-!
# B-MOM: Brownian lifetime moments

Every positive integer moment of the anchored and the optimal Brownian lifetime is read out
from a second-order coefficient-polynomial recurrence and finitely many odd zeta values. The
optimal variance and fourth central moment constants are also included.

## Main theorems

* `BrownianAffine.anchoredUnitLifetime_moment_eq_coeff_readout`
* `BrownianAffine.optimalUnitLifetime_moment_eq`
* `BrownianAffine.optimalUnitLifetime_variance_eq_constant`
* `BrownianAffine.optimalUnitLifetime_fourth_central_eq_constant`
-/
