import PLAStochastic.Affine.Process.Killed.Boundary.CrossGreen
import PLAStochastic.Brownian.Construction.ContinuousVersion

/-! Pure analytic boundary identities, discharged using the constructed Brownian law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The heat kernel is strictly positive at every pair of interior points. -/
theorem dirichletHeatKernel_strictlyPositive {r t x z : ℝ}
    (hr : 0 < r) (ht : 0 < t) (hx : x ∈ Ioo 0 r) (hz : z ∈ Ioo 0 r) :
    0 < dirichletHeatKernel r t x z :=
  dirichletHeatKernel_pos isBrownianReal_canonicalBrownian hr ht hx hz

theorem heatBoundaryLeft_strictlyPositive {r t x : ℝ}
    (hr : 0 < r) (ht : 0 < t) (hx : x ∈ Ioo 0 r) : 0 < heatBoundaryLeft r t x :=
  heatBoundaryLeft_pos isBrownianReal_canonicalBrownian hr ht hx

theorem heatBoundaryRight_strictlyPositive {r t x : ℝ}
    (hr : 0 < r) (ht : 0 < t) (hx : x ∈ Ioo 0 r) : 0 < heatBoundaryRight r t x :=
  heatBoundaryRight_pos isBrownianReal_canonicalBrownian hr ht hx

theorem heatCrossBoundary_strictlyPositive {r t : ℝ}
    (hr : 0 < r) (ht : 0 < t) : 0 < heatCrossBoundary r t :=
  heatCrossBoundary_pos isBrownianReal_canonicalBrownian hr ht

theorem integrableOn_laplace_heatBoundaryLeft {r k x : ℝ}
    (hr : 0 < r) (hk : 0 < k) (hx : x ∈ Ioo 0 r) :
    IntegrableOn (fun t => Real.exp (-(k^2/2)*t)*heatBoundaryLeft r t x) (Ioi 0) :=
  (laplace_heatBoundaryLeft_integrable_bound isBrownianReal_canonicalBrownian hr hk hx).1

theorem integrableOn_laplace_heatBoundaryRight {r k x : ℝ}
    (hr : 0 < r) (hk : 0 < k) (hx : x ∈ Ioo 0 r) :
    IntegrableOn (fun t => Real.exp (-(k^2/2)*t)*heatBoundaryRight r t x) (Ioi 0) :=
  (laplace_heatBoundaryRight_integrable_bound isBrownianReal_canonicalBrownian hr hk hx).1

theorem integrableOn_laplace_heatCrossBoundary {r k : ℝ}
    (hr : 0 < r) (hk : 0 < k) :
    IntegrableOn (fun t => Real.exp (-(k^2/2)*t)*heatCrossBoundary r t) (Ioi 0) :=
  (laplace_heatCrossBoundary_integrable_bound isBrownianReal_canonicalBrownian hr hk).1

theorem integral_laplace_heatBoundaryLeft_eq_sinh {r k x : ℝ}
    (hr : 0 < r) (hk : 0 < k) (hx : x ∈ Ioo 0 r) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(k^2/2)*t)*heatBoundaryLeft r t x) =
      2*Real.sinh (k*(r-x))/Real.sinh (k*r) :=
  integral_laplace_heatBoundaryLeft isBrownianReal_canonicalBrownian hr hk hx

theorem integral_laplace_heatBoundaryRight_eq_sinh {r k x : ℝ}
    (hr : 0 < r) (hk : 0 < k) (hx : x ∈ Ioo 0 r) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(k^2/2)*t)*heatBoundaryRight r t x) =
      2*Real.sinh (k*x)/Real.sinh (k*r) :=
  integral_laplace_heatBoundaryRight isBrownianReal_canonicalBrownian hr hk hx

theorem integral_laplace_heatCrossBoundary_eq_sinh {r k : ℝ}
    (hr : 0 < r) (hk : 0 < k) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(k^2/2)*t)*heatCrossBoundary r t) =
      2*k/Real.sinh (k*r) :=
  integral_laplace_heatCrossBoundary isBrownianReal_canonicalBrownian hr hk

end BrownianAffine
