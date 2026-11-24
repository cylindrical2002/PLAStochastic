import PLAStochastic.ForMathlib.Probability.LatticeConcentration.KolmogorovRogozin
import PLAStochastic.ForMathlib.Probability.LatticeConcentration.Kesten

/-!
# Kesten's lattice inequality, unconditionally

`PGM.kesten_lattice` proves Kesten's sharper concentration bound from the lattice
Kolmogorov–Rogozin inequality; `PGM.rogozinLattice` proves the latter with constant `6`.
Together: for iid integer variables with largest atom `p < 1`,
`sup_k P(S_n = k) · √(n (1 - p)) ≤ 224 p`.
-/

namespace PGM

open MeasureTheory

/-- **Kesten 1969, Theorem 2, iid lattice case.** -/
theorem kesten_iid {μ : Measure ℤ} [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n)
    (hp : lconc μ 1 < 1) :
    lconc (convFin n (fun _ => μ)) 1 * Real.sqrt (n * (1 - lconc μ 1)) ≤ 224 * lconc μ 1 := by
  have h := kesten_lattice rogozinLattice (by norm_num [CRog]) hn hp
  have e : KKes CRog = 224 := by norm_num [KKes, CRog]
  rwa [e] at h

end PGM
