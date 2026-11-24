import PLAStochastic.Index.CEPS.Total.Discharge
import PLAStochastic.Index.CEPS.Total.Taylor
import PLAStochastic.Index.CEPS.Glue.MeanClose

/-! # Unconditional flat error between the actual mean and the fixed normal slope -/

noncomputable section
open MeasureTheory
namespace PGM

theorem ceps_normal_mean_close :
    ∀ P : ℕ, ∃ m : ℕ, ∀ D θ vlo vhi η : ℝ,
      0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → 0 < η →
      ∃ r : ℝ, 0 < r ∧ ∃ K eps₀ : ℝ, ∀ eps : ℝ, eps₀ ≤ eps →
        ∀ ν : ProbabilityMeasure ℝ, CepsInputClass D θ vlo vhi m η r ν →
          ‖((lawC eps ν / eps ^ 2 : ℝ) : ℂ) + 4 * cepsNormalDn eps ν‖ ≤
            K * (eps⁻¹) ^ P :=
  ceps_normal_mean_close_of_normal cepsNormalClose cepsNormalTaylor

end PGM
