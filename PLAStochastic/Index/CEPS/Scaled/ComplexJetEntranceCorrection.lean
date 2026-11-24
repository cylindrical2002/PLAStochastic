import PLAStochastic.Index.CEPS.Scaled.ComplexJetHalfFactors
import PLAStochastic.Index.CEPS.Normal.DividedDifferenceSymmetry

/-! # Exact complete entrance subtraction for arbitrary finite complex input vectors -/

noncomputable section
open Complex
namespace PGM

theorem cepsComplexKernelEntranceJetModel_sub_half_eq_first_slope
    (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b : ℂ)
    (hS : cepsComplexKernelDenominatorJetModel p N lam z b ≠ 0)
    (hQ : cepsComplexCumulantJetQuotient p N lam z b (b * z) ≠ 0)
    (ht : b * z ≠ cepsComplexCumulantRootModel p N lam z (-1) N b) :
    cepsComplexKernelEntranceJetModel p N lam z b - cepsComplexKernelHalfEntranceJetModel p N lam z b =
      -cepsComplexKernelHalfEntranceJetModel p N lam z b *
        dslope (cepsComplexKernelGJetModel p N lam z b)
          (cepsComplexCumulantRootModel p N lam z 1 N b) (b * z) /
            cepsComplexKernelDenominatorJetModel p N lam z b := by
  let G := cepsComplexKernelGJetModel p N lam z b
  let rp := cepsComplexCumulantRootModel p N lam z 1 N b
  let rm := cepsComplexCumulantRootModel p N lam z (-1) N b
  let t := b * z
  have hG : Differentiable ℂ G := cepsComplexKernelGJetModel_spatial_differentiable p N lam z b
  have hswap := cepsNormal_second_dslope_swap (hG rp) (hG rm) t
  have hid := sub_smul_dslope (dslope G rp) rm t
  rw [smul_eq_mul, ← hswap, cepsNormal_dslope_swap G rp rm] at hid
  change (t - rm) * dslope (dslope G rm) rp t =
    dslope G rp t - cepsComplexKernelDenominatorJetModel p N lam z b at hid
  have ht₀ : t - rm ≠ 0 := sub_ne_zero.mpr ht
  unfold cepsComplexKernelEntranceJetModel cepsComplexKernelHalfEntranceJetModel
    cepsComplexKernelEntranceSlopeJetModel
  change -_ * dslope (dslope G rm) rp t / (_ * _) - _ / (_ * (t - rm)) =
    -(_ / (_ * (t - rm))) * dslope G rp t / _
  field_simp
  linear_combination -hid

end PGM
