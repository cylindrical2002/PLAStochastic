import PLAStochastic.Index.GEP.StrongApprox.Tree.Construction
import PLAStochastic.Index.GEP.StrongApprox.Endgame.DyadicScale
import PLAStochastic.Index.GEP.StrongApprox.Endgame.HorizonReduction
import PLAStochastic.Index.GEP.Universality.LayerTail

/-! # Final desmoothing and probability bookkeeping at powers of sixteen -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory

/-- An actual finite dyadic leaf estimate implies the required original-sample
coupling, with all within-block and smoothing failures paid for explicitly. -/
theorem sa_coupling_pow_sixteen_of_leaf
    {vlo vhi κ₃ B θ A w : ℝ} (hvlo : 0 < vlo) (hθ : 0 < θ)
    (hA : 0 ≤ A) (hw : 20 ≤ w) (hcw : 10 ≤ bernsteinRate θ B * w)
    (ν : ProbabilityMeasure ℝ) (hν : UnivClass vlo vhi κ₃ B θ ν)
    (k : ℕ) (hN : 16 ≤ ((16 ^ k : ℕ) : ℝ))
    (hH : 1 ≤ Real.log (16 ^ k : ℕ))
    (hlarge : w * Real.log (16 ^ k : ℕ) ≤ (2 ^ k : ℝ))
    (hlog : Real.log (16 ^ k : ℕ) ^ 2 ≤ Real.sqrt (2 ^ k : ℝ))
    (hnoise : 8 * ((16 ^ k : ℕ) : ℝ) * Real.exp (-(((16 ^ k : ℕ) : ℝ) / 2)) ≤
      ((16 ^ k : ℕ) : ℝ) ^ (-(3 : ℝ)))
    (hleaf : ∀ hs : 0 < 1 / ((16 ^ k : ℕ) : ℝ) ^ 2,
      ∀ hV : 0 < lawVar ν + (1 / ((16 ^ k : ℕ) : ℝ) ^ 2) ^ 2,
      (saDyadicLeafCoupling ν hs (show 0 < 2 ^ k by positivity) hV (3 * k)).real
        (saLeafBad (2 ^ (3 * k))
          (A * Real.log (16 ^ k : ℕ) ^ 2 * Real.sqrt (Real.log (16 ^ k : ℕ)))) ≤
        ((16 ^ k : ℕ) : ℝ) ^ (-(3 : ℝ))) :
    HasSACoupling ν (16 ^ k)
      ((A + Real.sqrt w * (1 + Real.sqrt (vhi + 1)) + 1 + 1 / (2 * Real.sqrt vlo)) *
        ((16 ^ k : ℕ) : ℝ) ^ ((1 : ℝ) / 8) * Real.sqrt (Real.log (16 ^ k : ℕ)))
      (((16 ^ k : ℕ) : ℝ) ^ (-(2 : ℝ))) := by
  let N : ℝ := (16 ^ k : ℕ)
  let m : ℕ := 2 ^ k
  let L : ℕ := 2 ^ (3 * k)
  let s : ℝ := 1 / N ^ 2
  let H : ℝ := Real.log N
  let a : ℝ := A * H ^ 2 * Real.sqrt H
  let b : ℝ := Real.sqrt (w * m * H)
  have hm : 0 < m := by dsimp [m]; positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hL1 : (1 : ℝ) ≤ L := by
    simp only [L, Nat.cast_pow, Nat.cast_ofNat]
    exact one_le_pow₀ (by norm_num)
  have hNm : L * m = 16 ^ k := sa_pow_sixteen_partition k
  have hNmr : N = (L : ℝ) * m := by
    dsimp only [N]
    exact_mod_cast hNm.symm
  have hN1 : 1 ≤ N := by dsimp [N]; linarith
  obtain ⟨hs, hs1, hsN, hsN2⟩ := sa_smoothing_scale_bounds hN1
  have hv : 0 < lawVar ν := hvlo.trans_le hν.var_ge
  have hV : 0 < lawVar ν + s ^ 2 := by positivity
  have hwp : 0 < w := by linarith
  have hHp : 0 < H := by dsimp [H, N]; linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hNp : 0 < N := by linarith
  let π := saDyadicLeafCoupling ν hs hm hV (3 * k)
  obtain ⟨hπ, hleft, hright⟩ := saDyadicLeafCoupling_laws ν hs hm hV (3 * k)
  let := hπ
  have hlarge' : w * Real.log N ≤ (m : ℝ) := by simpa [m, N] using hlarge
  have hlog' : Real.log N ^ 2 ≤ Real.sqrt (m : ℝ) := by simpa [m, N] using hlog
  have hcoup := sa_coupling_of_leaf_coupling ν hv hs hm L π hleft hright (hleaf hs hV) b b N
  rw [hNm] at hcoup
  apply hcoup.mono le_rfl
  · have he := sa_final_error_bound hvlo hν.var_ge hν.var_le hs.le hs1 hm1 hH hA hwp.le hsN hsN2 hlog'
    rw [sa_pow_sixteen_eighth]
    simpa only [a, b, H, N, m, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using he
  · have hsrc := saBlocksBad_source_bound hθ hν.pos hν.mean hν.expMom' hm L hb
    have hgauss := saBlocksBad_gaussian_bound m L hb
    have hwalk : (iidLaw gaussPM).real (saWalkBad (16 ^ k) 0 N) ≤
        2 * (N + 1) * Real.exp (-(N ^ 2 / (2 * N))) := by
      simpa only [saWalkBad, zero_mul, sub_zero] using sa_gaussian_walk_max_tail (16 ^ k) hNp
    have hprob := sa_final_probability_bound hN hm1 hL1 hNmr hw
      (bernsteinRate_pos hθ hν.B_pos).le hcw hlarge' hnoise
    change N ^ (-(3 : ℝ)) + _ + _ + _ ≤ N ^ (-(2 : ℝ))
    dsimp only [b, H] at hsrc hgauss
    linarith

end
end PGM
