import PLAStochastic.Index.GEP.StrongApprox.Block.NodeNumerics

/-! # WP5: class-uniform defects of the actual root and split quantiles -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory

set_option maxHeartbeats 800000 in
/-- Every numerical condition in the root and conditional quantile estimates is
absorbed into one class-uniform horizon threshold. -/
theorem exists_uniform_saNodeDefect
    (vlo vhi κ₃ B θ D c A₀ : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) (hA₀ : 0 ≤ A₀) :
    ∃ Cd H₀ : ℝ, 0 < Cd ∧ 1 ≤ H₀ ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ H : ℝ, H₀ ≤ H → ∀ s : ℝ, ∀ hs : 0 < s, s ≤ 1 →
      ∀ l : ℕ, ∀ hl : 2 ≤ l,
      Real.exp (H / 4) ≤ (l : ℝ) → (l : ℝ) ≤ Real.exp H → 1 / s ≤ (l : ℝ) ^ 8 →
      ∀ z : ℝ, |z| ≤ Real.sqrt (10 * H) →
      (|saQuantile (cdf ((saDensity_centeredSum ν hs (show 0 < l by omega)).law : Measure ℝ))
          (cdf (gaussianReal 0 1) z) - Real.sqrt ((l : ℝ) * (lawVar ν + s ^ 2)) * z| ≤
        Cd * H * Real.sqrt H) ∧
      ∀ u : ℝ, |u| * Real.sqrt l ≤ A₀ * Real.sqrt H →
      |saSplitQuantile (saDensity_centeredSum ν hs (show 0 < l by omega))
          (2 * l * u) (cdf (gaussianReal 0 1) z) - (l : ℝ) * u -
          Real.sqrt ((l : ℝ) * (lawVar ν + s ^ 2) / 2) * z| ≤ Cd * H * Real.sqrt H := by
  obtain ⟨C₁, K₁, hC₁, hK₁, hroot⟩ := exists_uniform_saCenteredSumQuantile_block_error
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  obtain ⟨C₂, K₂, hC₂, hK₂, hsplit⟩ := exists_uniform_saSplitQuantile_block_error
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  let C := C₁ + C₂
  let K := K₁ + K₂
  let r := saMeanRadius vlo B θ
  let b := 2 / (5 * (vhi + 1))
  let S := Real.sqrt (vhi + 1)
  let L := saLogVarianceConstant vlo B θ
  let T := saRateThird vlo B θ
  have hC : 0 < C := by dsimp [C]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hr : 0 < r := saMeanRadius_pos hvlo hθ
  have hb : 0 < b := by dsimp [b]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have hL : 0 < L := saLogVarianceConstant_pos hvlo hθ
  have hT : 0 < T := saRateThird_pos hvlo hθ
  obtain ⟨Y₀, hY₀, hwindow, hrate, hgaussrate⟩ := exists_saNodeWindow hb hS
  let E := saNodeErrorConstant C L T A₀ Y₀
  obtain ⟨hE, hEC⟩ := saNodeErrorConstant_bounds hC.le hL.le hT.le hA₀ hY₀.le
  have hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE
  obtain ⟨H₀, hH₀, hnum⟩ := exists_saBlockWindowInputs hC hK hr hb hS hA₀ hY₀
    hE hEC hwindow hrate hgaussrate
  refine ⟨32 * S * E, H₀, by positivity, hH₀, ?_⟩
  intro ν hν hsm H hH s hs hs1 l hl hlo hhi hscale z hz
  have hl0 : 0 < l := by omega
  have hlr : 0 < (l : ℝ) := by exact_mod_cast hl0
  have hd : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr hlr
  have hH1 : 1 ≤ H := hH₀.trans hH
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hsH : 0 < Real.sqrt H := Real.sqrt_pos.mpr hHpos
  have hV : 0 < lawVar ν + s ^ 2 := by nlinarith [hν.var_ge, sq_nonneg s]
  have hVhi : lawVar ν + s ^ 2 ≤ vhi + 1 := by nlinarith [hν.var_le]
  obtain ⟨hdlo, hdhi⟩ := sa_sqrt_block_range hl hlo hhi
  have hn := hnum H hH (Real.sqrt l) hdlo hdhi
  let A := A₀ * Real.sqrt H
  let Y := Y₀ * Real.sqrt H
  let ε := E * H * Real.sqrt H / Real.sqrt l
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hlocal : A + Y ≤ r * Real.sqrt l := by
    simpa only [A, Y, add_mul] using hn.local_window
  have hYscale : Y ≤ r / 2 * Real.sqrt l := hn.tail_window
  have hYroot : Y ≤ r * Real.sqrt l := by
    have he : r / 2 * Real.sqrt l ≤ r * Real.sqrt l := by nlinarith only [mul_pos hr hd]
    exact hYscale.trans he
  have hlarge₁ : 2 * C₁ ≤ Real.sqrt l := by dsimp [C] at hn; linarith [hn.large]
  have hlarge₂ : 2 * C₂ ≤ Real.sqrt l := by dsimp [C] at hn; linarith [hn.large]
  have hpoly : (6 * C + L / 2 * (3 * A + 2 * Y) + T * (A * Y ^ 2 + Y ^ 3 / 3)) /
      Real.sqrt l ≤ ε := by
    apply (div_le_div_iff_of_pos_right hd).mpr
    exact saNodeError_polynomial hC.le hL.le hT.le hA₀ hY₀.le hH1
  have hpoly₁ : (2 * C₁ + L / 2 * Y + T * Y ^ 3 / 6) / Real.sqrt l ≤ ε := by
    apply le_trans _ hpoly
    apply (div_le_div_iff_of_pos_right hd).mpr
    have he := saNodeError_root_le_split hC.le hL.le hT.le hA hY.le
    dsimp [C] at he
    linarith
  have hpoly₂ : (6 * C₂ + L / 2 * (3 * A + 2 * Y) + T * (A * Y ^ 2 + Y ^ 3 / 3)) /
      Real.sqrt l ≤ ε := by
    apply le_trans _ hpoly
    apply (div_le_div_iff_of_pos_right hd).mpr
    dsimp [C]
    linarith
  have hsig₁ : 0 < Real.sqrt ((l : ℝ) * (lawVar ν + s ^ 2)) := by positivity
  have hsig₂ : 0 < Real.sqrt ((l : ℝ) * (lawVar ν + s ^ 2) / 2) := by positivity
  have hsigBound₁ : Real.sqrt ((l : ℝ) * (lawVar ν + s ^ 2)) ≤ S * Real.sqrt l := by
    calc
      _ ≤ Real.sqrt ((l : ℝ) * (vhi + 1)) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hVhi hlr.le)
      _ = S * Real.sqrt l := by rw [Real.sqrt_mul hlr.le]; dsimp [S]; ring
  have hsigBound₂ : Real.sqrt ((l : ℝ) * (lawVar ν + s ^ 2) / 2) ≤ S * Real.sqrt l := by
    apply le_trans _ hsigBound₁
    apply Real.sqrt_le_sqrt
    nlinarith only [mul_pos hlr hV]
  have htail (K' b' : ℝ) (hKK : K' ≤ K) (hbb : b ≤ b') :
      K' * Real.exp (-b' * Y ^ 2) / (b' * Y) ≤ ε * saGaussianTail (Real.sqrt (10 * H)) := by
    apply le_trans _ (hn.density_tail b' hbb)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKK (Real.exp_nonneg _)) (mul_nonneg (hb.le.trans hbb) hY.le)
  have hK₁K : K₁ ≤ K := by dsimp [K]; linarith
  have hK₂K : K₂ ≤ K := by dsimp [K]; linarith
  have hbb : b ≤ 4 / (5 * (vhi + 1)) := by
    dsimp [b]
    apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
  constructor
  · have he := hroot ν hν hsm s hs hs1 l hl hscale hlarge₁ Y hY hYroot ε
      (Real.sqrt (10 * H)) z hn.error_nonneg hn.error_small (Real.sqrt_nonneg _) hz hpoly₁
      (hn.quantile_window _ hsig₁ hsigBound₁) (htail K₁ b hK₁K le_rfl)
      (hn.gaussian_tail _ hsig₁ hsigBound₁)
    exact he.trans (hn.defect _ hsig₁ hsigBound₁)
  · intro u hu
    have huR : |u| ≤ r / 2 := (mul_le_mul_iff_left₀ hd).mp (by
      simpa only [mul_comm] using hu.trans hn.parent_window)
    have he := hsplit ν hν hsm s hs hs1 l hl hscale hlarge₂ A Y hA hY hlocal hYscale u hu huR
      ε (Real.sqrt (10 * H)) z hn.error_nonneg hn.error_small (Real.sqrt_nonneg _) hz hpoly₂
      (hn.quantile_window _ hsig₂ hsigBound₂) (htail K₂ _ hK₂K hbb)
      (hn.gaussian_tail _ hsig₂ hsigBound₂)
    exact he.trans (hn.defect _ hsig₂ hsigBound₂)

end
end PGM
