import PLAStochastic.Index.GEP.StrongApprox.Tree.EndpointNumerics
import PLAStochastic.Index.GEP.StrongApprox.Block.NodeDefect
import PLAStochastic.Index.GEP.StrongApprox.Block.Moderation

/-! # Class-uniform endpoint approximation for the actual dyadic coupling -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- One class-uniform threshold controls every actual root and conditional split in the shared tree.
All parent/child block-size conditions and the finite node union bound are discharged here. -/
theorem exists_uniform_saDyadicLeafCoupling_bound
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ C H₀ : ℝ, 0 < C ∧ 4 ≤ H₀ ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ H : ℝ, H₀ ≤ H → ∀ s : ℝ, ∀ hs : 0 < s, s ≤ 1 →
      ∀ m : ℕ, ∀ hm : 0 < m, ∀ J : ℕ,
      Real.exp (H / 4) ≤ (m : ℝ) → (m * 2 ^ J : ℕ) ≤ Real.exp H → 1 / s ≤ (m : ℝ) ^ 8 →
      ∀ hV : 0 < lawVar ν + s ^ 2,
      (saDyadicLeafCoupling ν hs hm hV J).real
        (saLeafBad (2 ^ J) (((J : ℝ) + 1) * (3 * C * H * Real.sqrt H))) ≤
          3 * (2 : ℝ) ^ J * Real.exp (-(5 * H)) := by
  obtain ⟨A₀, H₁, hA₀, hH₁, htail⟩ := exists_uniform_saCenteredSum_moderation
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  obtain ⟨C, H₂, hC, hH₂, hdefect⟩ := exists_uniform_saNodeDefect
    vlo vhi κ₃ B θ D c A₀ hvlo hvhi hB hθ hD hc hA₀.le
  refine ⟨C, max 4 (max H₁ H₂), hC, le_max_left _ _, ?_⟩
  intro ν hν hsm H hH s hs hs1 m hm J hlo hhi hscale hV
  have hH4 : 4 ≤ H := (le_max_left _ _).trans hH
  have hHpos : 0 ≤ H := by linarith
  have hH₁' : H₁ ≤ H := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hH
  have hH₂' : H₂ ≤ H := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hH
  have hm2 : 2 ≤ m := by
    have hr : (2 : ℝ) ≤ m := by linarith [Real.add_one_le_exp (H / 4)]
    exact_mod_cast hr
  have hlength (j : ℕ) (hj : j ≤ J) :
      2 ≤ m * 2 ^ j ∧ Real.exp (H / 4) ≤ (m * 2 ^ j : ℕ) ∧
        (m * 2 ^ j : ℕ) ≤ Real.exp H ∧ 1 / s ≤ ((m * 2 ^ j : ℕ) : ℝ) ^ 8 := by
    obtain ⟨hmin, hmax⟩ := sa_dyadic_block_bounds m J j hj
    have hminr : (m : ℝ) ≤ (m * 2 ^ j : ℕ) := by exact_mod_cast hmin
    have hmaxr : ((m * 2 ^ j : ℕ) : ℝ) ≤ (m * 2 ^ J : ℕ) := by exact_mod_cast hmax
    exact ⟨hm2.trans hmin, hlo.trans hminr, hmaxr.trans hhi,
      hscale.trans (pow_le_pow_left₀ (by positivity) hminr 8)⟩
  have hbound := saDyadicLeafCoupling_bad_bound_window ν hs hm hV J
    (C * H * Real.sqrt H) (C * H * Real.sqrt H) H
    (fun d => A₀ * Real.sqrt (((m * 2 ^ (J - d) : ℕ) : ℝ) * H))
    (by positivity) (by positivity) hHpos
  have hroot : ∀ z : ℝ, |z| ≤ Real.sqrt (10 * H) →
      |saQuantile (cdf ((saSourceTreeRegular ν hs hm J).law : Measure ℝ))
        (cdf (gaussianReal 0 1) z) - Real.sqrt ((m * 2 ^ J : ℕ) * (lawVar ν + s ^ 2)) * z| ≤
          C * H * Real.sqrt H := by
    intro z hz
    obtain ⟨hl, hlmin, hlmax, hls⟩ := hlength J le_rfl
    exact (hdefect ν hν hsm H hH₂' s hs hs1 (m * 2 ^ J) hl hlmin hlmax hls z hz).1
  have hlocal : ∀ d < J, ∀ a z : ℝ,
      |a| ≤ A₀ * Real.sqrt (((m * 2 ^ (J - d) : ℕ) : ℝ) * H) →
      |z| ≤ Real.sqrt (10 * H) →
      |saSplitQuantile (saSourceTreeRegular ν hs hm (J - d - 1)) a
          (cdf (gaussianReal 0 1) z) - a / 2 -
        Real.sqrt ((m * 2 ^ (J - d - 1) : ℕ) * (lawVar ν + s ^ 2) / 2) * z| ≤
          C * H * Real.sqrt H := by
    intro d hd a z ha hz
    let l := m * 2 ^ (J - d - 1)
    obtain ⟨hl, hlmin, hlmax, hls⟩ := hlength (J - d - 1) (by omega)
    have hlpos : 0 < (l : ℝ) := by dsimp only [l]; exact_mod_cast (show 0 < m * 2 ^ (J - d - 1) by omega)
    have hparent : ((m * 2 ^ (J - d) : ℕ) : ℝ) = 2 * (l : ℝ) := by
      dsimp only [l]
      exact_mod_cast sa_dyadic_parent_length m J d hd
    rw [hparent] at ha
    have hu := sa_parent_window_to_split_mean hA₀.le hHpos hlpos ha
    have he := (hdefect ν hν hsm H hH₂' s hs hs1 l hl hlmin hlmax hls z hz).2
      (a / (2 * l)) hu
    have harg : 2 * (l : ℝ) * (a / (2 * l)) = a := by field_simp [ne_of_gt hlpos]
    have hcenter : (l : ℝ) * (a / (2 * l)) = a / 2 := by field_simp [ne_of_gt hlpos]
    rw [harg, hcenter] at he
    exact he
  have hsource : ∀ d < J,
      ((saSourceTreeRegular ν hs hm (J - d)).law : Measure ℝ).real
        {a | A₀ * Real.sqrt (((m * 2 ^ (J - d) : ℕ) : ℝ) * H) < |a|} ≤
          Real.exp (-(5 * H)) := by
    intro d hd
    obtain ⟨hl, hlmin, hlmax, hls⟩ := hlength (J - d) (by omega)
    exact htail ν hν hsm H hH₁' s hs hs1 (m * 2 ^ (J - d)) hl hlmin hlmax hls
  have he := hbound hroot hlocal hsource
  convert he using 2
  congr 1
  ring

end

end PGM
