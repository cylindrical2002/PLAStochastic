import PLAStochastic.Index.GEP.Kernel.Marked.Pin.FullFarWindow

/-! # Saddle and far-window estimates for every legitimate density representative -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 1200000

theorem kernel_regLaw_saddle_scaled_of_density (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ δ c : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x = 0) → (∀ x, f x ≤ D * Real.exp (-θ * x)) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
        ∀ a : ℝ, |a - 1| ≤ δ →
          let lam := kernelTiltSaddle D θ vlo ν a
          ∃ τ : ProbabilityMeasure ℝ,
            (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun x => lam * x) ∧
            (τ : Measure ℝ) = volume.withDensity
              (fun x => ENNReal.ofReal (kernelTiltDensity ν lam f x)) ∧
            |lam| ≤ kernelTiltClassRadius D θ vlo vhi ∧
            c * (a - 1) ^ 2 ≤ kernelTiltRate ν a lam ∧
            RegLaw (2 * D * Real.exp θ) (θ / 4) (3 * vlo / 16) (5 * vhi) (kernelScaledLaw τ a) ∧
            (kernelScaledLaw τ a : Measure ℝ) = volume.withDensity
              (fun x => ENNReal.ofReal (kernelScaledDensity a (kernelTiltDensity ν lam f) x)) ∧
            Measurable (kernelScaledDensity a (kernelTiltDensity ν lam f)) ∧
            (∀ x, 0 ≤ kernelScaledDensity a (kernelTiltDensity ν lam f) x) ∧
            (∀ x ≤ 0, kernelScaledDensity a (kernelTiltDensity ν lam f) x = 0) ∧
            (∀ x, kernelScaledDensity a (kernelTiltDensity ν lam f) x ≤ 2 * D * Real.exp θ) ∧
            (∀ x, kernelScaledDensity a (kernelTiltDensity ν lam f) x ≤
              (2 * D * Real.exp θ) * Real.exp (-(θ / 4) * x)) ∧
            (∀ J : Set ℝ, ∀ β : ℝ, ∀ n : ℕ, ∀ φ : ℝ → ℝ,
              krRow J (τ : Measure ℝ) β (β * a) n φ = krRow J (kernelScaledLaw τ a : Measure ℝ) β β n φ) ∧
            (∀ J : Set ℝ, MeasurableSet J → ∀ β : ℝ, ∀ n : ℕ, ∀ y z : ℝ,
              krDens J τ (kernelTiltDensity ν lam f) β (β * a) n y z =
                krDens J (kernelScaledLaw τ a) (kernelScaledDensity a (kernelTiltDensity ν lam f))
                  β β n y z) := by
  obtain ⟨δ, c, hδ, hδhi, hc, hnorm⟩ := kernel_regLaw_saddle_normalized D θ vlo vhi hD hθ hvlo hv
  refine ⟨δ, c, hδ, hδhi, hc, ?_⟩
  intro ν hν f hf hf0 hfD hfz hfe hνf a ha
  dsimp only
  let lam := kernelTiltSaddle D θ vlo ν a
  obtain ⟨hlam, _, hrate, ρ, hρ, hρreg⟩ := hnorm ν hν a ha
  have ha0 : 0 < a := by linarith [(abs_le.mp ha).1]
  have halo : 1 / 2 ≤ a := by linarith [(abs_le.mp ha).1]
  have hahi : a ≤ 2 := by linarith [(abs_le.mp ha).2]
  have hl : |lam| ≤ θ / 2 := (hlam.trans (min_le_left _ _)).trans
    ((saTiltRadius_le_half _ _ (by positivity)).trans (by linarith))
  have hU := hν.univClass hθ hvlo
  let := hU.isProbabilityMeasure_centeredTilt hl
  have hp : IsProbabilityMeasure ((ν : Measure ℝ).tilted (fun x => lam * x)) := by
    rw [← kernel_centeredTilt_eq_raw]
    infer_instance
  let τ : ProbabilityMeasure ℝ := ⟨(ν : Measure ℝ).tilted (fun x => lam * x), hp⟩
  have hτ : (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun x => lam * x) := rfl
  have hτf : (τ : Measure ℝ) = volume.withDensity
      (fun x => ENNReal.ofReal (kernelTiltDensity ν lam f x)) :=
    kernel_tilt_density_measure ν hf hf0 hνf (hU.kernel_integrable_exp_raw hl)
  have hρeq : kernelScaledLaw τ a = ρ := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [kernelScaledLaw, ProbabilityMeasure.toMeasure_map, hτ, hρ]
  have hft : Measurable (kernelTiltDensity ν lam f) := by unfold kernelTiltDensity; fun_prop
  have hft0 (x : ℝ) : 0 ≤ kernelTiltDensity ν lam f x := mul_nonneg (Real.exp_nonneg _) (hf0 x)
  have hftz (x : ℝ) (hx : x ≤ 0) : kernelTiltDensity ν lam f x = 0 := by
    simp only [kernelTiltDensity, hfz x hx, mul_zero]
  have hfte (x : ℝ) : kernelTiltDensity ν lam f x ≤
      (D * Real.exp θ) * Real.exp (-(θ / 2) * x) := hν.kernel_tilt_density_envelope hθ hvlo hfz hfe hl x
  have hftD (x : ℝ) : kernelTiltDensity ν lam f x ≤ D * Real.exp θ :=
    hν.kernelTiltDensity_le hθ hvlo hfz hfe hl x
  refine ⟨τ, hτ, hτf, hlam, hrate, hρeq.symm ▸ hρreg, kernel_scaled_density_measure τ hτf ha0.ne',
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold kernelScaledDensity
    fun_prop
  · intro x
    exact div_nonneg (hft0 _) (abs_nonneg _)
  · intro x hx
    rw [kernelScaledDensity, hftz (x / a) (div_nonpos_of_nonpos_of_nonneg hx ha0.le), zero_div]
  · intro x
    rw [kernelScaledDensity, abs_of_pos ha0]
    apply (div_le_div_of_nonneg_right (hftD _) ha0.le).trans
    rw [div_le_iff₀ ha0]
    have hh := mul_le_mul_of_nonneg_right halo (show 0 ≤ D * Real.exp θ by positivity)
    nlinarith
  · intro x
    have hh := kernel_scaled_density_envelope (by positivity) (by positivity : 0 ≤ θ / 2)
      halo hahi hftz hfte x
    rw [show 2 * (D * Real.exp θ) = 2 * D * Real.exp θ by ring,
      show (θ / 2) / 2 = θ / 4 by ring] at hh
    exact hh
  · intro J β n φ
    simpa only [mul_div_cancel_right₀ _ ha0.ne'] using
      (kernel_krRow_scaled J τ β (β * a) ha0.ne' n φ).symm
  · intro J hJ β n y z
    simpa only [mul_div_cancel_right₀ _ ha0.ne'] using
      (kernel_krDens_scaled hJ τ hft hft0 hftD β (β * a) ha0.ne' n y z).symm


theorem kernel_regLaw_saddle_full_marked_pin_decay_of_density (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ δ c d k K : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < c ∧ 0 < d ∧ 0 < k ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x = 0) → (∀ x, f x ≤ D * Real.exp (-θ * x)) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
        ∀ a : ℝ, |a - 1| ≤ δ → ∀ α w : ℝ, 1 ≤ w → ∀ t y z : ℝ,
        ∀ l r M : ℕ, 1 ≤ l + r → 1 ≤ M →
          kernelMarkedFullDens (Icc α (α + w)) ν f 1 a t l r y z *
            krDens (Icc α (α + w)) ν f 1 a M z y ≤
            K * w * Real.exp (-c * ((l : ℝ) + r + M) * (a - 1) ^ 2 +
              kernelTiltSaddle D θ vlo ν a * t - kernelTiltSaddle D θ vlo ν a / a -
              d * min ((z - y) ^ 2 / (M : ℝ)) |z - y| -
              k * (((l : ℝ) + r + M) - 8) / w ^ 2) := by
  let D' := 2 * D * Real.exp θ
  let θ' := θ / 4
  let vlo' := 3 * vlo / 16
  let vhi' := 5 * vhi
  have hD' : 0 < D' := by positivity
  have hθ' : 0 < θ' := by positivity
  have hvlo' : 0 < vlo' := by positivity
  have hv' : vlo' ≤ vhi' := by dsimp [vlo', vhi']; linarith
  obtain ⟨d, hd, hdisp⟩ := kernel_regLaw_displacement D' θ' vlo' vhi' hD' hθ' hvlo' hv'
  obtain ⟨k, hk, hspec⟩ := kernel_regLaw_full_marked_pair_spectral D' θ' vlo' vhi' 1
    hD' hθ' hvlo' hv' (by norm_num)
  obtain ⟨δ, c, hδ, hδhi, hc, hdata⟩ := kernel_regLaw_saddle_scaled_of_density D θ vlo vhi hD hθ hvlo hv
  let K := D' ^ 2 * (Real.exp θ' + 2 + 18 * D')
  have hK : 0 < K := by positivity
  refine ⟨δ, c, d / 2, k / 8, K, hδ, hδhi, hc, by positivity, by positivity, hK, ?_⟩
  intro ν hν f hf hf0 hfD hfz hfe hνf
  have hscaled := hdata ν hν f hf hf0 hfD hfz hfe hνf
  intro a ha α w hw t y z l r M hlr hM
  obtain ⟨τ, hτ, _, hlam, hrate, hreg, hgf, hg, hg0, hgz, hgD, hge, _, hds⟩ := hscaled a ha
  let lam := kernelTiltSaddle D θ vlo ν a
  let ρ := kernelScaledLaw τ a
  let g := kernelScaledDensity a (kernelTiltDensity ν lam f)
  let J := Icc α (α + w)
  let N : ℝ := (l : ℝ) + r + M
  let Q := min ((z - y) ^ 2 / (M : ℝ)) |z - y|
  let P := kernelMarkedFullDens J ρ g 1 1 (a * t) l r y z * krDens J ρ g 1 1 M z y
  have hJ : MeasurableSet J := measurableSet_Icc
  have hJfin : volume J ≠ ⊤ := by simp [J]
  have hP0 : 0 ≤ P := mul_nonneg (kernelMarkedFullDens_nonneg ρ hg0 _ _ _ _ _ _ _) (krDens_nonneg ρ hg0 _ _ _)
  have ha0 : 0 < a := by linarith [(abs_le.mp ha).1]
  have hlam' : |lam| ≤ θ / 2 := (hlam.trans (min_le_left _ _)).trans
    ((saTiltRadius_le_half _ _ (by positivity)).trans (by linarith))
  have hftD (x : ℝ) : kernelTiltDensity ν lam f x ≤ D * Real.exp θ :=
    hν.kernelTiltDensity_le hθ hvlo hfz hfe hlam' x
  have hscale (n : ℕ) (u v : ℝ) : krDens J τ (kernelTiltDensity ν lam f) 1 a n u v =
      krDens J ρ g 1 1 n u v := by simpa only [one_mul] using hds J hJ 1 n u v
  have hmScale : kernelMarkedFullDens J τ (kernelTiltDensity ν lam f) 1 a t l r y z =
      kernelMarkedFullDens J ρ g 1 1 (a * t) l r y z := by
    cases l <;> cases r
    · rfl
    · simp only [kernelMarkedFullDens, hscale, one_mul]
    · simp only [kernelMarkedFullDens, hscale, one_mul]
    · unfold kernelMarkedFullDens kernelMarkedDens
      apply integral_congr_ae
      filter_upwards [] with u
      rw [hscale, hscale]
      simp only [one_mul]
  have hmark : kernelMarkedFullDens J ρ g 1 1 (a * t) l r y z ≤ D' := by
    simpa only [abs_one, div_one] using kernelFar_fullDens_le_div (β := 1) (t := a * t) hJ hJfin ρ hg hg0 hgD
      hgf (by norm_num : (1 : ℝ) ≠ 0) l r y z
  have hpin : krDens J ρ g 1 1 M z y ≤ (D' * Real.exp θ') * Real.exp (-d * Q) := by
    have hh := hdisp ρ hreg g hg hg0 hgz hge hgf J hJ 1 (Or.inl rfl) M hM z y
    have hs : (y - z) ^ 2 = (z - y) ^ 2 := by ring
    simpa only [hs, abs_sub_comm y z] using hh
  have hcross : P ≤ (D' * (D' * Real.exp θ')) * Real.exp (-d * Q) := by
    have hh := mul_le_mul hmark hpin (krDens_nonneg ρ hg0 _ _ _) hD'.le
    simpa only [mul_assoc] using hh
  have hspectral : P ≤ (D' * (1 + 3 * Real.sqrt (D' * w))) ^ 2 *
      Real.exp (-(k * (N - 8) / (4 * w ^ 2))) := by
    simpa only [abs_one, div_one] using hspec ρ hreg g hg hg0 hgD hgf α w 1 1 hw
      (by norm_num : (1 : ℝ) ≤ |(1 : ℝ)|) (a * t) y z l r M hlr hM
  have hgeom := kernelFar_geometric_bound hP0 (by positivity) (sq_nonneg _) hcross hspectral
  have hcoef : D' * (D' * Real.exp θ') + (D' * (1 + 3 * Real.sqrt (D' * w))) ^ 2 ≤ K * w := by
    have hs : Real.sqrt (D' * w) ^ 2 = D' * w := Real.sq_sqrt (by positivity)
    have hsq : (1 + 3 * Real.sqrt (D' * w)) ^ 2 ≤ 2 + 18 * D' * w := by
      nlinarith [sq_nonneg (1 - 3 * Real.sqrt (D' * w))]
    have hh := mul_le_mul_of_nonneg_left hsq (sq_nonneg D')
    have he := mul_le_mul_of_nonneg_left hw (show 0 ≤ D' ^ 2 * (Real.exp θ' + 2) by positivity)
    dsimp [K]
    nlinarith
  have hbound : P ≤ K * w * Real.exp ((-d * Q + -(k * (N - 8) / (4 * w ^ 2))) / 2) :=
    hgeom.trans (mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _))
  have hpair := kernel_full_marked_pin_tilt hJ ν τ hf hf0 hfD
    ((hν.univClass hθ hvlo).kernel_integrable_exp_raw hlam') hτ hftD 1 t ha0.ne' l r hM y z
  simp only [mul_one] at hpair
  change kernelMarkedFullDens J ν f 1 a t l r y z * krDens J ν f 1 a M z y =
    Real.exp (-N * kernelTiltRate ν a lam + lam * t - lam / a) *
      (kernelMarkedFullDens J τ (kernelTiltDensity ν lam f) 1 a t l r y z *
        krDens J τ (kernelTiltDensity ν lam f) 1 a M z y) at hpair
  rw [hmScale, hscale] at hpair
  rw [hpair]
  have hexp : Real.exp (-N * kernelTiltRate ν a lam + lam * t - lam / a) ≤
      Real.exp (-c * N * (a - 1) ^ 2 + lam * t - lam / a) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hrate (show 0 ≤ N by positivity)
    nlinarith
  calc
    _ ≤ Real.exp (-c * N * (a - 1) ^ 2 + lam * t - lam / a) *
        (K * w * Real.exp ((-d * Q + -(k * (N - 8) / (4 * w ^ 2))) / 2)) :=
      mul_le_mul hexp hbound hP0 (Real.exp_nonneg _)
    _ = _ := by
      change _ = K * w * Real.exp (-c * N * (a - 1) ^ 2 + lam * t - lam / a -
        d / 2 * Q - k / 8 * (N - 8) / w ^ 2)
      rw [mul_left_comm _ (K * w), ← Real.exp_add]
      congr 2
      ring


theorem kernel_regLaw_full_marked_pin_far_window_of_density (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ δ q k K : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < q ∧ 0 < k ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x = 0) → (∀ x, f x ≤ D * Real.exp (-θ * x)) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
        ∀ a : ℝ, |a - 1| ≤ δ → ∀ w : ℝ, 1 ≤ w → ∀ t : ℝ, 0 ≤ t →
        ∀ A : ℝ, A ≤ w * |a - 1| → ∀ y z : ℝ, |z - y| = w →
        ∀ l r M : ℕ, 1 ≤ l + r → 1 ≤ M →
          kernelMarkedFullDens (Icc 0 w) ν f 1 a t l r y z * krDens (Icc 0 w) ν f 1 a M z y ≤
            K * w * Real.exp (θ / 2 * t - q * A - k * ((l : ℝ) + r + M) / w ^ 2) := by
  obtain ⟨δ, c, d, k, K, hδ, hδhi, hc, hd, hk, hK, hdecay⟩ :=
    kernel_regLaw_saddle_full_marked_pin_decay_of_density D θ vlo vhi hD hθ hvlo hv
  obtain ⟨δ', c', hδ', _, _, hsaddle⟩ := kernel_regLaw_saddle_rate D θ vlo vhi hθ hvlo hv
  let q := min c d
  have hq : 0 < q := lt_min hc hd
  refine ⟨min δ δ', q, k, K * Real.exp (θ + 8 * k), lt_min hδ hδ',
    (min_le_left _ _).trans hδhi, hq, hk, by positivity, ?_⟩
  intro ν hν f hf hf0 hfD hfz hfe hνf
  have hb := hdecay ν hν f hf hf0 hfD hfz hfe hνf
  intro a ha w hw t ht A hA y z hyz l r M hlr hM
  have haδ := ha.trans (min_le_left δ δ')
  have haδ' := ha.trans (min_le_right δ δ')
  have hh := hb a haδ 0 w hw t y z l r M hlr hM
  have hyz2 : (z - y) ^ 2 = w ^ 2 := by rw [← sq_abs (z - y), hyz]
  simp only [zero_add, hyz, hyz2] at hh
  let N : ℝ := (l : ℝ) + r + M
  let Q := min (w ^ 2 / (M : ℝ)) w
  let lam := kernelTiltSaddle D θ vlo ν a
  have hw0 : 0 < w := by linarith
  have hM0 : 0 < (M : ℝ) := by exact_mod_cast hM
  have hmN : (M : ℝ) ≤ N := by
    dsimp [N]
    linarith [Nat.cast_nonneg (α := ℝ) l, Nat.cast_nonneg (α := ℝ) r]
  have hs : |a - 1| ≤ 1 := (haδ.trans hδhi).trans (by norm_num)
  have henergy := kernelFar_crossing_energy hw0.le hM0 hmN hs
  have hQ0 : 0 ≤ Q := le_min (by positivity) hw0.le
  have hcost : q * w * |a - 1| ≤ c * N * (a - 1) ^ 2 + d * Q := by
    have h₁ := mul_le_mul_of_nonneg_left henergy hq.le
    have h₂ := mul_le_mul_of_nonneg_right (min_le_left c d)
      (show 0 ≤ N * (a - 1) ^ 2 by positivity)
    have h₃ := mul_le_mul_of_nonneg_right (min_le_right c d) hQ0
    change q * (w * |a - 1|) ≤ q * (N * (a - 1) ^ 2 + Q) at h₁
    change q * (N * (a - 1) ^ 2) ≤ c * (N * (a - 1) ^ 2) at h₂
    change q * Q ≤ d * Q at h₃
    nlinarith
  have hlam := (hsaddle ν hν a haδ').1
  have hlam' : |lam| ≤ θ / 2 := (hlam.trans (min_le_left _ _)).trans
    ((saTiltRadius_le_half _ _ (by positivity)).trans (by linarith))
  have ha0 : 0 < a := by linarith [(abs_le.mp haδ).1]
  have halo : 1 / 2 ≤ a := by linarith [(abs_le.mp haδ).1]
  have hquot : -lam / a ≤ θ := by
    apply (div_le_iff₀ ha0).mpr
    have hh' := (neg_le_abs lam).trans hlam'
    nlinarith
  have hins : lam * t - lam / a ≤ θ / 2 * t + θ := by
    have hh' := mul_le_mul_of_nonneg_right ((le_abs_self lam).trans hlam') ht
    rw [neg_div] at hquot
    linarith only [hh', hquot]
  have htime : k * 8 / w ^ 2 ≤ 8 * k := by
    apply (div_le_iff₀ (sq_pos_of_pos hw0)).mpr
    have hw2 : 1 ≤ w ^ 2 := by nlinarith
    nlinarith
  have hqA := mul_le_mul_of_nonneg_left hA hq.le
  have hexp : -c * N * (a - 1) ^ 2 + lam * t - lam / a - d * Q -
      k * (N - 8) / w ^ 2 ≤ (θ + 8 * k) + (θ / 2 * t - q * A - k * N / w ^ 2) := by
    have he : k * (N - 8) / w ^ 2 = k * N / w ^ 2 - k * 8 / w ^ 2 := by ring
    rw [he]
    nlinarith
  apply hh.trans
  have hex := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
    (show 0 ≤ K * w by positivity)
  change K * w * Real.exp (-c * N * (a - 1) ^ 2 + lam * t - lam / a - d * Q -
      k * (N - 8) / w ^ 2) ≤ _
  refine hex.trans_eq ?_
  rw [Real.exp_add]
  ring


end
end PGM
