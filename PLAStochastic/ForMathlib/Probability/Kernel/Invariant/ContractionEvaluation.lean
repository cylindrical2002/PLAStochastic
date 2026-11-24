import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Invariance

/-! # Abstract contraction-and-evaluation theorem for a slope kernel

This is the kernel-theoretic skeleton of Theorem I.1 (`thm:constantcontraction`)
and of the geometric bound in Theorem 4.4.  A kernel `T` on the line acts on
test functions by `act T f a = ∫ f dT(a)`.  On a set `S` of admissible slopes
we assume

* `T a` is a probability measure concentrated on `S` for `a ∈ S`;
* Lipschitz test functions on `S` are integrable under every `T a`, `a ∈ S`;
* the observable `W₁`-contraction: `act T` maps `L`-Lipschitz test functions
  on `S` to `q L`-Lipschitz functions on `S`.

Then for every invariant probability `λ` concentrated on `S` with a first
moment, every iterate satisfies
`|(T^m f)(x) - ∫ f dλ| ≤ q^m L ∫ |b - x| dλ(b)`, and if in addition `T`
reverses stochastic order and `x` is the least point of `S`, the even iterates
increase to `∫ f dλ` and the odd iterates decrease to it.

Nothing here is specific to Swing: the file is consumed by
`SlopeKernelReduction`, which supplies the concrete kernel `T = 𝖠𝖡`, the
stationary slope law `λ = ν_∞𝖠` and the reward `h = 𝖡v`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
namespace SwingRepair
namespace SlopeEvaluation

/-- The action of a kernel on real test functions. -/
def act (T : Kernel ℝ ℝ) (f : ℝ → ℝ) (a : ℝ) : ℝ := ∫ b, f b ∂T a

/-- Measurable, `L`-Lipschitz on `S`. -/
structure IsTest (S : Set ℝ) (L : ℝ≥0) (f : ℝ → ℝ) : Prop where
  meas : Measurable f
  lip : LipschitzOnWith L f S

/-- The observable `W₁`-contraction of `T` on `S` with rate `q`. -/
structure Contraction (T : Kernel ℝ ℝ) (S : Set ℝ) (q : ℝ≥0) : Prop where
  prob : ∀ a ∈ S, IsProbabilityMeasure (T a)
  supp : ∀ a ∈ S, T a Sᶜ = 0
  integrable : ∀ (L : ℝ≥0) (f : ℝ → ℝ), IsTest S L f → ∀ a ∈ S, Integrable f (T a)
  lip : ∀ (L : ℝ≥0) (f : ℝ → ℝ), IsTest S L f → LipschitzOnWith (q * L) (act T f) S

/-- `T` reverses stochastic order on `S`. -/
structure OrderReversing (T : Kernel ℝ ℝ) (S : Set ℝ) : Prop where
  anti : ∀ (L : ℝ≥0) (f : ℝ → ℝ), IsTest S L f → MonotoneOn f S → AntitoneOn (act T f) S

variable {T : Kernel ℝ ℝ} {S : Set ℝ} {q : ℝ≥0}

theorem act_measurable [IsSFiniteKernel T] {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (act T f) := by
  have hsm : StronglyMeasurable (fun p : ℝ × ℝ => f p.2) :=
    (hf.comp measurable_snd).stronglyMeasurable
  exact (hsm.integral_kernel_prod_right' (κ := T)).measurable

theorem IsTest.map [IsSFiniteKernel T] (h : Contraction T S q) {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : IsTest S L f) : IsTest S (q * L) (act T f) :=
  ⟨act_measurable hf.meas, h.lip L f hf⟩

theorem IsTest.iterate [IsSFiniteKernel T] (h : Contraction T S q) {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : IsTest S L f) (m : ℕ) : IsTest S (q ^ m * L) ((act T)^[m] f) := by
  induction m with
  | zero => simpa using hf
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have e : q ^ (m + 1) * L = q * (q ^ m * L) := by ring
    rw [e]
    exact ih.map h

/-! ### Measures concentrated on `S` -/

theorem ae_mem_of_compl_eq_zero {lam : Measure ℝ} (hsupp : lam Sᶜ = 0) :
    ∀ᵐ b ∂lam, b ∈ S := by
  have := compl_mem_ae_iff.mpr hsupp
  filter_upwards [this] with b hb
  simpa using hb

/-- A test function grows at most linearly on `S`, hence is integrable under a
finite measure concentrated on `S` with a first moment. -/
theorem IsTest.integrable_of_moment {lam : Measure ℝ} [IsFiniteMeasure lam]
    (hsupp : lam Sᶜ = 0) (hmom : Integrable (fun b : ℝ => b) lam)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : IsTest S L f) {a₀ : ℝ} (ha₀ : a₀ ∈ S) :
    Integrable f lam := by
  have hbound : Integrable (fun b : ℝ => |f a₀| + (L : ℝ) * |b - a₀|) lam := by
    refine (integrable_const _).add ((hmom.sub (integrable_const a₀)).abs.const_mul _)
  refine hbound.mono' hf.meas.aestronglyMeasurable ?_
  filter_upwards [ae_mem_of_compl_eq_zero hsupp] with b hb
  rw [Real.norm_eq_abs]
  have hd := hf.lip.dist_le_mul b hb a₀ ha₀
  rw [Real.dist_eq, Real.dist_eq] at hd
  calc |f b| = |(f b - f a₀) + f a₀| := by ring_nf
    _ ≤ |f b - f a₀| + |f a₀| := abs_add_le _ _
    _ ≤ (L : ℝ) * |b - a₀| + |f a₀| := by linarith
    _ = |f a₀| + (L : ℝ) * |b - a₀| := by ring

/-! ### Invariance -/

/-- `∫ Tf dλ = ∫ f dλ` for an invariant `λ`. -/
theorem integral_act_eq_of_invariant [IsSFiniteKernel T] {lam : Measure ℝ} [SFinite lam]
    (hlam : T ∘ₘ lam = lam) {f : ℝ → ℝ} (hint : Integrable f lam) :
    ∫ a, act T f a ∂lam = ∫ b, f b ∂lam := by
  have hint' : Integrable f (T ∘ₘ lam) := by rw [hlam]; exact hint
  conv_rhs => rw [← hlam]
  rw [Measure.comp_eq_comp_const_apply] at hint' ⊢
  rw [Kernel.integral_comp hint']
  simp only [Kernel.const_apply]
  rfl

theorem integral_iterate_eq_of_invariant [IsSFiniteKernel T] (h : Contraction T S q)
    {lam : Measure ℝ} [IsProbabilityMeasure lam] (hlam : T ∘ₘ lam = lam) (hsupp : lam Sᶜ = 0)
    (hmom : Integrable (fun b : ℝ => b) lam) {L : ℝ≥0} {f : ℝ → ℝ} (hf : IsTest S L f)
    {a₀ : ℝ} (ha₀ : a₀ ∈ S) (m : ℕ) :
    ∫ a, (act T)^[m] f a ∂lam = ∫ b, f b ∂lam := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ← ih]
    exact integral_act_eq_of_invariant hlam
      ((hf.iterate h m).integrable_of_moment hsupp hmom ha₀)

/-! ### The geometric bound -/

/-- **Geometric evaluation bound.**  For an invariant probability `λ`
concentrated on `S` with a first moment, every iterate of an `L`-Lipschitz test
function at a point `x ∈ S` is within `q^m L ∫|b - x| dλ` of its `λ`-mean. -/
theorem abs_iterate_sub_integral_le [IsSFiniteKernel T] (h : Contraction T S q)
    {lam : Measure ℝ} [IsProbabilityMeasure lam] (hlam : T ∘ₘ lam = lam) (hsupp : lam Sᶜ = 0)
    (hmom : Integrable (fun b : ℝ => b) lam) {L : ℝ≥0} {f : ℝ → ℝ} (hf : IsTest S L f)
    {x : ℝ} (hx : x ∈ S) (m : ℕ) :
    |(act T)^[m] f x - ∫ b, f b ∂lam| ≤
      (q : ℝ) ^ m * L * ∫ b, |b - x| ∂lam := by
  set g := (act T)^[m] f with hg
  have hgtest : IsTest S (q ^ m * L) g := hf.iterate h m
  have hgint : Integrable g lam := hgtest.integrable_of_moment hsupp hmom hx
  have hdist : Integrable (fun b : ℝ => |b - x|) lam := (hmom.sub (integrable_const x)).abs
  rw [← integral_iterate_eq_of_invariant h hlam hsupp hmom hf hx m, ← hg]
  have h1 : g x - ∫ b, g b ∂lam = ∫ b, (g x - g b) ∂lam := by
    rw [integral_sub (integrable_const _) hgint, integral_const, probReal_univ,
      one_smul]
  rw [h1]
  calc |∫ b, (g x - g b) ∂lam| ≤ ∫ b, |g x - g b| ∂lam := abs_integral_le_integral_abs
    _ ≤ ∫ b, (q : ℝ) ^ m * L * |b - x| ∂lam := by
        refine integral_mono_ae ((integrable_const _).sub hgint).abs (hdist.const_mul _) ?_
        filter_upwards [ae_mem_of_compl_eq_zero hsupp] with b hb
        have hd := hgtest.lip.dist_le_mul x hx b hb
        rw [Real.dist_eq, Real.dist_eq] at hd
        have : ((q ^ m * L : ℝ≥0) : ℝ) = (q : ℝ) ^ m * L := by push_cast; ring
        rw [this] at hd
        rw [abs_sub_comm b x]
        exact hd
    _ = (q : ℝ) ^ m * L * ∫ b, |b - x| ∂lam := integral_const_mul _ _

/-- The one-step width: consecutive iterates at `x` differ by at most
`q^m L ∫ |b - x| dT(x)(b)`. -/
theorem abs_iterate_succ_sub_iterate_le [IsSFiniteKernel T] (h : Contraction T S q)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : IsTest S L f) {x : ℝ} (hx : x ∈ S)
    (hmomx : Integrable (fun b : ℝ => b) (T x)) (m : ℕ) :
    |(act T)^[m + 1] f x - (act T)^[m] f x| ≤
      (q : ℝ) ^ m * L * ∫ b, |b - x| ∂T x := by
  have hprob := h.prob x hx
  set g := (act T)^[m] f with hg
  have hgtest : IsTest S (q ^ m * L) g := hf.iterate h m
  have hgint : Integrable g (T x) := h.integrable _ _ hgtest x hx
  have hdist : Integrable (fun b : ℝ => |b - x|) (T x) := (hmomx.sub (integrable_const x)).abs
  rw [Function.iterate_succ_apply', ← hg]
  have h1 : act T g x - g x = ∫ b, (g b - g x) ∂T x := by
    rw [integral_sub hgint (integrable_const _), integral_const, probReal_univ,
      one_smul]
    rfl
  rw [h1]
  calc |∫ b, (g b - g x) ∂T x| ≤ ∫ b, |g b - g x| ∂T x := abs_integral_le_integral_abs
    _ ≤ ∫ b, (q : ℝ) ^ m * L * |b - x| ∂T x := by
        refine integral_mono_ae (hgint.sub (integrable_const _)).abs (hdist.const_mul _) ?_
        filter_upwards [ae_mem_of_compl_eq_zero (h.supp x hx)] with b hb
        have hd := hgtest.lip.dist_le_mul b hb x hx
        rw [Real.dist_eq, Real.dist_eq] at hd
        have : ((q ^ m * L : ℝ≥0) : ℝ) = (q : ℝ) ^ m * L := by push_cast; ring
        rw [this] at hd
        exact hd
    _ = (q : ℝ) ^ m * L * ∫ b, |b - x| ∂T x := integral_const_mul _ _

/-! ### Order reversal and the brackets -/

theorem OrderReversing.iterate_even [IsSFiniteKernel T] (h : Contraction T S q)
    (hrev : OrderReversing T S) {L : ℝ≥0} {f : ℝ → ℝ} (hf : IsTest S L f)
    (hmono : MonotoneOn f S) (m : ℕ) :
    MonotoneOn ((act T)^[2 * m] f) S ∧ AntitoneOn ((act T)^[2 * m + 1] f) S := by
  induction m with
  | zero =>
    refine ⟨by simpa using hmono, ?_⟩
    simp only [Nat.mul_zero, Nat.zero_add, Function.iterate_one]
    exact hrev.anti L f hf hmono
  | succ m ih =>
    obtain ⟨hev, hodd⟩ := ih
    have hodd_test : IsTest S (q ^ (2 * m + 1) * L) ((act T)^[2 * m + 1] f) := hf.iterate h _
    have hev' : MonotoneOn ((act T)^[2 * (m + 1)] f) S := by
      have e : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
      rw [e, Function.iterate_succ_apply']
      have hneg_test : IsTest S (q ^ (2 * m + 1) * L) (-(act T)^[2 * m + 1] f) :=
        ⟨hodd_test.meas.neg, by
          have := hodd_test.lip
          intro x hx y hy
          simpa [Pi.neg_apply, edist_neg_neg] using this hx hy⟩
      have hanti := hrev.anti _ (-(act T)^[2 * m + 1] f) hneg_test
        (fun a ha b hb hab => by
          simp only [Pi.neg_apply, neg_le_neg_iff]
          exact hodd ha hb hab)
      intro a ha b hb hab
      have := hanti ha hb hab
      have hneg : ∀ c, act T (-(act T)^[2 * m + 1] f) c = -act T ((act T)^[2 * m + 1] f) c := by
        intro c
        unfold act
        simp only [Pi.neg_apply]
        exact integral_neg _
      rw [hneg, hneg] at this
      linarith
    refine ⟨hev', ?_⟩
    have e : 2 * (m + 1) + 1 = 2 * (m + 1) + 1 := rfl
    rw [Function.iterate_succ_apply']
    have hev_test : IsTest S (q ^ (2 * (m + 1)) * L) ((act T)^[2 * (m + 1)] f) := hf.iterate h _
    exact hrev.anti _ _ hev_test hev'

/-- A monotone test function at the least point of `S` is below its mean under
any probability concentrated on `S`. -/
theorem le_integral_of_monotoneOn {lam : Measure ℝ} [IsProbabilityMeasure lam]
    (hsupp : lam Sᶜ = 0) {g : ℝ → ℝ} (hg : MonotoneOn g S) (hgint : Integrable g lam)
    {a₀ : ℝ} (ha₀ : IsLeast S a₀) :
    g a₀ ≤ ∫ b, g b ∂lam := by
  have : ∫ _b, g a₀ ∂lam ≤ ∫ b, g b ∂lam := by
    refine integral_mono_ae (integrable_const _) hgint ?_
    filter_upwards [ae_mem_of_compl_eq_zero hsupp] with b hb
    exact hg ha₀.1 hb (ha₀.2 hb)
  simpa using this

theorem integral_le_of_antitoneOn {lam : Measure ℝ} [IsProbabilityMeasure lam]
    (hsupp : lam Sᶜ = 0) {g : ℝ → ℝ} (hg : AntitoneOn g S) (hgint : Integrable g lam)
    {a₀ : ℝ} (ha₀ : IsLeast S a₀) :
    ∫ b, g b ∂lam ≤ g a₀ := by
  have : ∫ b, g b ∂lam ≤ ∫ _b, g a₀ ∂lam := by
    refine integral_mono_ae hgint (integrable_const _) ?_
    filter_upwards [ae_mem_of_compl_eq_zero hsupp] with b hb
    exact hg ha₀.1 hb (ha₀.2 hb)
  simpa using this

/-- Two steps of `T` from the least point do not decrease a monotone test
function: `T²g(a₀) ≥ g(a₀)`. -/
theorem le_act_act_of_monotoneOn [IsSFiniteKernel T] (h : Contraction T S q)
    {L : ℝ≥0} {g : ℝ → ℝ} (hg : IsTest S L g) (hmono : MonotoneOn g S)
    {a₀ : ℝ} (ha₀ : IsLeast S a₀) :
    g a₀ ≤ act T (act T g) a₀ := by
  have hprob := h.prob a₀ ha₀.1
  have hgtest := hg.map h
  have hinner : ∀ b ∈ S, g a₀ ≤ act T g b := fun b hb => by
    have := h.prob b hb
    exact le_integral_of_monotoneOn (h.supp b hb) hmono (h.integrable L g hg b hb) ha₀
  have : ∫ _b, g a₀ ∂T a₀ ≤ ∫ b, act T g b ∂T a₀ := by
    refine integral_mono_ae (integrable_const _) (h.integrable _ _ hgtest a₀ ha₀.1) ?_
    filter_upwards [ae_mem_of_compl_eq_zero (h.supp a₀ ha₀.1)] with b hb
    exact hinner b hb
  show g a₀ ≤ ∫ b, act T g b ∂T a₀
  simpa using this

end SlopeEvaluation
end SwingRepair
