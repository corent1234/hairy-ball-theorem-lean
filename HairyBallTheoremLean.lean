import Mathlib.Topology.MetricSpace.PseudoMetric
import Mathlib.Topology.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Topology.ContinuousFunction.Polynomial
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

set_option autoImplicit false



variable (n : ℕ) (n_pos : 0 < n) (n_even : Even n)

abbrev E := EuclideanSpace ℝ (Fin (n+1))
abbrev unitSphere := Metric.sphere (0 : E n) 1

/- structure ?-/
structure IsVectorFieldOnSn (v : E n → E n) where
  isCont : Continuous v
  isTang : ∀ x : EuclideanSpace ℝ (Fin (n+1)), x ∈ unitSphere n → ⟪x, (v x)⟫_ℝ = 0



section

variable (v : E n → E n) (hv : IsVectorFieldOnSn n v)
  {vContDiff : ContDiff ℝ 1 v}
  {vUnit : ∀ x : EuclideanSpace ℝ (Fin (n+1)), ‖v x‖ = ‖x‖}
  {A : Set (EuclideanSpace ℝ (Fin (n+1)))} (AComp : IsCompact A)

instance instComp : CompactSpace (A : Type) :=
  isCompact_iff_compactSpace.1 AComp

local notation "f" => fun (t : ℝ) (x : EuclideanSpace ℝ (Fin (n+1))) ↦ x + t • (v x)

open Topology

variable {v}

lemma measurable_ft : ∀ t, Measurable (f t) :=
  fun _ => measurable_id.add (measurable_const.smul hv.isCont.measurable)

/- v est lipschitzienne sur A -/
lemma vLip : ∃ c > 0, LipschitzOnWith c v A := by
  sorry

lemma ftx_eq_fty (t : ℝ) {x y : E n} {hx : x ∈ A} {hy : y ∈ A} (h : f t x = f t y) : x - y = t • (v y - v x) := by
  sorry

lemma eq_zero_of_le_self {α t : ℝ} (ht : |t| < 1) (h : α ≤ |t| * α) : α = 0 := by
  sorry

/- f t est injectif sur A pour t assez petit -/
lemma InjOn_A_ft : ∀ᶠ t in 𝓝 0, A.InjOn (f t) := by
  sorry
/-  let ⟨c, cpos, vlip⟩ := vLip (v := v) (A := A)
  use c⁻¹
  constructor
  · exact inv_pos.mpr cpos
  · intro t ht x hx y hy hxy
    apply eq_of_sub_eq_zero
    apply norm_eq_zero.1
    have : |t * c| < 1 := by sorry
    apply eq_zero_of_le_self this
    nth_rw 1 [ftx_eq_fty _ hxy]
    rw [norm_smul, abs_mul, mul_assoc]
    sorry
    sorry
    sorry
    sorry -/

/- v est différentiable -/
lemma Diff_v : Differentiable ℝ v :=
  vContDiff.differentiable le_rfl

/- f t est différentiable -/
lemma Diff_ft : ∀ t : ℝ, Differentiable ℝ (f t) := by
  sorry

/- différentielle de f t en x -/
local notation "f'" =>
  fun (t : ℝ) (x : E n) ↦ (ContinuousLinearMap.id ℝ (E n)) + (t • (fderiv ℝ v x))
/- noncomputable def f' (t : ℝ) (x : E n) :=
  (ContinuousLinearMap.id ℝ _) + (t • (fderiv ℝ v x)) -/

/- f' t x est la différentielle de f t en x ∈ A -/
lemma ftDeriv : ∀ t : ℝ, ∀ x ∈ A, HasFDerivWithinAt (f t) (f' t x) A x := by
  sorry

/- f' t x est la différentielle (stricte) de f t en x -/
lemma ftStrictDeriv (t : ℝ) (x : E n) : HasStrictFDerivAt (f t) (f' t x) x := by
  sorry

open MeasureTheory

/- A est mesurable -/
lemma meas_A : MeasurableSet A :=
  AComp.isClosed.measurableSet

lemma lintegral_abs_det_f't : ∀ᶠ t in 𝓝 0,
    ∫⁻ x in A, ENNReal.ofReal |(f' t x).det| ∂volume = volume ((f t) '' A) := by
  filter_upwards [@InjOn_A_ft n v A] with t hinj
  exact lintegral_abs_det_fderiv_eq_addHaar_image volume (meas_A n AComp) (ftDeriv n t) hinj

lemma ft_volume_withDensity_abs_det_f't_eq_volume : ∀ᶠ t in 𝓝 0,
    Measure.map (f t) ((volume.restrict A).withDensity fun x => ENNReal.ofReal |(f' t x).det|)
    = volume.restrict ((f t) '' A) := by
  filter_upwards [@InjOn_A_ft n v A] with t hinj
  exact map_withDensity_abs_det_fderiv_eq_addHaar volume (meas_A n AComp) (ftDeriv n t) hinj (measurable_ft n hv t)

open Polynomial
open Finset

/- LinearMap.toMatrix : ça devrait aller
+ det commute avec les morphismes d'algebre -/
/- det (f' t x) est polynomial en t et les coefficients sont continus en x -/
lemma f't_det_poly : ∃ P : E n → Polynomial ℝ,
    (∀ x : E n, (P x).natDegree ≤ n)
    ∧ (∀ x : E n, (P x).coeff 0 = 1)
    ∧ (∀ t : ℝ, ∀ x : E n, (f' t x).det = (P x).eval t)
    ∧ (∀ k : ℕ, Continuous fun x => (P x).coeff k)
    ∧ (∀ k : ℕ, Measurable fun x => (P x).coeff k) := by
  sorry

lemma zero_lt_continuous (g : ℝ → ℝ) (hg : Continuous g) (h0 : g 0 = 1) : ∀ᶠ t in 𝓝 0, 0 < g t :=
  eventually_gt_of_tendsto_gt (by linarith) (hg.tendsto' _ _ rfl)

/- si P 0 = 1 alors P t > 0 pour t assez petit -/
lemma zero_lt_poly (P : Polynomial ℝ) (h0 : P.coeff 0 = 1) : ∀ᶠ t in 𝓝 0, 0 < P.eval t := by
  apply zero_lt_continuous P.toContinuousMap P.toContinuousMap.continuous
  simpa [← P.coeff_zero_eq_eval_zero]

lemma continuous_bound (M : ℝ) :
    Continuous (fun t => 1 - M * (range n).sum fun k => |t| ^ (k + 1)) :=
  continuous_const.sub ((continuous_mul_left M).comp
    (continuous_finset_sum _ (fun _ _ => (continuous_pow _).comp continuous_abs)))

lemma pos_bound (M : ℝ) : ∀ᶠ t in 𝓝 0,
    0 < 1 - M * (range n).sum fun k => |t| ^ (k + 1) := by
  apply zero_lt_continuous _ (continuous_bound n M)
  simp

lemma range_bounded (ι : ℕ → ℝ) (m : ℕ) (hm : m > 0) (hι : ι 0 > 0) :
    ∃ M > 0, ∀ k ∈ range m, ι k ≤ M :=
  ⟨((range m).image ι).max' ((nonempty_range_iff.2 (by linarith)).image ι),
    by linarith [((range m).image ι).le_max' (ι 0) (mem_image_of_mem ι (mem_range.2 (by linarith)))],
    fun _ hk => le_max' _ _ (mem_image_of_mem ι hk)⟩

lemma unif_bounded_range_of_bounded {α : Type} (ι : ℕ → α → ℝ) (h : ∀ k, ∃ M, ∀ x, |ι k x| ≤ M) (m : ℕ) :
    ∃ M, ∀ k ∈ range m, ∀ x, |ι k x| ≤ M := by
  induction' m with m hm
  · simp
  · let ⟨M₀, hM₀⟩ := hm
    let ⟨M, hM⟩ := h m
    use max M M₀
    simp
    intro k k_le_m x
    by_cases hk : k = m
    · rw [hk]
      exact Or.inl (hM x)
    · exact Or.inr (hM₀ k (mem_range.2 (lt_of_le_of_ne (Nat.le_of_lt_succ k_le_m) hk)) x)

lemma useless_lemma (g : ℕ → ℝ) (n : ℕ) :
    (range (n + 1)).sum g = (range (1 + n)).sum g := by
  rw [add_comm]

lemma bound_poly (P : E n → Polynomial ℝ) (hdeg : ∀ x, (P x).natDegree ≤ n)
    (h0 : ∀ x, (P x).coeff 0 = 1) (hcont : ∀ k, Continuous (fun x => (P x).coeff k)) :
    ∃ M, ∀ t : ℝ, ∀ x : A,
    1 - M * ((range n).sum fun k => |t| ^ (k + 1)) ≤ (P x).eval t := by
  let continuous_coeff (k : ℕ) : C(A,ℝ) := ContinuousMap.restrict A ⟨_, hcont k⟩
  let bounded_continuous_coeff (k : ℕ) := @BoundedContinuousFunction.mkOfCompact A ℝ _ _ (instComp n AComp) (continuous_coeff k)
  have : ∀ k, ∃ M, ∀ x : A, |(P x).coeff k| ≤ M :=
    fun k => ⟨‖bounded_continuous_coeff k‖, fun x => ((bounded_continuous_coeff k).norm_coe_le_norm x)⟩
  let ⟨M, hM⟩ := unif_bounded_range_of_bounded (fun k (x : A) => (P x).coeff k) this (m := n + 1)
  have : ∀ t, ∀ x : A, ∀ k ∈ range n, - M * |t| ^ (k + 1) ≤ ((P x).coeff (1 + k)) * t ^ (1 + k) := by
    refine fun t x k hk => le_trans ?_ (neg_abs_le _)
    simp [abs_mul, abs_pow, add_comm]
    by_cases h₀ : t = 0
    · simp [h₀]
    · exact (mul_le_mul_right (pow_pos (abs_pos.2 h₀) _)).2 (hM (k + 1) (mem_range_succ_iff.2 (by linarith [mem_range.1 hk])) x)
  use M
  intro t x
  rw [(P x).eval_eq_sum_range' (lt_of_le_of_lt (hdeg x) (lt_add_one n)),
    useless_lemma, sum_range_add, sum_range_one, h0 x,
    pow_zero, mul_one, sub_eq_neg_add, ←neg_mul, mul_sum, add_comm]
  exact add_le_add_left (sum_le_sum (this t x)) _

/- det (f' t x) > 0 pour t assez petit -/
lemma zero_lt_det_f't : ∀ᶠ t in 𝓝 0, ∀ x : A, 0 < (f' t x).det := by
  have ⟨P, hP⟩ := @f't_det_poly n v
  have ⟨M, hM⟩ := bound_poly n AComp P hP.1 hP.2.1 hP.2.2.2.1
  filter_upwards [pos_bound n M] with t ht x
  rw [hP.2.2.1 t x]
  exact lt_of_lt_of_le ht (hM t x)

/- |det (f' t x)| est polynomial en t et les coefficients sont continus en x -/
lemma abs_det_f't_poly : ∃ P : E n → Polynomial ℝ,
    (∀ x : E n, (P x).natDegree ≤ n)
    ∧ (∀ᶠ t in 𝓝 0, ∀ x : A, |(f' t x).det| = (P x).eval t)
    ∧ (∀ k : ℕ, Continuous fun x => (P x).coeff k)
    ∧ (∀ k : ℕ, Measurable fun x => (P x).coeff k) := by
  have ⟨P, hP⟩ := @f't_det_poly n v
  refine' ⟨P, hP.1, _, hP.2.2.2⟩
  filter_upwards [zero_lt_det_f't n AComp] with t hpos x
  rw [abs_of_pos (hpos x), hP.2.2.1 t]

lemma cont_abs_det_f't (t : ℝ) : Continuous (fun x => |(f' t x).det|) := by
  sorry

lemma nonneg_ae_abs_det_f't (t : ℝ) : 0 ≤ᵐ[volume.restrict A] fun x => |(f' t x).det| :=
  sorry

/- ecrire le polynome comme somme finie -/
/- le volume de (f t)''(A) est polynomial en t -/
lemma vol_ft_A_poly : ∃ P : Polynomial ℝ, ∀ᶠ t in 𝓝 0,
    (volume ((f t) '' A)).toReal = (P.eval t) := by
  let ⟨P, hP⟩ := @abs_det_f't_poly n v A AComp
  use (range (n + 1)).sum (fun i => C (∫ x in A, (P x).coeff i ∂volume) * X ^ i)
  filter_upwards [@lintegral_abs_det_f't n v A AComp, hP.2.1] with t hInt hP1
  have meas_coeff : ∀ k ∈ range n, Measurable fun x => ENNReal.ofReal ((P x).coeff k * t ^ k) :=
    fun k _ => ENNReal.measurable_ofReal.comp ((hP.2.2.2 k).mul measurable_const)
  simp [← hInt, eval_finset_sum,
    ← integral_eq_lintegral_of_nonneg_ae (nonneg_ae_abs_det_f't n t) (cont_abs_det_f't n t).aestronglyMeasurable]
  have : A.EqOn (fun x => |(f' t x).det|) (fun x => (range (n + 1)).sum (fun n => (P x).coeff n * t ^ n)) := by
    sorry
  rw [set_integral_congr (meas_A n AComp) this]
  have integrable_coeff (i : ℕ) : Integrable (fun x => (P x).coeff i * t ^ i) (volume.restrict A) :=
    sorry
  rw [integral_finset_sum _ (fun i _ => integrable_coeff i)]
  have : (fun i => ∫ x in A, (P x).coeff i * t ^ i) = (fun i => (∫ x in A, (P x).coeff i) * t ^ i) :=
    sorry
  rw [this]

/- LinearMap.equivOfDetNeZero, toContinuousLinearEquiv -/
/- f' t est une equivalence linéaire si t est assez petit -/
@[simps!?]
noncomputable def f't_equiv (t : ℝ) (x : E n) : E n ≃L[ℝ] E n where
  toLinearMap := f' t x
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry

lemma inner_self_v_eq_zero (t : ℝ) (x : E n) : ⟪x, t • v x⟫_ℝ = 0 := by
  sorry

lemma im_ft_subset (t : ℝ) : (f t) '' (unitSphere n) ⊆ Metric.sphere 0 (Real.sqrt (1 + t*t)) := by
  intro y ⟨x, xUnit, hxy⟩
  rw [← hxy]
  simp
  unfold unitSphere at xUnit
  have : ‖x‖ = 1 := by simp at xUnit; assumption
  rw [← Real.sqrt_mul_self (norm_nonneg _), norm_add_sq_eq_norm_sq_add_norm_sq_real (inner_self_v_eq_zero n t x)]
  rw [this, norm_smul, vUnit x, this]
  simp

lemma rank_EuclideanSpace : FiniteDimensional.finrank ℝ (E n) = n + 1 := by
  sorry

lemma one_lt_rank_EuclideanSpace : 1 < Module.rank ℝ (E n) := by
  apply FiniteDimensional.one_lt_rank_of_one_lt_finrank
  rw [rank_EuclideanSpace]
  linarith

local notation "f_restr" => fun (t : ℝ) ↦ Set.restrictPreimage (Metric.sphere 0 (Real.sqrt (1 + t*t))) (f t)

lemma ft_preimage (t : ℝ) : (f t) ⁻¹' (Metric.sphere 0 (Real.sqrt (1 + t*t))) = unitSphere n := by
  sorry

/- Mq f(unitSphere) = f(E) ∩ Metric.sphere 0 (Real.sqrt (1 + t*t)) puis OK -/
/- f t est ouverte pour t assez petit (théorème d'inversion globale) -/
lemma ft_open : ∀ᶠ t in 𝓝 0, IsOpenMap (f_restr t) := by
  sorry
/-  let ⟨ε, εpos, h⟩ := @ftStrictDeriv n v /- ??? -/
  use ε
  constructor; assumption
  intro t ht
  /- apply open_map_of_strict_fderiv_equiv (𝕜 := ℝ) (h t ht) -/
  sorry -/

lemma connected_sphere (t : ℝ) : IsConnected (Metric.sphere (0 : E n) (Real.sqrt (1 + t*t))) :=
  isConnected_sphere (one_lt_rank_EuclideanSpace n n_pos) 0 (Real.sqrt_nonneg (1 + t*t))

lemma im_ft_open : ∀ᶠ t in 𝓝 0, IsOpen ((f t) '' (unitSphere n)) := by
  sorry

lemma im_ft_closed : ∀ᶠ t in 𝓝 0, IsClosed ((f t) '' (unitSphere n)) := by
  sorry

lemma im_ft : ∀ᶠ t in 𝓝 0,
  (f t) '' (unitSphere n) = Metric.sphere 0 (Real.sqrt (1 + t*t)) := by
  sorry

theorem HairyBallDiff : ∃ x, v x = 0 := by
  sorry

end



section

variable (v : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1))) (hv : IsVectorFieldOnSn n v)

theorem HairyBallTheorem : ∃ x, v x = 0 := by
  sorry

end
