import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Dimension.Finrank
-- import Mathlib.Algebra.BigOperators.Group.Finset

set_option autoImplicit false

open scoped RealInnerProductSpace



variable (n : ℕ) (n_pos : 0 < n)

abbrev E := EuclideanSpace ℝ (Fin n)
abbrev unitSphere := Metric.sphere (0 : E n) 1

/- structure ?-/
structure IsExtensionOfVectorFieldOnSn (v : E n → E n) where
  isCont : Continuous v
  isTang : ∀ x : E n, ⟪x, (v x)⟫ = 0
  isExtension : ∀ x : E n, ∀ r > 0, v (r • x) = r • v x



section

variable (v : E n → E n) (hv : IsExtensionOfVectorFieldOnSn n v)
  {vContDiff : ContDiff ℝ 1 v}
  {vUnit : ∀ x : E n, ‖v x‖ = ‖x‖}
  {A : Set (E n)} (AComp : IsCompact A)

instance instComp : CompactSpace (A : Type) :=
  isCompact_iff_compactSpace.1 AComp

local notation "f" => fun (t : ℝ) (x : E n) ↦ x + t • (v x)

open Topology

variable {v}

include vContDiff in
lemma continuous_ft (t : ℝ) : Continuous (f t) :=
  continuous_id.add (continuous_const.smul vContDiff.continuous)

include hv in
lemma measurable_ft (t : ℝ) : Measurable (f t) :=
  measurable_id.add (measurable_const.smul hv.isCont.measurable)

lemma vLip' : ∃ c : NNReal, LipschitzWith c (fun x : A => v x) := by
  have : HasCompactSupport (fun x : A => v x) := by
    sorry
  -- apply ContDiff.lipschitzWith_of_hasCompactSupport this _ (le_refl)
  sorry

/- v est lipschitzienne sur A -/
include AComp vContDiff in
lemma vLip : ∃ c, LipschitzOnWith c v A := by
  let ⟨r, hr⟩ := AComp.isBounded.subset_ball 0
  let ⟨c, hc⟩ := (Euclidean.isCompact_closedBall (x := (0 : E n))
    (r := |r|)).exists_bound_of_continuousOn ((vContDiff.continuous_fderiv (le_refl 1)).continuousOn)
  use ⟨c, le_trans (norm_nonneg _) (hc 0 (Metric.mem_closedBall_self (abs_nonneg r)))⟩
  apply LipschitzOnWith.mono _ ((hr.trans (Metric.ball_subset_ball (le_abs_self r))).trans Metric.ball_subset_closedBall)
  apply (convex_closedBall 0 |r|).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    (fun x _ => vContDiff.contDiffAt.differentiableAt (le_refl 1))
  intro x hx
  have : x ∈ Euclidean.closedBall 0 |r| := by
    simp [Euclidean.closedBall_eq_preimage]
    rw [← sub_zero x]
    sorry
  rw [Euclidean.closedBall_eq_preimage] at hc
  simp at hc
  sorry

lemma ftx_eq_fty (t : ℝ) {x y : E n} (h : f t x = f t y) :
    x - y = t • (v y - v x) := by
  rw [smul_sub, sub_eq_sub_iff_add_eq_add, add_comm _ y]
  exact h

lemma eq_zero_of_le_self {α t : ℝ} (hα : 0 ≤ α) (ht : |t| < 1) (h : α ≤ |t| * α) :
    α = 0 := by
  by_contra h_contra
  have : 1 ≤ |t| := by
    rwa [← mul_le_mul_right (hα.lt_of_ne (ne_comm.1 h_contra)), one_mul]
  linarith

/- f t est injectif sur A pour t assez petit -/
lemma injOn_A_ft : ∀ᶠ t in 𝓝 0, A.InjOn (f t) := by
  /- let ⟨c, hc⟩ := @vLip n v vContDiff A AComp
  rw [eventually_nhds_iff]
  use (Metric.ball 0 c⁻¹)
  simp
  refine ⟨fun t ht x hx y hy hxy => ?_, Metric.isOpen_ball, by assumption⟩
  apply sub_eq_zero.1
  apply norm_eq_zero.1
  apply eq_zero_of_le_self (t := c * |t|)
  · rw [abs_mul, abs_abs, abs_eq_self.2 cpos.le]
    apply (@mul_lt_mul_left _ c⁻¹.toReal (c * |t|) 1 _ _ _ _ _ (inv_pos_of_pos cpos)).1
    rw [← mul_assoc]
    show (c⁻¹ * c).toReal * |t| < c⁻¹ * 1
    simp [@inv_mul_cancel_of_invertible _ _ _ (invertibleOfNonzero cpos.ne.symm), ht]
  · have : x - y = t • v y - t • v x := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm _ y]
      exact hxy
    rw [this, ← smul_sub, norm_smul]
    by_cases ht0 : t = 0
    · rw [ht0]
      simp
    · -- apply le_trans ((mul_le_mul_left (abs_pos.2 ht0)).2 (hc hy hx))
      sorry -/
  sorry

/- différentielle de f t en x -/
local notation "f'" =>
  fun (t : ℝ) (x : E n) ↦ (ContinuousLinearMap.id ℝ (E n)) + (t • (fderiv ℝ v x))
/- noncomputable def f' (t : ℝ) (x : E n) :=
  (ContinuousLinearMap.id ℝ _) + (t • (fderiv ℝ v x)) -/

/- f' t x est la différentielle de f t en x ∈ A -/
include vContDiff in
lemma ftDeriv (t : ℝ) : ∀ x ∈ A, HasFDerivWithinAt (f t) (f' t x) A x :=
  fun x _ => ((hasFDerivAt_id x).add
    ((vContDiff.differentiable le_rfl).differentiableAt.hasFDerivAt.const_smul t)).hasFDerivWithinAt

/- f' t x est la différentielle (stricte) de f t en x -/
include vContDiff in
lemma ftStrictDeriv (t : ℝ) (x : E n) : HasStrictFDerivAt (f t) (f' t x) x :=
  (hasStrictFDerivAt_id x).add
    ((vContDiff.contDiffAt.hasStrictFDerivAt le_rfl).const_smul t)


section vol_poly

local notation "jac_f" =>
  fun (x : E n) ↦ LinearMap.toMatrix' (fderiv ℝ v x : E n →ₗ[ℝ] E n)

open MeasureTheory

/- A est mesurable -/
include AComp in
lemma meas_A : MeasurableSet A :=
  AComp.isClosed.measurableSet

include AComp vContDiff in
lemma lintegral_abs_det_f't : ∀ᶠ t in 𝓝 0,
    ∫⁻ x in A, ENNReal.ofReal |(f' t x).det| ∂volume = volume ((f t) '' A) := by
  filter_upwards [@injOn_A_ft n v A] with t hinj
  exact lintegral_abs_det_fderiv_eq_addHaar_image volume
    (meas_A n AComp) (@ftDeriv n v vContDiff A t) hinj

include AComp vContDiff hv in
lemma ft_volume_withDensity_abs_det_f't_eq_volume : ∀ᶠ t in 𝓝 0,
    Measure.map (f t) ((volume.restrict A).withDensity fun x => ENNReal.ofReal |(f' t x).det|)
    = volume.restrict ((f t) '' A) := by
  filter_upwards [@injOn_A_ft n v A] with t hinj
  exact map_withDensity_abs_det_fderiv_eq_addHaar volume
    (meas_A n AComp) (@ftDeriv n v vContDiff A t) hinj (measurable_ft n hv t)

open Polynomial
open Finset
open Matrix

lemma natDegree_det (M : Matrix (Fin n) (Fin n) ℝ[X]) (h : ∀ i j, (M i j).natDegree ≤ 1) :
    M.det.natDegree ≤ n := by
  rw [det_apply]
  refine le_trans (natDegree_sum_le _ _) ((fold_max_le n).2 ⟨zero_le n, fun σ _ => ?_⟩)
  show natDegree ((Equiv.Perm.sign σ).val • univ.prod fun i => M (σ i) i) ≤ n
  rw [← @Int.cast_smul_eq_zsmul ℝ ℝ[X] _ _ _ (Equiv.Perm.sign σ) (univ.prod fun i => M (σ i) i)]
  refine le_trans (natDegree_smul_le (Equiv.Perm.sign σ : ℝ) (univ.prod fun i => M (σ i) i))
    (le_trans (natDegree_prod_le _ _) (le_trans (sum_le_sum (fun i _ => h (σ i) i)) ?_))
  simp

lemma prod_perm_fixpoint (σ : Equiv.Perm (Fin n)) :
    univ.prod (fun i => if σ i = i then (1 : ℝ) else 0) = if 1 = σ then 1 else 0 := by
  by_cases hσ : 1 = σ
  · simp [← hσ]
  · have : ¬(∀ i, (1 : Equiv.Perm (Fin n)) i = σ i) :=
      not_imp_not.2 Equiv.ext hσ
    simp at this
    have ⟨j, hj⟩ := this
    rw [prod_eq_zero (Finset.mem_univ j)]
    · simp [eq_false hσ]
    · simp [eq_false (fun (e : σ j = j) => hj (by rw [e]))]

lemma sum_perm_sign_smul_prod_fixpoint : univ.sum (fun (σ : Equiv.Perm (Fin n)) =>
    Equiv.Perm.sign σ • univ.prod (fun i => if σ i = i then (1 : ℝ) else 0)) = 1 := by
  have : (fun (σ : Equiv.Perm (Fin n)) =>
      Equiv.Perm.sign σ • univ.prod (fun i => if (σ i) = i then (1 : ℝ) else 0))
      = (fun σ => if 1 = σ then 1 else 0) := by
    ext σ
    rw [prod_perm_fixpoint n σ, apply_ite (fun ε => Equiv.Perm.sign σ • ε)]
    by_cases hσ : 1 = σ
    · simp [← hσ]
    · simp [eq_false hσ]
  rw [this, sum_ite_eq]
  simp

lemma univ_fin_one_singleton : (univ : Finset (Fin 1)) = {0} := rfl

lemma prod_fin_one {α : Type} [CommMonoid α] (g : Fin 1 → α) :
    univ.prod g = g 0 := by
  rw [univ_fin_one_singleton, prod_singleton]

lemma coeff_ite (p : Prop) [Decidable p] (P Q : ℝ[X]) (k : ℕ) :
    (if p then P else Q).coeff k = if p then P.coeff k else Q.coeff k :=
  apply_ite (fun q : ℝ[X] => q.coeff k) p P Q

lemma continuous_coeff_C_mul_X {b : E n → ℝ} {k : ℕ} (h : Continuous b) :
    Continuous (fun x => (C (b x) * X).coeff k) := by
  by_cases k_one : k = 1
  · have : (fun x => (C (b x) * X).coeff k) = b := by
      ext x
      simp [k_one, coeff_C_mul_X]
    rwa [this]
  · have : (fun x => (C (b x) * X).coeff k) = 0 := by
      ext x
      rw [coeff_C_mul_X]
      simp [k_one]
    rw [this]
    exact continuous_zero

lemma C_add_C_mul_X_coeff_0 (a : ℝ) (b : ℝ) : (C a + C b * X).coeff 0 = a := by
  simp [coeff_add, coeff_C, coeff_C_mul_X]

lemma C_add_C_mul_X_coeff_1 (a : ℝ) (b : ℝ) : (C a + C b * X).coeff 1 = b := by
  simp [coeff_add, coeff_C, coeff_C_mul_X]

lemma C_add_C_mul_X_coeff_of_one_lt (a : ℝ) (b : ℝ) (k : ℕ) (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    (C a + C b * X).coeff k = 0 := by
  rw [coeff_add, coeff_C, coeff_C_mul_X]
  simp [hk0, hk1]

lemma continuous_coeff_C_add_C_mul_X {a : ℝ} {b : E n → ℝ} {k : ℕ} (h : Continuous b) :
    Continuous (fun x => (C a + C (b x) * X).coeff k) := by
  by_cases hk0 : k = 0
  · rw [hk0, funext (fun x => C_add_C_mul_X_coeff_0 _ _)]
    exact continuous_const
  · by_cases hk1 : k = 1
    · rwa [hk1, funext (fun x => C_add_C_mul_X_coeff_1 _ _)]
    · rw [funext (fun x => C_add_C_mul_X_coeff_of_one_lt _ _ k hk0 hk1)]
      exact continuous_const

def my_coe (u : E n →L[ℝ] E n) : E n → E n := u

lemma continuous_my_coe : Continuous (my_coe n) :=
  continuous_pi fun x => (ContinuousLinearMap.apply ℝ (E n) x).continuous

include vContDiff in
lemma continuous_jac_f_apply {i j : Fin n} :
    Continuous (fun x => jac_f x i j) := by
  simp
  exact (continuous_apply_apply _ _).comp
    ((continuous_my_coe n).comp
    (vContDiff.continuous_fderiv (by rfl)))

lemma ofNat'_val (m : ℕ) (hm : 0 < m) (i : Fin m) : @Fin.ofNat' m (NeZero.of_gt hm) i.val = i := by
  apply Fin.eq_of_val_eq
  show i.val % m = i.val
  rw [Nat.mod_eq_of_lt (Fin.prop i)]

lemma univ_Fin_map_val_eq_range (m : ℕ) :
    (univ : Finset (Fin m)).map Fin.valEmbedding = range m := by
  by_cases hm : m = 0
  · subst hm
    simp
  · ext i
    rw [mem_range, mem_map]
    exact ⟨fun ⟨j,_,hj⟩ => by rw [← hj]; exact (Fin.prop j),
      fun hi => ⟨@Fin.ofNat' m (NeZero.mk hm) i, mem_univ _, Nat.mod_eq_of_lt hi⟩⟩

lemma prod_univ_Fin_eq_prod_range {α : Type} [CommMonoid α] (m : ℕ) (g : ℕ → α) :
    (univ : Finset (Fin m)).prod (fun i => g i.val) = (range m).prod g := by
  rw [← univ_Fin_map_val_eq_range, prod_map]
  rfl

include n_pos in
lemma continuous_coeff_prod (m : ℕ) (hm : 0 < m) (hmn : m ≤ n) (k : ℕ)
    (P : Fin n → E n → ℝ[X]) (hP : ∀ i k', Continuous (fun x => (P i x).coeff k')) :
    Continuous fun x => ((univ : Finset (Fin m)).prod (fun i => P (@Fin.ofNat' n (NeZero.of_gt n_pos) i) x)).coeff k := by
  have : (fun x => ((univ : Finset (Fin m)).prod (fun i => P (@Fin.ofNat' n (NeZero.of_gt n_pos) i) x)).coeff k)
      = (fun x => ((range m).prod (fun i => P (@Fin.ofNat' n (NeZero.of_gt n_pos) i) x)).coeff k) := by
    ext x
    rw [← prod_univ_Fin_eq_prod_range]
  rw [this]
  induction' m with m ih generalizing k
  · simp [coeff_one, continuous_const]
  · have : (fun x => (∏ i ∈ range (m + 1), P (@Fin.ofNat' n (NeZero.of_gt n_pos) i) x).coeff k)
        = (fun x => ∑ μ ∈ antidiagonal k, (P (@Fin.ofNat' n (NeZero.of_gt n_pos) m) x).coeff μ.1
        * (∏ i ∈ range m, P (@Fin.ofNat' n (NeZero.of_gt n_pos) i) x).coeff μ.2) := by
      ext x
      rw [range_succ, prod_insert not_mem_range_self, coeff_mul]
    rw [this]
    refine continuous_finset_sum _ (fun μ _ => (hP _ _).mul ?_)
    by_cases mz : m = 0
    · have : (fun x => ((range m).prod fun i => P (@Fin.ofNat' n (NeZero.of_gt n_pos) i) x).coeff μ.2)
          = (fun x => if μ.2 = 0 then 1 else 0) := by
        ext x
        simp [mz, coeff_one]
      rw [this]
      exact continuous_const
    · exact ih (pos_iff_ne_zero.2 mz) (lt_of_lt_of_le (Nat.lt_succ_self m) hmn).le
        μ.2 (by ext x; rw [← prod_univ_Fin_eq_prod_range])

include n_pos in
lemma continuous_coeff_prod' (k : ℕ) (P : Fin n → E n → ℝ[X])
    (hP : ∀ i k', Continuous (fun x => (P i x).coeff k')) :
    Continuous fun x => ((univ : Finset (Fin n)).prod (fun i => P i x)).coeff k := by
  have : (fun x => (univ.prod (fun i => P i x)).coeff k)
      = (fun x => ((univ : Finset (Fin n)).prod
      (fun i => P (@Fin.ofNat' n (NeZero.of_gt n_pos) i) x)).coeff k) :=
    (funext fun x => congrArg (fun p => coeff p k)
      (congrArg _ (funext fun i => (congrArg (fun j => P j x) (by rw [ofNat'_val _ n_pos])))))
  rw [this]
  exact continuous_coeff_prod _ n_pos _ n_pos le_rfl _ _ hP

/- det (f' t x) est polynomial en t et les coefficients sont continus en x -/
include n_pos vContDiff in
lemma f't_det_poly : ∃ P : E n → Polynomial ℝ,
    (∀ x : E n, (P x).natDegree ≤ n)
    ∧ (∀ x : E n, (P x).coeff 0 = 1)
    ∧ (∀ t : ℝ, ∀ x : E n, (f' t x).det = (P x).eval t)
    ∧ (∀ k : ℕ, Continuous fun x => (P x).coeff k) := by
  let P := (fun x =>
    (of (fun i j => (if i = j then 1 else 0) + C (jac_f x i j) * X)).det)
  use P
  constructor
  · refine fun x => natDegree_det _ _ (fun i j => ?_)
    rw [of_apply]
    apply le_trans (natDegree_add_le _ _)
    rw [apply_ite natDegree, natDegree_one, natDegree_zero, ite_id, Nat.zero_max]
    apply le_trans natDegree_mul_le
    simp
  · constructor
    · intro x
      dsimp [P]
      rw [det_apply, finset_sum_coeff, ← sum_perm_sign_smul_prod_fixpoint]
      apply congrArg
      ext σ
      rw [coeff_smul, coeff_zero_prod]
      apply congrArg (fun α => _ • univ.prod α)
      ext i
      simp [apply_ite (fun p => coeff p 0)]
    · constructor
      · intro t x
        show LinearMap.det (f' t x : E n →ₗ[ℝ] E n) = eval t (P x)
        have useless : LinearMap.det (f' t x : E n →ₗ[ℝ] E n) =
            (LinearMap.toMatrix' (LinearMap.id + t • (fderiv ℝ v x : E n →ₗ[ℝ] E n))).det := by
          rw [LinearMap.det_toMatrix']
          rfl
        rw [useless]
        simp
        rw [LinearMap.toMatrix'_id]
        have : 1 + t • jac_f x = (of (fun i j => ((if i = j then 1 else 0)
            + C (jac_f x i j) * X))).map (eval t) := by
          ext i j
          simp
          rw [one_apply, mul_comm, apply_ite (eval t)]
          simp
        rw [this, ← coe_evalRingHom, ← RingHom.mapMatrix_apply (evalRingHom t), ← RingHom.map_det]
      · intro k
        have P_coeff : (fun x => (P x).coeff k)
            = (fun x => univ.sum (fun σ => Equiv.Perm.sign σ
            • (univ.prod (fun i => of (fun i j => (if i = j then 1 else 0)
            + C (jac_f x i j) * X) (σ i) i)).coeff k)) := by
          ext x
          dsimp [P]
          rw [det_apply, finset_sum_coeff]
          apply congrArg
          ext σ
          simp [coeff_smul]
        rw [P_coeff]
        refine continuous_finset_sum _ (fun σ _ => Continuous.const_smul
          (continuous_coeff_prod' _ n_pos _ _ (fun i k' => ?_)) _)
        have : (fun x => (of (fun i j => (if i = j then 1 else 0)
            + C (jac_f x i j) * X) (σ i) i).coeff k')
            = (fun x => if k' = 0 then (if σ i = i then 1 else 0)
            else (if k' = 1 then jac_f x (σ i) i else 0)) := by
          ext x
          rw [of_apply, ← C_1, ← C_0, ← apply_ite C]
          by_cases hk'0 : k' = 0
          · rw [hk'0, C_add_C_mul_X_coeff_0]
            simp
          · by_cases hk'1 : k' = 1
            · rw [hk'1, C_add_C_mul_X_coeff_1]
              simp
            · rw [C_add_C_mul_X_coeff_of_one_lt _ _ k' hk'0 hk'1]
              simp [hk'0, hk'1]
        rw [this]
        exact continuous_if_const _ (fun _ => continuous_const)
            (fun _ => continuous_if_const _
            (fun _ => (@continuous_jac_f_apply n v vContDiff _ _))
            (fun _ => continuous_const))

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

include AComp in
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
include n_pos vContDiff AComp in
lemma zero_lt_det_f't : ∀ᶠ t in 𝓝 0, ∀ x : A, 0 < (f' t x).det := by
  have ⟨P, hP⟩ := @f't_det_poly n n_pos v vContDiff
  have ⟨M, hM⟩ := bound_poly n AComp P hP.1 hP.2.1 hP.2.2.2
  filter_upwards [pos_bound n M] with t ht x
  rw [hP.2.2.1 t x]
  exact lt_of_lt_of_le ht (hM t x)

/- |det (f' t x)| est polynomial en t et les coefficients sont continus en x -/
include n_pos vContDiff AComp in
lemma abs_det_f't_poly : ∃ P : E n → Polynomial ℝ,
    (∀ x : E n, (P x).natDegree ≤ n)
    ∧ (∀ᶠ t in 𝓝 0, ∀ x : A, |(f' t x).det| = (P x).eval t)
    ∧ (∀ k : ℕ, Continuous fun x => (P x).coeff k) := by
  have ⟨P, hP⟩ := @f't_det_poly n n_pos v vContDiff
  refine ⟨P, hP.1, ?_, hP.2.2.2⟩
  filter_upwards [@zero_lt_det_f't n n_pos v vContDiff A AComp] with t hpos x
  rw [abs_of_pos (hpos x), hP.2.2.1 t]

include vContDiff in
lemma cont_abs_det_f't (t : ℝ) : Continuous (fun x => |(f' t x).det|) :=
  continuous_abs.comp (ContinuousLinearMap.continuous_det.comp (continuous_const.add
    (continuous_const.smul (vContDiff.continuous_fderiv (by rfl)))))

lemma nonneg_ae_abs_det_f't (t : ℝ) : 0 ≤ᵐ[volume.restrict A] fun x => |(f' t x).det| := by
  filter_upwards
  simp

/- le volume de (f t)''(A) est polynomial en t -/
include n_pos vContDiff AComp in
lemma vol_ft_A_poly : ∃ P : Polynomial ℝ, ∀ᶠ t in 𝓝 0,
    (volume ((f t) '' A)).toReal = (P.eval t) := by
  let ⟨P, hP⟩ := @abs_det_f't_poly n n_pos v vContDiff A AComp
  use (range (n + 1)).sum (fun i => C (∫ x in A, (P x).coeff i ∂volume) * X ^ i)
  filter_upwards [@lintegral_abs_det_f't n v vContDiff A AComp, hP.2.1] with t hInt hP1
  simp [← hInt, eval_finset_sum,
    ← integral_eq_lintegral_of_nonneg_ae (nonneg_ae_abs_det_f't n t) (@cont_abs_det_f't n v vContDiff t).aestronglyMeasurable]
  have : A.EqOn (fun x => |(f' t x).det|) (fun x => (range (n + 1)).sum (fun n => (P x).coeff n * t ^ n)) := by
    intro x xA
    simp [hP1 ⟨x, xA⟩]
    nth_rw 1 [(P x).as_sum_range' (n + 1) (Nat.lt_succ_of_le (hP.1 x))]
    simp [eval_finset_sum]
  have integrable_coeff (i : ℕ) : Integrable (fun x => (P x).coeff i * t ^ i) (volume.restrict A) :=
    ContinuousOn.integrableOn_compact AComp (Continuous.continuousOn ((hP.2.2 i).smul continuous_const))
  rw [setIntegral_congr (meas_A n AComp) this, integral_finset_sum _ (fun i _ => integrable_coeff i)]
  have : (fun i => ∫ x in A, (P x).coeff i * t ^ i) = (fun i => (∫ x in A, (P x).coeff i) * t ^ i) := by
    ext i
    show ∫ x in A, (P x).coeff i • t ^ i = (∫ x in A, (P x).coeff i) • t ^ i
    rw [integral_smul_const]
  rw [this]

end vol_poly


open Set

/- LinearMap.equivOfDetNeZero, toContinuousLinearEquiv -/
/- f' t est une equivalence linéaire si t est assez petit -/
-- @[simps!?]
/- noncomputable def f't_equiv : ∀ᶠ t in 𝓝 0, E n ≃L[ℝ] E n :=
  -- LinearEquiv.toContinuousLinearEquiv (LinearMap.equivOfDDetNeZero (f' t x) )
  sorry -/

include hv in
lemma inner_self_v_eq_zero_of_norm_one (t : ℝ) (x : E n) :
    ⟪x, t • v x⟫ = 0 := by
  rw [inner_smul_right, hv.isTang x, mul_zero]

include hv vUnit in
lemma ft_mem_sphere_of_mem_sphere (t : ℝ) (x : unitSphere n) :
    f t x ∈ Metric.sphere 0 (Real.sqrt (1 + t*t)) := by
  rw [mem_sphere_iff_norm, sub_zero, ← Real.sqrt_mul_self (norm_nonneg _),
    norm_add_sq_eq_norm_sq_add_norm_sq_real
    (inner_self_v_eq_zero_of_norm_one n hv t x)]
  simp [mem_sphere_zero_iff_norm.1 (Subtype.mem x), norm_smul, vUnit x]

include hv vUnit in
lemma image_ft_subset_sphere (t : ℝ) :
    (f t) '' (unitSphere n) ⊆ Metric.sphere 0 (Real.sqrt (1 + t*t)) :=
  fun y ⟨x, hx, hxy⟩ => by
    rw [← hxy]
    exact @ft_mem_sphere_of_mem_sphere _ _ hv vUnit t ⟨x, hx⟩

include hv vUnit in
lemma ft_mapsTo_sphere (t : ℝ) : MapsTo (f t) (unitSphere n)
    (Metric.sphere 0 (Real.sqrt (1 + t * t))) :=
  fun x hx => @ft_mem_sphere_of_mem_sphere n _ hv vUnit t ⟨x, hx⟩

variable (hn : 1 < n) (vContDiff) (vUnit)

include hn in
lemma one_lt_rank_EuclideanSpace : 1 < Module.rank ℝ (E n) := by
  apply Module.lt_rank_of_lt_finrank
  rw [finrank_euclideanSpace, Fintype.card_fin]
  exact hn

local notation "f_restr" =>
  fun (t : ℝ) ↦ restrictPreimage (Metric.sphere 0 (Real.sqrt (1 + t * t))) (f t)

include vContDiff in
lemma continuous_ft_restr (t : ℝ) : Continuous (f_restr t) :=
  (@continuous_ft n _ vContDiff t).restrict _

include hv vUnit in
lemma ft_preimage_sphere (t : ℝ) :
    (f t) ⁻¹' (Metric.sphere 0 (Real.sqrt (1 + t * t))) = unitSphere n := by
  ext x
  rw [mem_preimage, mem_sphere_iff_norm, sub_zero,
    ← (sq_eq_sq (norm_nonneg _) (Real.sqrt_nonneg _)),
    Real.sq_sqrt (add_nonneg (zero_le_one) (mul_self_nonneg _)),
    norm_add_sq_real, mem_sphere_zero_iff_norm, norm_smul, inner_smul_right,
    vUnit, hv.isTang, ← abs_mul_abs_self, Real.norm_eq_abs, ← mul_one (1 + _)]
  simp only [mul_zero, add_zero]
  have : ‖x‖ ^ 2 + (|t| * ‖x‖) ^ 2 = (1 + |t| * |t|) * ‖x‖ ^ 2 := by ring
  rw [this, mul_eq_mul_left_iff, sq_eq_one_iff]
  simp only [(add_pos_of_pos_of_nonneg (zero_lt_one) (mul_self_nonneg |t|)).ne.symm,
    (lt_of_lt_of_le neg_one_lt_zero (norm_nonneg _)).ne.symm]
  simp

instance instCompactPreimageSphere (t : ℝ) :
    CompactSpace ((f t) ⁻¹' (Metric.sphere 0 (Real.sqrt (1 + t * t)))) := by
  rw [ft_preimage_sphere n hv vUnit]
  exact Metric.sphere.compactSpace _ _

/- lemma ft_restr_strictFDeriv (t : ℝ) (x : Metric.ball (0 : E n) 2) :
    HasStrictFDerivAt (restrict (Metric.ball 0 2) (f t)) (f' t x) x := by
  sorry -/

/- lemma ft_restr_eq_restrictPreimage_restrict (t : ℝ) :
    f_restr t = restrictPreimage (Metric.sphere 0 (Real.sqrt (1 + t * t))) (f t) := by
  sorry -/

lemma preimage_restrict {α β : Type} (s : Set α) (g : α → β) (t : Set β) :
    (restrict s g) ⁻¹' t = s ∩ (g ⁻¹' t) := by
  rw [restrict_eq, preimage_comp]
  exact eq_of_subset_of_subset (subset_inter (Subtype.coe_image_subset _ _)
    (image_preimage_subset _ _))
    (fun x hx => ⟨⟨x, hx.1⟩, ⟨mem_preimage.2 hx.2, rfl⟩⟩)

include n_pos vContDiff in
lemma isOpenMap_ft : ∀ᶠ t in 𝓝 0, IsOpenMap (restrict (Metric.ball 0 2) (f t)) := by
  filter_upwards [@zero_lt_det_f't n n_pos _ vContDiff _
    (ProperSpace.isCompact_closedBall 0 2)] with t ht
  refine isOpenMap_iff_nhds_le.2 (fun ⟨x, hx⟩ => ?_)
  rw [restrict_apply, restrict_eq, ← Filter.map_map,
    ← @HasStrictFDerivAt.map_nhds_eq_of_equiv ℝ _ _ _ _ _ _ _ _
    ((f' t x).equivOfDetNeZero (ht ⟨x, mem_closedBall_zero_iff.2
    (le_of_lt (mem_ball_zero_iff.1 hx))⟩).ne.symm).toContinuousLinearEquiv _ _
    (@ftStrictDeriv n _ vContDiff t x)]
  have : Filter.map Subtype.val (𝓝 (⟨x, hx⟩ : Metric.ball (0 : E n) 2)) = 𝓝 x :=
    eq_of_le_of_le continuous_subtype_val.continuousAt.tendsto
      (isOpenMap_iff_nhds_le.1 Metric.isOpen_ball.isOpenMap_subtype_val ⟨x, hx⟩)
  rw [this]

include hv vUnit in
lemma subtype_val_preimage_ball_eq_sphere (t : ℝ) :
    (univ : Set ((f t) ⁻¹' (Metric.sphere 0 (Real.sqrt (1 + t * t)))))
    = (Subtype.val ⁻¹' (Metric.ball (0 : E n) 2)) := by
  apply eq_preimage_subtype_val_iff.2
  rw [ft_preimage_sphere n hv vUnit]
  exact fun x hx =>
    ⟨fun _ => mem_ball_zero_iff.2 (by rw [mem_sphere_zero_iff_norm.1 hx]; linarith),
    fun _ => mem_univ _⟩

include n_pos hv vContDiff vUnit in
/- f t : unitSphere n → Metric.sphere 0 (sqrt (1 + t*t)) est ouverte pour t assez petit -/
lemma isOpenMap_ft_restr : ∀ᶠ t in 𝓝 0, IsOpenMap (f_restr t) := by
  filter_upwards [@isOpenMap_ft n n_pos v vContDiff] with t ht
  intro U ⟨V, hV, hUV⟩
  have : U = Subtype.val ⁻¹' (V ∩ Metric.ball 0 2) := by
    rw [preimage_inter, hUV, ← subtype_val_preimage_ball_eq_sphere n hv vUnit, inter_univ]
  rw [this, image_restrictPreimage, ← image_restrict]
  exact continuous_subtype_val.isOpen_preimage _
    (ht _ (continuous_subtype_val.isOpen_preimage _ hV))

include hn in
lemma isConnected_sphere_E (t : ℝ) : IsConnected (Metric.sphere (0 : E n) (Real.sqrt (1 + t*t))) :=
  isConnected_sphere (one_lt_rank_EuclideanSpace n hn) 0 (Real.sqrt_nonneg (1 + t*t))

include hv vUnit in
lemma image_ft_eq_image_ft_restr (t : ℝ) :
    (f t) '' (unitSphere n) = range (f_restr t) := by
  ext y
  refine ⟨fun ⟨x, hx, hxy⟩ => (mem_image _ _ _).2 ?_,
    fun ⟨y', ⟨x, hxy'⟩, hyy'⟩ => (mem_image _ _ _).2
    ⟨x, ⟨by simp [← ft_preimage_sphere n hv vUnit t, Subtype.mem x],
    by simp [← hyy', ← hxy']⟩⟩⟩
  have y_mem_sphere : y ∈ Metric.sphere 0 (Real.sqrt (1 + t * t)) := by
    rw [← hxy]
    exact @ft_mem_sphere_of_mem_sphere _ _ hv vUnit t ⟨x, hx⟩
  use ⟨y, y_mem_sphere⟩
  exact ⟨mem_range.2 ⟨⟨x, by rwa [mem_preimage, hxy]⟩,
    Subtype.val_injective (by simp [hxy])⟩, by simp⟩

include n_pos hv vContDiff vUnit in
lemma isOpen_image_ft_restr : ∀ᶠ t in 𝓝 0, IsOpen (range (f_restr t)) := by
  filter_upwards [isOpenMap_ft_restr n n_pos hv vContDiff vUnit] with t ht
  exact ht.isOpen_range

include vContDiff in
lemma isClosed_image_ft (t : ℝ) : IsClosed ((f t) '' (unitSphere n)) :=
  ((isCompact_sphere _ _).image (@continuous_ft n v vContDiff t)).isClosed

include hv vContDiff vUnit in
lemma isClosed_image_ft_restr (t : ℝ) : IsClosed (range (f_restr t)) :=
  (@isCompact_range _ _ _ _ (instCompactPreimageSphere n hv vUnit t) _
  (continuous_ft_restr n vContDiff t)).isClosed

instance instNontrivialE : Nontrivial (E n) := by
  sorry

lemma image_preimage_eq_self {α : Type} (s : Set α) :
    Subtype.val '' (Subtype.val ⁻¹' s : Set s) = s := by
  rw [Subtype.image_preimage_coe, inter_self]

lemma useless_lemma2 {α : Type} {s s' t : Set α} (h : s = s') (h' : s ⊆ t) : s' ⊆ t := by
  rwa [← h]

include n_pos hn hv vContDiff vUnit in
lemma image_ft_eq_sphere : ∀ᶠ t in 𝓝 0,
    (f t) '' (unitSphere n) = Metric.sphere 0 (Real.sqrt (1 + t*t)) := by
  filter_upwards [isOpen_image_ft_restr n n_pos hv vContDiff vUnit] with t ht
  apply eq_of_subset_of_subset (@image_ft_subset_sphere _ _ hv vUnit t)
  rw [@image_ft_eq_image_ft_restr _ _ hv vUnit]
  apply useless_lemma2 (image_preimage_eq_self _)
  apply (image_subset_image_iff Subtype.val_injective).2
  rw [Subtype.coe_preimage_self]
  refine (Subtype.connectedSpace
    (isConnected_sphere_E n hn t)).isPreconnected_univ.subset_isClopen
    ⟨isClosed_image_ft_restr _ hv vContDiff vUnit t, ht⟩ ?_
  rw [univ_inter]
  apply Nonempty.of_image
  rw [← @image_ft_eq_image_ft_restr _ _ hv vUnit]
  apply (NormedSpace.sphere_nonempty.2 (zero_le_one)).image

variable (odd_n : Odd n)

open Polynomial

lemma one_add_sq_natDegree : (1 + X * X : Polynomial ℝ).natDegree = 2 := by
  rw [← C_1, natDegree_C_add, natDegree_mul X_ne_zero X_ne_zero, natDegree_X]

lemma C_mul_X_add_C_mul_self (a b : ℝ) : (C a * X + C b) * (C a * X + C b)
    = C (a * a) * X * X + C (2 * a * b) * X + C (b * b) := by
  simp only [map_mul, map_ofNat]
  ring

lemma not_sqrt_one_add_sq_eq_poly :
    ¬ (∃ P : Polynomial ℝ, ∀ t, Real.sqrt (1 + t * t) = P.eval t) := by
  intro ⟨P, hP⟩
  have eq_P_sq : 1 + X * X = P * P := by
    refine Polynomial.funext (fun t => ?_)
    rw [eval_mul, ← hP t, Real.mul_self_sqrt (add_nonneg (zero_le_one) (mul_self_nonneg _))]
    simp
  have P_ne_zero : P ≠ 0 :=
    fun h => two_ne_zero (by simp [← one_add_sq_natDegree, eq_P_sq, h])
  have P_natDegree_eq_one : P.natDegree = 1 := by
    apply mul_left_cancel₀ two_ne_zero
    rw [two_mul, ← natDegree_mul P_ne_zero P_ne_zero, ← eq_P_sq, one_add_sq_natDegree]
  let ⟨a, b, hab⟩ := (exists_eq_X_add_C_of_natDegree_le_one (by rw [P_natDegree_eq_one]) :
    ∃ a b, P = C a * X + C b)
  rw [hab, C_mul_X_add_C_mul_self] at eq_P_sq
  have h0 : coeff (1 + X * X) 0
      = coeff (C (a * a) * X * X + C (2 * a * b) * X + C (b * b)) 0 := by
    rw [eq_P_sq]
  have h1 : coeff (1 + X * X) 1
      = coeff (C (a * a) * X * X + C (2 * a * b) * X + C (b * b)) 1 := by
    rw [eq_P_sq]
  simp at h0
  simp at h1
  rw [← C_1, coeff_C_ne_zero (one_ne_zero)] at h1
  have a0 : a = 0 :=
    mul_left_cancel₀ two_ne_zero ((mul_right_cancel₀
      (left_ne_zero_of_mul (ne_zero_of_eq_one h0.symm))) (by simp [← h1]))
  rw [hab, a0, C_0, zero_mul, zero_add, natDegree_C] at P_natDegree_eq_one
  exact zero_ne_one P_natDegree_eq_one

include odd_n in
lemma not_one_add_sq_pow_n_div_two_eq_poly :
    ¬ (∃ P : Polynomial ℝ, ∀ t, (1 + t * t) ^ (n / 2 : ℝ) = P.eval t) := by
  let ⟨m, hm⟩ := odd_n
  rw [hm]
  clear hm
  induction' m with m ih <;> intro ⟨P, hP⟩
  · simp only [Nat.zero_eq, mul_zero, zero_add, Nat.cast_one, ← Real.sqrt_eq_rpow] at hP
    exact not_sqrt_one_add_sq_eq_poly ⟨P, hP⟩
  · have : ∀ t : ℝ, (2 * m + 3) * t * (1 + t * t) ^ ((2 * m + 1) / 2 : ℝ)
        = eval t (derivative P) := by
      intro t
      rw [← Polynomial.deriv, ← _root_.funext hP, deriv_rpow_const
        ((differentiableAt_id'.mul differentiableAt_id').const_add 1)
        (Or.inl (lt_add_of_pos_of_le zero_lt_one (mul_self_nonneg t)).ne.symm),
        deriv_const_add, deriv_mul differentiableAt_id differentiableAt_id,
        deriv_id'', Nat.cast_add, Nat.cast_mul, Nat.cast_succ]
      ring_nf
    have derivative_coeff_zero : (derivative P).coeff 0 = 0 := by
      simp [coeff_zero_eq_eval_zero, ← this]
    have X_mul_divX_derivative : derivative P = X * divX (derivative P) := by
      rw [← add_zero (_ * _), ← C_0, ← derivative_coeff_zero, X_mul_divX_add]
    rw [X_mul_divX_derivative] at this
    apply ih
    use C (1 / (2 * m + 3) : ℝ) * divX (derivative P)
    intro t
    rw [eval_mul, eval_C]
    sorry

theorem HairyBallDiff : ∃ x, v x = 0 := by
  sorry

end



section

variable (v : E n → E n) (hv : IsExtensionOfVectorFieldOnSn n v) (odd_n : Odd n)

theorem HairyBallTheorem : ∃ x, v x = 0 := by
  sorry

end
