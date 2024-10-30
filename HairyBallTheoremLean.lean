import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
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

set_option autoImplicit false

open scoped RealInnerProductSpace
open scoped BigOperators



variable (n : ℕ) (n_pos : 0 < n) (hn : 1 < n) (odd_n : Odd n)

abbrev E := EuclideanSpace ℝ (Fin n)
abbrev unitSphere := Metric.sphere (0 : E n) 1

structure IsExtensionOfVectorFieldOnSn (v : E n → E n) where
  isCont : Continuous v
  isTang : ∀ x : E n, ⟪x, (v x)⟫ = 0
  isExtension : ∀ x : E n, ∀ r : ℝ, r ≥ 0 → v (r • x) = r • v x



section Lipschitz_section

lemma ContDiffOn.locallyLipschitzOn_of_isOpen {𝕂 : Type} [RCLike 𝕂] {E' : Type} [NormedAddCommGroup E']
    [NormedSpace 𝕂 E'] {F' : Type} [NormedAddCommGroup F'] [NormedSpace 𝕂 F'] {f : E' → F'}
    {s : Set E'} (hf : ContDiffOn 𝕂 1 f s) (hs : IsOpen s) :
    LocallyLipschitzOn s f := by
  intro x hx
  obtain ⟨K, t', ht', hK⟩ := (hf.contDiffAt (hs.mem_nhds hx)).exists_lipschitzOnWith
  exact ⟨K, t', mem_nhdsWithin_of_mem_nhds ht', hK⟩

lemma ENNReal.ofReal_ne_zero {p : ℝ} : ENNReal.ofReal p ≠ 0 ↔ 0 < p := by
  rw [← not_le, not_iff_not, ENNReal.ofReal_eq_zero]

/- lemma LocallyLipschitz.lipshitzWith_of_CompactSpace {𝕂 : Type} [RCLike 𝕂] {E' : Type}
    [NormedAddCommGroup E'] [NormedSpace 𝕂 E'] [CompactSpace E'] {F' : Type}
    [NormedAddCommGroup F'] [NormedSpace 𝕂 F'] {f : E' → F'} (hf : LocallyLipschitz f) :
    ∃ (K : NNReal), LipschitzWith K f := by
  have f_continuous : Continuous f := hf.continuous
  choose K s hK using hf
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (interior ∘ s)
    (fun x => interior_mem_nhds.2 (hK x).1)
  by_cases t_empty : t = ∅
  · simp only [t_empty, Finset.not_mem_empty, Function.comp_apply, Set.iUnion_of_empty,
      Set.iUnion_empty, Set.top_eq_univ] at ht
    exact ⟨0, lipschitzOnWith_univ.1 (by simp [← ht])⟩
  have ht' : Set.univ ⊆ Set.iUnion (fun (x : t) => interior (s x)) := by
    apply subset_of_eq
    rw [← Set.top_eq_univ, ← ht]
    exact (Set.iUnion_subtype (Membership.mem t) fun x => interior (s x)).symm
  let ⟨ε', hε', hε's⟩ := lebesgue_number_lemma_of_metric CompactSpace.isCompact_univ
    (fun (x : t) => isOpen_interior) ht'
  let K' : ℝ := (t.image K).max' ((Finset.nonempty_iff_ne_empty.2 t_empty).image _)
  let K'' := (Metric.diam (Set.range f)) / ε'
  by_cases hK'' : K'' = 0
  · have : Metric.diam (Set.range f) = 0 := by
      rwa [← zero_mul ε', ← div_eq_iff hε'.ne.symm]
    refine ⟨0, fun x y => ?_⟩
    rw [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero, edist_eq_zero, ← dist_le_zero,
      ← zero_mul ε', ← hK'', div_mul_cancel₀ _ hε'.ne.symm]
    exact Metric.dist_le_diam_of_mem (isCompact_range f_continuous).isBounded
      (Set.mem_range_self _) (Set.mem_range_self _)
  have K''_pos : 0 < K'' := lt_of_le_of_ne (div_nonneg Metric.diam_nonneg hε'.le) (fun h => hK'' h.symm)
  have max_pos : 0 < max K' K'' := lt_max_of_lt_right K''_pos
  refine ⟨⟨max K' K'', le_max_of_le_left (NNReal.coe_nonneg _)⟩, fun x y => ?_⟩
  by_cases hxy : edist x y < ENNReal.ofReal ε'
  · by_cases hxy' : x = y
    · simp [hxy']
    obtain ⟨i, hi⟩ := hε's x (Set.mem_univ _)
    have K_le_max : K i ≤ max K' K'' :=
      le_trans (Finset.le_max' (Finset.image K t) (K i) (Finset.mem_image.2 ⟨i, i.2, rfl⟩)) (le_max_left _ _)
    refine le_trans ?_ ((ENNReal.mul_le_mul_right (edist_pos.2 hxy').ne.symm
      (lt_of_lt_of_le hxy le_top).ne).2 (ENNReal.coe_le_coe.2 K_le_max))
    exact (hK i).2 (interior_subset (hi (Metric.mem_ball_self hε')))
      (interior_subset (hi (Metric.mem_ball'.2 (edist_lt_ofReal.1 hxy))))
  · have x_ne_y : x ≠ y :=
      edist_pos.1 (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hε') (not_lt.1 hxy))
    by_cases hxy' : edist x y = ⊤
    · rw [hxy', ENNReal.mul_top (by rwa [← ENNReal.ofReal_coe_nnreal, NNReal.coe_mk, ENNReal.ofReal_ne_zero])]
      exact le_top
    refine le_trans ?_ ((ENNReal.mul_le_mul_right (edist_pos.2 x_ne_y).ne.symm hxy').2
      (ENNReal.ofReal_le_of_le_toReal (le_max_right K' K'')))
    refine le_trans ?_ ((ENNReal.mul_le_mul_left (ENNReal.ofReal_ne_zero.2 K''_pos)
      ENNReal.ofReal_ne_top).2 (not_lt.1 hxy))
    rw [← ENNReal.ofReal_mul K''_pos.le, div_mul_cancel₀ _ hε'.ne.symm, edist_dist]
    exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem
      (isCompact_range f_continuous).isBounded (Set.mem_range_self _) (Set.mem_range_self _)) -/

lemma LocallyLipschitzOn.lipshitzOnWith_of_isCompact {𝕂 : Type} [RCLike 𝕂] {E' : Type}
    [NormedAddCommGroup E'] [NormedSpace 𝕂 E'] {F' : Type} [NormedAddCommGroup F']
    [NormedSpace 𝕂 F'] {f : E' → F'} {s t : Set E'} (hf : LocallyLipschitzOn t f)
    (hs : IsCompact s) (ht : t ∈ nhdsSet s) :
    ∃ K, LipschitzOnWith K f s := by
  have f_continuousOn : ContinuousOn f s :=
    hf.continuousOn.mono (subset_of_mem_nhdsSet ht)
  choose K s' hK using hf
  obtain ⟨t', ht'⟩ := hs.elim_nhds_subcover' (fun x hx => interior (s' (subset_of_mem_nhdsSet ht hx)))
    (fun x hx => interior_mem_nhds.2 (nhds_of_nhdsWithin_of_nhds (nhds_le_nhdsSet hx ht)
    (hK (subset_of_mem_nhdsSet ht hx)).1))
  by_cases t'_empty : t' = ∅
  · simp only [t'_empty, Finset.not_mem_empty, Set.iUnion_of_empty, Set.iUnion_empty,
      Set.subset_empty_iff] at ht'
    rw [ht']
    exact ⟨0, lipschitzOnWith_empty _ _⟩
  have ht'' : s ⊆ Set.iUnion (fun (x : t') => interior (s' (subset_of_mem_nhdsSet ht x.1.2))) := by
    rwa [Set.iUnion_subtype]
  let ⟨ε', hε', hε's⟩ := lebesgue_number_lemma_of_metric hs
    (fun (x : t') => isOpen_interior) ht''
  let K' : ℝ := (t'.image (fun x => K (subset_of_mem_nhdsSet ht x.2))).max'
    ((Finset.nonempty_iff_ne_empty.2 t'_empty).image _)
  let K'' := (Metric.diam (f '' s)) / ε'
  by_cases hK'' : K'' = 0
  · have : Metric.diam (f '' s) = 0 := by
      rwa [← zero_mul ε', ← div_eq_iff hε'.ne.symm]
    refine ⟨0, fun x hx y hy => ?_⟩
    rw [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero, edist_eq_zero, ← dist_le_zero,
      ← zero_mul ε', ← hK'', div_mul_cancel₀ _ hε'.ne.symm]
    exact Metric.dist_le_diam_of_mem (hs.image_of_continuousOn f_continuousOn).isBounded
      (Set.mem_image_of_mem _ hx) (Set.mem_image_of_mem _ hy)
  have K''_pos : 0 < K'' := lt_of_le_of_ne (div_nonneg Metric.diam_nonneg hε'.le) (fun h => hK'' h.symm)
  have max_pos : 0 < max K' K'' := lt_max_of_lt_right K''_pos
  refine ⟨⟨max K' K'', le_max_of_le_left (NNReal.coe_nonneg _)⟩, fun x hx y hy => ?_⟩
  by_cases hxy : edist x y < ENNReal.ofReal ε'
  · by_cases hxy' : x = y
    · simp [hxy']
    obtain ⟨i, hi⟩ := hε's x hx
    have hit : i.1.1 ∈ t := subset_of_mem_nhdsSet ht i.1.2
    have K_le_max : K hit ≤ max K' K'' := by
      refine le_trans (Finset.le_max' _ (K hit) (Finset.mem_image.2 ?_)) (le_max_left _ _)
      exact ⟨i, i.2, rfl⟩
    refine le_trans ?_ ((ENNReal.mul_le_mul_right (edist_pos.2 hxy').ne.symm
      (lt_of_lt_of_le hxy le_top).ne).2 (ENNReal.coe_le_coe.2 K_le_max))
    exact (hK hit).2 (interior_subset (hi (Metric.mem_ball_self hε')))
      (interior_subset (hi (Metric.mem_ball'.2 (edist_lt_ofReal.1 hxy))))
  · have x_ne_y : x ≠ y :=
      edist_pos.1 (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hε') (not_lt.1 hxy))
    by_cases hxy' : edist x y = ⊤
    · rw [hxy', ENNReal.mul_top (by rwa [← ENNReal.ofReal_coe_nnreal, NNReal.coe_mk, ENNReal.ofReal_ne_zero])]
      exact le_top
    refine le_trans ?_ ((ENNReal.mul_le_mul_right (edist_pos.2 x_ne_y).ne.symm hxy').2
      (ENNReal.ofReal_le_of_le_toReal (le_max_right K' K'')))
    refine le_trans ?_ ((ENNReal.mul_le_mul_left (ENNReal.ofReal_ne_zero.2 K''_pos)
      ENNReal.ofReal_ne_top).2 (not_lt.1 hxy))
    rw [← ENNReal.ofReal_mul K''_pos.le, div_mul_cancel₀ _ hε'.ne.symm, edist_dist]
    exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem
      (hs.image_of_continuousOn f_continuousOn).isBounded
      (Set.mem_image_of_mem _ hx) (Set.mem_image_of_mem _ hy))

lemma LocallyLipschitz.lipshitzWith_of_CompactSpace {𝕂 : Type} [RCLike 𝕂] {E' : Type}
    [NormedAddCommGroup E'] [NormedSpace 𝕂 E'] [CompactSpace E'] {F' : Type}
    [NormedAddCommGroup F'] [NormedSpace 𝕂 F'] {f : E' → F'} (hf : LocallyLipschitz f) :
    ∃ K, LipschitzWith K f := by
  obtain ⟨K, hK⟩ := hf.locallyLipschitzOn.lipshitzOnWith_of_isCompact (𝕂 := 𝕂)
    isCompact_univ Filter.univ_mem
  exact ⟨K, lipschitzOnWith_univ.1 hK⟩

lemma ContDiffOn.lipschitzOnWith_of_isCompact {𝕂 : Type} [RCLike 𝕂] {E' : Type}
    [NormedAddCommGroup E'] [NormedSpace 𝕂 E'] {F' : Type} [NormedAddCommGroup F']
    [NormedSpace 𝕂 F'] {f : E' → F'} {s t : Set E'} (hf : ContDiffOn 𝕂 1 f s)
    (ht : IsCompact t) (hs : s ∈ nhdsSet t) :
    ∃ K, LipschitzOnWith K f t :=
  ((hf.mono interior_subset).locallyLipschitzOn_of_isOpen (isOpen_interior)).lipshitzOnWith_of_isCompact
    (𝕂 := 𝕂) ht (isOpen_interior.mem_nhdsSet.2 (subset_interior_iff_mem_nhdsSet.2 hs))

end Lipschitz_section


section other_lemmas

lemma continuousOn_if_const {α : Type}  {β : Type}  [TopologicalSpace α]
    [TopologicalSpace β]  (p : Prop) {s : Set α} {f : α → β}  {g : α → β} [Decidable p]
    (hf : p → ContinuousOn f s)  (hg : ¬p → ContinuousOn g s) :
    ContinuousOn (fun a => if p then f a else g a) s := by
  split_ifs with h
  exacts [hf h, hg h]

end other_lemmas



section

variable (v : E n → E n) (hv : IsExtensionOfVectorFieldOnSn n v)
  {vUnit : ∀ x : E n, ‖v x‖ = ‖x‖}
  {A : Set (E n)} (AComp : IsCompact A)
  {s : Set (E n)} (hs : s ∈ nhdsSet A) (s_isOpen : IsOpen s)
  (vContDiff : ContDiffOn ℝ 1 v s)

local notation "f" => fun (t : ℝ) (x : E n) ↦ x + t • (v x)

local notation "crown" => fun (a b : ℝ) =>
  (Metric.ball (0 : E n) b) \ (Metric.closedBall 0 a)

local notation "closedCrown" => fun (a b : ℝ) =>
  (Metric.closedBall (0 : E n) b) \ (Metric.ball 0 a)

instance instComp : CompactSpace (A : Type) :=
  isCompact_iff_compactSpace.1 AComp


section crown_section

open Metric Set

variable {n}

lemma mem_crown {a b : ℝ} {x : E n} : x ∈ crown a b ↔ a < ‖x‖ ∧ ‖x‖ < b := by
  rw [mem_diff, mem_ball_zero_iff, mem_closedBall_zero_iff, not_le, and_comm]

lemma isOpen_crown (a b : ℝ) : IsOpen (crown a b) :=
  isOpen_ball.sdiff isClosed_ball

lemma isCompact_closedCrown (a b : ℝ) : IsCompact (closedCrown a b) :=
  (ProperSpace.isCompact_closedBall _ _).diff isOpen_ball

lemma crown_subset_closedCrown {a b : ℝ} : crown a b ⊆ closedCrown a b :=
  fun _ ⟨hxb, hxa⟩ => ⟨ball_subset_closedBall hxb,
    (compl_subset_compl.2 ball_subset_closedBall) hxa⟩

lemma measurableSet_closedCrown {a b : ℝ} : MeasurableSet (closedCrown a b) :=
  measurableSet_closedBall.diff measurableSet_ball

end crown_section


open Topology

variable {n} {v} (hs_crown : s ∈ nhdsSet ((Metric.closedBall (0 : E n) 2) \ (Metric.ball 0 2⁻¹)))

include hv in
lemma continuous_ft (t : ℝ) : Continuous (f t) :=
  continuous_id.add (continuous_const.smul hv.isCont)

include hv in
lemma measurable_ft (t : ℝ) : Measurable (f t) :=
  measurable_id.add (measurable_const.smul hv.isCont.measurable)

lemma vLip' : ∃ c : NNReal, LipschitzOnWith c v A := by
  have : HasCompactSupport (fun x : A => v x) := by
    sorry
  -- apply ContDiff.lipschitzWith_of_hasCompactSupport this _ (le_refl)
  sorry

/- v est lipschitzienne sur A -/
include AComp vContDiff in
lemma vLip : ∃ c, LipschitzOnWith c v A := by
  sorry
  /- let ⟨r, hr⟩ := AComp.isBounded.subset_ball 0
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
  sorry -/

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
local notation "f'" t:max x:max =>
  (ContinuousLinearMap.id ℝ (E n)) + ((t : ℝ) • (fderiv ℝ v x))

/- f' t x est la différentielle de f t en x ∈ A -/
include vContDiff hs in
lemma ftDeriv (t : ℝ) : ∀ x ∈ A, HasFDerivWithinAt (f t) (f' t x) A x :=
  fun x hx => ((hasFDerivAt_id x).add
    (((vContDiff.differentiableOn le_rfl).differentiableAt
    (nhds_le_nhdsSet hx hs)).hasFDerivAt.const_smul t)).hasFDerivWithinAt

/- f' t x est la différentielle (stricte) de f t en x -/
include vContDiff hs in
lemma ftStrictDeriv (t : ℝ) : ∀ x ∈ A, HasStrictFDerivAt (f t) (f' t x) x :=
  fun x hx => (hasStrictFDerivAt_id x).add
    (((vContDiff.contDiffAt (nhds_le_nhdsSet hx hs)).hasStrictFDerivAt le_rfl).const_smul t)


section vol_poly

local notation "jac_f" =>
  fun (x : E n) ↦ LinearMap.toMatrix' (fderiv ℝ v x : E n →ₗ[ℝ] E n)

open MeasureTheory

/- A est mesurable -/
include AComp in
lemma meas_A : MeasurableSet A :=
  AComp.isClosed.measurableSet

include AComp vContDiff hs in
lemma lintegral_abs_det_f't : ∀ᶠ t in 𝓝 0,
    ∫⁻ x in A, ENNReal.ofReal |(f' t x).det| ∂volume = volume ((f t) '' A) := by
  filter_upwards [@injOn_A_ft n v A] with t hinj
  exact lintegral_abs_det_fderiv_eq_addHaar_image volume
    (meas_A AComp) (ftDeriv hs vContDiff t) hinj

/- include AComp vContDiff hv in
lemma ft_volume_withDensity_abs_det_f't_eq_volume : ∀ᶠ t in 𝓝 0,
    Measure.map (f t) ((volume.restrict A).withDensity fun x => ENNReal.ofReal |(f' t x).det|)
    = volume.restrict ((f t) '' A) := by
  filter_upwards [@injOn_A_ft n v A] with t hinj
  exact map_withDensity_abs_det_fderiv_eq_addHaar volume
    (meas_A n AComp) (@ftDeriv n v vContDiff A t) hinj (measurable_ft n hv t) -/

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
    rw [prod_perm_fixpoint σ, apply_ite (fun ε => Equiv.Perm.sign σ • ε)]
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

lemma continuous_my_coe : Continuous (@my_coe n) :=
  continuous_pi fun x => (ContinuousLinearMap.apply ℝ (E n) x).continuous

include vContDiff s_isOpen in
lemma continuousOn_jac_f_apply {i j : Fin n} :
    ContinuousOn (fun x => jac_f x i j) s := by
  simp only [LinearMap.toMatrix'_apply]
  refine (continuous_apply_apply _ _).comp_continuousOn
    (continuous_my_coe.comp_continuousOn
    (vContDiff.continuousOn_fderiv_of_isOpen s_isOpen (le_refl _)))

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
lemma continuousOn_coeff_prod (m : ℕ) (hm : 0 < m) (hmn : m ≤ n) (k : ℕ)
    (P : Fin n → E n → ℝ[X]) (hP : ∀ i k', ContinuousOn (fun x => (P i x).coeff k') s) :
    ContinuousOn (fun x => ((univ : Finset (Fin m)).prod
    (fun i => P (@Fin.ofNat' n (NeZero.of_gt n_pos) i) x)).coeff k) s := by
  have : (fun x => ((univ : Finset (Fin m)).prod (fun i => P (@Fin.ofNat' n (NeZero.of_gt n_pos) i) x)).coeff k)
      = (fun x => ((range m).prod (fun i => P (@Fin.ofNat' n (NeZero.of_gt n_pos) i) x)).coeff k) := by
    ext x
    rw [← prod_univ_Fin_eq_prod_range]
  rw [this]
  induction' m with m ih generalizing k
  · simp [coeff_one, continuousOn_const]
  · have : (fun x => (∏ i ∈ range (m + 1), P (@Fin.ofNat' n (NeZero.of_gt n_pos) i) x).coeff k)
        = (fun x => ∑ μ ∈ antidiagonal k, (P (@Fin.ofNat' n (NeZero.of_gt n_pos) m) x).coeff μ.1
        * (∏ i ∈ range m, P (@Fin.ofNat' n (NeZero.of_gt n_pos) i) x).coeff μ.2) := by
      ext x
      rw [range_succ, prod_insert not_mem_range_self, coeff_mul]
    rw [this]
    refine continuousOn_finset_sum _ (fun μ _ => (hP _ _).mul ?_)
    by_cases mz : m = 0
    · have : (fun x => ((range m).prod fun i => P (@Fin.ofNat' n (NeZero.of_gt n_pos) i) x).coeff μ.2)
          = (fun x => if μ.2 = 0 then 1 else 0) := by
        ext x
        simp [mz, coeff_one]
      rw [this]
      exact continuousOn_const
    · exact ih (pos_iff_ne_zero.2 mz) (lt_of_lt_of_le (Nat.lt_succ_self m) hmn).le
        μ.2 (by ext x; rw [← prod_univ_Fin_eq_prod_range])

include n_pos in
lemma continuousOn_coeff_prod' (k : ℕ) (P : Fin n → E n → ℝ[X])
    (hP : ∀ i k', ContinuousOn (fun x => (P i x).coeff k') s) :
    ContinuousOn (fun x => ((univ : Finset (Fin n)).prod (fun i => P i x)).coeff k) s := by
  have : (fun x => (univ.prod (fun i => P i x)).coeff k)
      = (fun x => ((univ : Finset (Fin n)).prod
      (fun i => P (@Fin.ofNat' n (NeZero.of_gt n_pos) i) x)).coeff k) :=
    (funext fun x => congrArg (fun p => coeff p k)
      (congrArg _ (funext fun i => (congrArg (fun j => P j x) (by rw [ofNat'_val _ n_pos])))))
  rw [this]
  exact continuousOn_coeff_prod n_pos _ n_pos le_rfl _ _ hP

/- det (f' t x) est polynomial en t et les coefficients sont continus en x -/
include n_pos vContDiff s_isOpen in
lemma f't_det_poly : ∃ P : E n → Polynomial ℝ,
    (∀ x : E n, (P x).natDegree ≤ n)
    ∧ (∀ x : E n, (P x).coeff 0 = 1)
    ∧ (∀ t : ℝ, ∀ x : E n, (f' t x).det = (P x).eval t)
    ∧ (∀ k : ℕ, ContinuousOn (fun x => (P x).coeff k) s) := by
  let P := (fun x => (of (fun i j => (if i = j then 1 else 0) + C (jac_f x i j) * X)).det)
  use P
  constructor
  · refine fun x => natDegree_det _ (fun i j => ?_)
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
        refine continuousOn_finset_sum _ (fun σ _ => ContinuousOn.const_smul
          (continuousOn_coeff_prod' n_pos _ _ (fun i k' => ?_)) _)
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
        exact continuousOn_if_const _ (fun _ => continuousOn_const)
          (fun _ => continuousOn_if_const _
          (fun _ => (continuousOn_jac_f_apply s_isOpen vContDiff))
          (fun _ => continuousOn_const))

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
  apply zero_lt_continuous _ (continuous_bound M)
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

include AComp hs in
lemma bound_poly (P : E n → Polynomial ℝ) (hdeg : ∀ x, (P x).natDegree ≤ n)
    (h0 : ∀ x, (P x).coeff 0 = 1) (hcont : ∀ k, ContinuousOn (fun x => (P x).coeff k) s) :
    ∃ M, ∀ t : ℝ, ∀ x : A,
    1 - M * ((range n).sum fun k => |t| ^ (k + 1)) ≤ (P x).eval t := by
  let continuous_coeff (k : ℕ) : C(A,ℝ) := ⟨_, ((hcont k).mono (subset_of_mem_nhdsSet hs)).restrict⟩
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
include n_pos vContDiff AComp hs s_isOpen in
lemma zero_lt_det_f't : ∀ᶠ t in 𝓝 0, ∀ x : A, 0 < (f' t x).det := by
  have ⟨P, hP⟩ := f't_det_poly n_pos s_isOpen vContDiff
  have ⟨M, hM⟩ := bound_poly AComp hs P hP.1 hP.2.1 hP.2.2.2
  filter_upwards [pos_bound M] with t ht x
  rw [hP.2.2.1 t x]
  exact lt_of_lt_of_le ht (hM t x)

/- |det (f' t x)| est polynomial en t et les coefficients sont continus en x -/
include n_pos vContDiff AComp hs s_isOpen in
lemma abs_det_f't_poly : ∃ P : E n → Polynomial ℝ,
    (∀ x : E n, (P x).natDegree ≤ n)
    ∧ (∀ᶠ t in 𝓝 0, ∀ x : A, |(f' t x).det| = (P x).eval t)
    ∧ (∀ k : ℕ, ContinuousOn (fun x => (P x).coeff k) s) := by
  have ⟨P, hP⟩ := f't_det_poly n_pos s_isOpen vContDiff
  refine ⟨P, hP.1, ?_, hP.2.2.2⟩
  filter_upwards [zero_lt_det_f't n_pos AComp hs s_isOpen vContDiff] with t hpos x
  rw [abs_of_pos (hpos x), hP.2.2.1 t]

include vContDiff s_isOpen in
lemma continuousOn_abs_det_f't (t : ℝ) : ContinuousOn (fun x => |(f' t x).det|) s :=
  continuous_abs.comp_continuousOn (ContinuousLinearMap.continuous_det.comp_continuousOn
    (continuous_const.continuousOn.add (continuous_const.continuousOn.smul
    (vContDiff.continuousOn_fderiv_of_isOpen s_isOpen (by rfl)))))

lemma nonneg_ae_abs_det_f't (t : ℝ) : 0 ≤ᵐ[volume.restrict A] fun x => |(f' t x).det| := by
  filter_upwards
  simp

/- le volume de (f t)''(A) est polynomial en t -/
include n_pos vContDiff AComp hs s_isOpen in
lemma vol_ft_A_poly : ∃ P : Polynomial ℝ, ∀ᶠ t in 𝓝 0,
    (volume ((f t) '' A)).toReal = (P.eval t) := by
  let ⟨P, hP⟩ := abs_det_f't_poly n_pos AComp hs s_isOpen vContDiff
  use (range (n + 1)).sum (fun i => C (∫ x in A, (P x).coeff i ∂volume) * X ^ i)
  filter_upwards [lintegral_abs_det_f't AComp hs vContDiff, hP.2.1] with t hInt hP1
  rw [← hInt, eval_finset_sum, ← integral_eq_lintegral_of_nonneg_ae (nonneg_ae_abs_det_f't t)
    (((continuousOn_abs_det_f't s_isOpen vContDiff t).mono (subset_of_mem_nhdsSet hs)).aestronglyMeasurable
    (meas_A AComp))]
  have : A.EqOn (fun x => |(f' t x).det|) (fun x => (range (n + 1)).sum (fun n => (P x).coeff n * t ^ n)) := by
    intro x xA
    simp [hP1 ⟨x, xA⟩]
    nth_rw 1 [(P x).as_sum_range' (n + 1) (Nat.lt_succ_of_le (hP.1 x))]
    simp [eval_finset_sum]
  have integrable_coeff (i : ℕ) : Integrable (fun x => (P x).coeff i * t ^ i) (volume.restrict A) :=
    ContinuousOn.integrableOn_compact AComp (((hP.2.2 i).smul continuousOn_const).mono (subset_of_mem_nhdsSet hs))
  rw [setIntegral_congr (meas_A AComp) this, integral_finset_sum _ (fun i _ => integrable_coeff i)]
  simp_rw [eval_mul, eval_C, eval_pow, eval_X, integral_mul_right]

end vol_poly


section image_ft_sphere

open Set

include hv in
lemma inner_self_v_eq_zero_of_norm_one (t : ℝ) (x : E n) :
    ⟪x, t • v x⟫ = 0 := by
  rw [inner_smul_right, hv.isTang x, mul_zero]

include hv vUnit in
lemma ft_mem_sphere_of_mem_sphere (t : ℝ) (x : unitSphere n) :
    f t x ∈ Metric.sphere 0 (Real.sqrt (1 + t*t)) := by
  rw [mem_sphere_zero_iff_norm, ← Real.sqrt_mul_self (norm_nonneg _),
    norm_add_sq_eq_norm_sq_add_norm_sq_real
    (inner_self_v_eq_zero_of_norm_one hv t x)]
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

variable (vUnit)

include hn in
lemma one_lt_rank_EuclideanSpace : 1 < Module.rank ℝ (E n) := by
  apply Module.lt_rank_of_lt_finrank
  rw [finrank_euclideanSpace, Fintype.card_fin]
  exact hn

local notation "f_restr" =>
  fun (t : ℝ) ↦ restrictPreimage (Metric.sphere 0 (Real.sqrt (1 + t * t))) (f t)

include hv in
lemma continuous_ft_restr (t : ℝ) : Continuous (f_restr t) :=
  (continuous_ft hv t).restrict _

include hv vUnit in
lemma ft_preimage_sphere (t : ℝ) :
    (f t) ⁻¹' (Metric.sphere 0 (Real.sqrt (1 + t * t))) = unitSphere n := by
  ext x
  rw [mem_preimage, mem_sphere_zero_iff_norm,
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
  rw [ft_preimage_sphere hv vUnit]
  exact Metric.sphere.compactSpace _ _

lemma preimage_restrict {α β : Type} (s : Set α) (g : α → β) (t : Set β) :
    (restrict s g) ⁻¹' t = s ∩ (g ⁻¹' t) := by
  rw [restrict_eq, preimage_comp]
  exact eq_of_subset_of_subset (subset_inter (Subtype.coe_image_subset _ _)
    (image_preimage_subset _ _))
    (fun x hx => ⟨⟨x, hx.1⟩, ⟨mem_preimage.2 hx.2, rfl⟩⟩)

include n_pos vContDiff s_isOpen hs_crown in
lemma isOpenMap_ft : ∀ᶠ t in 𝓝 0, IsOpenMap (restrict (crown 2⁻¹ 2) (f t)) := by
  filter_upwards [zero_lt_det_f't n_pos (isCompact_closedCrown 2⁻¹ 2)
    hs_crown s_isOpen vContDiff] with t ht
  refine isOpenMap_iff_nhds_le.2 (fun ⟨x, hx⟩ => ?_)
  rw [restrict_apply, restrict_eq, ← Filter.map_map,
    ← @HasStrictFDerivAt.map_nhds_eq_of_equiv ℝ _ _ _ _ _ _ _ _
    ((f' t x).equivOfDetNeZero (ht ⟨x, crown_subset_closedCrown hx⟩).ne.symm).toContinuousLinearEquiv _ _
    (ftStrictDeriv hs_crown vContDiff t x (crown_subset_closedCrown hx))]
  have : Filter.map Subtype.val (𝓝 (⟨x, hx⟩ : crown 2⁻¹ 2)) = 𝓝 x :=
    eq_of_le_of_le continuous_subtype_val.continuousAt.tendsto
      (isOpenMap_iff_nhds_le.1 (isOpen_crown _ _).isOpenMap_subtype_val ⟨x, hx⟩)
  rw [this]

include hv vUnit in
lemma subtype_val_preimage_crown_eq_sphere (t : ℝ) :
    (univ : Set ((f t) ⁻¹' (Metric.sphere 0 (Real.sqrt (1 + t * t)))))
    = Subtype.val ⁻¹' (crown 2⁻¹ 2) := by
  apply eq_preimage_subtype_val_iff.2
  rw [ft_preimage_sphere hv vUnit]
  refine fun x hx => ⟨fun _ => ?_, fun _ => mem_univ _⟩
  rw [mem_crown, mem_sphere_zero_iff_norm.1 hx]
  refine ⟨two_inv_lt_one, one_lt_two⟩

include n_pos hv vContDiff vUnit s_isOpen hs_crown in
/- f t : unitSphere n → Metric.sphere 0 (sqrt (1 + t*t)) est ouverte pour t assez petit -/
lemma isOpenMap_ft_restr : ∀ᶠ t in 𝓝 0, IsOpenMap (f_restr t) := by
  filter_upwards [isOpenMap_ft n_pos s_isOpen vContDiff hs_crown] with t ht
  intro U ⟨V, hV, hUV⟩
  have : U = Subtype.val ⁻¹' (V ∩ crown 2⁻¹ 2) := by
    rw [preimage_inter, hUV, ← subtype_val_preimage_crown_eq_sphere hv vUnit, inter_univ]
  rw [this, image_restrictPreimage, ← image_restrict]
  exact continuous_subtype_val.isOpen_preimage _
    (ht _ (continuous_subtype_val.isOpen_preimage _ hV))

include hn in
lemma isConnected_sphere_E (t : ℝ) : IsConnected (Metric.sphere (0 : E n) (Real.sqrt (1 + t*t))) :=
  isConnected_sphere (one_lt_rank_EuclideanSpace hn) 0 (Real.sqrt_nonneg (1 + t*t))

include hv vUnit in
lemma image_ft_eq_image_ft_restr (t : ℝ) :
    (f t) '' (unitSphere n) = range (f_restr t) := by
  ext y
  refine ⟨fun ⟨x, hx, hxy⟩ => (mem_image _ _ _).2 ?_,
    fun ⟨y', ⟨x, hxy'⟩, hyy'⟩ => (mem_image _ _ _).2
    ⟨x, ⟨by simp [← ft_preimage_sphere hv vUnit t, Subtype.mem x],
    by simp [← hyy', ← hxy']⟩⟩⟩
  have y_mem_sphere : y ∈ Metric.sphere 0 (Real.sqrt (1 + t * t)) := by
    rw [← hxy]
    exact @ft_mem_sphere_of_mem_sphere _ _ hv vUnit t ⟨x, hx⟩
  use ⟨y, y_mem_sphere⟩
  exact ⟨mem_range.2 ⟨⟨x, by rwa [mem_preimage, hxy]⟩,
    Subtype.val_injective (by simp [hxy])⟩, by simp⟩

include n_pos hv vContDiff vUnit s_isOpen hs_crown in
lemma isOpen_image_ft_restr : ∀ᶠ t in 𝓝 0, IsOpen (range (f_restr t)) := by
  filter_upwards [isOpenMap_ft_restr n_pos hv vUnit s_isOpen vContDiff hs_crown] with t ht
  exact ht.isOpen_range

include hv in
lemma isClosed_image_ft (t : ℝ) : IsClosed ((f t) '' (unitSphere n)) :=
  ((isCompact_sphere _ _).image (continuous_ft hv t)).isClosed

include hv vUnit in
lemma isClosed_image_ft_restr (t : ℝ) : IsClosed (range (f_restr t)) :=
  (@isCompact_range _ _ _ _ (instCompactPreimageSphere hv vUnit t) _
  (continuous_ft_restr hv t)).isClosed

instance instNontrivialE : Nontrivial (E n) :=
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp n_pos
  inferInstance

lemma image_preimage_eq_self {α : Type} (s : Set α) :
    Subtype.val '' (Subtype.val ⁻¹' s : Set s) = s := by
  rw [Subtype.image_preimage_coe, inter_self]

lemma useless_lemma2 {α : Type} {s s' t : Set α} (h : s = s') (h' : s ⊆ t) : s' ⊆ t := by
  rwa [← h]

include hn hv vContDiff vUnit s_isOpen hs_crown in
lemma image_ft_eq_sphere : ∀ᶠ t in 𝓝 0,
    (f t) '' (unitSphere n) = Metric.sphere 0 (Real.sqrt (1 + t * t)) := by
  filter_upwards [isOpen_image_ft_restr (one_pos.trans hn) hv vUnit s_isOpen
    vContDiff hs_crown] with t ht
  apply eq_of_subset_of_subset (@image_ft_subset_sphere _ _ hv vUnit t)
  rw [@image_ft_eq_image_ft_restr _ _ hv vUnit]
  apply useless_lemma2 (image_preimage_eq_self _)
  apply (image_subset_image_iff Subtype.val_injective).2
  rw [Subtype.coe_preimage_self]
  refine (Subtype.connectedSpace
    (isConnected_sphere_E hn t)).isPreconnected_univ.subset_isClopen
    ⟨isClosed_image_ft_restr hv vUnit t, ht⟩ ?_
  rw [univ_inter]
  apply Nonempty.of_image
  rw [← @image_ft_eq_image_ft_restr _ _ hv vUnit]
  have := instNontrivialE (one_pos.trans hn)
  apply ((NormedSpace.sphere_nonempty).2 (zero_le_one)).image

-- use group actions ? image_smul_set...
include hn hv vContDiff vUnit s_isOpen hs_crown in
lemma image_ft_sphere_eq_sphere : ∀ᶠ t in 𝓝 0, ∀ r > 0,
    (f t) '' (Metric.sphere 0 r) = Metric.sphere 0 (r * Real.sqrt (1 + t * t)) := by
  filter_upwards [image_ft_eq_sphere hn hv vUnit s_isOpen vContDiff hs_crown] with t ht r r_pos
  refine eq_of_subset_of_subset
    (fun y ⟨x, hx, hxy⟩ => mem_sphere_zero_iff_norm.2
    (mul_left_cancel₀ (inv_pos.2 r_pos).ne.symm ?_))
    (fun y hy => ?_)
  · rw [← mul_assoc, inv_mul_cancel₀ r_pos.ne.symm, one_mul, ← abs_eq_self.2 r_pos.le,
      ← abs_inv, ← Real.norm_eq_abs,  ← norm_smul, ← mem_sphere_zero_iff_norm, ← ht]
    refine ⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.2 ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀]
      rw [mem_sphere_zero_iff_norm.1 hx]
      exact r_pos.ne.symm
    · simp only [mem_sphere_zero_iff_norm.1 hx, ← hxy,
        hv.isExtension _ _ (inv_nonneg.2 r_pos.le), smul_add, smul_smul]
      ac_rfl
  · have : r⁻¹ • y ∈ Metric.sphere 0 √(1 + t * t) := by
      apply mem_sphere_zero_iff_norm.2
      rw [norm_smul, mem_sphere_zero_iff_norm.1 hy, norm_inv, Real.norm_eq_abs,
        abs_eq_self.2 r_pos.le, ← mul_assoc, inv_mul_cancel₀ r_pos.ne.symm, one_mul]
    rw [← ht] at this
    let ⟨x, hx, hxy⟩ := this
    refine ⟨r • x, by rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_eq_self.2 r_pos.le, mem_sphere_zero_iff_norm.1 hx, mul_one], ?_⟩
    simp only [hv.isExtension _ _ r_pos.le]
    simp only at hxy
    rw [smul_smul, mul_comm, ← smul_smul, ← smul_add, hxy, smul_smul,
      mul_inv_cancel₀ r_pos.ne.symm, one_smul]

end image_ft_sphere


section volume_closedCrown

open Set Metric MeasureTheory

variable (vUnit)

include n_pos in
lemma measure_closedCrown {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (volume (closedCrown a b)).toReal = (b ^ n - a ^ n) * (volume (ball (0 : E n) 1)).toReal := by
  have := instNontrivialE n_pos
  rw [measure_diff ((ball_subset_ball hab).trans ball_subset_closedBall)
    measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne,
    Measure.addHaar_closedBall _ _ (ha.trans hab), Measure.addHaar_ball _ _ ha,
    finrank_euclideanSpace, Fintype.card_fin, ENNReal.toReal_sub_of_le
    ((ENNReal.mul_le_mul_right (measure_ball_pos _ _ one_pos).ne.symm measure_ball_lt_top.ne).2
    (ENNReal.ofReal_le_ofReal (pow_le_pow_left ha hab n)))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)]
  simp [ENNReal.toReal_ofReal (pow_nonneg ha _),
    ENNReal.toReal_ofReal (pow_nonneg (ha.trans hab) _), sub_mul]

include n_pos in
lemma measure_closedCrown_ne_zero {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (volume (closedCrown a b)).toReal ≠ 0 := by
  rw [measure_closedCrown n_pos ha hab.le]
  exact mul_ne_zero (sub_ne_zero.2 (not_imp_not.2 (pow_eq_pow_iff_of_ne_zero n_pos.ne.symm).1
    (not_or.2 ⟨hab.ne.symm, not_and_or.2 (Or.inl (by linarith))⟩)))
    (ENNReal.toReal_ne_zero.2 ⟨(measure_ball_pos _ _ one_pos).ne.symm, measure_ball_lt_top.ne⟩)

lemma closedCrown_eq_union_sphere (a b : ℝ) : closedCrown a b = ⋃ (r : Icc a b), sphere 0 r := by
  refine eq_of_subset_of_subset
    (fun x ⟨hxb, hxa⟩ => mem_iUnion.2
    ⟨⟨‖x‖, ⟨not_lt.1 (fun h => hxa (mem_ball_zero_iff.2 h)),
    mem_closedBall_zero_iff.1 hxb⟩⟩, mem_sphere_zero_iff_norm.2 rfl⟩)
    (fun x hx => ?_)
  let ⟨r, hr⟩ := mem_iUnion.1 hx
  let ⟨hra, hrb⟩ := r.2
  rw [← mem_sphere_zero_iff_norm.1 hr] at hra
  rw [← mem_sphere_zero_iff_norm.1 hr] at hrb
  exact ⟨mem_closedBall_zero_iff.2 hrb,
    mem_compl (fun h => not_lt.2 hra (mem_ball_zero_iff.1 h))⟩

lemma sqrt_one_add_sq_pos {t : ℝ} : 0 < √(1 + t * t) :=
  Real.sqrt_pos_of_pos (lt_add_of_pos_of_le one_pos (mul_self_nonneg _))

include hn hv vContDiff vUnit s_isOpen hs_crown in
lemma image_ft_closedCrown_eq_closedCrown (a b : ℝ) (ha : 0 < a) : ∀ᶠ t in 𝓝 0,
    (f t) '' (closedCrown a b) = closedCrown (a * √(1 + t * t)) (b * √(1 + t * t)) := by
  filter_upwards [image_ft_sphere_eq_sphere hn hv vUnit s_isOpen vContDiff hs_crown] with t ht
  simp only [closedCrown_eq_union_sphere]
  rw [image_iUnion]
  refine eq_of_subset_of_subset (fun y hy => ?_) ?_
  · let ⟨r, ⟨x, hxr, hxy⟩⟩ := mem_iUnion.1 hy
    refine mem_iUnion.2 ⟨⟨r * √(1 + t * t),
      ⟨(mul_le_mul_right sqrt_one_add_sq_pos).2 r.2.1,
      (mul_le_mul_right sqrt_one_add_sq_pos).2 r.2.2⟩⟩, ?_⟩
    rw [← ht _ (lt_of_lt_of_le ha r.2.1)]
    use x
  · intro x hx
    let ⟨r, hr⟩ := mem_iUnion.1 hx
    refine mem_iUnion.2 ⟨⟨r.1 * (√(1 + t * t))⁻¹,
      ⟨(le_mul_inv_iff₀ sqrt_one_add_sq_pos).2 r.2.1,
      (mul_inv_le_iff₀ sqrt_one_add_sq_pos).2 r.2.2⟩⟩, ?_⟩
    rwa [ht _ (mul_pos (lt_of_lt_of_le (mul_pos ha sqrt_one_add_sq_pos) r.2.1)
      (inv_pos_of_pos sqrt_one_add_sq_pos)), mul_assoc,
      inv_mul_cancel₀ sqrt_one_add_sq_pos.ne.symm, mul_one]

include hn hv vContDiff vUnit s_isOpen hs_crown in
lemma volume_image_closedCrown {a b : ℝ} (ha : 0 < a) (hab : a ≤ b): ∀ᶠ t in 𝓝 0,
    (volume ((f t) '' (closedCrown a b))).toReal = √(1 + t * t) ^ n * (volume (closedCrown a b)).toReal := by
  filter_upwards [image_ft_closedCrown_eq_closedCrown hn hv vUnit s_isOpen vContDiff hs_crown a b ha] with t ht
  rw [ht, measure_closedCrown (one_pos.trans hn) ha.le hab, ← mul_assoc, mul_sub, ← mul_pow, ← mul_pow,
    measure_closedCrown (one_pos.trans hn) (mul_nonneg ha.le (Real.sqrt_nonneg _))
    ((mul_le_mul_right sqrt_one_add_sq_pos).2 hab)]
  ac_rfl

end volume_closedCrown


section sq_ne_poly

open Polynomial

lemma one_add_sq_natDegree : (1 + X * X : Polynomial ℝ).natDegree = 2 := by
  rw [← C_1, natDegree_C_add, natDegree_mul X_ne_zero X_ne_zero, natDegree_X]

lemma C_mul_X_add_C_mul_self (a b : ℝ) : (C a * X + C b) * (C a * X + C b)
    = C (a * a) * X * X + C (2 * a * b) * X + C (b * b) := by
  simp only [map_mul, map_ofNat]
  ring

lemma funext_ne_zero {P Q : ℝ[X]} : P = Q ↔ ∀ t ≠ 0, eval t P = eval t Q :=
  ⟨fun h t _ => by rw [h], fun h => funext (congr_fun
    (Continuous.ext_on (dense_compl_singleton _) P.continuous Q.continuous h))⟩

lemma not_sqrt_one_add_sq_eq_poly :
    ¬ (∃ P : Polynomial ℝ, ∀ t ≠ 0, Real.sqrt (1 + t * t) = P.eval t) := by
  intro ⟨P, hP⟩
  have eq_P_sq : 1 + X * X = P * P := by
    refine funext_ne_zero.2 (fun t ht => ?_)
    rw [eval_mul, ← hP t ht, Real.mul_self_sqrt (add_nonneg (zero_le_one) (mul_self_nonneg _))]
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

lemma continuous_one_add_sq_rpow (k : ℝ) (hk : 0 ≤ k) : Continuous (fun t : ℝ => (1 + t * t) ^ k) := by
  fun_prop (disch := assumption)

lemma continuous_mul_id_mul_one_add_sq_rpow (m : ℕ) :
    Continuous (fun t : ℝ => (2 * m + 3) * t * (1 + t * t) ^ ((2 * m + 1) / 2 : ℝ)) :=
  (continuous_const.mul continuous_id).mul (continuous_one_add_sq_rpow _
    (div_nonneg (by linarith) zero_le_two))

include odd_n in
lemma not_one_add_sq_pow_n_div_two_eq_poly :
    ¬ ∃ P : Polynomial ℝ, ∀ t, (1 + t * t) ^ (n / 2 : ℝ) = P.eval t := by
  suffices ¬ ∃ P : Polynomial ℝ, ∀ t ≠ 0, (1 + t * t) ^ (n / 2 : ℝ) = P.eval t from
    not_imp_not.mpr (Exists.imp fun P h t _ ↦ h t) this
  let ⟨m, hm⟩ := odd_n
  rw [hm]
  clear hm
  induction' m with m ih <;> intro ⟨P, hP⟩
  · simp only [Nat.zero_eq, mul_zero, zero_add, Nat.cast_one, ← Real.sqrt_eq_rpow] at hP
    exact not_sqrt_one_add_sq_eq_poly ⟨P, hP⟩
  · have : ∀ t, (2 * m + 3) * t * (1 + t * t) ^ ((2 * m + 1) / 2 : ℝ)
        = eval t (derivative P) := by
      intro t
      rw [← Polynomial.deriv]
      have : (fun t => (1 + t * t) ^((2 * (m + 1) + 1) / 2 : ℝ)) = (fun t => eval t P) :=
        Continuous.ext_on (dense_compl_singleton 0)
          (continuous_one_add_sq_rpow _ (div_nonneg (by linarith) zero_le_two))
          P.continuous (by exact_mod_cast hP)
      rw [← this, deriv_rpow_const
        ((differentiableAt_id'.mul differentiableAt_id').const_add 1)
        (Or.inl (lt_add_of_pos_of_le zero_lt_one (mul_self_nonneg t)).ne.symm),
        deriv_const_add, deriv_mul differentiableAt_id differentiableAt_id,
        deriv_id'']
      ring_nf
    have derivative_coeff_zero : (derivative P).coeff 0 = 0 := by
      simp [coeff_zero_eq_eval_zero, ← this]
    have X_mul_divX_derivative : derivative P = X * divX (derivative P) := by
      rw [← add_zero (_ * _), ← C_0, ← derivative_coeff_zero, X_mul_divX_add]
    rw [X_mul_divX_derivative] at this
    refine ih ⟨C (1 / (2 * m + 3) : ℝ) * divX (derivative P), fun t ht => ?_⟩
    rw [eval_mul, eval_C]
    apply mul_left_cancel₀ (by linarith : 2 * (m : ℝ) + 3 ≠ 0)
    rw [← mul_assoc, mul_div_cancel₀ _ (by linarith), one_mul]
    apply mul_left_cancel₀ ht
    nth_rw 4 [← @eval_X _ _ t]
    rw [← eval_mul, ← this t]
    norm_cast
    ac_rfl

include odd_n in
lemma not_one_add_sq_pow_n_div_two_eq_poly' :
    ¬ ∃ P : Polynomial ℝ, ∀ᶠ t in 𝓝 0, (1 + t * t) ^ (n / 2 : ℝ) = P.eval t := by
  sorry
  /- suffices ¬ ∃ P : Polynomial ℝ, ∀ᶠ t in 𝓝 0, t ≠ 0 → (1 + t * t) ^ (n / 2 : ℝ) = P.eval t from
    not_imp_not.mpr (Exists.imp fun P h t _ ↦ h t) this
  let ⟨m, hm⟩ := odd_n
  rw [hm]
  clear hm
  induction' m with m ih <;> intro ⟨P, hP⟩
  · simp only [Nat.zero_eq, mul_zero, zero_add, Nat.cast_one, ← Real.sqrt_eq_rpow] at hP
    exact not_sqrt_one_add_sq_eq_poly ⟨P, hP⟩
  · have : ∀ t, (2 * m + 3) * t * (1 + t * t) ^ ((2 * m + 1) / 2 : ℝ)
        = eval t (derivative P) := by
      intro t
      rw [← Polynomial.deriv]
      have : (fun t => (1 + t * t) ^((2 * (m + 1) + 1) / 2 : ℝ)) = (fun t => eval t P) :=
        Continuous.ext_on (dense_compl_singleton 0)
          (continuous_one_add_sq_rpow _ (div_nonneg (by linarith) zero_le_two))
          P.continuous (by exact_mod_cast hP)
      rw [← this, deriv_rpow_const
        ((differentiableAt_id'.mul differentiableAt_id').const_add 1)
        (Or.inl (lt_add_of_pos_of_le zero_lt_one (mul_self_nonneg t)).ne.symm),
        deriv_const_add, deriv_mul differentiableAt_id differentiableAt_id,
        deriv_id'']
      ring_nf
    have derivative_coeff_zero : (derivative P).coeff 0 = 0 := by
      simp [coeff_zero_eq_eval_zero, ← this]
    have X_mul_divX_derivative : derivative P = X * divX (derivative P) := by
      rw [← add_zero (_ * _), ← C_0, ← derivative_coeff_zero, X_mul_divX_add]
    rw [X_mul_divX_derivative] at this
    refine ih ⟨C (1 / (2 * m + 3) : ℝ) * divX (derivative P), fun t ht => ?_⟩
    rw [eval_mul, eval_C]
    apply mul_left_cancel₀ (by linarith : 2 * (m : ℝ) + 3 ≠ 0)
    rw [← mul_assoc, mul_div_cancel₀ _ (by linarith), one_mul]
    apply mul_left_cancel₀ ht
    nth_rw 4 [← @eval_X _ _ t]
    rw [← eval_mul, ← this t]
    norm_cast
    ac_rfl -/

end sq_ne_poly


open Polynomial

include hn odd_n hv vUnit in
lemma contradiction (hvs_crown : ContDiffOn ℝ 1 v {0}ᶜ) : False := by
  let ⟨P, hP⟩ := vol_ft_A_poly (one_pos.trans hn) (isCompact_closedCrown _ _)
    (isOpen_compl_singleton.mem_nhdsSet.2 (by simp : closedCrown 1 2 ⊆ {0}ᶜ))
    isOpen_compl_singleton hvs_crown
  refine not_one_add_sq_pow_n_div_two_eq_poly' odd_n
    ⟨P * C (MeasureTheory.volume (closedCrown 1 2)).toReal⁻¹, ?_⟩
  filter_upwards [hP, volume_image_closedCrown hn hv vUnit isOpen_compl_singleton
    hvs_crown (isOpen_compl_singleton.mem_nhdsSet.2 (by simp : closedCrown 2⁻¹ 2 ⊆ {0}ᶜ))
    one_pos one_le_two] with t ht1 ht2
  rw [eval_mul, eval_C, ← ht1, ht2, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (add_nonneg zero_le_one (mul_self_nonneg _)), one_div_mul_eq_div,
    mul_assoc, mul_inv_cancel₀ (measure_closedCrown_ne_zero (one_pos.trans hn) zero_le_one one_lt_two), mul_one]

include hv in
lemma v_zero : v 0 = 0 := by
  rw [← zero_smul ℝ 0, hv.isExtension _ _ (le_refl _), zero_smul, zero_smul]

include hn odd_n hv in
theorem HairyBallDiff (contDiffOn_v : ContDiffOn ℝ 1 v {0}ᶜ): ∃ x ∈ unitSphere n, v x = 0 := by
  by_contra!
  have v_ne_zero : ∀ x, x ≠ 0 → v x ≠ 0 := by
    intro x hx
    rw [← one_smul ℝ x, ← mul_inv_cancel₀ (norm_ne_zero_iff.2 hx), ← smul_smul,
      hv.isExtension _ _ (norm_nonneg _), smul_ne_zero_iff, norm_ne_zero_iff]
    refine ⟨hx, this (‖x‖⁻¹ • x) (mem_sphere_zero_iff_norm.2 ?_)⟩
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
  let v' : E n → E n := fun x => ‖x‖ • ‖v x‖⁻¹ • v x
  have v'ContDiff : ContDiffOn ℝ 1 v' {0}ᶜ :=
    ContDiffOn.smul (fun x hx => (contDiffAt_norm ℝ hx).contDiffWithinAt)
      (ContDiffOn.smul ((contDiffOn_inv ℝ).comp (ContDiffOn.norm ℝ contDiffOn_v v_ne_zero)
      fun x hx => norm_ne_zero_iff.2 (v_ne_zero x hx)) contDiffOn_v)
  have hv' : IsExtensionOfVectorFieldOnSn _ v' :=
    ⟨continuous_iff_continuousAt.2 (fun x => by
      by_cases hx : x = 0
      · rw [hx]
        unfold ContinuousAt v'
        rw [norm_zero, zero_smul]
        refine Filter.Tendsto.zero_smul_isBoundedUnder_le tendsto_norm_zero
          (Filter.isBoundedUnder_of ⟨1, fun y => ?_⟩)
        rw [Function.comp_apply, norm_smul, norm_inv, norm_norm]
        by_cases hy : y = 0
        · rw [hy, v_zero hv, norm_zero, mul_zero]
          exact zero_le_one
        · rw [inv_mul_cancel₀ (norm_ne_zero_iff.2 (v_ne_zero _ hy))]
      · exact ContinuousOn.continuousAt (continuous_norm.continuousOn.smul
          (((continuous_norm.comp hv.isCont).continuousOn.inv₀
          (fun y hy => norm_ne_zero_iff.2 (v_ne_zero _ hy))).smul hv.isCont.continuousOn))
          (compl_singleton_mem_nhds hx)),
    fun x => by rw [inner_smul_right, inner_smul_right, hv.isTang, mul_zero, mul_zero],
    fun x r hr => by
      unfold v'
      simp only [hv.isExtension x r hr, norm_smul, Real.norm_eq_abs, abs_eq_self.2 hr.le]
      by_cases hr' : r = 0
      · rw [hr', zero_mul, zero_smul, zero_smul]
      · rw [mul_inv, smul_smul _ r, mul_comm _ r, ← mul_assoc, mul_inv_cancel₀ hr',
          one_mul, smul_smul r]⟩
  have v'Unit : ∀ x, ‖v' x‖ = ‖x‖ := by
    intro x
    by_cases hx : x = 0
    · rw [hx, norm_smul, norm_zero, norm_zero, zero_mul]
    · rw [norm_smul, norm_smul, norm_inv, norm_norm, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 (v_ne_zero _ hx)), mul_one]
  exact @contradiction _ hn odd_n _ hv' v'Unit v'ContDiff

end



section

open MvPolynomial

variable {σ : Type*} {R : Type*}

namespace MvPolynomial

variable [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R]

@[simps]
def toContinuousMap (p : MvPolynomial σ R) : C(σ → R, R) :=
  ⟨fun x => eval x p, by continuity⟩

@[simps]
def toContinuousMapOn (p : MvPolynomial σ R) (X : Set (σ → R)) : C(X, R) :=
  ⟨fun x => p.toContinuousMap x, by fun_prop⟩

@[simps]
def toContinuousMapAlgHom : MvPolynomial σ R →ₐ[R] C(σ → R, R) where
  toFun p := p.toContinuousMap
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
  commutes' _ := by ext; simp

@[simps]
def toContinuousMapOnAlgHom (X : Set (σ → R)): MvPolynomial σ R →ₐ[R] C(X, R) where
  toFun p := p.toContinuousMapOn X
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
  commutes' _ := by ext; simp

end MvPolynomial

section

variable [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R]

noncomputable def mvPolynomialFunctions (X : Set (σ → R)) : Subalgebra R C(X, R) :=
  (⊤ : Subalgebra R (MvPolynomial σ R)).map (MvPolynomial.toContinuousMapOnAlgHom X)

theorem mvPolynomialFunctions_separatesPoints (X : Set (σ → R)) :
    (mvPolynomialFunctions X).SeparatesPoints := by
  intro x y h
  obtain ⟨s, hs⟩ := Classical.exists_not_of_not_forall
    (not_imp_not.mpr funext_iff.mpr (Subtype.coe_ne_coe.mpr h))
  exact ⟨_, ⟨_, ⟨MvPolynomial.X s, ⟨Algebra.mem_top, rfl⟩⟩, rfl⟩, by simp [hs]⟩

theorem mvPolynomialFunctions.topologicalClosure (X : Set (σ → ℝ)) [CompactSpace X] :
    (mvPolynomialFunctions X).topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (mvPolynomialFunctions_separatesPoints X)

theorem mvPolynomialFunctions.starClosure_topologicalClosure {𝕜 : Type*} [RCLike 𝕜]
    (X : Set (σ → 𝕜)) [CompactSpace X] :
    (mvPolynomialFunctions X).starClosure.topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (Subalgebra.separatesPoints_monotone le_sup_left (mvPolynomialFunctions_separatesPoints X))

end

end



section

variable (odd_n : Odd n) {v : unitSphere n → E n} (isContinuous_v : Continuous v)
  (isTang_v : ∀ x : unitSphere n, ⟪(x : E n), v x⟫ = 0)



theorem HairyBallTheorem : ∃ x, v x = 0 := by
  sorry

end
