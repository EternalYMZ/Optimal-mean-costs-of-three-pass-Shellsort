import Shellsort.F09SecondCritical

noncomputable section
namespace Shellsort.F09
open Filter
open scoped Topology

/-- Transfer the two measured physical gap scales to the reduced gcd classes,
including the actual short-chain quotient, the heat time and the final-cost
normalization. No limiting source parameters are independently assumed. -/
theorem phase_reduced_critical_scales (N H G : ℕ → ℕ) (d : ℕ) (hd : 0<d)
    (grow : Tendsto N atTop atTop) (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (first : Tendsto (fun i => ((d*H i:ℕ):ℝ)/Real.sqrt (N i)) atTop (𝓝 a))
    (second : Tendsto (fun i => ((d*G i:ℕ):ℝ)/Real.sqrt (Real.sqrt (N i))) atTop (𝓝 b)) :
    Tendsto (fun n => (G n:ℝ)) atTop atTop ∧
    Tendsto (fun n => (H n:ℝ)) atTop atTop ∧
    Tendsto (fun n => (G n:ℝ)/(H n:ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun n => ((N n / (d*H n):ℕ):ℝ)/(G n:ℝ)^2) atTop (𝓝 ((d:ℝ)^2/(a*b^2))) ∧
    Tendsto (fun n => (G n:ℝ)*Real.sqrt (H n)/Real.sqrt (N n))
      atTop (𝓝 (b*Real.sqrt a/(d*Real.sqrt d))) := by
  let s i := Real.sqrt (N i:ℝ)
  let t i := Real.sqrt (s i)
  let U i := (H i:ℝ)/s i
  let Q i := (G i:ℝ)/t i
  let q i := (N i:ℝ)/((d:ℝ)*H i)
  let m i := N i / (d*H i)
  have dp : (0:ℝ) < d := by exact_mod_cast hd
  have stop : Tendsto s atTop atTop := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp grow)
  have ttop : Tendsto t atTop atTop := Real.tendsto_sqrt_atTop.comp stop
  have ss i : s i ^ 2 = N i := Real.sq_sqrt (Nat.cast_nonneg _)
  have tt i : t i ^ 2 = s i := Real.sq_sqrt (Real.sqrt_nonneg _)
  have ul : Tendsto U atTop (𝓝 (a/d)) := (first.div_const d).congr fun i => by
    dsimp [U,s]; push_cast; field_simp
  have ql : Tendsto Q atTop (𝓝 (b/d)) := (second.div_const d).congr fun i => by
    dsimp [Q,t,s]; push_cast; field_simp
  have ispos := grow.eventually_ge_atTop 1
  have pos_s {i} (hn : 1≤N i) : 0<s i := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have Gn : Tendsto (fun i => (G i:ℝ)) atTop atTop := by
    apply (ql.pos_mul_atTop (div_pos hb dp) ttop).congr'
    filter_upwards [ispos] with i ni
    exact div_mul_cancel₀ _ (Real.sqrt_pos.2 (pos_s ni)).ne'
  have Hn : Tendsto (fun i => (H i:ℝ)) atTop atTop := by
    apply (ul.pos_mul_atTop (div_pos ha dp) stop).congr'
    filter_upwards [ispos] with i ni
    exact div_mul_cancel₀ _ (pos_s ni).ne'
  have gh : Tendsto (fun i => (G i:ℝ)/(H i:ℝ)) atTop (𝓝 0) := by
    apply ((ql.div ul (div_pos ha dp).ne').div_atTop ttop).congr'
    filter_upwards [ispos,Hn.eventually_gt_atTop 0] with i ni hp
    have sp := pos_s ni
    have tp : 0 < t i := Real.sqrt_pos.2 sp
    change (Q i/U i)/t i = _
    dsimp [Q,U]; rw [← tt i]
    field_simp
  have qtop : Tendsto q atTop atTop := by
    apply (stop.atTop_mul_pos (inv_pos.mpr ha) (first.inv₀ ha.ne')).congr
    intro i
    change s i*((((d*H i:ℕ):ℝ)/s i)⁻¹) = q i
    dsimp only [q]; rw [Nat.cast_mul,← ss i, inv_div]; ring
  have fl : Tendsto (fun i => (m i:ℝ)/q i) atTop (𝓝 1) := by
    simpa only [Function.comp_def,m,q,← Nat.cast_mul,Nat.floor_div_eq_div] using tendsto_nat_floor_div_atTop.comp qtop
  have heat : Tendsto (fun i => (m i:ℝ)/(G i:ℝ)^2) atTop (𝓝 ((d:ℝ)^2/(a*b^2))) := by
    have lim := fl.div (first.mul (ql.pow 2)) (by positivity)
    rw [show (1:ℝ)/(a*(b/d)^2)=(d:ℝ)^2/(a*b^2) by field_simp] at lim
    apply lim.congr'
    filter_upwards [ispos,Hn.eventually_gt_atTop 0,Gn.eventually_gt_atTop 0] with i ni hp gp
    have sp := pos_s ni
    have tp : 0 < t i := Real.sqrt_pos.2 sp
    change ((m i:ℝ)/q i)/((((d*H i:ℕ):ℝ)/s i)*(Q i)^2) = _
    dsimp only [q,Q]; rw [Nat.cast_mul,← ss i,← tt i]
    field_simp
  have fac : Tendsto (fun i => (G i:ℝ)*Real.sqrt (H i)/s i) atTop (𝓝 (b*Real.sqrt a/(d*Real.sqrt d))) := by
    have lim := ql.mul (Real.continuous_sqrt.continuousAt.tendsto.comp ul)
    rw [show b/d*Real.sqrt (a/d)=b*Real.sqrt a/(d*Real.sqrt d) by rw [Real.sqrt_div ha.le]; ring] at lim
    apply lim.congr'
    filter_upwards [ispos] with i ni
    have sp := pos_s ni; have tp := Real.sqrt_pos.2 sp
    change (Q i)*Real.sqrt (U i) = _
    dsimp only [Q,U]; rw [Real.sqrt_div (Nat.cast_nonneg _)]
    change ((G i:ℝ)/t i)*(Real.sqrt (H i)/t i) = _
    rw [← tt i]; ring
  exact ⟨Gn,Hn,gh,heat,fac⟩

end Shellsort.F09
