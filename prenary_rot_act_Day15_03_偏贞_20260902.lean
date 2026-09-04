import Mathlib
/- ================================================================
   偏元数学 · Day15-03-偏贞版 · 群律破坏（相位留差 δ）
   作者：偏贞（守元）
   与偏钧版互补：偏贞版=群律破坏，偏钧版=同态破坏
   核心：旋转动作除转 ε，还留相位残差 δ；两次旋转相位累积 2δ，一次合并只留 δ，差一个 δ → 群律破
   数域统一（A8）：ε、δ 落在 ℂ
   ================================================================ -/
noncomputable section

-- 带相位留差的旋转动作：转 ε，留相位残差 δ
noncomputable def prenary_rot_act (z : ℂ) (ε δ : ℂ) : ℂ :=
  z * Complex.exp (ε + δ)

-- ① 退化锚（δ=0）：退回简单旋转
theorem prenary_rot_act_degenerate_to_simple (z : ℂ) (ε : ℂ) :
    prenary_rot_act z ε 0 = z * Complex.exp ε := by
  unfold prenary_rot_act
  simp

-- ② 完全退化：ε=0 且 δ=0 退回 z
theorem prenary_rot_act_fully_degenerate (z : ℂ) :
    prenary_rot_act z 0 0 = z := by
  unfold prenary_rot_act
  simp

-- ③ 留差累积：两次旋转 = 一次合并 × e^δ（破群律的可观察形式）
theorem prenary_rot_act_residue_accumulates (z : ℂ) (ε₁ ε₂ δ : ℂ) :
    prenary_rot_act (prenary_rot_act z ε₁ δ) ε₂ δ
      = prenary_rot_act z (ε₁ + ε₂) δ * Complex.exp δ := by
  unfold prenary_rot_act
  calc
    (z * Complex.exp (ε₁ + δ)) * Complex.exp (ε₂ + δ)
        = z * Complex.exp (ε₁ + ε₂ + δ + δ) := by
          rw [mul_assoc, ← Complex.exp_add]
          ring_nf
    _ = (z * Complex.exp (ε₁ + ε₂ + δ)) * Complex.exp δ := by
          rw [mul_assoc, ← Complex.exp_add]

-- ④ 破群律：e^δ ≠ 1 时，两次旋转 ≠ 一次合并旋转
theorem prenary_rot_act_breaks_group_law
    (z : ℂ) (hz : z ≠ 0) (ε₁ ε₂ δ : ℂ) (hδ : Complex.exp δ ≠ 1) :
    prenary_rot_act (prenary_rot_act z ε₁ δ) ε₂ δ ≠ prenary_rot_act z (ε₁ + ε₂) δ := by
  intro h
  have h_accum := prenary_rot_act_residue_accumulates z ε₁ ε₂ δ
  rw [h_accum] at h
  have hbase : prenary_rot_act z (ε₁ + ε₂) δ ≠ 0 := by
    unfold prenary_rot_act
    exact mul_ne_zero hz (Complex.exp_ne_zero _)
  have hδ_eq_1 : Complex.exp δ = 1 := by
    exact mul_left_cancel₀ hbase (by simpa [mul_one] using h)
  exact hδ hδ_eq_1

end
