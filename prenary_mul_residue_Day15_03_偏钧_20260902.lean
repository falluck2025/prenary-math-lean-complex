import Mathlib
/- ================================================================
   偏元数学 · Day15-03-陈偏钧版 · 同态破坏（旋转不分配）
   作者：陈偏钧（偏钧立器）
   与偏贞版互补：偏贞版=群律破坏，偏钧版=同态破坏
   核心：rot 不是乘法同态（先旋后乘 ≠ 先乘后旋），差一个 e^ε
   数域统一（A8）：ε、z 落在 ℂ
   ================================================================ -/
noncomputable section

/-- 复数乘性旋转：z ↦ z * e^ε -/
noncomputable def prenary_mul_rot (z : ℂ) (ε : ℂ) : ℂ :=
  z * Complex.exp ε

/-- 相位平移算子 -/
noncomputable def phase_shift (ε : ℂ) : ℂ :=
  Complex.exp ε

-- 一、经典侧：群律保持
theorem phase_is_group_homomorphism (ε₁ ε₂ : ℂ) :
    phase_shift ε₁ * phase_shift ε₂ = phase_shift (ε₁ + ε₂) := by
  unfold phase_shift
  rw [← Complex.exp_add]

theorem prenary_mul_rot_group_law (z : ℂ) (ε₁ ε₂ : ℂ) :
    prenary_mul_rot (prenary_mul_rot z ε₁) ε₂ = prenary_mul_rot z (ε₁ + ε₂) := by
  unfold prenary_mul_rot
  rw [mul_assoc, ← Complex.exp_add]

theorem prenary_mul_rot_degenerate (z : ℂ) :
    prenary_mul_rot z 0 = z := by
  unfold prenary_mul_rot
  simp

theorem prenary_mul_rot_inverse (z : ℂ) (ε : ℂ) :
    prenary_mul_rot (prenary_mul_rot z ε) (-ε) = z := by
  unfold prenary_mul_rot
  rw [mul_assoc, ← Complex.exp_add]
  simp

-- 二、Day15-03 主刀：动作组合破坏
theorem mul_then_rot (z₁ z₂ : ℂ) (ε : ℂ) :
    prenary_mul_rot (z₁ * z₂) ε = z₁ * z₂ * Complex.exp ε := by
  rfl

theorem rot_then_mul (z₁ z₂ : ℂ) (ε : ℂ) :
    (prenary_mul_rot z₁ ε) * (prenary_mul_rot z₂ ε) =
      z₁ * z₂ * Complex.exp ε * Complex.exp ε := by
  unfold prenary_mul_rot
  ring_nf

theorem action_composition_crack (z₁ z₂ : ℂ) (ε : ℂ) :
    (prenary_mul_rot z₁ ε) * (prenary_mul_rot z₂ ε) =
      prenary_mul_rot (z₁ * z₂) ε * Complex.exp ε := by
  unfold prenary_mul_rot
  ring_nf

-- 三、偏元侧：额外留差结构
noncomputable def mul_residue (z₁ z₂ : ℂ) (ε : ℂ) : ℂ :=
  (prenary_mul_rot z₁ ε) * (prenary_mul_rot z₂ ε) - prenary_mul_rot (z₁ * z₂) ε

theorem mul_residue_explicit (z₁ z₂ : ℂ) (ε : ℂ) :
    mul_residue z₁ z₂ ε = z₁ * z₂ * Complex.exp ε * (Complex.exp ε - 1) := by
  unfold mul_residue prenary_mul_rot
  ring_nf

theorem mul_residue_is_action_crack (z₁ z₂ : ℂ) (ε : ℂ) :
    mul_residue z₁ z₂ ε = prenary_mul_rot (z₁ * z₂) ε * (Complex.exp ε - 1) := by
  unfold mul_residue prenary_mul_rot
  ring_nf

-- 四、留差的两个关键退化
theorem mul_residue_degenerate_zero (z₁ z₂ : ℂ) :
    mul_residue z₁ z₂ 0 = 0 := by
  unfold mul_residue prenary_mul_rot
  simp

theorem mul_residue_degenerate_mul_zero (z₁ z₂ : ℂ) (ε : ℂ) (h : z₁ * z₂ = 0) :
    mul_residue z₁ z₂ ε = 0 := by
  unfold mul_residue prenary_mul_rot
  rcases mul_eq_zero.mp h with hz₁ | hz₂
  · rw [hz₁]
    simp
  · rw [hz₂]
    simp

theorem mul_residue_nonzero_example : mul_residue 1 1 1 ≠ 0 := by
  unfold mul_residue prenary_mul_rot
  simp only [one_mul]
  have h_exp_ne_zero : Complex.exp (1 : ℂ) ≠ 0 := Complex.exp_ne_zero 1
  have h_exp_ne_one : Complex.exp (1 : ℂ) ≠ 1 := by
    intro h
    have hre : Real.exp 1 = 1 := by
      simpa [Complex.exp_re] using congrArg Complex.re h
    have hgt : (1 : ℝ) < Real.exp 1 := by
      nlinarith [Real.exp_zero, Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)]
    linarith
  have h_sub : Complex.exp (1 : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr h_exp_ne_one
  have h_mul : Complex.exp (1 : ℂ) * Complex.exp (1 : ℂ) - Complex.exp (1 : ℂ)
      = Complex.exp (1 : ℂ) * (Complex.exp (1 : ℂ) - 1) := by ring
  rw [h_mul]
  exact mul_ne_zero h_exp_ne_zero h_sub

-- 五、留差与偏元单位偏移的关系（修正：补回"旋转补偿" e^ε 因子）
noncomputable def prenary_mul_unit (ε : ℂ) : ℂ :=
  Complex.exp (-ε)

theorem mul_residue_via_unit (z₁ z₂ : ℂ) (ε : ℂ) :
    mul_residue z₁ z₂ ε =
      (z₁ * z₂) * (prenary_mul_rot 1 ε - 1) * prenary_mul_rot 1 ε := by
  unfold mul_residue prenary_mul_rot
  rw [one_mul]
  ring_nf

end
