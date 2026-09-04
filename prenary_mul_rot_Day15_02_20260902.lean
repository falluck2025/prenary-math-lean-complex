import Mathlib
/- ================================================================
   偏元数学 · Day15-02 · 复数乘性旋转留差（P0 第一刀）
   数域统一为 ℂ（A8）：ε 直接落在复数域，不跨域构造
   物理侧 + 数学侧：ε 是同一个根
   本稿焊：经典侧四骨架（群同态/退化/群律/逆元）+ 复数零=相位零 + 单位元偏移 + 物理侧对齐
   ================================================================ -/
noncomputable section

/-- 复数乘性旋转：z ↦ z * e^ε -/
noncomputable def prenary_mul_rot (z : ℂ) (ε : ℂ) : ℂ :=
  z * Complex.exp ε

/-- 相位平移算子：ε ↦ e^ε -/
noncomputable def phase_shift (ε : ℂ) : ℂ :=
  Complex.exp ε

-- 一、经典侧四骨架（必须稳过）
theorem phase_is_group_homomorphism (ε₁ ε₂ : ℂ) :
    phase_shift ε₁ * phase_shift ε₂ = phase_shift (ε₁ + ε₂) := by
  unfold phase_shift
  rw [← Complex.exp_add]

theorem prenary_mul_rot_eq_phase (z : ℂ) (ε : ℂ) :
    prenary_mul_rot z ε = z * phase_shift ε := by
  rfl

theorem prenary_mul_rot_degenerate (z : ℂ) :
    prenary_mul_rot z 0 = z := by
  unfold prenary_mul_rot
  simp

theorem prenary_mul_rot_group_law (z : ℂ) (ε₁ ε₂ : ℂ) :
    prenary_mul_rot (prenary_mul_rot z ε₁) ε₂ = prenary_mul_rot z (ε₁ + ε₂) := by
  unfold prenary_mul_rot
  rw [mul_assoc, ← Complex.exp_add]

theorem prenary_mul_rot_inverse (z : ℂ) (ε : ℂ) :
    prenary_mul_rot (prenary_mul_rot z ε) (-ε) = z := by
  unfold prenary_mul_rot
  rw [mul_assoc, ← Complex.exp_add]
  simp

-- 二、偏元侧第一刀：复数零 vs 相位零
def complex_zero : ℂ := 0
def phase_zero : ℂ := 0 * Complex.I

theorem complex_zero_eq_phase_zero : complex_zero = phase_zero := by
  unfold complex_zero phase_zero
  simp

theorem both_zeros_same_rotation (z : ℂ) :
    prenary_mul_rot z complex_zero = z ∧ prenary_mul_rot z phase_zero = z := by
  constructor
  · unfold prenary_mul_rot complex_zero
    simp
  · unfold prenary_mul_rot phase_zero
    simp

theorem zero_identity_observation : complex_zero = 0 ∧ phase_shift phase_zero = 1 := by
  constructor
  · rfl
  · unfold phase_shift phase_zero
    simp

-- 三、偏元侧第二刀：乘法单位元偏移
noncomputable def prenary_mul_unit (ε : ℂ) : ℂ :=
  Complex.exp (-ε)

theorem prenary_mul_unit_offset (ε : ℂ) :
    prenary_mul_rot 1 ε * prenary_mul_unit ε = 1 := by
  unfold prenary_mul_rot prenary_mul_unit
  rw [one_mul]
  rw [← Complex.exp_add]
  simp

theorem prenary_mul_unit_degenerate : prenary_mul_unit 0 = 1 := by
  unfold prenary_mul_unit
  simp

-- 四、物理侧：相位旋转 ↔ 乘性旋转对齐
noncomputable def phase_rotation (z : ℂ) (θ : ℝ) : ℂ :=
  z * Complex.exp (θ * Complex.I)

theorem phase_rotation_is_prenary_mul_rot (z : ℂ) (θ : ℝ) :
    phase_rotation z θ = prenary_mul_rot z (θ * Complex.I) := by
  unfold phase_rotation prenary_mul_rot
  rfl

theorem physical_math_epsilon_unified (z : ℂ) (θ : ℝ) :
    let ε : ℂ := θ * Complex.I
    phase_rotation z θ = prenary_mul_rot z ε := by
  intro ε
  unfold phase_rotation prenary_mul_rot
  rfl

theorem zero_phase_rotation_is_identity (z : ℂ) :
    phase_rotation z 0 = z := by
  unfold phase_rotation
  simp

theorem phase_rotation_composition (z : ℂ) (θ₁ θ₂ : ℝ) :
    phase_rotation (phase_rotation z θ₁) θ₂ = phase_rotation z (θ₁ + θ₂) := by
  unfold phase_rotation
  rw [mul_assoc]
  rw [← Complex.exp_add]
  congr 1
  rw [← add_mul]
  norm_num

end
