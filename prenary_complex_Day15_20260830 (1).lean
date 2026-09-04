import Mathlib

/- ================================================================
   偏元数学 · 复数域 ε 第一步（Day15，动作留差从实数推广到复数）
   核心：复数有两个自由度——模（大小）+ 辐角（相位/方向）。
         复数 ε 比实数 ε 多一个"相位/方向"维度，对应"旋转"。
   本稿焊「加性留差」 z + ε（ε ∈ ℂ）；「乘性旋转」 z·e^{iε} 待 Day15-02 专门开。
   注：复数 ε 的深层物理含义（相位 ↔ 呼吸子 ↔ 量子相位）进迷雾储物箱。
   ================================================================ -/

noncomputable section

-- 偏元复数动作：复数 z 加复数残差 ε（动作留差推广到复数域）
noncomputable def prenary_complex_op (z ε : ℂ) : ℂ :=
  z + ε

-- 退化：ε=0 → 经典复数
theorem prenary_complex_op_degenerate (z : ℂ) :
    prenary_complex_op z 0 = z := by
  unfold prenary_complex_op
  rw [add_zero]

-- 非平凡：ε≠0 → 偏元复数 ≠ 经典复数
theorem prenary_complex_op_non_trivial (z : ℂ) {ε : ℂ} (hε : ε ≠ 0) :
    prenary_complex_op z ε ≠ z := by
  intro h
  unfold prenary_complex_op at h
  have hε0 : ε = 0 := by
    have h' : z + ε = z + 0 := by simpa using h
    exact add_left_cancel h'
  exact hε hε0

-- 相位残差：纯虚数 ε = i·δ 是"相位残差"（只改虚部，对应旋转/相位）
theorem prenary_complex_phase_residual (z δ : ℂ) :
    prenary_complex_op z (Complex.I * δ) = z + Complex.I * δ := by
  unfold prenary_complex_op
  rfl

end
