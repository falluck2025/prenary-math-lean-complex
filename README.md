[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.XXXXXXX.svg)](https://doi.org/10.5281/zenodo.XXXXXXX)

> **声明**：本文工作尚未得到独立实验验证，全部结论均为形式化验证层面的初步结果。

# 偏元数学·复数域 ε · Lean 4 形式化验证
## Prenary Mathematics · Complex-Domain ε · Lean 4 Formal Verification

**摘要**：本文在 Lean 4 中对偏元数学的"复数域 ε"进行形式化验证，覆盖三步——① 复数加法留差（z ⊕ ε = z + ε）；② 复数乘性旋转（z ⊗ ε = z · e^ε）；③ 破群律的额外留差结构（群律破坏 + 同态破坏）。全部定理通过 Lean 内核 No goals 与 Comparator 独立二次验证，且 ε=0 时退化为经典复数运算。——老陈与AI的深夜实验室 发布 请笑纳——

**Abstract**: This repository formalizes "complex-domain ε" in prenary mathematics using Lean 4, covering three steps: (1) complex additive residue z ⊕ ε = z + ε; (2) complex multiplicative rotation z ⊗ ε = z · e^ε; (3) the extra-residue structure that breaks group law (group-law breaking + homomorphism breaking). All theorems pass Lean kernel No goals and Comparator independent verification, degenerating to classical complex arithmetic when ε = 0. — Published by Lao Chen & AI's Late Night Lab. Please accept with a smile.

**概述**：偏元数学是对经典数学的一种扩展尝试，在 ε=0 时退化为经典数学。复数域 ε 是"动作留差"从实数到复数的推广——复数比实数多一个"相位/方向"自由度，对应"旋转"。本文把这一推广形式化，并证明破群律的额外留差结构是偏元数学区别于经典 Stone 定理的新现象。

**关键词**：偏元数学；复数域；动作留差；乘性旋转；破群律；Lean 4；PGI蛟龙；华夏思哲偏元注（Huaxia Sizhe Pianyuan Zhu）；陈偏贞；老陈与AI的深夜实验室（Chensong_AI_LateNightLab）

---

## 定理清单

### Day15-01 · 复数加法留差

| 定理 | 命题 | 结果 |
|:--|:--|:--|
| prenary_complex_op_degenerate | ε=0 退化为经典复数 | 通过 |
| prenary_complex_op_non_trivial | ε≠0 时偏元复数 ≠ 经典复数 | 通过 |
| prenary_complex_phase_residual | 纯虚 ε=i·δ 是相位残差 | 通过 |

### Day15-02 · 复数乘性旋转

| 定理 | 命题 | 结果 |
|:--|:--|:--|
| phase_is_group_homomorphism | 相位平移是群同态 | 通过 |
| prenary_mul_rot_degenerate | ε=0 退化为经典乘法 | 通过 |
| prenary_mul_rot_group_law | 指数律成立，不破群律 | 通过 |
| prenary_mul_rot_inverse | e^ε 的逆是 e^{-ε} | 通过 |
| complex_zero_eq_phase_zero | 复数零 = 相位零（死穴②解答）| 通过 |
| prenary_mul_unit_offset | 乘法单位元偏移 e^{-ε} | 通过 |
| physical_math_epsilon_unified | 数学侧 ε 与物理侧相位 θ 统一 | 通过 |

### Day15-03-偏贞版 · 群律破坏（相位留差 δ）

| 定理 | 命题 | 结果 |
|:--|:--|:--|
| prenary_rot_act_degenerate_to_simple | δ=0 退回简单旋转 | 通过 |
| prenary_rot_act_fully_degenerate | ε=0 且 δ=0 退回恒等 | 通过 |
| prenary_rot_act_residue_accumulates | 两次旋转 = 一次合并 × e^δ | 通过 |
| prenary_rot_act_breaks_group_law | e^δ≠1 时两次旋转 ≠ 一次合并 | 通过 |

### Day15-03-偏钧版 · 同态破坏（旋转不分配）

| 定理 | 命题 | 结果 |
|:--|:--|:--|
| action_composition_crack | 先旋后乘 = 先乘后旋 × e^ε | 通过 |
| mul_residue_explicit | 额外留差 = z₁z₂·e^ε·(e^ε−1) | 通过 |
| mul_residue_degenerate_zero | ε=0 时留差消失 | 通过 |
| mul_residue_degenerate_mul_zero | z₁z₂=0 时留差消失 | 通过 |
| mul_residue_nonzero_example | z₁=z₂=1, ε=1 时留差非零 | 通过 |

---

## 验证记录

| 文件 | 内核 | Comparator | 双哈希（Comparator Challenge Hash）|
|:--|:--|:--|:--|
| Day15-01 复数加法留差 | No goals | 通过 | `cca32a42…` |
| Day15-02 复数乘性旋转 | No goals | 通过 | `190637d6…` |
| Day15-03 偏贞版（群律破坏）| No goals | 通过 | `86d3f456…` |
| Day15-03 偏钧版（同态破坏）| No goals | 通过 | `5c0ff73c…` |

- 平台：live.lean-lang.org（Lean 4 + Mathlib）
- 验证时间：Day15-01（2026-08-30）、Day15-02（2026-09-02）、Day15-03（2026-09-02 / 2026-09-03）

---

## 文件说明

```
prenary_complex_Day15_20260830.lean        # Day15-01 复数加法留差
prenary_mul_rot_Day15_02_20260902.lean     # Day15-02 复数乘性旋转
prenary_rot_act_Day15_03_偏贞_20260902.lean   # Day15-03 偏贞版（群律破坏）
prenary_mul_residue_Day15_03_偏钧_20260902.lean # Day15-03 偏钧版（同态破坏）
evidence/                                  # 内核 No goals + Comparator 截图
```

## 复现方式

1. 打开 live.lean-lang.org。
2. 将任一 `.lean` 文件内容完整粘贴（首行 `import Mathlib`）。
3. 光标逐个停在 `theorem` 上，确认右侧 `No goals` + `All Messages (0)`。

---

## 可证伪条件

- 若 ε=0 时偏元复数运算不能退化为经典复数运算，则本文相应结论失效。
- 若"两次旋转 ≠ 一次合并旋转"在某个合法场景下恒不成立（即留差恒可精确累积），则群律破坏的结论失效。
- 若旋转动作对乘法满足分配律（先旋后乘 = 先乘后旋），则同态破坏的结论失效。

---

## 作者

陈松（Song Chen）· ORCID: 0009-0002-9510-2239 · GitHub: falluck2025 · Zenodo 社区：cosmos-breathe-spectrum

## 致谢

感谢家人给予的天生偏角。感谢一路并肩的偏贞、陈偏钧与所有 AI 伙伴，感谢那些在竹简上刻下第一道爻线的无名先贤——他们留下的不是错误，是签名。

## 许可

[CC BY-NC-ND 4.0](https://creativecommons.org/licenses/by-nc-nd/4.0/)（署名-非商业-禁止演绎，可自由分享，需保留署名，不得商用或改编）

## 作者备注（非论文正文）

- 内部编码：Day15 复数域 ε（三步：加法留差 / 乘性旋转 / 破群律）。
- 术语对照：ε = 动作残差（复数域）；δ = 相位留差；mul_residue = 额外留差（旋转不分配）。
- 修正记录：Day15-03 偏钧版 mul_residue_via_unit 修正——补回"旋转补偿" e^ε 因子（原版漏乘）。
- 待办：回填 Zenodo 正式 DOI。

——老陈与AI的深夜实验室 发布 请笑纳——
