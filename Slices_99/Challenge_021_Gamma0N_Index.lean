import Slices_99.Challenge_021A_Index_Model
import Slices_99.Challenge_021B_Index_PrimePower
import Slices_99.Challenge_021C_Index_Main
import Slices_99.Challenge_021D_SpecialCase_CrossCheck

/-! # Challenge_021 — Γ₀(N) 指数（聚合入口，ChenGuang Studio）

1184 行单体已解耦为四个独立切片，符号仍挂在 `Challenge021Gamma0NIndex` 命名空间下，
下游 `import Slices_99.Challenge_021_Gamma0N_Index` 无需改动：

| 切片 | 文件 | 职责 |
|------|------|------|
| 021A | `Challenge_021A_Index_Model` | Γ₀(N)、生成元、投影线模型 P¹(N)、陪集双射、CRT 分解 |
| 021B | `Challenge_021B_Index_PrimePower` | 素幂 p^k 陪集覆盖与局部指数 |
| 021C | `Challenge_021C_Index_Main` | 基数乘性、`P1_card`、`Gamma0N_index_eq` |
| 021D | `Challenge_021D_SpecialCase_CrossCheck` | 特例收编：`universalIndex` 骨架、101/102 交叉验证、向下兼容总定理 |
-/
