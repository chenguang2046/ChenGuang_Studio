# analytic_core

Lean 4 + mathlib 形式化验证仓库：99 个独立切片全量编译 EXIT=0，零 `sorry` / `admit`，公理审计仅报告标准公理。

## 项目简介

本项目使用 Lean 4 + mathlib 对数论与分析中的一系列命题进行形式化验证，共包含 **99 个独立切片**，由 **64 个基础切片** 与 **35 个挑战切片** 组成。所有切片均在本机编译通过（退出码 0），不含任何 `sorry` / `admit`，`#print axioms` 审计仅报告三条标准公理：

```
propext, Classical.choice, Quot.sound
```

少数早期切片依赖额外的计算性公理（如 `native_decide.ax_1_1`），已在交付记录中逐一披露。

## 环境要求

- Lean 4.34.0（`lean-toolchain` 锁定为 `leanprover/lean4:v4.34.0`）
- mathlib v4.34.0

## 目录结构

```
goldbach/
├── README.md              # 本文件
├── lakefile.toml          # 项目级 Lake 配置（包名 analytic_core）
├── LICENSE                # MIT 许可证
├── Slices_99/             # 99 切片合集
│   ├── All_Slices.lean    # 总控文件，import 全部 99 个切片
│   ├── lakefile.toml      # 子目录 Lake 配置
│   ├── lean-toolchain     # 锁定的 Lean 工具链
│   ├── Universal_Slice_001.lean ... Universal_Slice_031.lean  # 31 个通用基础切片
│   ├── Zeta_Slice_001.lean ... Zeta_Slice_009.lean            # 10 个 zeta 切片（含 002B）
│   ├── Elliptic_Slice_001.lean ... Elliptic_Slice_006.lean    # 6 个椭圆曲线切片
│   ├── BSD_Ext_Slice_001.lean ... BSD_Ext_Slice_005.lean      # 5 个扩展切片
│   ├── GoldbachCheck.lean, PhiFull_v4.lean, ...               # 哥德巴赫相关切片
│   └── Challenge_*.lean, Slice_Challenge_*.lean               # 35 个挑战切片
└── Base_64/             # 64 基础切片子集（可选参考）
    ├── All_Slices.lean  # 总控文件，import 全部 64 个切片
    └── 其余基础切片与 lean-toolchain
```

总控文件 `Slices_99/All_Slices.lean` import 全部 99 个切片，编译该文件即可验证整个合集。

## 分类统计

| 层 | 数量 | 说明 |
|---|---:|---|
| Universal（通用基础） | 31 | 通用逻辑基础：欧拉乘积、Gamma 函数、模形式、素数、集合论基础 |
| Zeta（zeta 函数） | 10 | zeta 相关切片（含 002B：Möbius 求和恒等式） |
| Elliptic（椭圆曲线） | 11 | 椭圆曲线切片（001–006 及 BSD_Ext 001–005） |
| Goldbach（哥德巴赫） | 12 | 哥德巴赫相关切片：zeta / L 函数 / PNT 前置 |
| Challenge（挑战） | 35 | 挑战定理：CBS、2-torsion、Rouché、004–018 系列 |
| **合计** | **99** | **64 基础 + 35 挑战，全部 EXIT=0，零 sorry** |

## 使用说明

在仓库根目录（使用项目级 Lake 配置）编译：

```bash
lake env lean Slices_99/All_Slices.lean
```

或直接进入切片目录编译：

```bash
cd Slices_99
lake env lean All_Slices.lean
```

公理审计：编译总控文件后，对编译出的模块执行 `#print axioms` 检查。全部切片预期仅报告上述标准公理。

## 许可证

本项目基于 MIT 许可证发布，Copyright (c) 2026 Chen Yong。详见 [LICENSE](LICENSE)。
