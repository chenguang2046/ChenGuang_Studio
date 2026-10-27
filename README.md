# ChenGuang 99 切片形式化验证合集

> 99 个独立的 Lean 4 形式化验证切片 · 全量编译 EXIT=0 · 零 `sorry` / `admit` · 公理审计仅限标准公理

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
├── README.md                    # 本文件
├── lakefile.toml                # 项目级 Lake 配置
├── ChenGuang_99_Slices/         # 99 切片合集
│   ├── All_Slices.lean          # 总控文件，import 全部 99 个切片
│   ├── lakefile.toml            # 子目录 Lake 配置
│   ├── lean-toolchain           # 锁定的 Lean 工具链
│   ├── Universal_Slice_001.lean ... Universal_Slice_031.lean   # 31 个通用基础切片
│   ├── Riemann_Slice_001.lean ... Riemann_Slice_009.lean       # 10 个黎曼切片（含 002B）
│   ├── BSD_Slice_001.lean ... BSD_Slice_006.lean               # 11 个 BSD 切片（含 Ext1–Ext5）
│   ├── GoldbachCheck.lean, PhiFull_v4.lean, ...                # 12 个哥德巴赫相关切片
│   └── Challenge_*.lean, Slice_Challenge_*.lean                # 35 个挑战切片
└── ChenGuang_Universal_Base_64/ # 64 基础切片子集（可选参考）
```

总控文件 `ChenGuang_99_Slices/All_Slices.lean` import 全部 99 个切片，编译该文件即可验证整个合集。

## 分类统计

| 层 | 数量 | 说明 |
|---|---:|---|
| Universal（通用基础） | 31 | 通用逻辑基础：欧拉乘积、Gamma 函数、模形式、素数、集合论基础 |
| Riemann（黎曼） | 10 | 黎曼 zeta 相关切片（含 002B：Möbius 求和恒等式） |
| BSD | 11 | 椭圆曲线切片（001–006 及 Ext1–Ext5） |
| Goldbach（哥德巴赫） | 12 | 哥德巴赫相关切片：zeta / L 函数 / PNT 前置 |
| Challenge（挑战） | 35 | 挑战定理：CBS、2-torsion、Rouché、004–018 系列 |
| **合计** | **99** | **64 基础 + 35 挑战，全部 EXIT=0，零 sorry** |

## 使用说明

在仓库根目录（使用项目级 Lake 配置）编译：

```bash
lake env lean ChenGuang_99_Slices/All_Slices.lean
```

或直接进入切片目录编译：

```bash
cd ChenGuang_99_Slices
lake env lean All_Slices.lean
```

公理审计：编译总控文件后，对编译出的模块执行 `#print axioms` 检查。全部切片预期仅报告上述标准公理。

## 许可证

本仓库当前未包含 LICENSE 文件，默认保留所有权利；如需授权使用或分发，请联系作者。
