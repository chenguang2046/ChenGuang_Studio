# Base_64

Lean 4 + mathlib 基础切片子集：**64 个基础切片**，全量编译 EXIT=0，零 `sorry` / `admit`，公理审计仅报告标准公理。

## 项目简介

`Base_64` 是 `analytic_core` 仓库中的 64 个基础切片子集，由 `Slices_99` 合集共享。所有切片均在本机编译通过（退出码 0），不含任何 `sorry` / `admit`，`#print axioms` 审计仅报告三条标准公理：

```
propext, Classical.choice, Quot.sound
```

## 环境要求

- Lean 4.34.0（`lean-toolchain` 锁定为 `leanprover/lean4:v4.34.0`）
- mathlib v4.34.0

## 目录结构

```
Base_64/
├── All_Slices.lean        # 总控文件，import 全部 64 个切片
├── lean-toolchain         # 锁定的 Lean 工具链
├── Universal_Slice_001.lean ... Universal_Slice_031.lean  # 31 个通用基础切片
├── Zeta_Slice_001.lean ... Zeta_Slice_009.lean            # 10 个 zeta 切片（含 002B）
├── Elliptic_Slice_001.lean ... Elliptic_Slice_006.lean    # 6 个椭圆曲线切片
├── BSD_Ext_Slice_001.lean ... BSD_Ext_Slice_005.lean      # 5 个扩展切片
└── GoldbachCheck.lean, PhiFull_v4.lean, ...               # 其余基础切片
```

## 使用说明

在仓库根目录（使用项目级 Lake 配置）编译：

```bash
lake env lean Base_64/All_Slices.lean
```

公理审计：编译总控文件后，对编译出的模块执行 `#print axioms` 检查。全部切片预期仅报告上述标准公理。

## 许可证

本项目基于 MIT 许可证发布，Copyright (c) 2026 Chen Yong。详见仓库根目录 [LICENSE](../LICENSE)。
