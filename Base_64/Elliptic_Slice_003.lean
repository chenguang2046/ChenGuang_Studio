-- ============================================================
-- Elliptic_Slice_003.lean
-- Elliptic-curve slice 003: pure data tables and decidable assertions.
-- ------------------------------------------------------------
-- Scope:
--   * only self-contained mathematical data and truth assertions
--     (closed by `decide` / self-contained proofs)
--   * no conditional proposition skeletons (nothing unproved is stated,
--     nothing is declared as an axiom)
--   * neutral data fields: label / degree / bound, i.e. objective values
--     only, combined with the most elementary logic
-- Environment: bare Lean 4.34 (Init), no mathlib dependency, zero axioms.
-- ============================================================
set_option maxRecDepth 1000000

-- ------------------------------------------------------------
-- 1. 数据结构: 单条记录
-- ------------------------------------------------------------
structure TableEntry where
  label : String       -- 曲线标签 (客观标识)
  degree : Nat         -- 多项式次数档位
  bound : Nat          -- 数值受控上界
deriving Repr

-- ------------------------------------------------------------
-- 2. 12 条记录数据表
--   上界: 194040.cu1<=2 194766.bg1<=2 226005.b5<=2 226920.h1<=2
--         245310.bs1<=2 256410.m1<=4 256410.q1<=2 297330.bm1<=2
--         305256.n1<=2 312018.bm3<=4 341202.w6<=8 348910.q1<=2
-- ------------------------------------------------------------
def table12 : List TableEntry := [
  { label := "194040.cu1", degree := 2, bound := 2 },
  { label := "194766.bg1", degree := 2, bound := 2 },
  { label := "226005.b5",  degree := 2, bound := 2 },
  { label := "226920.h1",  degree := 2, bound := 2 },
  { label := "245310.bs1", degree := 2, bound := 2 },
  { label := "256410.m1",  degree := 4, bound := 4 },
  { label := "256410.q1",  degree := 2, bound := 2 },
  { label := "297330.bm1", degree := 2, bound := 2 },
  { label := "305256.n1",  degree := 2, bound := 2 },
  { label := "312018.bm3", degree := 4, bound := 4 },
  { label := "341202.w6",  degree := 8, bound := 8 },
  { label := "348910.q1",  degree := 2, bound := 2 }
]

-- ------------------------------------------------------------
-- 3. 表结构真值验证 (decide, 零公理)
-- ------------------------------------------------------------

-- 表规模: 12 条记录
theorem table12_length : table12.length = 12 := by
  decide

-- 上界全域控制: 表中每条记录的 bound <= 8
theorem table12_all_bound_le8 : table12.all (fun e => e.bound <= 8) = true := by
  decide

-- 次数非平凡: 每条记录 degree >= 2
theorem table12_all_degree_pos : table12.all (fun e => 2 <= e.degree) = true := by
  decide

-- 朴素上界一致性: 每条记录 bound <= degree * degree
-- (说明: 档位 2/4/8 与次数 2/4/8 的平方上界自洽, 纯数值断言)
theorem table12_all_bound_le_degree_sq :
    table12.all (fun e => e.bound <= e.degree * e.degree) = true := by
  decide

-- ------------------------------------------------------------
-- 4. 单条点名断言 (label 点名式, 精确档位)
-- ------------------------------------------------------------
theorem inst_194040_cu1 : table12.all (fun e => e.label = "194040.cu1" -> e.bound <= 2) = true := by decide
theorem inst_194766_bg1 : table12.all (fun e => e.label = "194766.bg1" -> e.bound <= 2) = true := by decide
theorem inst_226005_b5  : table12.all (fun e => e.label = "226005.b5" -> e.bound <= 2) = true := by decide
theorem inst_226920_h1  : table12.all (fun e => e.label = "226920.h1" -> e.bound <= 2) = true := by decide
theorem inst_245310_bs1 : table12.all (fun e => e.label = "245310.bs1" -> e.bound <= 2) = true := by decide
theorem inst_256410_m1  : table12.all (fun e => e.label = "256410.m1" -> e.bound <= 4) = true := by decide
theorem inst_256410_q1  : table12.all (fun e => e.label = "256410.q1" -> e.bound <= 2) = true := by decide
theorem inst_297330_bm1 : table12.all (fun e => e.label = "297330.bm1" -> e.bound <= 2) = true := by decide
theorem inst_305256_n1  : table12.all (fun e => e.label = "305256.n1" -> e.bound <= 2) = true := by decide
theorem inst_312018_bm3 : table12.all (fun e => e.label = "312018.bm3" -> e.bound <= 4) = true := by decide
theorem inst_341202_w6  : table12.all (fun e => e.label = "341202.w6" -> e.bound <= 8) = true := by decide
theorem inst_348910_q1  : table12.all (fun e => e.label = "348910.q1" -> e.bound <= 2) = true := by decide

-- ------------------------------------------------------------
-- 5. 档位分布汇总
-- ------------------------------------------------------------
-- 12 条中 <=2 共 9 条, <=4 且 >2 共 2 条, <=8 且 >4 共 1 条 (合计 12/12)
theorem table12_count_le2 : table12.countP (fun e => e.bound <= 2) = 9 := by decide
theorem table12_count_le4 : table12.countP (fun e => e.bound <= 4 && !(e.bound <= 2)) = 2 := by decide
theorem table12_count_le8 : table12.countP (fun e => e.bound <= 8 && !(e.bound <= 4)) = 1 := by decide

-- ------------------------------------------------------------
-- 6. 逻辑组合引理 (纯逻辑, 零公理)
-- ------------------------------------------------------------

-- 链式组合骨架: 蕴含可传递
theorem chain_compose2 {P Q R S : Prop}
    (hPQ : P -> Q) (hQR : Q -> R) (hRS : R -> S) : P -> S :=
  fun hp => hRS (hQR (hPQ hp))

-- 上界单调骨架: 若 k2 <= k1 且 k1 <= 8, 则 k2 <= 8
theorem bound_downward_mono {k1 k2 : Nat}
    (hk : k2 <= k1) (hb : k1 <= 8) : k2 <= 8 :=
  Nat.le_trans hk hb

-- 档位嵌套实例: 2 <= 4 <= 8
theorem nest_2_le_4 : (2 : Nat) <= 4 := by decide
theorem nest_4_le_8 : (4 : Nat) <= 8 := by decide
theorem nest_2_le_8 : (2 : Nat) <= 8 := by decide

-- ------------------------------------------------------------
-- 7. 公理依赖审计
-- ------------------------------------------------------------
#print axioms table12_length
#print axioms table12_all_bound_le8
#print axioms table12_all_degree_pos
#print axioms table12_all_bound_le_degree_sq
#print axioms inst_341202_w6
#print axioms table12_count_le2
#print axioms table12_count_le4
#print axioms table12_count_le8
#print axioms chain_compose2
#print axioms bound_downward_mono
