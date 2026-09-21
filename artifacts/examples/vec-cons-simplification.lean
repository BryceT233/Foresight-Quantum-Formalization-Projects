module

public import Mathlib

/-!
# 「4V 的 `vecCons` 化简路径未通」到底是怎么回事

自包含的最小复现，全部经 `lake env lean artifacts/examples/vec-cons-simplification.lean` 验证。

一句话：**不是 `vecCons` 不规约，是当初用了 `simp only`**。`simp` 的默认集里有
`Matrix.cons_val_zero` / `Matrix.cons_val_succ` 这类引理，能化简向量字面量上的 `get`；
`simp only [<数据 def>]` 把这些全关掉了，于是字面量摊在目标里没人管，
`rw [← Rat.norm_cast_real]` 随之找不到着力点，最后只留一个 `⊢ False` 的残局。
-/

/-- 一条 `Fin 5 → ℤ` 字面量，就是生成器发射的那种数据（旧方案的 `ℤ` 版）。 -/
def v : Fin 5 → ℤ := ![-1, 4, -6, 4, -1]

/-- 同样内容换成 `List ℚ`：生成器的新方案。 -/
def vq : List ℚ := [(-1 : ℚ) / 720, 4 / 720, -6 / 720, 4 / 720, -1 / 720]

/-!
## 一、字面量本身最不成问题：`rfl` 一条
-/

example : v 0 = -1 := rfl
example : v ⟨0, by decide⟩ = -1 := rfl
example : v 0 = -1 := by decide

/-!
## 二、`simp only` 与 `simp` 的差别就是全部答案

同一个目标 `(v 0 : ℝ) = -1`，几种写法：

| 写法 | 结果 |
|---|---|
| `by simp only [v]` | ✘ 残局 `⊢ ↑(![-1, 4, -6, 4, -1] 0) = -1` |
| `by simp only [v, Fin.isValue]` | ✘ 同上（补这两个还不够） |
| `by simp only [v, Fin.isValue, Matrix.cons_val_zero]` | ✔ 化简掉，只剩 `⊢ ↑(-1) = -1` |
| `by simp [v]` | ✔ 一条过 |
| `by norm_num` | ✘ 把 `v` 当原子，残局 `⊢ ↑(v 0) = -1` |
| `by decide` | ✔（走规约，不经过 simp） |

`simp` 的默认集带来 `Matrix.cons_val_zero/succ`，`simp only` 和 `norm_num` 都没有。`simp?` 会
直接把它要用的引理列出来：

```
Try this: simp only [v, Int.reduceNeg, Fin.isValue, Matrix.cons_val_zero, Int.cast_neg, Int.cast_one]
```

下面这条跟着建议写，能过：
-/

example : (v 0 : ℝ) = -1 := by
  simp only [v, Int.reduceNeg, Fin.isValue, Matrix.cons_val_zero, Int.cast_neg, Int.cast_one]

-- 原始写法（模拟 `708c9fd`）：展开数据、再想改写 cast，`Vector.get` 没人化简
-- example (i : Fin 5) : ‖(v i : ℝ)‖ ≤ 6 := by
--   fin_cases i <;> simp only [v] <;> rw [← Rat.norm_cast_real] <;> norm_num
-- 报：Did not find an occurrence of the pattern ‖?r‖，残局
--     ‖↑(![-1, 4, -6, 4, -1] ⟨0, ⋯⟩)‖ ≤ 6

/-!
## 三、`simp [v]` 之下，原来那三条界全部能写

注意 `simp` 收不掉的纯算术尾巴（`4 ≤ 6` 之类）还是要 `norm_num` 补一刀——
`simp` 不是万能的，但它负责把字面量摊平，这一步才是当初卡住的地方。
-/

-- 4V 那一格：原始形状，把 `simp only` 换成 `simp`
example (i : Fin 5) : ‖(v i : ℝ)‖ ≤ 6 := by
  fin_cases i <;> simp [v] <;> norm_num

-- `simp only` 版本，把 `cons_val` 家族补回去也能过
example (i : Fin 5) : ‖(v i : ℝ)‖ ≤ 6 := by
  fin_cases i <;>
    simp only [v, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
    norm_num

-- `ℤ → ℚ → ℝ` 的 cast：完整 simp 集 + `← Rat.norm_cast_real`
example (i : Fin 5) : ‖(((v i : ℚ)) : ℝ)‖ ≤ 6 := by
  fin_cases i <;> simp [v, ← Rat.norm_cast_real] <;> norm_num

/-!
## 四、`List` 数据上完整 simp 集同样够用

生成代码走 `List ℚ` + 模式访问函数，`simp` 全默认集加上 `← Rat.norm_cast_real` 即可。
-/

def nth : Fin 5 → ℚ
  | 0 => -1 / 720
  | 1 => 4 / 720
  | 2 => -6 / 720
  | 3 => 4 / 720
  | 4 => -1 / 720

example (i : Fin 5) : ‖(nth i : ℚ)‖ ≤ 6 / 720 := by
  fin_cases i <;> simp [nth, ← Rat.norm_cast_real] <;> norm_num

example : vq.length = 5 := rfl
example : nth 2 = (-6 : ℚ) / 720 := rfl
