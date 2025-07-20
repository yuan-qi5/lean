# Tactics

本章描述了一种使用策略构建证明的替代方法。证明项是数学证明的表示；策略是命令或指令，描述了如何构建这些证明。策略是告诉 Lean 如何构建证明项的指令，它们自然支持一种增量式的写证明风格。即将证明分解，并一步一步地处理目标。
> 证明项（proof term）：一个数据结构或计算机程序，本身就是其对应逻辑命题的一个形式化、可验证的证明。

将由一系列策略组成的证明描述称为 “策略风格” 证明（tactic-style proofs），区别于之前所书写的证明项，称为 “项风格” 证明。每种风格各有优缺点，如策略风格证明更短但更难阅读。

此外，策略为使用的 Lean 的自动化提供了一个入口，因为自动化的本身也是策略。

## 5.1 Entering Tactic Mode

从概念上讲，陈述一个定理或引入一个 **have** 语句会创建一个目标，即构建具有期望类型的项的目标。

通常我们会编写一个明确的项来处理这样的目标，但在任何期望项的地方，Lean 允许我们插入一个 `by <tactics>` 块，其中 `<tactics>` 式由**分号或换行符**分隔的一系列命令。

可以用下面方式证明定理：
``` lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
     apply And.intro
     exact hp
     apply And.intro
     exact hq
     exact hp
```
**apply** 策略应用一个表达式，该表达式被视为一个带有零个或多个参数的函数。它会将当前目标的**结论**与该表达式进行**合一**（unify），然后为该表达式中尚未满足的**参数**创建新的子目标。但被转化为新目标的参数，不能被它之后的其他参数所依赖。

> 合一（Unification）：指在逻辑和计算机科学中，通过寻找变量的合适赋值，使两个或多个符号表达式（terms）完全相同的过程。

**exact** 是 **apply** 的一个变体，它表明所给出的表达式应该能**完全**满足当前目标。在策略证明使用它是一种良好的风格，因为它一旦失败，就明确地表示出错了。比 apply 更健壮。apply 更推荐转换证明目标时使用。

策略命令可以接受复合表达式，而不仅仅是单个标识符。如：
``` lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp
```

多个策略应用可以通过使用分号 `;` 进行连接，在单行中编写。
``` lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp
```

可能产生多个子目标的策略通常会标记它们。例如，策略 **apply** And.intro 讲第一个子目标标记为 left，第二个标记为 right。在 apply 策略的情况下，这些标签是从 `And.intro` 声明中所使用的**参数名**推断出来的。可使用 `case <tag> => <tactics>` 这样的写法来结构化策略代码。
``` lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
```

可以使用 **case** 符号在 left 之前解决子目标 right。注意 Lean 将其他目标隐藏在 **case** 块中，即 **case** 会 “聚焦” 于选定的目标。此外，Lean 若在 case 块结束时选定的目标为完全解决，则会报错。

对于简单的子目标，使用标签去选中有些小题大作，但仍可能希望将其证明结构化。Lean 还提供了 “项目符号”（bullet）表示法 `· <tactics>`（或 `* <tactics>`）来结构化证明。
``` lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  · exact hp
  · apply And.intro
    · exact hq
    · exact hp
```


## 5.2 Basic Tactics

### intro

除了 **apply** 和 **exact** 外，另一个有用的策略为 **intro**，它引入一个假设。
``` lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr
```

**intro** 命令可以更一般地用于引入任何类型的变量
``` lean
example (α : Type) : α → α := by
  intro a
  exact a

example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x
```

**intro** 还可用于引入多个变量：
``` lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁
```

`apply` 策略是用于交互式地构造**函数应用**的命令，而 `intro` 策略则是用于交互式地构造**函数抽象**（即 `fun x => e` 形式的项）的命令。与 lambda 抽象的表示法一样， `intro` 策略允许我们使用一种隐式的 `match`。
``` lean
example (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩
```

当假设包含多种可能性时，`intro` 可以像 `match ... with ...` 语句一样进行分类讨论。
```
example (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
  | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩
```

**intro** 策略可以不带任何参数使用，在这种情况下，他会选择名称并尽可能引入多个变量。
``` lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption
```

注意，Lean 自动生成的名称默认是不可访问的，这是为了确保你的策略证明不依赖于这些自动生成的名称，从而使证明更健壮。然后，可以使用组合子（combinator）`unhygienic` 来禁用
``` lean
------ (不推荐使用)
 example : ∀ a b c : Nat, a = b → a = c → c = b := by
  unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1
```

也可使用 `rename_i` 策略来重命名上下文中最近的那些不可访问的名称。下面例子中，`rename_i h1 _ h2` 重命名了上下文中最近三个假设中的两个：
``` lean
---------------------   推荐使用
example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  rename_i h1 _ h2
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1
```



### assumption

**assumption** 策略会检查当前目标上下文中的假设，若有一个于结论匹配，它会应用它。
``` lean
variable (x y z w : Nat)

example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption   -- applied h₃
```

**assumption** 策略在尝试完成目标时，若目标中含有待定的 “洞”（元变量），它会尝试通过匹配一个已知的假设来自动 “填上” 这些洞。
```
variable (x y z w : Nat)

example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans
  assumption      -- solves x = ?b with h₁
  apply Eq.trans
  assumption      -- solves y = ?h₂.b with h₂
  assumption      -- solves z = w with h₃
```

### rf1

`rf1` 策略解决的是将**自反关系**应用于**定义性相等**的参数所形成的目标。
``` lean
example (y : Nat) : (fun x : Nat => 0) y = 0 := by
  rfl
```

### repeat

`repeat` 组合子（combinator）可以被用来多次应用一个策略，直到该策略无法被应用为止：
``` lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption
```

语法为：`repeat <tactic>`，注意 `repeat` 策略本身永远不会失败，即使它一次都没有成功应用 `<tactic>`，整个 `repeat <tactic>`

### revert

`revert` 策略是将在本地上下文中的一个或多个假设或变量 “恢复” 或 “撤回” 到证明目标中，通常是在目标前面加上一个全称量词 `(∀)` 或蕴含箭头 `(→)` 是 `intro` 策略的逆操作。

基本语法为：`revert h1 h2 ...`，这里 `h1`, `h2` 等是想从上下文中移回目标的一个或多个假设或变量的名称。

``` lean
example (x : Nat) : x = x := by
  revert x
  intro y
  rfl
```

`revert` 应用后，证明状态变为：
```
⊢ ∀ (x : Nat), x = x
∀ (x : Nat), x = x
```

`intro y` 应用后为 
```
y : Nat
⊢ y = y  y = y
```

`revert` 和 `intro` 关系：

- `revert` 从证明上下文中取出一个本地变量或假设，将其 “放回” 到证明目标中，通常是在目标前面加一个 `∀` 或 `→`

- `intro` 将前提 `p` 或量词 `∀ x` 从目标中 “拿出来”，将其作为一个新的本地假设或本地变量放入到证明的上下文中

`revert` 不仅会放回上下文中的一个元素，还会放回所有依赖于它的后续上下文元素。例如下面：
``` lean
example (x y : Nat) (h : x = y) : y = x := by
  revert x
  intros
  apply Eq.symm
  assumption
```

在 `revert x` 之后，目标是：
``` lean
y : Nat
⊢ ∀ (x : Nat), x = y → y = x
```

### generalize

只能 `revert` 本地上下文中的一个元素，即一个本地变量或假设。而 `generalize` 策略将目标中的任意表达式替换成一个全新的变量。基本语法为 `generalize e = x`，将当前目标中所有表达式中 `e` 替换为 `x`

``` lean
example : 3 = 3 := by
  generalize 3 = x
  revert x
  intro y
  rfl
```

注意：并非所有的泛化都能保持目标的有效性。下例中 `genelize` 将一个可以用 `rfl` 证明的目标替换成了一个不可证明的目标：
```
example : 2 + 3 = 5 := by
  generalize 3 = x
  -- 此处证明状态为:
  -- x : Nat
  -- ⊢ 2 + x = 5
  sorry
```

因为单纯的泛化会丢失信息，上例中丢失了 `3 = x`。为解决这问题，`generalize` 允许提供一个 “标签”，用来保存被替换掉的值和新变量之间的等式关系。

## 5.3 More Tactics

一些额外的策略对于构造和解构命题与数据很有用。

### cases

当应用于一个形如 `` 的目标时，可以使用像 `apply Or.inl` 和 `apply Or.inl` 等策略，反过来，`cases` 策略可用来分解一个析取式：
```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq
```

注意，`cases` 语法与 `match` 语法相似，新的子目标可以按任何顺序被解决：
``` lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inr hq => apply Or.inl; exact hq  --- 更常用 left 代替 apply Or.inl
  | inl hp => apply Or.inr; exact hp  --- 更常用 right 代替 apply Or.inr
```

也可以使用一个没有 `with` 的（非结构化）`cases`，并为每个分支提供一个策略：
``` lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption
```

当可以用同一个策略来关闭多个子目标时，（非结构化）`cases` 就非常有用：
``` lean
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption
```

你也可以使用组合子 `tac1 <;> tac2` 来将策略 `tac2` 应用于策略 `tac1` 生成的每一个子目标，
```
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption
```

可以将非结构化的 `cases` 策略与 `case` 和 `.` 表示法结合起来：
> - `cases` 是一个**分裂**策略：它作用于一个假设或表达式，根据其内部结构将一个证明目标分裂成多个子目标
>
> - `case` 是一个**选择**策略：它作用于已经存在的多个子目标，并选择其中一个带有特定标签的子目标来集中处理

``` lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  case inl h =>
    apply Or.inr
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  . apply Or.inr
    assumption
```

`cases` 策略也可以用来分解合取式：
``` lean
example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => constructor; exact hq; exact hp
```

`constructor` 策略应用了合取的唯一构造器 And.intro。

在 Inductive Types 章节，会发现这些策略相当通用。`cases` 策略可用来分解任何归纳定义类型的一个元素；`constructor` 策略总是应用归纳定义类型中的第一个适配的构造器。例如，可以使用 `cases` 和 `constructor` 于存在量词符：
``` lean
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; exact px
```

`exists` 策略是用于构造存在量词（`∃`）证明的核心策略。语法为：`exist <witness>`
``` lean
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px
```

这些策略同样适用于数据，就像命题一样，下个示例中，它们被用来定义交换积类型和和类型组件的函数：
``` lean
def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption

def swap_sum : Sum α β → Sum β α := by
  intro p
  cases p
  . apply Sum.inr; assumption
  . apply Sum.inl; assumption
```

注意，除了我们为变量选择的名字，这些定义与合取和析取的类似命题的证明是相同的。`cases` 策略也会对自然数进行情况区分：
``` lean
open Nat
example (P : Nat → Prop)
    (h₀ : P 0) (h₁ : ∀ n, P (succ n))
    (m : Nat) : P m := by
  cases m with
  | zero    => exact h₀
  | succ m' => exact h₁ m'
```

`cases` 策略及其配套的 `induction` 策略，在 Tactics for Inductive Types 有更详细的讨论。

`contradiction` 策略在当前目标的假设中搜索矛盾，从而由爆炸原理完成任何证明目标：
```
example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction
```

也可以在策略块中使用 **match** 或将 **intro** 与 **match** 组合起来。
``` lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨_, Or.inl _⟩ =>
      apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ =>
      apply Or.inr; constructor <;> assumption
  . intro h
    match h with
    | Or.inl ⟨hp, hq⟩ =>
      constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ =>
      constructor; exact hp; apply Or.inr; exact hr
```
``` lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
    | ⟨hp, Or.inl hq⟩ =>
      apply Or.inl; constructor <;> assumption
    | ⟨hp, Or.inr hr⟩ =>
      apply Or.inr; constructor <;> assumption
  . intro
    | Or.inl ⟨hp, hq⟩ =>
      constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨hp, hr⟩ =>
      constructor; assumption; apply Or.inr; assumption

```

## 5.4 Structuring Tactic Proofs

策略构建为构建证明提供一种高效的方式，但一长串的指令可能会掩盖论证的结构。本节描述一些有助于为策略式证明提供结构的方式，式这类证明更具可读性和健壮性。

Lean 证明编写语法的一个优点是，它允许混合使用证明项风格和策略风格的证明，并在这两者之间自由切换。

如 `apply` 和 `exact` 等策略接受任意的证明项（term），可以使用 `have`、`show` 等关键字来编写这些证明项。反之在编写任意 Lean 证明项时，随时可以通过插入一个 `by` 代码来调用策略模式。

``` lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq => exact Or.inl ⟨h.left, hq⟩
    | inr hr => exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq => exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr => exact ⟨hpr.left, Or.inr hpr.right⟩
```



`show` 策略实际上可以用来将一个目标重写为定义上等价的事物：
``` lean
example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl
```

`have` 策略引入一个新的子目标，就像在编写证明项一样，和证明项一样，在 have 策略中可以省略标签，这种情况下使用默认标签 this：



## 5.5 Tactic Combinators






## 5.6 Rewriting

`rw` 策略为应用于目标和假设的替换提供了一种基本机制，提供了一种方便高效地处理等式的方法。该策略最基本的形式是 `rw[t]`，其中 t 是一个类型断言等式的项。
``` lean
variable (k : Nat) (f : Nat → Nat)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂] -- replace k with 0
  rw [h₁] -- replace f 0 with 0
```

可以使用 `rw [t_1, ..., t_n]` 的表示法组合多次重写，这不过是 `rw [t_1]; ...; rw [t_n]` 的简写，
``` lean
variable (k : Nat) (f : Nat → Nat)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂, h₁]
```

默认情况下，`rw` 使用正向的等式，将表达式与左侧匹配，并用右侧替换。可以使用 `←t` 的表示法指示策略以反向方式使用等式 `t`。下例中，可通过输入 `\l` 或 `<-` 作为反向箭头 `←`。
``` lean
variable (a b : Nat) (f : Nat → Nat)

example (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [←h₁, h₂]
```

有时，一个等式的左侧可以匹配模式中的多个子项，在这种情况下，`rw` 策略在遍历该项时会选择它找到的第一个匹配项。若不是你想要的，可使用附加参数来指定正确的子项。
``` lean
example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]
```

可用 `at` 指定 `rw` 重写规则的应用位置。默认情况下，`rw` 应用在证明目标上，而 `rw ... at h` 则将重写规则应用在名为 `h` 的假设上。
> `rw [rule] at *` 在所有假设和目标中所有可能的地方进行重写
>  
``` lean
example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := 
by
  rw [Nat.add_zero] at h
  rw [h]
```

rw 策略不仅限于命题，在以下示例中，使用 `rw [h] at t` 将假设 `t : Tuple α n` 重写为 `t : Tuple α 0 `。
> `//` 是子类型的符号，用于定义一个依赖类型。
``` lean
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := 
by
  rw [h] at t
  exact t
```


## 5.7 Using the Simplifier

`rw` 设计为一种外科手术工具来操作目标，简化器（simplifier）提供一种更强大的自动化形式。Lean 库中许多恒等式被标记为 `[simp]` 属性，simp 策略利用它们来迭代地重写表达式中地子项。

```lean
example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption
```

``` lean
open List

example (xs : List Nat)
        : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := 
by  
  simp
```

> List.reverse 是 Lean 核心库中定义在列表 (List) 上的一个函数。它的作用非常直接：将一个列表的元素顺序完全颠倒。



## 5.8 Split Tactic





## 5.9 Extensible Tactics




