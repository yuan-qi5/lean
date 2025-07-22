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

可以使用 **case** 符号在 left 之前解决子目标 right。注意 Lean 将其他目标隐藏在 **case** 块中，即 **case** 会 “聚焦” 于选定的目标。此外，Lean 若在 case 块结束时选定的目标未完全解决，则会报错。

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
``` lean
example : 2 + 3 = 5 := by
  generalize 3 = x
  -- 此处证明状态为:
  -- x : Nat
  -- ⊢ 2 + x = 5
  sorry
```

因为单纯的泛化会丢失信息，上例中丢失了 `3 = x`。为解决这问题，`generalize` 允许提供一个 “标签”，用来保存被替换掉的值和新变量之间的等式关系。
``` lean
example : 2 + 3 = 5 := by
     generalize h : 3 = x
     rw [← h]
```

## 5.3 More Tactics

一些额外的策略对于构造和解构命题与数据很有用。

### cases

当应用于一个形如 `p ∨ q` 的目标时，可以使用像 `apply Or.inl` 和 `apply Or.inl` 等策略，反过来，`cases` 策略可用来分解一个析取式：
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

存在 `show` 策略，类似证明项中的 `show` 表达式。它只是声明即将解决的目标的类型，同时保持策略模式。
```
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inl ⟨h.left, hq⟩
    | inr hr =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq =>
      show p ∧ (q ∨ r)
      exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr =>
      show p ∧ (q ∨ r)
      exact ⟨hpr.left, Or.inr hpr.right⟩
```

`show` 策略实际上可以用来将一个目标重写为定义上等价的事物：
``` lean
example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl
```

`have` 策略引入一个新的子目标，就像在编写证明项一样，和证明项一样，
``` lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have hpq : p ∧ q := And.intro hp hq
    apply Or.inl
    exact hpq
  | inr hr =>
    have hpr : p ∧ r := And.intro hp hr
    apply Or.inr
    exact hpr
```

在 have 策略中可以省略标签，这种情况下使用默认标签 this：
```
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have : p ∧ q := And.intro hp hq
    apply Or.inl
    exact this
  | inr hr =>
    have : p ∧ r := And.intro hp hr
    apply Or.inr
    exact this
```

`have` 策略甚至可以省略类型和标签，这种情况下，新的事实用标签 *this* 引入：
```
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  cases hqr with
  | inl hq =>
    have := And.intro hp hq
    apply Or.inl; exact this
  | inr hr =>
    have := And.intro hp hr
    apply Or.inr; exact this
```

`let` 策略类似于 `have` 策略，但用于引入局部定义而不是辅助事实。它是证明项中 `let` 项中 `let` 策略的对应物：
```
example : ∃ x, x + 2 = 8 := by
  let a : Nat := 3 * 2  
  exists a
```

和 `have` 一样，可以通过 `let a := 3 * 2` 来隐式地指定类型。

我们使用 `.` 来创建嵌套地策略块。在一个嵌套块中，Lean 会专注于第一个目标，若在块结束时还没有被完全解决，就会生成一个错误。但 `.` 符号对空白敏感，并依赖于缩进来检测策略块是否结束。可以用**花括号**和**分号**来定义策略块：
``` lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  { intro h;
    cases h.right;
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inl ⟨h.left, ‹q›⟩ }
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inr ⟨h.left, ‹r›⟩ } }
  { intro h;
    cases h;
    { show p ∧ (q ∨ r);
      rename_i hpq;
      exact ⟨hpq.left, Or.inl hpq.right⟩ }
    { show p ∧ (q ∨ r);
      rename_i hpr;
      exact ⟨hpr.left, Or.inr hpr.right⟩ } }
```

使用缩进来组织证明是有用的：每当一个策略留下多个子目标时，通过将它们括在块中并缩进来分隔剩余的子目标。因此，若将定理 `foo` 应用于单个目标并产生了四个子目标，那么证明原告看起来类似这样：
```
apply foo
  . <proof of first goal>
  . <proof of second goal>
  . <proof of third goal>
  . <proof of final goal>
```
或
```
apply foo
  case <tag of first goal>  => <proof of first goal>
  case <tag of second goal> => <proof of second goal>
  case <tag of third goal>  => <proof of third goal>
  case <tag of final goal>  => <proof of final goal>
```
或
```
 apply foo
  { <proof of first goal>  }
  { <proof of second goal> }
  { <proof of third goal>  }
  { <proof of final goal>  }
```


## 5.5 Tactic Combinators

Tactic combinators（策略组合子）是用于从旧策略中形成新策略的操作。顺序组合子（sequence combinator）已经在 `by` 块中隐含：
```
example (p q : Prop) (hp : p) : p ∨ q :=
  by apply Or.inl; assumption
```

在 `t1 <;> t2` 中，`<;>` 提供了顺序操作的并行版本：t1 应用于当前目标，然后 t2 应用于所有结果子目标。当最终目标能够以统一的方式完成时很有用。
``` example
example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by constructor <;> assumption
```

`first | t1 | t2 | ... | tn` 对每个 `ti` 进行应用，知道其中一个成功，否则失败。
```
example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q : Prop) (hq : q) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption
```

策略（tactics）可能会失败，而 `try` 组合子则构建一个永远会成功的策略，尽管其成功可能是无意义的（in a trivial）。`try t` 会执行策略 `t`，并且即使 `t` 失败了也会报告成功，这等价于 `first | t | skip`，其中 `skip` 是一个什么都不做（但总会成功）的策略。
```
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption
```

请注意：`repeat (try t)` 会无限循环，因为其内部的策略永远不会失败。

在一个证明中，通常有多个未解决的问题。并行排序是其中一种方法，通过这种方法可以将单个策略应用多个问题，但还有其他方法可以实现。例如，`all_goals t` 将 `t` 应用于所有打开的问题：
```
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption
```

但更推荐 `any_goals`，它与 `all_goals` 类似，但它会在其参数至少一个问题上成功时成功。
```
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption
```

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

和 `rw` 一样，可使用 `at` 来指定简化假设：
``` lean
example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; assumption
```

可以使用通配符星号 `*` 来简化所有假设和目标：
``` lean
attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp at *; assumption

example (x y z : Nat) (p : Nat → Prop)
        (h₁ : p (1 * x + y)) (h₂ : p (x * z * 1))
        : p (y + 0 + x) ∧ p (z * x) := by
  simp at * <;> constructor <;> assumption
```

`local` 修饰符告诉简化在当前文件（或视情况而定的命名空间）中使用这些规则。重复应用交换律和左交换律似乎会引发循环问题，但简化器能检测到那些仅仅时置换器参数的恒等式，并使用一种称为 **有序重写（ordered rewriting）** 的技术。这意味着系统维护着一个内部的项（term）的顺序。

对上述三个恒等式，其效果时表达式中所有括号都会以一种标准方式关联，并且表达式中的项会以一种规范的方式顺序排列。

与 `rw` 一样，你可以给 `simp` 提供一个要使用的事实列表，包括通用的引理、局部的假设、需要展开的定义以及复合表达式。`simp` 策略也能识别 `rewrite` 所使用的 `←t` 语法。这些额外的规则都会被添加到用于简化表达式的恒等式集合中。
``` lean
def f (m n : Nat) : Nat :=
  m + n + m

example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h, ←h', f]
```

在简化时使用本地环境中所有现有的假设，可以使用通配符 `*`：
```
variable (k : Nat) (f : Nat → Nat)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*]
```

simplifier 也会进行**命题重写**。例如，使用假设 p ，它将 p ∧ q 重写为 q 并将 p ∨ q 重写为 True ，然后它轻易地证明了这些。迭代这样的重写会产生非平凡的命题推理。
``` lean
example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  simp [*]

example (p q : Prop) (hp : p) : p ∨ q := by
  simp [*]

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [*]
```

下一个例子简化了所有假设，然后使用它们来证明目标：
``` lean
example (u w x x' y y' z : Nat) (p : Nat → Prop)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  simp at *
  simp [*]
```

让 `simplifier` 特别有用的一点是，随着库的发展，功能可以不断扩展。例如，假设定义了一个列表操作，通过追加其反转来对称化其输入：
``` lean
def mk_symm (xs : List α) :=
  xs ++ xs.reverse
```

然后对于任何列表 xs，(mk_symm xs).reverse 等于 mk_symm xs，这可通过展开定义证明：
``` lean
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]
```

然后可以使用这个定理去证明新的结果，如果这个定理是对的，我们希望不必显示地调用。可以通过在定理定义时，将其标记为简化规则来实现这一点：
``` lean
@[simp] theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp
```

符号 `@[simp]` 声明 `reverse_mk_symm` 具有属性 `[simp]`，并且可以更明确的表示。
``` lean
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
     simp [mk_symm]

attribute [simp] reverse_mk_symm

example (xs ys : List Nat)
: (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
     simp
```

然而，一旦应用了属性，就再也无法永久移除了；它将已知存在于任何导入分配了该属性的文件中。但可以使用 `local` 修饰符将属性的作用范围限制在当前文件或命名空间中。
``` lean
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

section
attribute [local simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

end
```

在 section 外，简化器将不再默认使用 `reverse_mk_symm`

`simp` 策略有许多配置选项。例如，可以按如下方式启用上下文简化：
```
example : if x = 0 then y + x =y else x ≠ 0 := by 
     sim +contextual
```

另一个有用的配置选项时 `+arith`，它启用算术简化：
```
example : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
     simp +arith
```

## 5.8 Split Tactic

`split` 策略在分解嵌套 `if-then-else` 和 `match` 表达式时很有用。对于具有 match 个分支的 n 表达式，split 策略最多生成 n 个子目标。
```
def f (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _, _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by
  intros
  simp [f]
  split
  . contradiction
  . contradiction
  . contradiction
  . rfl
```

可以将上述策略压缩如下：
```
example (x y z : Nat) :
  x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w →
  f x y w = 1 := by
  intros; simp [f]; split <;> first | contradiction | rfl

```

## 5.9 Extensible Tactics

以 `triv` 为例如何定义策略：

- 可使用 `syntax` 声明符号 `triv` 为策略。然后，使用命令

- `macro_rules` 指定当使用 `triv` 时应执行的操作。可以提供不同的扩展，策略解释器会尝试所有扩展直到一个成功。
``` lean
macro_rules
  | `(tactic| 你的策略名) => `(tactic| 实现该功能的现有策略)
```

- 扩展现有策略的功能，即增加更多的 `macro_rules`。Lean 会将这些规则视为一个 “备选方案列表”。

**工作机制（回溯 Backtracking）**：
当 Lean 执行策略时：

1. 按定义顺序尝试第一条 `macro_rules`
2. 如果该规则展开后的策略执行成功，则整个策略成功
3. 如果该规则展开后的策略执行失败，Lean 不会报错，而是会**自动回溯**，并尝试列表中的下一条 `macro_rules`
4. 这个过程会持续进行，直到有一条规则成功，或者所有规则都产生过hi失败（此时整个策略才算失败）











