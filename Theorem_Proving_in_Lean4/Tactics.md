# Tactics

本章描述了一种使用策略构建证明的替代方法。证明项是数学证明的表示；策略是命令或指令，描述了如何构建这些证明。策略是告诉 Lean 如何构建证明项的指令，它们自然支持一种增量式的写证明风格。即将证明分解，并一步一步地处理目标。

将由一系列策略组成的证明描述 “策略风格” 证明（tactic-style proofs），，于区别于之前所书写的证明项，称为 “项风格” 证明。每种风格各有优缺点，如策略风格证明更短但更难阅读。

此外，策略为使用的 Lean 的自动化提供了一个入口，因为自动化的本身也是策略。

## 5.1 Entering Tactic Mode

从概念上讲，陈述一个定理或引入一个 **have** 语句会创建一个目标，即构建具有期望类型的项的目标。

通常我们会编写一个明确的项来处理这样的目标，但在任何期望项的地方，Lean 允许我们插入一个 `by <tactics>` 块，其中 `<tactics>` 式由分号或换行符分隔的一系列命令。

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
## 5.3 More Tactics







## 5.4 Structuring Tactic Proofs










## 5.5 Tactic Combinators






## 5.6 Rewriting







## 5.7 Using the Simplifier






## 5.8 Split Tactic





## 5.9 Extensible Tactics




