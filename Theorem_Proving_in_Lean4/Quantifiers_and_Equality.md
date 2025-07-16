# Quantifiers and Equality

本章将逻辑构造的范围扩展到包括全称量词、存在量词和等价关系。

## 4.1 The Universal Quantifier 全称量词

**全称量词**：`∀ x : a, p x` 表示 “对每一个 `x : a`, `p x` 都成立”。在自然演绎系统中，与命题联结词一样，“任意”（forall）也是由一条引入规则和一条消去规则来支配。

非形式化讲，**引入规则**陈述如下：在一个 `x : a` 是任意的上下文中，如果我们有一个 `p x` 的证明，那就得到了 `∀ x : a, p x` 的一个证明。

**消除规则**陈述如下：给定一个 `∀ x : a, p x`的横眉，以及任意一个类型为 `a` 的项 `t`，能获得一个 `p t` 的证明

可以将命题之间的蕴含 `p → q` 视为 `∀ x : p, q` 的特殊情况，其中表达式 `q` 不依赖于 `x`。

作为一个书写惯例，我们默认给予全称量词尽可能宽的作用范围。因此，在像 (∀ x : α, p x) → q 这样的例子中，必须使用括号来将量词 ∀ x 的作用范围限制在蕴涵（→）的假设部分（即左边的部分）。

尽管绑定变量的命名不同，但表达式仍被视为等价。因此，可以在假设和结论中使用相同的变量 x，并在证明中用不同的变量 z 对其进行实例化：
``` lean
example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from And.left (h z)
```

`Prop` 在类型宇宙的特殊规则：只要一个函数返回的是 `Prop`，那么无论输入类型 `a` 的宇宙层级有多高，这个函数类型本身永远都只在 `Prop`(`Sort 0`)级别。

`Prop` 上述的特殊规则，被称为非全称性（Imprediactivity）。即一个定义是非全称的，如果它通过一个包含了该定义物本身的集合来定义该事物。因为 `Prop` 被看作纯粹的逻辑问题只关心真假，所以不会导致罗素悖论。

## 4.2 Equality 相等

在 chapter7 Inductive types 解释如何从 Lean 的逻辑框架的基本原理定义 equality。这里将解释如何使用 equality。

等价的基本关系：

- `Eq.refl` 等于的自反性（Reflexivity）

  - 类型签名：`Eq.refl {α : Sort u}(a : α) : a = a`
  - 函数 `Eq.refl` 接受参数 a，返回 `a = a` 的证明

- `Eq.symm` 等于的对称性（Symmetry）

  - 类型签名：`Eq.symm {α : Sort u} {a b : α} (h : a = b) b = a`
  - 函数 `Eq.symm` 接受证明作为参数，返回等式的反转
 
- `Eq.trans` 等于的传递性（Transitivity）

  - 类型签名：`(Eq.trans {α : Sort u} {a b c : α} (h1 : a = b) (h2 : b = c) : a = c)`
  - 函数 `Eq.trans` 接受两个证明作为参数的函数，把两个证明做连接起来

``` lean
variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
```
上述过程也可使用点表示法：
``` lean
example : a = d := (hab.trans hcb.symm).trans hcd
```

自反性（Reflexivity）比其看起来更有用。因为在构造演算（Calculus of Construction）中，项（terms）具有计算性解释，且该逻辑框架将具有**共同规约形式**（common reduct）的项时为相同。所以，一些非平凡等式可通过自反性来证明：
``` lean
variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _
```

该框架的这个特性非常重要，所以库中定义了符号 `rfl` 来表示 `Eq.refl _`

``` lean
example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : β) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl
```

由于每个断言都 “尊重” 这种等价关系，可以替换相等的表达式而不改变其真值。即给定 `h1 : a = b` 和 `h2 : p a`，可以通过替换构造一个 `p b` 的证明：`Eq.subst h1 h2`

``` lean
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2
```
第二种表示法中的三角形符号是一个基于 `Eq.subst` 和 `Eq.symm` 构建的宏，可通过输入 `\t` 来打印出它。`h1 ▸ h2`: 这行代码可以直观地解读为 "将 `h1` 应用于 `h2`" 或 "用 `h1` 重写 `h2`"

规则 `Eq.subst` 用来定义下列辅助规则 `congrArg`、`congrFun` 和 `congr`

- `congrArg` 可用来替换参数（Argument）
  - 含义：Congruence for Argument（参数的一致性）
  - 规则：当有两个相等的参数，将其分别应用到同一个函数上，得到的结果也相等
 
- `congrFun` 可用来替换被应用的函数
  - 含义：Congruence for Fuction
  - 规则：当有两个相等的函数，将同一个参数应用到它们上面，得到的结果也相等
 
- `congr` 可用来同时替换两者
  - 含义：Congruence
  - 规则：当有两个相等的函数并且有两个相等的参数，那么将它们分别应用的结果也是相等的 

``` lean
variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁
```

注意，`Eq.subst` 的第二个隐式参数（它提供了替换发生的上下文）的类型是 `α → Prop`。因此，要推断出这个为此需要一个**高阶合一（high-order unification）** 的实例，但在完全泛化的场景下，“确定一个高阶合一是否存在” 这个问题是**不可判定的（undecidable）**，因此 Lean 最多只能为该问题提供不完美和近似的解决方案。结果就是，`Eq.sunst` 并不总能做到期望解决的事情，而宏 `h ▸ e` 使用启发式方法来计算这个隐式参数，应用成功可能性更高。

> High-Order Unification：合一（Unification）在计算机科学中，指 “解方程”，但解的是表达式。高阶（Higher-Order）指当方程里的未知数本身是函数就变成了 “函数”。
>
> 不可判定：不存在一个算法，能在有限时间内对所有可能的情况，都给出 “是” 或 “否” 的正确答案。


## 4.3 Calculational Proofs 计算性证明

一个计算性证明是一系列通过基本原理（如等价关系的传递性）组合起来的中间结果链。在 Lean 中，计算性证明以关键词 **calc** 开始，并具有以下语法：

``` lean
calc
    <expr>_0 'op_1' <expr_1> ':=' <proof>_1
    '_'      'op_2' <expr_2> ':=' <proof>_2
    ...
    '_'      'op_n' <expr_n> ':=' <proof>_n
```
请注意，所有 **calc** 关系都有相同的缩进，每个 <proof>_i 都是一个对 <expr>_{i-1} op_i <expr>_i 的证明。

也可以在第一个关系中使用 _ （紧接在 <expr>_0 之后），这有助于对其关系/证明序列对：
``` lean
calc <expr>_0
    '_' 'op_1' <expr>_1 ':=' <proof>_1
    '_' 'op_2' <expr>_2 ':=' <proof>_2
    ...
    '_' 'op_n' <expr>_n ':=' <proof>_n
```

这种证明风格在使用 **simp** 和 **rw** 策略时最为有效，这两个策略在下一章讨论。

`calc` 命令可被配置用于任何支持某种形式的传递性的关系。它甚至可以组合不同的关系。可以通过添加 `Trans` 类型类的新实例来 “教” `calc` 新的传递性定理。类型类（Type class）将在后面介绍，

TODO

## 4.4 The Existential Quantifier 存在量词

存在量词可以写成 `exists x : α , p x` 或 `∃ x : α, p x `。这两个版本实际上都是 Lean 库中定义的更长表达式 `fun x : α => p x` 的的缩写。

引入规则：要证明 `∃ x : α, p x`，只需提供一个合适的项 t 和 p t 的证明即可。
``` lean
#check @Exists.intro
| @Exists.intro : ∀ {α : Sort u_1} {p : α → Prop} (w : α), p w → Exists p

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)
```

当类型从上下文中清晰时，可以使用匿名构造器符号 `⟨t, h⟩` 来表示 `Exists.intro t h`
``` lean
example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩
```

![pack_unpack](./pictures/pack_unpack.png)

`|` ：用来分隔不同情况或不同分支的。

注意，`Exist.intro` 含有**隐式参数**（implicit arguments）：Lean 必须在结论 `∃ x, p x` 中推断出**谓词**（predicate）`p : α → Prop`，这并非易事。

例如，如果我们有 `hg : g 0 0 = 0`，然后我们写 `Exists.intro 0 hg`，那么谓词 `p` 会有很多可能的值，分别对应于 `∃ x, g x x = x`、`∃ x, g x x = 0`、`∃ x, g x 0 = x` 等不同的定理。

Lean 会利用**上下文**来推断哪一个是最合适的，下面例子阐释了这一点，该例子中把选项 `pp.explicit` 设置为 `true`，来让 Lean 的 pretty-printer 显示出那些隐式的参数。

可以将 `Exist.intro` 视为一种信息隐藏操作，因为它隐藏了断言主体中的见证。存在消去规则 `Exist.elim` 则执行相反的操作。它允许我们从 `∃ x : α, p x` 出发来证明一个命题 `q`，其方法是：对于一个任意值 `w`，我们证明 `q` 能从 `p w` 推导出来。
``` lean
#check Exists.elim
| Exists.elim.{u} {α : Sort u} {p : α → Prop} {b : Prop} (h₁ : ∃ x, p x) (h₂ : ∀ (a : α), p a → b) : b

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)
```

exists-elimination rule 和 or-elimination rule 关系：断言 `∃ x : α, p x` 可以被视为命题 `p a` 的一个大的析取，当 a 遍历 α 的所有元素时。 




## 4.5 More on the Proof Language 

















