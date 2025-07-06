# Dependent Type Theory

**Lean** 是基于一个被称为 “构造演算” 的依赖类型理论，它带有可数层级的非累积性宇宙（non-cumulative universes）和归纳类型（inductive type）

**依赖类型理论（Dependent Type Theory）**

- 在普通类型理论（如 Java 和 Python）中，值的类型不能依赖于值。
- 在依赖类型理论中，类型可以依赖于值。

**可数层级的非累积性宇宙（Countable hierarchy of non-cumulative universes）** ： 为解决罗素悖论（Russell's Paradox）

- **什么是宇宙（universe）？**
- 在 lean 中，每个东西都有一个类型，而类型本身也是一个类型。一个包含各种类型的 “类型” ，称为宇宙。
- **为什么要引入层级（hierachy）？**
- `Type`本身的类型是什么？若 `Type`的类型是自己，就会导致罗素悖论那样的自指问题，为避免该问题，lean 引入一个宇宙的层级：`Type0`，`Type1`，`Type2`... 等来消除 `Type: Type` 这种自指结构。可数表示该结构可用自然数索引。
- **什么是非累积性（non-cumulative）**
- 非累积性描述了不同层级宇宙之间的关系，意味着 `Type0` 和 `Type1` 是完全不相交的集合，若需要把它放在更高的宇宙层级中，需要一个明确的提升（lifiting）操作。

## 2.1 Simple Type Theory

类型论得名于每个表达式都有一个关联类型的这一事实。简单类型论的力量在于可从其他类型构造新的类型。

Lean 中多个箭头会从右向左进行组合，Lean 中绝大多数多参数函数都是以柯里化定义的。
> 柯里化（Currying）是一种将 “接受多个参数的函数” 转变为 “接受单一参数的函数序列” 的技术。主要了为了参数复用和创建专用函数，也方便进行延迟执行和函数组合。

&& ：Boolean and, ||: Boolean or

**/-** 和 **-/** 之间的任何文本构成 Lean 会忽略的注释块，**--** 表示该行其余部分会被忽视。

**def** 关键字向工作环境声明新的常量符号。eg: `def m : Nat := 1`

**#check** 命令要求 Lean 报告其类型，在 lean 中，查询系统信息的辅助命令常以 # 开头。

- #check 一个具体的值，返回该值的类型
- #check 一个函数，返回该函数的完整签名（参数和返回类型）
- #check 一个类型，返回该类型所属的 “宇宙”
- #check 一个定理，返回该定理的确切陈述

**#eval** 命令要求 Lean 计算给定表达式的值。

通过输入 `\to` 、`\r`、`\->` 来输入 Unicode 箭头 `→`，笛卡尔积的 Unicode 符号 × 通过输入 `\times` 来表示，小写希腊字母如 α 、β 和 γ 可用 `\a`、`\b` 和 `\g` 来表示。

函数 f 应用于值 x 表示为 f x，书写类型表达式时，箭头向右结合。

## 2.2 Type as objects

`List` 中元素类型必须相同，`Prod` 用来将两个不同类型的值组合成一个单一值的类型，构成数学上的笛卡尔积，通常不直接写 `Prod A B`，使用 `A × B`

某些操作需要针对类型宇宙进行多态，如 List 和 Prod 等：
``` lean
#check List
> List.{u} (α : Type u) : Type u

#check Prod
> Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)
```

为定义多态常量，Lean 允许用 universe 命令显示声明宇宙常量。
``` lean
universe u

def F (α : Type u) : Type u := Prod α α

#check F
> F.{u} (α : Type u) : Type u
```

也可以在定义 F 时提供宇宙参数来避免使用 universe 命令：
``` lean
def F.{u} (α : Type u) : Type u := Prod α α

#check F
> F.{u} (α : Type u) : Type u
```

## 2.3 Function Abstraction and Evaluation

Lean 提供 fun（或 λ）关键字，用于从表达式创建匿名函数（def 创建有名称的函数）

从另一个表达式创建一个函数是一个称为 lambda abstraction 的过程。

``` lean
#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
| fun x y => if (!y) = true then x + 1 else x + 2 : Nat → Bool → Nat
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
| fun x y => if (!y) = true then x + 1 else x + 2 : Nat → Bool → Nat
#check fun x y => if not y then x + 1 else x + 2
| fun x y => if (!y) = true then x + 1 else x + 2 : Nat → Bool → Nat
```

上述三种写法等价，更推荐第二种写法，第一种明确写出来柯里化过程。

lambda 表达式的通用形式是 `fun (x : α) => t` ，变量 x 是一个 “绑定变量”，实际上是一个占位符，其 “作用域” 不会超出表达式。

形式上，在绑定变量的重命名下相同的表达式被称为 α 等价（alpha equivalent）

Lean 中，几乎所有的表达式都像一段小程序，可以被 “执行” 或 “计算” 到一个最简形式。若两个不同的表达式计算后的最简形式相同，Lean 认为他们是完全相等，可以不加证明地相互替换。
> 范式化（Normalization）：将一个项进行持续计算和化简，直到它不能再被简化为止。这个最终的最简形式，被称为该项的范式（normal form）
>

## 2.4 Definitions

定义的一般形式为 `def foo : α := bar `，α 是从表达式 bar 返回的类型。Lean 通常可推断出 α 的类型，但最好显示写出。右侧 bar 可以是任何表达式，不仅是 lambda。

``` lean
def double (x : Nat) : Nat :=
  x + x

def double : Nat → Nat :=
  fun x => x + x
```

接受类型参数的函数：
``` lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```
compose 适用于任何类型 α β γ，使得 compose 可以组合几乎任何两个函数，只要它们各只接受一个参数，且第二个函数的输出类型于第一个函数的输入类型相匹配。
``` lean
#eval compose Nat Nat Nat double square 3
```

可用 {} 将类型参数写成隐式参数，让 Lean 自己推断，使得再调用时不在需要手动指定。
``` lean
def compose {α β γ : Type} (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

## 2.5 Local Definitions

Lean 允许使用 let 关键字引入 “局部” 定义。表达式 `let a := t1; t2` 在定义上等于将 t2 中的每个 a 出现替换为 t1 的结果。

``` lean
def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2
> 16
```

可通过串联 **let** 语句来组合多个赋值：
``` lean
#check let y := 2 + 2; let z := y + y; z * z
> let y := 2 + 2;
> let z := y + y;
> z * z : Nat
#eval  let y := 2 + 2; let z := y + y; z * z
> 64
```

当使用换行时，可以省略 `；`
```
def t (x : Nat) : Nat :=
  let y:= x + x
  y * y
```
注意 `let a := t1; t2` 和 `(fun a => t2) t1` 区别，核心在于信息可见的时间点不同：

- `let a := t1; t2` : 是一个**语法层面的直接替换**。在 Lean 对 `t2` 进行类型检查**之前**，把 `t2` 中所有 `a` 原地替换成 `t1`

- `(fun a => t2) t1` : 是一个**语义层面的函数应用**。Lean 必须**首先**独立地对函数 `fun a => t2` 进行类型检查，确保它本身是合法的。在这个阶段，它**不知道** `a` 的未来值是 `t1`。只有当这个函数被确认为合法后，Lean 才会将 `t1` 作为参数代入。

``` lean
def foo := let a := Nat; fun x : a => x + 2
/-
  def bar := (fun a => fun x : a => x + 2) Nat
-/
```
## 2.6 Variabless and Sections




## 2.7 Namespaces








## 2.8 What makes dependent type theory dependnet ?






## 2.9 Implicit Arguments




























