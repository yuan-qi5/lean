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

**def** 关键字想工作环境声明新的常量符号。eg: `def m : Nat := 1`

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

## 2.4 Definitions




## 2.5 Local Definitions




## 2.6 Variabless and Sections




## 2.7 Namespaces








## 2.8 What makes dependent type theory dependnet ?






## 2.9 Implicit Arguments




























