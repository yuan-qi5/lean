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
- **什么是非累积性（non-cumulative）？**
  - 非累积性描述了不同层级宇宙之间的关系，意味着 `Type0` 和 `Type1` 是完全不相交的集合，若需要把它放在更高的宇宙层级中，需要一个明确的提升（lifiting）操作。
- **什么是归纳类型（Inductive Types）？**
  - 归纳类型是一种通过明确列出其所有构造方式来定义新数据类型的方法。这些构造方式称为构造子（constructors）。 

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

通过输入 `\to` 、`\r`、`\->` 来输入 Unicode 箭头 `→`，笛卡尔积的 Unicode 符号 `×` 通过输入 `\times` 来表示，小写希腊字母如 α 、β 和 γ 可用 `\a`、`\b` 和 `\g` 来表示。

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

def F (α : Type u) : Type u := Prod α α  -- 一个类型到类型的函数

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

Lean 提供 fun（或 λ ）关键字，用于从表达式创建匿名函数（def 创建有名称的函数）

从一个表达式创建中通过 “提取” 变量的方式创建一个函数是一个称为 lambda abstraction 的过程。

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

def 定义函数的一般形式为 `def <函数名> <参数列表> : <返回类型> := <函数体> ` 。Lean 通常可推断出参数的类型，但最好显示写出。右侧函数体可以是任何表达式，不仅是 lambda。

def 定义常量一般形式: `def <常量名> : <类型> := <值>`

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

可用 { } 将类型参数写成隐式参数，让 Lean 自己推断，使得在调用时不在需要手动指定。
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
> Lean 中 `;` 是一个**动作或策略的连接器（sequencer）**，含义是 “**然后（then）**”

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

Lean 提供 variable 命令变量类型来使函数声明更紧凑。

``` lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

variable (α β γ : Type)
def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x) 
```

可以声明任何类型的变量，而不仅是 Type 本身。variable 命令指示 Lean 将已声明的变量作为绑定变量插入到通过名称引用他们的定义中。

``` lean
variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)
```

可通过 **section** 限制变量的作用域，当 section 部分关闭，变量会超出作用域，从而无法被引用。但函数会被打包创建出去。
``` lean
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end useful
```

若不需要命名，可以使用匿名的 **section**/**end** 对。

## 2.7 Namespaces

Lean 提供了讲定义分组到嵌套的、分层的命名空间中的能力。

```  lean
namespace Foo
  ...
end Foo
....
open Foo
``` 
在声明为 `Foo` 的命名空间中工作时，所声明的每一个标识符（identifier）都会带有 "Foo." 前缀的全名。在命名空间内部可以使用短名称来引用，但命名空间结束后，必须带上 `Foo.` 前缀引用。

`open` 命令打开命名空间，从而将较短的名称引入当前上下文，不需加前缀访问。

和 section 一样，嵌套的 namespaces 必须按照他们被打开的顺序关闭。

`namespace` 和 `section` 服务于不同目的，`namespace` 用来组织数据，而 `section` 用来为定义声明临时的变量。 `section` 对于界定像 `set_option` 和 `open` 这样命令的作用域也很有用。
> `set_option` 用来配置和调整 Lean 环境的行为，特别是代码的显示方式。（Pretty Printing）  `set_option <选项名称> <值>`
> 


## 2.8 What makes dependent type theory dependent ?

简单的解释是类型可以依赖于参数。

“依赖” 函数类型（Dependent Function Type）：函数的返回值的类型，可以依赖于输入的具体值而变化。            
即：`(a : α) → β a` （称为依赖函数类型或依赖箭头类型）β 是关于 α 的一个类型家族。

当 β 不依赖于 a 时， α → β 只是 (a : α) → β 的表示方式。

**依赖笛卡尔积类型** `(a : α) × β a` 以同样的方式泛化了笛卡尔积 `α × β`。依赖积也称为 sigma 类型，可以写成 `a : α, β a ` 或使用 `⟨a, b⟩` 或 `Sigma.mk a b` 来创建一个依赖对。字符 `⟨` 和 `⟩` 可以分别用 `\langle` 和 `\rangle` 或 `\<` 和 `\>` 来输入。   

Example:
``` lean
universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b
```

## 2.9 Implicit Arguments

依赖类型理论核心特征：项携带大量信息，且其中一些信息可以从上下文中推断出来。在 Lean 中，人们使用下划线 `_` 来指定系统应自动填充信息，这被称为 “隐式参数”

但输入所有下划线仍然很繁琐，Lean 允许你在定义函数时，将那些可以被推断的参数用花括号 `{}` 括起来，而不是圆括号 `()`。被花括号括起来的参数成了 **隐式参数**

``` lean
universe u
def ident {α : Type u} (x : α) := x

#check (ident)
> ident : ?m.22 → ?m.22
```
`#check (ident)` 检查 ident 的类型，`#check ident` 返回 ident 的函数签名。
> `?m22` : `?` 代表这是个 “未知数”，`m` 代表这是个 “元变量”，`.22` 是 Lean 内部给这个空格子的唯一编号，以防和别的空格子混淆。

``` lean
#check @ident
| @ident : {α : Type u_1} → α → α
```
这里的 @ 作用是：临时禁用某个函数的隐式参数机制，将它的所有参数（包括用 `{}` 定义的隐式参数）都变为显式参数。

当变量使用 **variable** 命令声明时，也可指定为隐式：
``` lean
universe u

section
  variable { α : Type u }  -- 声明时指定以后自动把 `α` 当作一个隐式参数
  variable ( x : α )
  def ident := x
end
```

Lean 拥有复杂的机制去实例化隐式参数，它们可被用来推断函数类型、甚至是证明。在项（term）中实例化这些 “空洞” 或 “占位符” 的过程，常被称为 **阐释（elaboration）**。隐式参数的存在意味着，有时可能没有足够的信息来精确地固定一个表达式的含义。

List.nil 是多态常量不是函数，简写为 `[]`。一个多态常量是一个单一的、固定的值，但它具体类型可以根据上下文动态变化。

在 Lean 中，数字是重载的，但当数字的类型无法推断时，Lean 默认假设它是自然数。
> 重载：让同一个符号或名字，根据上下文的不同，拥有多种不同的含义和功能。
```
#check 2
> 2 : Nat
#check (2 : Nat)
> 2 : Nat
#check (2 : Int)
> 2 : Int
```

有时我们已经将某个函数的参数声明为隐式，但现在想要显示地提供该参数。若 foo 是这样的函数，则 @foo 表示具有所有参数都显式地相同函数。







