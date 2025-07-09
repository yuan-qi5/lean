# Propositions and Proofs

本章解释如何使用依赖类型理论的语言来编写数学断言和证明。

## 3.1 Propositions as Types

依赖类型论：能在同一个通用框架中表示断言和证明。

> 构造器（constructor）：一个用来创建或构造某种数据类型实例的特殊函数或原始操作。
>
> 语法糖（Syntactic Sugar）：在编程语言中，提供一种更简洁、更易于人类读写的语法，而这种语法在底层会被 “翻译” 成一种更基础、更冗长的形式。
>
> 如在 Lean 中，句法糖：`p → q` 底层形式为：`Implies p q`

在自然演绎的证明系统中，关于 “蕴含” 的规则，与函数中关于 “抽象”（函数定义）和 “应用”（函数调用）的规则完全对应，这是 **柯里-霍华德同构（Curry-Howard Isomorphism）** 的一个实例，该理论有时也称为 **命题即类型（Propositions-as-Types）** 的范式。事实上，`Prop` 类型只是 `Sort 0` 的语法糖，`Sort 0` 是类型层级的最底层。且 `Type u` 也仅仅是 `Sort (u+1)` 的语法糖。Prop 有一些特殊性质（如类型无关性），但它也在箭头构造下是封闭的：若有 `p q : Prop`，那么 `p → q` 类型也是 `Prop`

Lean 中可将 Proof p 和 p 本身等同来避免重复编写项 Proof。即每当有 p : Prop 时，可将 p 解释为类型，即证明的类型。然后将 `t: p` 读作断言 t 是 p 的证明。

柯里-霍华德同构是核心思想，依赖构造演算是以此为基础功能更丰富的类型论系统，Lean 是基于 CIC 开发出来的具体的软件。

对于每个命题 p，将 p 关联一个类型，若 p 为假，则该类型为空；若 p 为真，则该类型有一个元素。在后种情形，说（与 p 关联的）类型是可被实例化的

若 p : Prop 是 Lean 中任何命题，Lean 核心将任何两个元素 `t1 t2 : p` 是为定义上相等，这被称为证明无关性。

在依赖类型论语言中形式地表达一个数学断言，需要展示一个项 `p : Prop`。要证明这个断言，需要展示一个项 `t : p`。Lean 作为证明助手，任务是帮助我们构建这样一个项 t，并验证它具有正确地形式和类型。

## 3.2 Working with Propositions as Types





## 3.3 Propositional Logic










## 3.4 Introducing Auxiliary Subgoals





## 3.5 Examples if Propositional Validities





