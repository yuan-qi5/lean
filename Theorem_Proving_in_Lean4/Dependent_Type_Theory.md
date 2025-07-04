# Dependent Type Theory

**Lean** 是基于一个被称为 “构造演算” 的依赖类型理论，它带有可数层级的非累积性宇宙（non-cumulative universes）和归纳类型（inductive type）

**依赖类型理论（Dependent Type Theory）**

**可数层级的非累积性宇宙（Countable hierarchy of non-cumulative universes）** ： 为解决罗素悖论（Russell's Paradox）

- **什么是宇宙（universe）？**
- 在 lean 中，每个东西都有一个类型，而类型本身也是一个类型。一个包含更重类型的 “类型” ，称为宇宙。
- **为什么要引入层级（hierachy）？**
- `Type`本身的类型是什么？若 `Type`的类型是自己，就会导致罗素悖论那样的自指问题，为避免该问题，lean 引入一个宇宙的层级：`Type0`，`Type1`，`Type2`... 等来消除 `Type: Type` 这种自指结构。可数表示该结构可用自然数索引。
- **什么是非累积性（non-cumulative）**
- 非累积性描述了不同层级宇宙之间的关系，意味着 `Type0` 和 `Type1` 是完全不相交的集合，若需要把它放在更高的宇宙层级中，需要一个明确的提升（lifiting）操作。

## 2.1 Simple Type Theory

**/-** 和 **-/** 之间的任何文本构成 Lean 会忽略的注释块，**--** 表示该行其余部分会被忽视。

**def** 关键字想工作环境声明新的常量符号。eg: `def m : Nat := 1`

**#check** 命令要求 Lean 报告其类型，在 lean 中，查询系统信息的辅助命令常以 # 开头。

**#eval** 命令要求 Lean 计算给定表达式的值。

通过输入 `\to` 、`\r`、`\->` 来输入 Unicode 箭头 `→`，笛卡尔积的 Unicode 符号 × 通过输入 `\times` 来表示，小写希腊字母如 α 、β 和 γ 可用 `\a`、`\b` 和 `\g` 来表示。











