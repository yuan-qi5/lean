# 7. Structures

现代数学广泛使用了代数结构，这些代数结构封装了可在不同环境中实例化的模式，而且往往有多种方法对它们进行定义和实例化。

因此，Lean 提供了相应的方法来形式化定义这些结构并对其进行操作。

本章解释之前出现过的方括号语法，比如 `[Ring α]`、`[Lattice α]` ，并介绍如何创建并使用自定义的代数结构

## 7.1 定义结构体

广义上说，结构体是对**特定形式数据集合**的约定，包括包含**数据的形式**以及这些数据要**满足的一些约束条件**。
``` lean
@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ
```

上面的 `@[ext]` 注解让 Lean 自动生成一个定理，内容是当该结构体的两个实例的**组成部分对应相同**时，这两个实例**相等**。该属性也成为**外延性（extensionality）**

```
example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  ext
  repeat' assumption
```
> `repeat'` 是 `repeat` 策略的一个变体，它的作用是 **重复应用一个策略直到目标没有变化**。 `repeat` 策略是 **重复应用一个策略直到策略失败**。区别在于策略可以成功应用但目标没有改变，推荐使用 `repeat'`。


实例化 `Point` 的不同方法：
```
def myPoint1 : Point where
  x := 2
  y := -1
  z := 4

def myPoint2 : Point :=
  ⟨2, -1, 4⟩

def myPoint3 :=
  Point.mk 2 (-1) 4
```
其中定义 `myPoint3` 时用到函数 `Point.mk` 叫做 `Point` 结构体的构造函数（constructor），用于构造结构体成员。也可以为构造函数指定一个不同的名字，比如 `build`。
```
structure Point' where build ::
  x : ℝ
  y : ℝ
  z : ℝ

#check Point'.build 2 (-1) 4
```

接下来两个例子展示了如何定义结构体的函数。
``` lean
namespace Point   --- 不打开命名空间，需要写完整名称

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def add' (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

#check add myPoint1 myPoint2
#check myPoint1.add myPoint2

end Point
```
> 匿名投影记号（Anonymous Projection Notation）是一种语法糖，允许在不明确提及结构体类型名称的情况下，访问或 “投影” 结构体实例的字段。例如用 `a.add b` 代替 `Point.add a b`

接下来继续在相关命名空间添加定义，但在引用的代码片段中省略开关命名空间的相关指令。
```
protected theorem add_comm (a b : Point) : add a b = add b a := by
  rw [add, add]
  ext <;> dsimp
  repeat' apply add_comm

example (a b : Point) : add a b = add b a := by simp [add, add_comm]
```
> `dsimp` 是一种策略，用于进行**定义性化简（definitional simplification）**。它的核心作用是**展开定义**，将表达式中符合 **“定义性相等”** 的部分进行替换，但**不会**使用任何定理或重写规则来 “证明” 相等。
>
> `protected` 是一个关键字，用于**限制对某个名称的访问**，使其名称不会被自动加入到根命名空间中。核心作用为：一个被标记为 `proteted` 的定义，只有在**打开其所在的命名空间**或者**使用完整的名称**时才能被访问。
>
> 在 Mathlib 中，乘法对加法的分配律区分**左分配律**和**右分配律**

![mul_add](./pictures/mul_add.png)

## 7.2 代数结构



## 7.3 构建高斯整数














## 







