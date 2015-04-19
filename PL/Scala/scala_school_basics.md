#Basics

Values: val two = 1 + 1

Variables: var name = "steve"

##Functions

Functions: def adder(m: Int, n: Int) = m + n

Anonymous Functions: (x: Int) => x + 1

Partial application: val add2 = adder(2, _:Int)

Curried functions:

```
def multiply(m: Int)(n: Int): Int = m * n

multiply(2)(3)

val timesTwo = multiply(2) _

timesTwo(3)

```

```

val curriedAdd = (adder _).curried

val addTwo = curriedAdd(2)

addTwo(4)

```

Variable length arguments:

```
def capitalizeAll(args: String*) = {
  args.map { arg =>
    arg.capitalize
  }
}

capitalizeAll("rarity", "applejack")

```

##Classes

```
class Calculator {
  val brand: String = "HP"
  def add(m: Int, n: Int): Int = m + n
}

val calc = new Calculator

calc.add(1, 2)

calc.brand

```

Constructor:

```
class Calculator(brand: String) {
  /**
   * A constructor.
   */
  val color: String = if (brand == "TI") {
    "blue"
  } else if (brand == "HP") {
    "black"
  } else {
    "white"
  }

  // An instance method.
  def add(m: Int, n: Int): Int = m + n
}

val calc = new Calculator("HP")

calc.color

```

Aside: Functions vs Methods

```
class C {
  var acc = 0
  def minc = { acc += 1 }
  val finc = { () => acc += 1 }
  val test = { () => acc }
}

val c = new C

c.minc

c.finc
```

Inheritance and overloading:

```
class ScientificCalculator(brand: String) extends Calculator(brand) {
  def log(m: Double, base: Double) = math.log(m) / math.log(base)
}

class EvenMoreScientificCalculator(brand: String) extends ScientificCalculator(brand) {
  def log(m: Int): Double = log(m, math.exp(1))
}
```

Abstract Classes

```
abstract class Shape {
  def getArea():Int    // subclass should define this
}

class Circle(r: Int) extends Shape {
  def getArea():Int = { r * r * 3 }
}

val c = new Circle(2)
```

Traits

```
trait Car {
  val brand: String
}

trait Shiny {
  val shineRefraction: Int
}

class BMW extends Car {
  val brand = "BMW"
}

class BMW extends Car with Shiny {
  val brand = "BMW"
  val shineRefraction = 12
}

```

Types
```
trait Cache[K, V] {
  def get(key: K): V
  def put(key: K, value: V)
  def delete(key: K)
}
```
