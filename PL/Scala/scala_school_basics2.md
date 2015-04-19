#Basics continued

##apply methods

```
class Foo {}

object FooMaker {
  def apply() = new Foo
}

val newFoo = FooMaker()
```

```
class Bar {
  def apply() = 0
}

val bar = new Bar

bar()
```

##Objects
```
object Timer {
  var count = 0

  def currentCount(): Long = {
    count += 1
    count
  }
}

Timer.currentCount()
```
```
class Bar(foo: String)

object Bar {
  def apply(foo: String) = new Bar(foo)
}
```

##Functions are Objects
```
object addOne extends Function1[Int, Int] {
  def apply(m: Int): Int = m + 1
}

addOne(1)
```

```
class AddOne extends (Int => Int) {
  def apply(m: Int): Int = m + 1
}
```

##Packages
```
package com.twitter.example

object colorHolder {
  val BLUE = "Blue"
  val RED = "Red"
}
```

##Pattern Matching

###Matching on value
```
val times = 1

times match {
  case 1 => "one"
  case 2 => "two"
  case _ => "some other number"
}

times match {
  case i if i == 1 => "one"
  case i if i == 2 => "two"
  case _ => "some other number"
}
```

###Matching on type
```
def bigger(o: Any): Any = {
  o match {
    case i: Int if i < 0 => i - 1
    case i: Int => i + 1
    case d: Double if d < 0.0 => d - 0.1
    case d: Double => d + 0.1
    case text: String => text + "s"
  }
}
```

###Matching on class members
```
class Calculator(_brand: String, _model: String) {
  val brand = _brand
  val model = _model
}

def calcType(calc: Calculator) = calc match {
  case _ if calc.brand == "hp" && calc.model == "20B" => "financial"
  case _ if calc.brand == "hp" && calc.model == "48G" => "scientific"
  case _ if calc.brand == "hp" && calc.model == "30B" => "business"
  case _ => "unknown"
}
```

##Case Classes
```
case class Calculator(brand: String, model: String)

val hp20b = Calculator("hp", "20B")
val hp30b = Calculator("hp", "30B")
val aa30b = Calculator("aa", "30B")


def calcType(calc: Calculator) = calc match {
  case Calculator("hp", "20B") => "financial"
  case Calculator("hp", "48G") => "scientific"
  case Calculator("hp", "30B") => "business"
  case c => "Calculator: %s of unknown type".format(c)
}
```

##Exceptions
```
try {
  remoteCalculatorService.add(1, 2)
} catch {
  case e: ServerIsDownException => log.error(e, "the remote calculator service is unavailable. should have kept your trusty HP.")
} finally {
  remoteCalculatorService.close()
}
```
```
val result: Int = try {
  remoteCalculatorService.add(1, 2)
} catch {
  case e: ServerIsDownException => {
    log.error(e, "the remote calculator service is unavailable. should have kept your trusty HP.")
    0
  }
} finally {
  remoteCalculatorService.close()
}
```
