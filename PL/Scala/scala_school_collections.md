#Collections
##Basic Data Structures

Lists: val numbers = List(1, 2, 3, 4)

Sets: Set(1, 1, 2)

Tuple:
```
val hostPort = ("localhost", 80)

hostPort._1

hostPort._2

hostPort match {
  case ("localhost", port) => ...
  case (host, port) => ...
}

1 -> 2

```

Maps:
```
Map(1 -> 2)
Map("foo" -> "bar")
Map(1 -> Map("foo" -> "bar"))
Map("timesTwo" -> { timesTwo(_) })

```

Option:
```
val numbers = Map("one" -> 1, "two" -> 2)

numbers.get("two")
numbers.get("three")

val result = if (res1.isDefined) {
  res1.get * 2
} else {
  0
}

val result = res1.getOrElse(0) * 2

val result = res1 match {
  case Some(n) => n * 2
  case None => 0
}

```

##Functional Combinators

val numbers = List(1, 2, 3, 4, 5, 6, 7, 8, 9, 10)

map: numbers.map((i: Int) => i * 2)

foreach: numbers.foreach((i: Int) => i * 2)

filter: numbers.filter((i: Int) => i % 2 == 0)

zip: List(1, 2, 3).zip(List("a", "b", "c"))

partition: numbers.partition(_ % 2 == 0)

find: numbers.find((i: Int) => i > 5)

drop: numbers.drop(5)

dropWihle: numbers.dropWhile(_ % 2 != 0)

foldLeft: numbers.foldLeft(0)((m: Int, n: Int) => m + n)

foldRight: numbers.foldRight(0) { (m: Int, n: Int) => println("m: " + m + " n: " + n); m + n }

flatten: List(List(1, 2), List(3, 4)).flatten

flatMap: nestedNumbers.flatMap(x => x.map(_ * 2))
