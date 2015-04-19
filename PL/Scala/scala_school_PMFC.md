#Pattern matching & functional composition

##Function Composition
```
def f(s: String) = "f(" + s + ")"
def g(s: String) = "g(" + s + ")"

val fComposeG = f _ compose g _
fComposeG("yay")
```
```
val fAndThenG = f _ andThen g _
fAndThenG("yay")

```

##PartialFunctions
```
val one: PartialFunction[Int, String] = { case 1 => "one" }

one.isDefinedAt(1)
one.isDefinedAt(2)
one(1)

val two: PartialFunction[Int, String] = { case 2 => "two" }
val three: PartialFunction[Int, String] = { case 3 => "three" }
val wildcard: PartialFunction[Int, String] = { case _ => "something else" }

val partial = one orElse two orElse three orElse wildcard

```

```
case class PhoneExt(name: String, ext: Int)

val extensions = List(PhoneExt("steve", 100), PhoneExt("robey", 200))

extensions.filter { case PhoneExt(name, extension) => extension < 200 }
```
