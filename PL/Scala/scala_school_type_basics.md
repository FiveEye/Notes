#Type & polymorphism basics

##Parametric polymorphism

```
2 :: 1 :: "bar" :: "foo" :: Nil
```

##Variance
  * covariant: [+T]
  * contravariant: [-T]
  * invariant: [T]

```
class Animal { val sound = "rustle" }
class Bird extends Animal { override val sound = "call" }
class Chicken extends Bird { override val sound = "cluck" }
val getTweet: (Bird => String) = ((a: Animal) => a.sound )
```

##Bounds
```
def biophony[T <: Animal](things: Seq[T]) = things map (_.sound)
biophony(Seq(new Chicken, new Bird))

val flock = List(new Bird, new Bird)
new Chicken :: flock
new Animal :: flock
```

##Quantification
```
def count[A](l: List[A]) = l.size
def count(l: List[_]) = l.size
def count(l: List[T forSome { type T }]) = l.size
```
