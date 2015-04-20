#Advanced types

##View bounds
```
implicit def strToInt(x: String) = x.toInt

class Container[A <% Int] { def addIt(x: A) = 123 + x }

(new Container[String]).addIt("123")

```
##Other type bounds
  * ``A =:= B``: A must be equal to B
  * ``A <:< B``: A must be a subtype of B
  * ``A <%< B``: A must be viewable as B

```
class Container[A](value: A) { def addIt(implicit evidence: A =:= Int) = 123 + value }

(new Container(123)).addIt

(new Container("123")).addIt
```

```
class Container[A](value: A) { def addIt(implicit evidence: A <%< Int) = 123 + value }

(new Container("123")).addIt
```

###Generic programming with views
```
List(1,2,3,4).min(new Ordering[Int] { def compare(a: Int, b: Int) = b compare a })

trait LowPriorityOrderingImplicits {
  implicit def ordered[A <: Ordered[A]]: Ordering[A] = new Ordering[A] {
    def compare(x: A, y: A) = x.compare(y)
  }
}
```

###Context bounds & implicitly[]
```
def foo[A](implicit x: Ordered[A]) {}
foo: [A](implicit x: Ordered[A])Unit

def foo[A : Ordered] {}

implicitly[Ordering[Int]]
```

##Higher-kinded types & ad-hoc polymorphism

```
trait Container[M[_]] { def put[A](x: A): M[A]; def get[A](m: M[A]): A }

val container = new Container[List] { def put[A](x: A) = List(x); def get[A](m: List[A]) = m.head }

container.put("hey")

implicit val listContainer = new Container[List] { def put[A](x: A) = List(x); def get[A](m: List[A]) = m.head }

def tupleize[M[_]: Container, A, B](fst: M[A], snd: M[B]) = {
  val c = implicitly[Container[M]]
  c.put(c.get(fst), c.get(snd))
}

```

##F-bounded polymorphism

```
trait Container[A <: Container[A]] extends Ordered[A]

class MyContainer extends Container[MyContainer] {
  def compare(that: MyContainer) = 0
}

List(new MyContainer, new MyContainer, new MyContainer).min

class YourContainer extends Container[YourContainer] { def compare(that: YourContainer) = 0 }

List(new MyContainer, new MyContainer, new MyContainer, new YourContainer)
```

##Structural types

```
def foo(x: { def get: Int }) = 123 + x.get

foo(new { def get = 10 })
```

##Abstract type members

```
trait Foo { type A; val x: A; def getX: A = x }

(new Foo { type A = Int; val x = 123 }).getX

(new Foo { type A = String; val x = "hey" }).getX

trait Foo[M[_]] { type t[A] = M[A] }

val x: Foo[List]#t[Int] = List(1)
```

##Type erasures & manifests

```
class MakeFoo[A](implicit manifest: Manifest[A]) { def make: A = manifest.erasure.newInstance.asInstanceOf[A] }

(new MakeFoo[String]).make
```

##Case study: Finagle
