package org.scalacheck

import cats.{Defer, Eq, Monad}
import cats.data._
import cats.laws.discipline.MonadTests
import cats.mtl.laws.discipline.MonadStateTests
import cats.tests.CatsSuite
import coop.rchain.models.Expr.ExprInstance.{EVarBody, GBool, GInt, GString}
import coop.rchain.models.Var.VarInstance.{BoundVar, FreeVar}
import coop.rchain.models._
import coop.rchain.models.rholang.implicits._
import coop.rchain.rholang.interpreter.PrettyPrinter
import org.scalacheck.rng.Seed
import org.scalatest.prop.PropertyChecks
import org.scalatest.{FlatSpec, Matchers}
import cats.implicits._

import scala.annotation.tailrec
import scala.util.{Failure, Random, Success, Try}

class SubSpec extends FlatSpec with Matchers with PropertyChecks {

  behavior of "StateGen"

  sealed trait Exp
  case class Lit(v: Int)                  extends Exp
  case class Add(l: Exp, r: Exp)          extends Exp
  case class Let(n: Char, v: Exp, r: Exp) extends Exp
  case class Ref(n: Char)                 extends Exp

  implicit def arbString: Arbitrary[Char] = Arbitrary(Gen.alphaChar)
  implicit def arbInt: Arbitrary[Int]     = Arbitrary(Gen.chooseNum(-5, 5))

  def print(e: Exp): String = e match {
    case Lit(v)       => v.toString
    case Add(l, r)    => s"(${print(l)} + ${print(r)})"
    case Let(n, v, r) => s"let\n  $n = ${print(v)} in ${print(r)})"
    case Ref(n)       => s"$n"
  }

  def print(e: New): String = PrettyPrinter().buildString(e)

  import GenInstances._

  type BindCount     = Int
  type Size          = Int
  type Env           = (BindCount, Size)
  type EnvT[F[_], A] = ReaderT[F, Env, A]
  type ArbEnv[A]     = ArbF[EnvT, A]

  object ArbEnv extends GenericArb[EnvT] {
    override def defer                                          = Defer[EnvT[Gen, ?]]
    override def monad                                          = Monad[EnvT[Gen, ?]]
    override def liftF[A](gen: Gen[A]): EnvT[Gen, A]            = ReaderT.liftF(gen)
  }

  case class Shape(breadth: Int, depths: List[Size]) {
    assert(breadth == depths.length)
  }

  def split[T](list: List[T], chunks: Int): List[List[T]] = {
    @tailrec
    def split(list: List[T], chunks: Int, size: Int, result: List[List[T]]): List[List[T]] =
      if (chunks == 0) result
      else if (chunks == 1) list +: result
      else {
        val avg = size / chunks
        val rand = (1.0 + Random.nextGaussian / 3) * avg
        val index = (rand.toInt max 1) min (size - chunks)
        val (h, t) = list splitAt index
        split(t, chunks - 1, size - index, h +: result)
      }
    split(list, chunks, list.size, Nil).reverse
  }

  def genShape(size: Size): EnvT[Gen, Shape] = ArbEnv.liftF(
    for {
      breadth <- Gen.chooseNum(1, size)
      leftover = size - breadth
      depths = split(List.fill(leftover)(1), breadth).map(_.sum)
    } yield Shape(breadth, depths)
  )

  def emptyListOf[T]: EnvT[Gen, List[T]] = ArbEnv.liftF(Gen.const(List[T]()))

  def genName(bindCount: BindCount): EnvT[Gen, Int] = ArbEnv.liftF(Gen.chooseNum(0, bindCount - 1))

  // Currently just creates a pattern with just one free var but could be used to create a pattern specific to a name
  def genPattern(name: BindCount): EnvT[Gen, Par] = ArbEnv.liftF(Gen.const(EVar(FreeVar(0))))

  implicit val arbFExpr: ArbF[EnvT, Expr] = ArbF[EnvT, Expr]{
    val genInt: Gen[GInt] = Gen.chooseNum(-5, 5).map(i => GInt(i.toLong))
    val genBool: Gen[GBool] = Gen.oneOf(GBool(true), GBool(false))
    val genString: Gen[GString] = Arbitrary.arbString.arbitrary.map(GString)
    ArbEnv.liftF(
      Gen.oneOf(
        genInt.map(Expr(_)),
        genString.map(Expr(_)),
        genBool.map(Expr(_))
      )
    )
  }

  implicit val arbFSend: ArbF[EnvT, Send] = ArbF[EnvT, Send](
    for {
      env               <- ReaderT.ask[Gen, Env]
      (bindCount, size) = env

      name <- genName(bindCount)
      expr <- ArbF.arbF[EnvT, Expr]
    } yield Send(chan = EVar(BoundVar(name)), data = List(expr))
  )

  implicit val arbFReceiveBind: ArbF[EnvT, ReceiveBind] = ArbF[EnvT, ReceiveBind](
    for {
      env               <- ReaderT.ask[Gen, Env]
      (bindCount, size) = env

      name <- genName(bindCount)
      pattern <- genPattern(name)
    } yield ReceiveBind(patterns = Seq(pattern), source = EVar(BoundVar(name)), freeCount = 1)
  )

  implicit val arbFReceive: ArbF[EnvT, Receive] = ArbF[EnvT, Receive](
    for {
      env       <- ReaderT.ask[Gen, Env]
      (bindCount, size) = env

      bind <- ArbF.arbF[EnvT, ReceiveBind]
      body <- ReaderT.local{env: Env => (env._1, env._2 - 1)}(ArbF.arbF[EnvT, Par])
    } yield Receive(binds = Seq(bind), body = body)
  )

  implicit val arbFPar: ArbF[EnvT, Par] = ArbF[EnvT, Par](
    for {
      env               <- ReaderT.ask[Gen, Env]
      (bindCount, size) = env

      par <- if (size > 0) {
        for {
          nReceives <- ArbEnv.liftF(Gen.chooseNum(0, size))
          nSends    = size - nReceives

          receives <- if (nReceives > 0) {
            for {
              shape <- genShape(nReceives)
              r <- shape.depths.map(d => ReaderT.local{env: Env => (env._1, d)}(ArbF.arbF[EnvT, Receive])).sequence
            } yield r
          } else emptyListOf[Receive]

          sends <- if (nSends > 0) {
            for {
              shape <- genShape(nSends)
              s <- shape.depths.map(d => ReaderT.local{env: Env => (env._1, d)}(ArbF.arbF[EnvT, Send])).sequence
            } yield s
          } else emptyListOf[Send]

        } yield Par(sends = sends, receives = receives)
      } else {
        ArbEnv.liftF(Gen.const(Par()))
      }

    } yield par
  )

  implicit val arbFNew: ArbF[EnvT, New] = ArbF[EnvT, New](
    for {
      env            <- ReaderT.ask[Gen, Env]
      (bindCount, _) = env
      par            <- ArbF.arbF[EnvT, Par]
    } yield New(bindCount = bindCount, p = par)
  )

  /*
  object Exp extends ExpLowPrio {

    implicit val arbFRef = {
      ArbF[EnvT, Ref](Defer[EnvT[Gen, ?]].defer {
        for {
          ns <- ReaderT.ask[Gen, Env]
          n  <- ArbEnv.liftF(if (ns.isEmpty) Gen.fail else Gen.oneOf(ns))
        } yield Ref(n)
      })
    }

    implicit val arbFLet = {
      ArbF[EnvT, Let](Defer[EnvT[Gen, ?]].defer {
        for {
          n <- ArbEnv.liftF(arbString.arbitrary)
          v <- ArbF.arbF[EnvT, Exp]
          r <- ReaderT.local { ns: Env =>
                n :: ns
              }(ArbF.arbF[EnvT, Exp])
        } yield Let(n, v, r)
      })
    }

  }

  trait ExpLowPrio {
    import ArbEnv._
    implicit val arbFExp: ArbEnv[Exp] = ArbEnv.gen[Exp]
  }

  import Exp._
  */

  case class ValidExp(e: New)

  implicit def validExp(implicit ev: ArbEnv[New]): Arbitrary[ValidExp] =
    Arbitrary(
      ev.arb.run((5,2)).map(ValidExp)
    )

  implicit override val generatorDrivenConfig: PropertyCheckConfiguration =
    PropertyCheckConfiguration(sizeRange = 200, minSize = 50, minSuccessful = 1000)

  it should "work" in {

    forAll { v: ValidExp =>
      println(print(v.e))
      println("=============")
    }

  }

}

object EqInstances {
  def sampledCogenEq[A](trials: Int)(implicit ev: Arbitrary[A]): Eq[Cogen[A]] =
    new Eq[Cogen[A]] {
      def eqv(x: Cogen[A], y: Cogen[A]): Boolean = {
        val gen: Gen[A]            = ev.arbitrary
        val params: Gen.Parameters = Gen.Parameters.default
        // Loop Function which checks that the seeds from perturbing
        // given cogens create equivalent seeds for x iterations
        // to consider them equal
        def loop(count: Int, retries: Int, seed: Seed): Boolean =
          if (retries <= 0) sys.error("Generator Function Failed")
          else if (count <= 0) true // If make it through count all equal these are equal
          else {
            val rx = gen.doApply(params, seed) // Get Value
            rx.retrieve.fold(
              loop(count, retries - 1, rx.seed) // Loop As Necessary
            ) { a =>
              val seed = Seed.random
              val sx   = x.perturb(seed, a)
              val sy   = y.perturb(seed, a)
              if (sx != sy) false // If they are not equivalent
              else loop(count - 1, retries, rx.seed) // Another trial
            }
          }
        // Initiate Loop
        loop(trials, trials, Seed.random)
      }
    }
  def sampledGenEq[A: Eq](trials: Int): Eq[Gen[A]] = Eq.instance[Gen[A]] {
    case (x, y) =>
      val params = Gen.Parameters.default
      def loop(count: Int, seed: Seed): Boolean =
        if (count <= 0) true
        else {
          // Leave this so the inequality creates the eq
          val tx = Try(x.doApply(params, seed))
          val ty = Try(y.doApply(params, seed))
          (tx, ty) match {
            case (Failure(_), Failure(_)) =>
              // They both failed, good, keep going
              loop(count - 1, Seed.random)
            case (Success(rx), Success(ry)) =>
              if (rx.retrieve != ry.retrieve) false
              else loop(count - 1, seed.next)
            case _ =>
              false
          }
        }
      loop(trials, Seed.random)
  }

}

trait ScalaCheckSetup {
//
  implicit def genEq[A: Eq]: Eq[Gen[A]] =
    EqInstances.sampledGenEq(1000)

  implicit def cogenEq[A: Arbitrary]: Eq[Cogen[A]] =
    EqInstances.sampledCogenEq(1000)

  implicit lazy val arbitrarySeed: Arbitrary[Seed] =
    Arbitrary(Gen.choose(Long.MinValue, Long.MaxValue).map(n => Seed(n)))

  implicit lazy val cogenSeed: Cogen[Seed] =
    Cogen[Long].contramap(_.long._1)

//  implicit def arbitraryNonEmptyList[A: Arbitrary]: Arbitrary[NonEmptyList[A]] =
//    Arbitrary(
//      (Arbitrary.arbitrary[A], Arbitrary.arbitrary[List[A]]).mapN(NonEmptyList(_, _))
//    )

  // Better Arbitrary Gen
  implicit def arbitraryGen[A: Arbitrary]: Arbitrary[Gen[A]] = {
    val simple = Gen.const(Arbitrary.arbitrary[A])
    val complex = Arbitrary.arbitrary[Seed => Seed].map { f =>
      Gen.gen((params, seed) => Arbitrary.arbitrary[A].doApply(params, f(seed)))
    }
    Arbitrary(Gen.oneOf(simple, complex))
  }
  //
  //  implicit def arbitraryCogen[A: Cogen]: Arbitrary[Cogen[A]] =
  //    Arbitrary(Arbitrary.arbitrary[Seed => Seed].map { f =>
  //      Cogen((seed, a) => f(Cogen[A].perturb(seed, a)))
  //    })
}

class GenLaws extends CatsSuite with ScalaCheckSetup {
  import GenInstances._

  type SGen[A] = StateT[Gen, Int, A]

  implicit def arbFAStaetT[A: Arbitrary]: Arbitrary[SGen[A]] =
    Arbitrary[SGen[A]](
      Arbitrary
        .arbitrary[A]
        .flatMap(
          a =>
            Gen.oneOf[SGen[A]](
              StateT.get[Gen, Int].as(a),
              StateT.modify[Gen, Int](_ + 1).as(a),
              StateT.modify[Gen, Int](_ - 1).as(a),
              StateT.modify[Gen, Int](_ * -1).as(a)
          )))

  implicit def eqFA[A: Eq]: Eq[SGen[A]] =
//    implicit def eqGenA: Eq[Gen[A]] = EqInstances.sampledGenEq(1000)
    Eq.by(_.run(0))

  // Tests Alternative
//  checkAll("Gen", AlternativeTests[Gen].alternative[Int, Int, Int])
  // Tests Monad
  checkAll("Gen", MonadTests[Gen].monad[Int, Int, Int])
  checkAll("Monad StateT Gen", MonadTests[SGen].monad[Int, Int, Int])

  import cats.mtl.implicits._

  checkAll("MonadStaete", MonadStateTests[SGen, Int].monadState[Int])

  // Tests FunctorFilter
  //  checkAll("Gen.FunctorFilterLaws", FunctorFilterTests[Gen].functorFilter[Int, Int, Int])
  //
  //  // Tests Monoid for Inner Given Monoid
  //  checkAll("Gen[String]", MonoidTests[Gen[String]].monoid)
  //  // Tests Low Priority Semigroup
  //  checkAll("Gen[NonEmptyList[Int]]", SemigroupTests[Gen[NonEmptyList[Int]]].semigroup)
}

object GenInstances {
  implicit val genInstances: Monad[Gen] with Defer[Gen] = new Monad[Gen] with Defer[Gen] {
    // Members declared in cats.Applicative
    override def pure[A](x: A): Gen[A] =
      Gen.const(x)

    // Members declared in cats.FlatMap
    override def flatMap[A, B](fa: Gen[A])(f: A => Gen[B]): Gen[B] =
      fa.flatMap(f)
    override def tailRecM[A, B](a: A)(f: A => Gen[Either[A, B]]): Gen[B] =
      GenShims.tailRecM(a)(f)

    override def defer[A](fa: => Gen[A]): Gen[A] = {
      import org.scalacheck.derive.GenExtra._
      Gen.delay(fa).failOnStackOverflow
    }
  }

}

object GenShims {

  type P = Gen.Parameters

  import Gen.{gen, r, R}

  def tailRecM[A, B](a0: A)(fn: A => Gen[Either[A, B]]): Gen[B] = {

    @tailrec
    def tailRecMR(a: A, seed: Seed, labs: Set[String])(fn: (A, Seed) => R[Either[A, B]]): R[B] = {
      val re       = fn(a, seed)
      val nextLabs = labs | re.labels
      re.retrieve match {
        case None           => r(None, re.seed).copy(l = nextLabs)
        case Some(Right(b)) => r(Some(b), re.seed).copy(l = nextLabs)
        case Some(Left(a))  => tailRecMR(a, re.seed, nextLabs)(fn)
      }
    }

    // This is the "Reader-style" appoach to making a stack-safe loop:
    // we put one outer closure around an explicitly tailrec loop
    gen[B] { (p: P, seed: Seed) =>
      tailRecMR(a0, seed, Set.empty) { (a, seed) =>
        fn(a).doApply(p, seed)
      }
    }
  }
}
