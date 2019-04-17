package org.scalacheck

import java.util.UUID
import java.util.concurrent.TimeoutException

import cats.data._
import cats.implicits._
import cats.laws.discipline.MonadTests
import cats.mtl.laws.discipline.MonadStateTests
import cats.tests.CatsSuite
import cats.{Defer, Eq, FlatMap, Monad}
import coop.rchain.metrics.Metrics
import coop.rchain.models.Expr.ExprInstance.{GBool, GInt, GString}
import coop.rchain.models.Var.VarInstance.{BoundVar, FreeVar, Wildcard}
import coop.rchain.models.Var.WildcardMsg
import coop.rchain.models._
import coop.rchain.models.rholang.implicits._
import coop.rchain.rholang.interpreter.accounting.{Cost, CostAccounting}
import coop.rchain.rholang.interpreter.{Interpreter, PrettyPrinter, Runtime, TestRuntime}
import coop.rchain.shared.Log
import monix.eval.Task
import monix.execution.Scheduler.Implicits.global
import monocle.Iso
import monocle.function.all._
import monocle.macros.GenLens
import org.scalacheck.rng.Seed
import org.scalatest.prop.PropertyChecks
import org.scalatest.{Assertion, FlatSpec, Matchers}

import scala.annotation.tailrec
import scala.concurrent.duration._
import scala.util.{Failure, Random, Success, Try}

class SubSpec extends FlatSpec with Matchers with PropertyChecks {

  behavior of "StateGen"

  def print(e: New): String = PrettyPrinter().buildString(e)

  import GenInstances._

  type NewVarCount    = Int
  type Size           = Int
  type Level          = Int
  type VarRef         = UUID
  type AttributeState = Map[VarRef, Attributes]
  type Scope          = Map[VarRef, Pos]
  type Env            = (NewVarCount, Level, Size, Scope)
  type EnvT[F[_], A]  = ReaderT[StateT[F, AttributeState, ?], Env, A]
  type ArbEnv[A]      = ArbF[EnvT, A]

  case class Attributes(
      readOnly: Boolean = false,
      writeOnly: Boolean = false,
      hasReadOnly: Boolean = false,
      hasWriteOnly: Boolean = false,
      assumeReadable: Boolean = false,
      assumeWritable: Boolean = false,
      isPatternOf: Option[VarRef] = None
  )

  object Attributes {
    def hasReadOnly(varRef: VarRef): EnvT[Gen, Boolean] =
      ArbEnv.getAttributeStore.map(store => store(varRef).hasReadOnly)

    def isAssumeWriteOnly(varRef: VarRef): EnvT[Gen, Boolean] =
      ArbEnv.getAttributeStore.map(store => store(varRef).assumeWritable)

    def setReadOnlyFlag(varRef: VarRef): EnvT[Gen, Unit] =
      ArbEnv.modifyAttributeStore(
        store => store ++ Map(varRef -> store(varRef).copy(readOnly = true))
      )

    def addPattern(pattern: VarRef, source: VarRef): EnvT[Gen, Unit] =
      ArbEnv.modifyAttributeStore(
        store => store ++ Map(pattern -> Attributes(isPatternOf = Some(source)))
      )

    implicit class RichAttributeState(state: Map[VarRef, Attributes]) {
      def setReadOnly(varRef: VarRef): Map[VarRef, Attributes] =
        (Iso
          .id[Map[VarRef, Attributes]] composeOptional index(varRef) composeLens GenLens[
          Attributes
        ](
          _.readOnly
        )).set(true)(state)

      def setHasReadOnly(varRef: VarRef): Map[VarRef, Attributes] =
        (Iso
          .id[Map[VarRef, Attributes]] composeOptional index(varRef) composeLens GenLens[
          Attributes
        ](
          _.hasReadOnly
        )).set(true)(state)
    }
  }

  case class Shape(breadth: Int, depths: List[Size]) {
    assert(breadth == depths.length)
  }

  case class Split(sends: Size, receives: Size, news: Size)

  case class Pos(level: Int, index: Int)

  private def unsafeGetBoundVar(ref: VarRef): EnvT[Gen, BoundVar] =
    for {
      scope <- ArbEnv.askScope
      boundVar <- {
        val refPos = scope(ref)
        val nBiggerPosThanRefPos = scope.count {
          case (_, pos) =>
            pos.level > refPos.level || (pos.level == refPos.level && pos.index > refPos.index)
        }
        ArbEnv.liftF(BoundVar(nBiggerPosThanRefPos))
      }
    } yield boundVar

  object ArbEnv extends GenericArb[EnvT] {
    override def defer = Defer[EnvT[Gen, ?]]
    override def monad = Monad[EnvT[Gen, ?]]
    override def liftF[A](gen: Gen[A]): EnvT[Gen, A] =
      ReaderT.liftF[StateT[Gen, AttributeState, ?], Env, A](
        StateT.liftF[Gen, AttributeState, A](gen)
      )
    def ask: EnvT[Gen, Env] = ReaderT.ask[StateT[Gen, AttributeState, ?], Env]
    def askNewVarCount: EnvT[Gen, NewVarCount] =
      ReaderT.ask[StateT[Gen, AttributeState, ?], Env].map(_._1)
    def askLevel: EnvT[Gen, Level]                   = ReaderT.ask[StateT[Gen, AttributeState, ?], Env].map(_._2)
    def askSize: EnvT[Gen, Size]                     = ReaderT.ask[StateT[Gen, AttributeState, ?], Env].map(_._3)
    def askScope: EnvT[Gen, Scope]                   = ReaderT.ask[StateT[Gen, AttributeState, ?], Env].map(_._4)
    def getAttributeStore: EnvT[Gen, AttributeState] = ReaderT.liftF(StateT.get)
    def modifyAttributeStore(f: AttributeState => AttributeState): EnvT[Gen, Unit] =
      ReaderT.liftF(StateT.modify(f))
    def pure: EnvT[Gen, Unit] =
      ReaderT.liftF[StateT[Gen, AttributeState, ?], Env, Unit](StateT.pure(()))
  }

  val setSize      = (size: Size) => (env: Env) => env.copy(_3 = size)
  val decreaseSize = (env: Env) => env.copy(_3 = env._3 - 1)
  val addFreeVars = (freeCount: Int) =>
    (env: Env) => (env._1 + freeCount, env._2 + freeCount, env._3)
  val setLevel = (level: Level) => (env: Env) => env.copy(_2 = level)
  val setScope = (scope: Scope) => (env: Env) => env.copy(_4 = scope)

  implicit val arbFBundle: ArbF[EnvT, Bundle] = ArbF[EnvT, Bundle](Defer[EnvT[Gen, ?]].defer {
    for {
      name <- genName
      boundVar <- unsafeGetBoundVar(name)
    } yield Bundle(body = EVar(boundVar), readFlag = true)
  })

  implicit val arbFExpr: ArbF[EnvT, Expr] = ArbF[EnvT, Expr](Defer[EnvT[Gen, ?]].defer {
    val genInt: Gen[GInt]       = Gen.chooseNum(-5, 5).map(i => GInt(i.toLong))
    val genBool: Gen[GBool]     = Gen.oneOf(GBool(true), GBool(false))
    val genString: Gen[GString] = Gen.alphaStr.map(GString)
    ArbEnv.liftF(
      Gen
        .oneOf(
          genInt,
          genString,
          genBool
        )
        .map(Expr(_))
    )
  })

  implicit val arbFSend: ArbF[EnvT, Option[Send]] = {
    // Returns the source, if `varRef` is a pattern
    def isPattern(varRef: VarRef): EnvT[Gen, Option[VarRef]] =
      ArbEnv.getAttributeStore.map(store => store(varRef).isPatternOf)

    def setAssumeWritableFlagIfPattern(varRef: VarRef): EnvT[Gen, Unit] =
      for {
        maybeSource <- isPattern(varRef)
        _ <- maybeSource match {
              case Some(source) =>
                ArbEnv.modifyAttributeStore(
                  store => store ++ Map(source -> store(source).copy(assumeWritable = true))
                )
              case None => ArbEnv.pure
            }
      } yield ()

    def genSendChan: EnvT[Gen, Option[VarRef]] = {
      val writableVars: EnvT[Gen, List[VarRef]] =
        for {
          store     <- ArbEnv.getAttributeStore
          allVars   <- ArbEnv.askScope.map(scope => scope.keys.toList)
          readOnly  = allVars.filter(store(_).readOnly)
          remaining = allVars.diff(readOnly)
        } yield remaining

      for {
        // Only send on vars that are not read-only bundles
        vars   <- writableVars
        varRef <- ArbEnv.liftF(if (vars.nonEmpty) Gen.oneOf(vars).map(_.some) else none[VarRef])
      } yield varRef
    }

    def genSendData(chan: VarRef): EnvT[Gen, List[Par]] = {
      // TODO: add write-only bundles
      def flagChannel(
          varRef: VarRef
      ): EnvT[Gen, Unit] = ArbEnv.modifyAttributeStore(_.setHasReadOnly(varRef))
      val exprGen = ArbF.arbF[EnvT, Expr]
      val bundleGen = ArbF.arbF[EnvT, Bundle] <* flagChannel(chan)

      FlatMap[EnvT[Gen, ?]].ifM(Attributes.isAssumeWriteOnly(chan))(
        ifTrue = frequency((1, exprGen.asPar), (0, bundleGen.asPar)),
        ifFalse = frequency((1, exprGen.asPar), (1, bundleGen.asPar))
      ).map(List(_))
    }

    ArbF[EnvT, Option[Send]](Defer[EnvT[Gen, ?]].defer {
      for {
        maybeChan <- genSendChan
        maybeSend <- maybeChan match {
                      case Some(chan) =>
                        for {

                          /**
                            * If `chan` is a pattern, set `assumeWritable` flag for source
                            *
                            * Example:
                            * 0: for(z <- x) {
                            * 1:  z!(Nil)
                            * 2: } |
                            * 3: x!(bundle+{*y})
                            *
                            * On line 1 set `assumeWritable` flag for `x` since `z` must be a name
                            * that can be written on.
                            */
                          _        <- setAssumeWritableFlagIfPattern(chan)
                          data     <- genSendData(chan)
                          boundVar <- unsafeGetBoundVar(chan)
                        } yield Some(Send(chan = EVar(boundVar), data = data))

                      case None => ArbEnv.liftF(none[Send])
                    }
      } yield maybeSend
    })
  }

  implicit val arbFReceive: ArbF[EnvT, Receive] = {
    def genReceiveBind: EnvT[Gen, (ReceiveBind, VarRef)] = {
      for {
        source <- genName
        sourceBoundVar <- unsafeGetBoundVar(source)
        pattern = createVarRef
        _ <- Attributes.addPattern(pattern, source)
        _ <- FlatMap[EnvT[Gen, ?]].ifM(Attributes.hasReadOnly(source))(
          ifTrue = Attributes.setReadOnlyFlag(pattern),
          ifFalse = ArbEnv.pure
        )
      } yield (ReceiveBind(patterns = List(EVar(FreeVar(0))), source = EVar(sourceBoundVar), freeCount = 1), pattern)
    }

    def genBody(patternVar: VarRef): EnvT[Gen, Par] =
      for {
        scope     <- ArbEnv.askScope
        level     <- ArbEnv.askLevel
        levelBody = level + 1
        scopeBody = Map(patternVar -> Pos(level = levelBody, index = 0))
        body <- ReaderT.local(
                 setScope(scope ++ scopeBody) andThen setLevel(levelBody) andThen decreaseSize
               )(ArbF.arbF[EnvT, Par])
      } yield body

    ArbF[EnvT, Receive](Defer[EnvT[Gen, ?]].defer {
      for {
        r            <- genReceiveBind
        (receiveBind, pattern) = r
        body         <- genBody(pattern)
        isPersistent <- ArbEnv.liftF(Gen.oneOf(true, false))
      } yield
        Receive(
          binds = List(receiveBind),
          body = body,
          persistent = isPersistent
        )
    })
  }

  implicit val arbFMatch: ArbF[EnvT, Match] = ArbF[EnvT, Match](Defer[EnvT[Gen, ?]].defer {
    for {
      target <- genName
      targetBoundVar <- unsafeGetBoundVar(target)
      par    <- ReaderT.local(decreaseSize)(ArbF.arbF[EnvT, Par])
      // TODO: Add more match cases
      wildcardCase = MatchCase(pattern = EVar(Wildcard(WildcardMsg())), source = par)
    } yield Match(target = EVar(targetBoundVar), cases = List(wildcardCase))
  })

  implicit val arbFPar: ArbF[EnvT, Par] = ArbF[EnvT, Par](Defer[EnvT[Gen, ?]].defer {
    for {
      size <- ArbEnv.askSize
      par <- if (size > 0) {
              for {
                // Split size between receives, sends and news
                // TODO: Make split consider available readonly names for send
                sizes     <- splitSizeWithScope(size)
                nReceives = sizes.receives
                nSends    = sizes.sends
                nNews     = sizes.news

                scope <- ArbEnv.askScope
                level <- ArbEnv.askLevel
                news  <- ReaderT.local(setLevel(level + 1))(genShaped[New](nNews))
                // TODO: Redistribute size of Nones
                sends    <- genShaped[Option[Send]](nSends)
                receives <- genShaped[Receive](nReceives)
              } yield Par(sends = sends.flatten, receives = receives, news = news)
            } else nil
    } yield par
  })

  /** Generates a `New`
    *
    * Creates `nNewVars` vars which are accessible in the scope of the
    * par that is generated subsequently.
    * The `New` has a `level` which describes at which level it occurs.
    * It also has a `newsIndex` which describes the number of preceding
    * news on its `level`.
    * Creates a new scope.
    */
  implicit val arbFNew: ArbF[EnvT, New] = ArbF[EnvT, New](Defer[EnvT[Gen, ?]].defer {
    def createLocalAttributeStore(varRefs: Seq[VarRef]): AttributeState =
      varRefs.map(ref => ref -> Attributes()).toMap
    def createLocalScope(newVarCount: NewVarCount, level: Level, scope: Scope): Scope =
      (0 until newVarCount).map(i => createVarRef -> Pos(level = level, index = i)).toMap

    for {
      newVarCount <- ArbEnv.askNewVarCount
      level       <- ArbEnv.askLevel
      scope       <- ArbEnv.askScope
      localScope  = createLocalScope(newVarCount, level, scope)
      localStore  = createLocalAttributeStore(localScope.keys.toList)
      _           <- ArbEnv.modifyAttributeStore(store => store ++ localStore)
      par         <- ReaderT.local(setScope(scope ++ localScope))(ArbF.arbF[EnvT, Par])
    } yield New(bindCount = newVarCount, p = par)
  })

  private def createVarRef: VarRef = UUID.randomUUID()

  private def splitSizeWithScope(size: Size): EnvT[Gen, Split] =
    for {
      scope                          <- ArbEnv.askScope
      store                          <- ArbEnv.getAttributeStore
      allNamesHaveReadOnlyProcSentOn = scope.keys.forall(ref => store(ref).readOnly)

      splits <- if (allNamesHaveReadOnlyProcSentOn) splitSize(2, size) else splitSize(3, size)
    } yield {
      if (allNamesHaveReadOnlyProcSentOn) {
        Split(sends = 0, receives = splits.head, news = splits(1))
      } else {
        Split(sends = splits.head, receives = splits(1), news = splits(2))
      }
    }

  private def splitSize(chunks: Int, size: Size): EnvT[Gen, List[Size]] =
    for {
      boundaries <- if (chunks < size)
                     ArbEnv
                       .liftF(Gen.pick(chunks - 1, 0 until size))
                       .map(0 +: _ :+ size)
                       .map(_.sorted)
                   else
                     ArbEnv
                       .liftF(Gen.pick(size - 1, 0 until size))
                       .map(0 +: _ :+ size)
                       .map(_.sorted)
                       .map(List.fill(chunks - size)(0) ++ _)
      sizes = boundaries.sliding(2).map(pair => pair(1) - pair.head)
    } yield Random.shuffle(sizes.toList)

  private def genShaped[T](size: Size)(implicit arbFT: ArbF[EnvT, T]): EnvT[Gen, List[T]] =
    if (size > 0) {
      for {
        shape <- genShape(size)
        listOfT <- shape.depths
                    .map(d => ReaderT.local(setSize(d))(ArbF.arbF[EnvT, T]))
                    .sequence
      } yield listOfT
    } else emptyList[T]

  // Decides how given size is split up between breadth and depth
  private def genShape(size: Size): EnvT[Gen, Shape] = ArbEnv.liftF(
    for {
      breadth  <- Gen.chooseNum(1, size)
      leftover = size - breadth
      depths   = split(List.fill(leftover)(1), breadth).map(_.sum)
    } yield Shape(breadth, depths)
  )

  private def genName: EnvT[Gen, VarRef] =
    for {
      scope  <- ArbEnv.askScope
      varRef <- ArbEnv.liftF(Gen.oneOf(scope.keys.toList))
    } yield varRef

  private def frequency[T](gs: (Int, EnvT[Gen, T])*): EnvT[Gen, T] = {
    def zip(listT: Seq[T], ints: Seq[Int]): List[(Int, Gen[T])] =
      ints.zip(listT.map(t => Gen.const(t))).toList
    val nonZeroGs   = gs.filter { case (i, _) => i > 0 }
    val sequenced   = nonZeroGs.map { case (_, envT) => envT }.toList.sequence
    val frequencies = nonZeroGs.map { case (i, _) => i }
    sequenced.flatMapF(listT => StateT.liftF(Gen.frequency(zip(listT, frequencies): _*)))
  }

  // Taken from: https://stackoverflow.com/questions/40958670/split-a-list-into-a-fixed-number-of-random-sized-sub-lists
  private def split[T](list: List[T], chunks: Int): List[List[T]] = {
    @tailrec
    def split(list: List[T], chunks: Int, size: Int, result: List[List[T]]): List[List[T]] =
      if (chunks == 0) result
      else if (chunks == 1) list +: result
      else {
        val avg    = size / chunks
        val rand   = (1.0 + Random.nextGaussian / 3) * avg
        val index  = (rand.toInt max 1) min (size - chunks)
        val (h, t) = list splitAt index
        split(t, chunks - 1, size - index, h +: result)
      }
    split(list, chunks, list.size, Nil).reverse
  }

  private def nil: EnvT[Gen, Par] = ArbEnv.liftF(Gen.const(Par()))

  private def emptyList[T]: EnvT[Gen, List[T]] = ArbEnv.liftF(Gen.const(List[T]()))

  implicit class RichMatch(val a: EnvT[Gen, Match]) {
    def asPar(): EnvT[Gen, Par] = a.map(m => Par(matches = List(m)))
  }

  implicit class RichExpr(val a: EnvT[Gen, Expr]) {
    def asPar: EnvT[Gen, Par] = a.map(e => Par(exprs = List(e)))
  }

  implicit class RichBundle(val a: EnvT[Gen, Bundle]) {
    def asPar: EnvT[Gen, Par] = a.map(b => Par(bundles = List(b)))
  }

  case class ValidExp(e: New)

  implicit def validExp(implicit ev: ArbEnv[New]): Arbitrary[ValidExp] =
    Arbitrary(
      // Run with 5 names introduced by initial `new` and a size of 10
      // Env = (NewVarCount, Level, Size, Scope)
      ev.arb.run((5, 0, 10, Map())).runA(Map()).map(ValidExp)
    )

  implicit override val generatorDrivenConfig: PropertyCheckConfiguration =
    PropertyCheckConfiguration(sizeRange = 2000, minSize = 50, minSuccessful = 100)
  //PropertyCheckConfiguration(sizeRange = 1, minSize = 1, minSuccessful = 1)

  it should "work" in {

    forAll { v: ValidExp =>
      println(print(v.e))
      println("=============")
    }

  }

  it should "execute without errors" in {
    forAll { v: ValidExp =>
      try {
        println()
        success(print(v.e)).runSyncUnsafe(3.seconds)
      } catch {
        //case e: TimeoutException =>
        //succeed
        case e: Throwable =>
          e match {
            case _: TimeoutException => succeed
            case e: Throwable =>
              println(e)
              println(print(v.e))
              fail
          }
      }
    }
  }

  def success(term: String): Task[Assertion] = {
    implicit val logF: Log[Task]            = new Log.NOPLog[Task]
    implicit val noopMetrics: Metrics[Task] = new Metrics.MetricsNOP[Task]

    for {
      runtime <- TestRuntime.create[Task, Task.Par]()
      _       <- runtime.reducer.setPhlo(Cost.UNSAFE_MAX)
      _       <- Runtime.injectEmptyRegistryRoot[Task](runtime.space, runtime.replaySpace)
      cost    <- CostAccounting.emptyCost[Task]
      res <- {
        implicit val c = cost
        Interpreter[Task].evaluate(runtime, term)
      }
    } yield assert(res.errors.isEmpty)
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
            )
        )
    )

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
