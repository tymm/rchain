package coop.rchain.casper

import coop.rchain.comm.rp.Connect.{ConnectionsCell, RPConfAsk}
import cats.{Applicative, Monad}
import cats.implicits._
import cats.mtl.implicits._
import cats.effect.{Concurrent, Sync}
import com.google.protobuf.ByteString
import coop.rchain.catscontrib.TaskContrib._
import coop.rchain.casper.protocol._
import coop.rchain.casper.util._
import coop.rchain.casper.util.ProtoUtil._
import coop.rchain.casper.util.comm.CommUtil
import coop.rchain.casper.util.rholang._
import coop.rchain.catscontrib._
import coop.rchain.crypto.codec.Base16
import coop.rchain.comm.CommError.ErrorHandler
import coop.rchain.comm.transport.TransportLayer
import coop.rchain.shared._
import coop.rchain.shared.AttemptOps._

import scala.annotation.tailrec
import scala.collection.{immutable, mutable}
import scala.collection.immutable.{HashMap, HashSet}
import cats.effect.concurrent.{Ref, Semaphore}
import coop.rchain.blockstorage.{BlockDagRepresentation, BlockDagStorage, BlockMetadata, BlockStore}
import coop.rchain.casper.EquivocationRecord.SequenceNumber
import coop.rchain.casper.Estimator.Validator
import coop.rchain.casper.util.rholang.RuntimeManager.StateHash
import coop.rchain.catscontrib.ski.kp2
import coop.rchain.rspace.Checkpoint
import monix.execution.Scheduler
import monix.execution.atomic.AtomicAny

import scala.concurrent.SyncVar

trait Casper[F[_], A] {
  def addBlock(
      b: BlockMessage,
      handleDoppelganger: (BlockMessage, Validator) => F[Unit]
  ): F[BlockStatus]
  def contains(b: BlockMessage): F[Boolean]
  def deploy(d: DeployData): F[Either[Throwable, Unit]]
  def estimator(dag: BlockDagRepresentation[F]): F[A]
  def createBlock: F[CreateBlockStatus]
}

trait MultiParentCasper[F[_]] extends Casper[F, IndexedSeq[BlockMessage]] {
  def blockDag: F[BlockDagRepresentation[F]]
  def fetchDependencies: F[Unit]
  // This is the weight of faults that have been accumulated so far.
  // We want the clique oracle to give us a fault tolerance that is greater than
  // this initial fault weight combined with our fault tolerance threshold t.
  def normalizedInitialFault(weights: Map[Validator, Long]): F[Float]
  def lastFinalizedBlock: F[BlockMessage]
  def storageContents(hash: ByteString): F[String]
  // TODO: Refactor hashSetCasper to take a RuntimeManager[F] just like BlockStore[F]
  def getRuntimeManager: F[Option[RuntimeManager]]
}

object MultiParentCasper extends MultiParentCasperInstances {
  def apply[F[_]](implicit instance: MultiParentCasper[F]): MultiParentCasper[F] = instance
  def ignoreDoppelgangerCheck[F[_]: Applicative]: (BlockMessage, Validator) => F[Unit] =
    kp2(().pure[F])

  def forkChoiceTip[F[_]: MultiParentCasper: Monad]: F[BlockMessage] =
    for {
      dag  <- MultiParentCasper[F].blockDag
      tips <- MultiParentCasper[F].estimator(dag)
      tip  = tips.head
    } yield tip
}

sealed abstract class MultiParentCasperInstances {

  def hashSetCasper[F[_]: Sync: Concurrent: Capture: ConnectionsCell: TransportLayer: Log: Time: ErrorHandler: SafetyOracle: BlockStore: RPConfAsk: BlockDagStorage: ToAbstractContext](
      runtimeManager: RuntimeManager,
      validatorId: Option[ValidatorIdentity],
      genesis: BlockMessage,
      shardId: String
  )(implicit scheduler: Scheduler): F[MultiParentCasper[F]] =
    for {
      // Initialize DAG storage with genesis block in case it is empty
      _   <- BlockDagStorage[F].insert(genesis)
      dag <- BlockDagStorage[F].getRepresentation
      maybePostGenesisStateHash <- InterpreterUtil
                                    .validateBlockCheckpoint[F](
                                      genesis,
                                      dag,
                                      runtimeManager
                                    )
      postGenesisStateHash <- maybePostGenesisStateHash match {
                               case Left(BlockException(ex)) => Sync[F].raiseError[StateHash](ex)
                               case Right(None) =>
                                 Sync[F].raiseError[StateHash](
                                   new Exception("Genesis tuplespace validation failed!")
                                 )
                               case Right(Some(hash)) => hash.pure[F]
                             }
      blockProcessingLock <- Semaphore[F](1)
    } yield
      new MultiParentCasperImpl[F](
        runtimeManager,
        validatorId,
        genesis,
        postGenesisStateHash,
        shardId,
        blockProcessingLock
      )
}
