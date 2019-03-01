package scalaz

package schema

import recursion._

import monocle.Iso

trait Realisation {
  type Prim[A]
  type SumTermId
  type ProductTermId
}

sealed trait SchemaF[Prim[_], SumTermId, ProductTermId, F[_], A] { //self =>
  def hmap[G[_]](nt: F ~> G): SchemaF[Prim, SumTermId, ProductTermId, G, A]
  //    def imap[B](iso: Iso[A, B]): Schema.FSchema[B] = Schema.IsoSchema(self, iso)

  def fold[S[_]](f: SchemaF.Algebra[Prim, SumTermId, ProductTermId, F, S]): S[A]
}

////////////////////
// The Schema ADT
////////////////////

// "Essential" nodes. In theory every possible type can be represented using only `One`, `:+:` and `:*:`

final case class One[Prim[_], SumTermId, ProductTermId, F[_]]()
    extends SchemaF[Prim, SumTermId, ProductTermId, F, Unit] {
  def hmap[G[_]](nt: F ~> G): SchemaF[Prim, SumTermId, ProductTermId, G, Unit] = One()

  @inline def fold[S[_]](f: SchemaF.Algebra[Prim, SumTermId, ProductTermId, F, S]): S[Unit] =
    f.one
}

/**
 * The sum of two schemas, yielding the schema for `A \/ B`
 */
final case class :+:[Prim[_], SumTermId, ProductTermId, F[_], A, B](left: F[A], right: F[B])
    extends SchemaF[Prim, SumTermId, ProductTermId, F, A \/ B] {

  def hmap[G[_]](nt: F ~> G): SchemaF[Prim, SumTermId, ProductTermId, G, A \/ B] =
    :+:(nt(left), nt(right))
  override def toString: String = s"$left :+: $right"

  @inline def fold[S[_]](
    f: SchemaF.Algebra[Prim, SumTermId, ProductTermId, F, S]
  ): S[A \/ B] =
    f.disjunction[A, B](left, right)
}

/**
 * The product of two schemas, yielding the schema for `(A, B)`
 */
final case class :*:[F[_], A, B, Prim[_], SumTermId, ProductTermId](left: F[A], right: F[B])
    extends SchemaF[Prim, SumTermId, ProductTermId, F, (A, B)] {

  def hmap[G[_]](nt: F ~> G): SchemaF[Prim, SumTermId, ProductTermId, G, (A, B)] =
    :*:(nt(left), nt(right))
  override def toString: String = s"$left :*: $right"

  @inline def fold[S[_]](
    f: SchemaF.Algebra[Prim, SumTermId, ProductTermId, F, S]
  ): S[(A, B)] =
    f.conjunction[A, B](left, right)
}

// "Extra" nodes, making it more convenient to represent real-world types

/**
 * The schema of a primitive type in the context of this `SchemaModule`
 */
final case class PrimSchema[F[_], A, Prim[_], SumTermId, ProductTermId](prim: Prim[A])
    extends SchemaF[Prim, SumTermId, ProductTermId, F, A] {

  def hmap[G[_]](nt: F ~> G): SchemaF[Prim, SumTermId, ProductTermId, G, A] =
    PrimSchema[G, A, Prim, SumTermId, ProductTermId](prim)

  @inline def fold[S[_]](f: SchemaF.Algebra[Prim, SumTermId, ProductTermId, F, S]): S[A] =
    f.prim[A](prim)
}

/**
 * A named branch of an union
 */
final case class SumTerm[F[_], A, Prim[_], SumTermId, ProductTermId](id: SumTermId, schema: F[A])
    extends SchemaF[Prim, SumTermId, ProductTermId, F, A] {

  def hmap[G[_]](nt: F ~> G): SchemaF[Prim, SumTermId, ProductTermId, G, A] =
    SumTerm(id, nt(schema))

  @inline def fold[S[_]](f: SchemaF.Algebra[Prim, SumTermId, ProductTermId, F, S]): S[A] =
    f.sumTerm[A](id, schema)
}

/**
 * An union, eg. a sum of named branches
 * This class cannot be constructed directly, you must use the `SchemaModule#union` method.
 */
final case class Union[Prim[_], SumTermId, ProductTermId, F[_], A, AE](
  choices: SchemaF.LabelledTree[\/, SumTermId, F, AE],
  iso: Iso[AE, A]
) extends SchemaF[Prim, SumTermId, ProductTermId, F, A] {

  def hmap[G[_]](nt: F ~> G): SchemaF[Prim, SumTermId, ProductTermId, G, A] = {
    val nt2 =
      LabelTree
        .labelTreeFunctor[\/]
        .andThen[λ[(F[_], X) => (SumTermId, F[X])]](SchemaF.labelledNT[SumTermId])
        .hmap(nt)
    Union[Prim, SumTermId, ProductTermId, G, A, AE](nt2(choices), iso)
  }

  def fold[S[_]](f: SchemaF.Algebra[Prim, SumTermId, ProductTermId, F, S]): S[A] =
    f.union(choices, iso)
}

/**
 * A named field of a record
 */
final case class ProductTerm[F[_], A, Prim[_], SumTermId, ProductTermId](
  id: ProductTermId,
  schema: F[A]
) extends SchemaF[Prim, SumTermId, ProductTermId, F, A] {

  def hmap[G[_]](nt: F ~> G): SchemaF[Prim, SumTermId, ProductTermId, G, A] =
    ProductTerm(id, nt(schema))

  @inline def fold[S[_]](f: SchemaF.Algebra[Prim, SumTermId, ProductTermId, F, S]): S[A] =
    f.productTerm[A](id, schema)
}

/**
 * A record, eg. a product of named fields
 * This class cannot be constructed directly, you must use the `SchemaModule#record` method.
 */
final case class Record[Prim[_], SumTermId, ProductTermId, F[_], A, AP](
  fields: SchemaF.LabelledTree[Tuple2, ProductTermId, F, AP],
  iso: Iso[AP, A]
) extends SchemaF[Prim, SumTermId, ProductTermId, F, A] {

  def hmap[G[_]](nt: F ~> G): SchemaF[Prim, SumTermId, ProductTermId, G, A] = {
    val nt2 =
      LabelTree
        .labelTreeFunctor[Tuple2]
        .andThen[λ[(F[_], X) => (ProductTermId, F[X])]](SchemaF.labelledNT[ProductTermId])
        .hmap(nt)
    Record[Prim, SumTermId, ProductTermId, G, A, AP](nt2(fields), iso)
  }

  def fold[S[_]](f: SchemaF.Algebra[Prim, SumTermId, ProductTermId, F, S]): S[A] =
    f.record(fields, iso)
}

/**
 * A sequence
 */
final case class SeqSchema[F[_], A, Prim[_], SumTermId, ProductTermId](element: F[A])
    extends SchemaF[Prim, SumTermId, ProductTermId, F, List[A]] {

  def hmap[G[_]](nt: F ~> G): SchemaF[Prim, SumTermId, ProductTermId, G, List[A]] =
    SeqSchema(nt(element))

  @inline def fold[S[_]](
    f: SchemaF.Algebra[Prim, SumTermId, ProductTermId, F, S]
  ): S[List[A]] =
    f.seqSchema[A](element)
}

/**
 * The schema obtained by "mapping" an Iso of top of a schema. If there is an isomorphism
 * between AO and A, then a schema of A0 can be used to represent values of A.
 */
final case class IsoSchema[Prim[_], SumTermId, ProductTermId, F[_], A0, A](
  base: F[A0],
  iso: Iso[A0, A]
) extends SchemaF[Prim, SumTermId, ProductTermId, F, A] {

  def hmap[G[_]](nt: F ~> G): SchemaF[Prim, SumTermId, ProductTermId, G, A] =
    IsoSchema(nt(base), iso)

  @inline def fold[S[_]](f: SchemaF.Algebra[Prim, SumTermId, ProductTermId, F, S]): S[A] =
    f.isoSchema[A0, A](base, iso)
}

/**
 * An interpreter able to derive a `F[A]` from a schema for `A` (for any `A`).
 * Such interpreters will usually be implemented using a recursion scheme like
 * 'cataNT`or hyloNT`.
 */
trait Interpreter[F[_], G[_]] { self =>

  /**
   * A natural transformation that will transform a schema for any type `A`
   * into an `F[A]`.
   */
  def interpret: F ~> G

  def compose[H[_]](nt: H ~> F) = self match {
    case i: ComposedInterpreter[h, G, F] => ComposedInterpreter(i.underlying, i.nt.compose(nt))
    case x                               => ComposedInterpreter(x, nt)
  }
}

final case class ComposedInterpreter[F[_], G[_], H[_]](underlying: Interpreter[F, G], nt: H ~> F)
    extends Interpreter[H, G] {
  final override val interpret = underlying.interpret.compose(nt)
}

class CataInterpreter[S[_[_], _], F[_]](
  algebra: HAlgebra[S, F]
)(implicit ev: HFunctor[S])
    extends Interpreter[Fix[S, ?], F] {
  final override val interpret = cataNT(algebra)
}

class HyloInterpreter[S[_[_], _], F[_], G[_]](
  coalgebra: HCoalgebra[S, G],
  algebra: HAlgebra[S, F]
)(implicit ev: HFunctor[S])
    extends Interpreter[G, F] {
  final override val interpret = hyloNT(coalgebra, algebra)
}

sealed abstract class LabelTree[D[_, _], F[_], A] {
  def fold[G[_]](leaf: F ~> G, node: LabelTree.ElimNode[D, G]): G[A]
}

object LabelTree {
  final case class Leaf[D[_, _], F[_], A](value: F[A]) extends LabelTree[D, F, A] {
    def fold[G[_]](leaf: F ~> G, node: LabelTree.ElimNode[D, G]): G[A] = leaf(value)

    @inline final def map2[G[_]](nt: F ~> G): LabelTree[D, G, A] =
      labelTreeFunctor[D].hmap(nt)(this)
  }
  final case class Node[D[_, _], F[_], A, B](
    left: LabelTree[D, F, A],
    right: LabelTree[D, F, B]
  ) extends LabelTree[D, F, D[A, B]] {

    def fold[G[_]](leaf: F ~> G, node: LabelTree.ElimNode[D, G]): G[D[A, B]] = {
      val l: G[A] = left.fold[G](leaf, node)
      val r: G[B] = right.fold[G](leaf, node)
      node[A, B](l, r)
    }
  }

  trait ElimNode[D[_, _], G[_]] {
    def apply[A, B](left: G[A], right: G[B]): G[D[A, B]]
  }

  @inline def leaf[D[_, _], F[_]]: F ~> LabelTree[D, F, ?] =
    new (F ~> LabelTree[D, F, ?]) {
      def apply[A](fa: F[A]): LabelTree[D, F, A] = Leaf(fa)
    }

  implicit def labelTreeFunctor[D[_, _]] = new HFunctor[LabelTree[D, ?[_], ?]] {

    def hmap[F[_], G[_]](nt: F ~> G) = new (LabelTree[D, F, ?] ~> LabelTree[D, G, ?]) {

      def apply[A](fa: LabelTree[D, F, A]): LabelTree[D, G, A] =
        fa match {
          case Leaf(fa) => Leaf(nt(fa))
          case n: Node[d, f, a, b] =>
            Node[d, G, a, b](apply[a](n.left), apply[b](n.right))
        }
    }
  }
}

trait Alter[F[_]] {
  def apply[A, B](fa: F[A], fb: F[B]): F[A \/ B]
}

object SchemaF {

  @inline def fold[Prim[_], SumTermId, ProductTermId, F[_], S[_]](
    f: SchemaF.Algebra[Prim, SumTermId, ProductTermId, F, S]
  ): SchemaF[Prim, SumTermId, ProductTermId, F, ?] ~> S =
    new (SchemaF[Prim, SumTermId, ProductTermId, F, ?] ~> S) {

      def apply[A](fa: SchemaF[Prim, SumTermId, ProductTermId, F, A]): S[A] =
        fa.fold[S](f)
    }

  type LabelledTree[D[_, _], TermId, F[_], A] = LabelTree[D, λ[X => (TermId, F[X])], A]

  implicit def labelledNT[TermId] = new HFunctor[λ[(F[_], X) => (TermId, F[X])]] {

    def hmap[F[_], G[_]](nt: F ~> G) = new (λ[X => (TermId, F[X])] ~> λ[X => (TermId, G[X])]) {

      def apply[A](fa: (TermId, F[A])): (TermId, G[A]) =
        (fa._1, nt(fa._2))
    }
  }

  def labelledLeaf[D[_, _], TermId, F[_], A](
    id: TermId,
    schema: F[A]
  ): LabelledTree[D, TermId, F, A] =
    LabelTree.Leaf[D, λ[X => (TermId, F[X])], A]((id, schema))

  trait Algebra[Prim[_], SumTermId, ProductTermId, F[_], S[_]] {
    def one: S[Unit]
    def prim[A](prim: Prim[A]): S[A]
    def disjunction[A, B](left: F[A], right: F[B]): S[A \/ B]
    def conjunction[A, B](left: F[A], right: F[B]): S[(A, B)]
    def sumTerm[A](id: SumTermId, fa: F[A]): S[A]
    def productTerm[A](id: ProductTermId, fa: F[A]): S[A]
    def seqSchema[A](elements: F[A]): S[List[A]]
    def isoSchema[AO, A](choices: F[AO], iso: Iso[AO, A]): S[A]
    def union[AE, A](choices: LabelledTree[\/, SumTermId, F, AE], iso: Iso[AE, A]): S[A]
    def record[AE, A](choices: LabelledTree[Tuple2, ProductTermId, F, AE], iso: Iso[AE, A]): S[A]
  }

  implicit def schemaHFunctor[Prim[_], SumTermId, ProductTermId] =
    new HFunctor[SchemaF[Prim, SumTermId, ProductTermId, ?[_], ?]] {

      def hmap[F[_], G[_]](nt: F ~> G) =
        new (SchemaF[Prim, SumTermId, ProductTermId, F, ?] ~> SchemaF[
          Prim,
          SumTermId,
          ProductTermId,
          G,
          ?
        ]) {
          def apply[A](fa: SchemaF[Prim, SumTermId, ProductTermId, F, A]) = fa.hmap(nt)
        }
    }

  type FSchema[Prim[_], SumTermId, ProductTermId, A] =
    Fix[SchemaF[Prim, SumTermId, ProductTermId, ?[_], ?], A]
}

trait SchemaModule[R <: Realisation] {

  val R: R

  import SchemaF._

  type RInterpreter[F[_]] = Interpreter[Schema, F]

  type RSchema[F[_], A] = SchemaF[R.Prim, R.SumTermId, R.ProductTermId, F, A]

  type Schema[A] = FSchema[R.Prim, R.SumTermId, R.ProductTermId, A]

  type LabelledSum[A]     = LabelTree[\/, λ[X => (R.SumTermId, Schema[X])], A]
  type LabelledProduct[A] = LabelTree[Tuple2, λ[X => (R.ProductTermId, Schema[X])], A]

  type ROne[F[_]]            = One[R.Prim, R.SumTermId, R.ProductTermId, F]
  type RSum[F[_], A, B]      = :+:[R.Prim, R.SumTermId, R.ProductTermId, F, A, B]
  type RProduct[F[_], A, B]  = :*:[F, A, B, R.Prim, R.SumTermId, R.ProductTermId]
  type RSumTerm[F[_], A]     = SumTerm[F, A, R.Prim, R.SumTermId, R.ProductTermId]
  type RUnion[F[_], AE, A]   = Union[R.Prim, R.SumTermId, R.ProductTermId, F, A, AE]
  type RProductTerm[F[_], A] = ProductTerm[F, A, R.Prim, R.SumTermId, R.ProductTermId]
  type RRecord[F[_], An, A]  = Record[R.Prim, R.SumTermId, R.ProductTermId, F, A, An]
  type RSeq[F[_], A]         = SeqSchema[F, A, R.Prim, R.SumTermId, R.ProductTermId]
  type RIso[F[_], A, B]      = IsoSchema[R.Prim, R.SumTermId, R.ProductTermId, F, A, B]

  object Interpreter {

    def cata[S[_[_], _], F[_]](alg: HAlgebra[S, F])(implicit ev: HFunctor[S]) =
      new CataInterpreter[S, F](alg)

    def hylo[S[_[_], _], F[_], G[_]](coalg: HCoalgebra[S, G], alg: HAlgebra[S, F])(
      implicit ev: HFunctor[S]
    ) = new HyloInterpreter(coalg, alg)

  }

  ////////////////
  // Public API
  ////////////////

  implicit final class SchemaSyntax[A](schema: Schema[A]) {

    def :*: [B](left: Schema[B]): Schema[(B, A)] = Fix(new :*:(left, schema))

    def :+: [B](left: Schema[B]): Schema[B \/ A] = Fix(new :+:(left, schema))

    def -*>: (id: R.ProductTermId): LabelledProduct[A] =
      labelledLeaf[Tuple2, R.ProductTermId, Schema, A](id, schema)

    def -+>: (id: R.SumTermId): LabelledSum[A] =
      labelledLeaf[\/, R.SumTermId, Schema, A](id, schema)

    def to[F[_]](implicit interpreter: RInterpreter[F]): F[A] = interpreter.interpret(schema)

    def imap[B](_iso: Iso[A, B]): Schema[B] = schema.unFix match {
      case IsoSchema(base, iso) => Fix(IsoSchema(base, iso.composeIso(_iso)))
      case _                    => Fix(IsoSchema(schema, _iso))
    }

  }

  final def unit: Schema[Unit] =
    Fix(
      One[R.Prim, R.SumTermId, R.ProductTermId, FSchema[R.Prim, R.SumTermId, R.ProductTermId, ?]]()
    )

  final def prim[A](prim: R.Prim[A]): Schema[A] =
    Fix(PrimSchema(prim))

  final def union[A, AE](choices: LabelledSum[AE], iso: Iso[AE, A]): Schema[A] =
    Fix(
      Union[
        R.Prim,
        R.SumTermId,
        R.ProductTermId,
        FSchema[R.Prim, R.SumTermId, R.ProductTermId, ?],
        A,
        AE
      ](choices, iso)
    )

  final def optional[A](aSchema: Schema[A]): Schema[Option[A]] =
    iso(
      Fix(
        new :+:[
          R.Prim,
          R.SumTermId,
          R.ProductTermId,
          FSchema[R.Prim, R.SumTermId, R.ProductTermId, ?],
          A,
          Unit
        ](aSchema, unit)
      ),
      Iso[A \/ Unit, Option[A]](_.swap.toOption)(_.fold[A \/ Unit](\/-(()))(-\/(_)))
    )

  final def record[A, An](terms: LabelledProduct[An], isoA: Iso[An, A]): Schema[A] =
    Fix(
      Record[
        R.Prim,
        R.SumTermId,
        R.ProductTermId,
        FSchema[R.Prim, R.SumTermId, R.ProductTermId, ?],
        A,
        An
      ](terms, isoA)
    )

  final def seq[A](element: Schema[A]): Schema[List[A]] =
    Fix(SeqSchema(element))

  final def iso[A0, A](base: Schema[A0], iso: Iso[A0, A]): Schema[A] =
    Fix(IsoSchema(base, iso))
}
