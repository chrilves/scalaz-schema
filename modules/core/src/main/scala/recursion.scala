package scalaz

package schema

package recursion {

  trait HFunctor[H[_[_], _]] { self =>
    def hmap[F[_], G[_]](nt: F ~> G): H[F, ?] ~> H[G, ?]

    @inline final def andThen[K[_[_], _]](K: HFunctor[K]) =
      new HFunctor[λ[(L[_], A) => H[K[L, ?], A]]] {

        def hmap[F[_], G[_]](nt: F ~> G): H[K[F, ?], ?] ~> H[K[G, ?], ?] =
          self.hmap(K.hmap(nt))
      }
  }

  object HFunctor {
    @inline def apply[H[_[_], _]](implicit ev: HFunctor[H]): ev.type = ev
  }

  trait ~~>[H[_[_], _], G[_[_], _]] {
    def apply[F[_], A](fa: H[F, A]): G[F, A]
  }

  final case class Fix[F[_[_], _], A](unFix: F[Fix[F, ?], A]) {

    @inline def map1[G[_[_], _]](nt: F ~~> G)(implicit F: HFunctor[F]): Fix[G, A] =
      Fix.map1(nt)(F)(this)
  }

  object Fix {

    @inline def map1[F[_[_], _], G[_[_], _]](
      nt: F ~~> G
    )(implicit F: HFunctor[F]): Fix[F, ?] ~> Fix[G, ?] =
      new (Fix[F, ?] ~> Fix[G, ?]) {

        def apply[A](fa: Fix[F, A]): Fix[G, A] = {
          val nt2: F[Fix[F, ?], ?] ~> F[Fix[G, ?], ?] = F.hmap[Fix[F, ?], Fix[G, ?]](this)
          Fix(nt(nt2(fa.unFix)))
        }
      }
  }

  final case class HEnvT[E, F[_[_], _], G[_], I](ask: E, fa: F[G, I])

  object HEnvT {

    implicit def hfunctor[E, F[_[_], _]](implicit F: HFunctor[F]): HFunctor[HEnvT[E, F, ?[_], ?]] =
      new HFunctor[HEnvT[E, F, ?[_], ?]] {

        def hmap[M[_], N[_]](nt: M ~> N) = new (HEnvT[E, F, M, ?] ~> HEnvT[E, F, N, ?]) {
          def apply[I](fm: HEnvT[E, F, M, I]) = HEnvT(fm.ask, F.hmap(nt)(fm.fa))
        }
      }
  }
}

package object recursion {
  type HAlgebra[F[_[_], _], G[_]]   = F[G, ?] ~> G
  type HCoalgebra[F[_[_], _], G[_]] = G ~> F[G, ?]

  def cataNT[S[_[_], _], F[_]](
    alg: HAlgebra[S, F]
  )(implicit S: HFunctor[S]): (Fix[S, ?] ~> F) =
    new (Fix[S, ?] ~> F) { self =>

      def apply[A](f: Fix[S, A]): F[A] =
        alg.apply[A](S.hmap(self)(f.unFix))
    }

  def hyloNT[S[_[_], _], F[_], G[_]](coalgebra: HCoalgebra[S, F], algebra: HAlgebra[S, G])(
    implicit S: HFunctor[S]
  ): F ~> G = new (F ~> G) { self =>

    def apply[A](fa: F[A]): G[A] =
      algebra(S.hmap(self)(coalgebra(fa)))
  }
}
