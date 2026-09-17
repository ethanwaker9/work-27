require import AllCore Int List Distr DProd FMap FSet Real.
require import IKEv2Core.
require (*--*) FinType PROM.

clone import FinType.FinType as QDom.

type qdom = QDom.t.

clone import PROM.FullRO as QRO with
  type in_t    <- qdom,
  type out_t   <- blk * blk,
  op   dout    <- fun (_ : qdom) => dblk `*` dblk,
  type d_in_t  <- int,
  type d_out_t <- bool.

clone import QRO.FinEager as QROE with
  theory FinFrom <- QDom.


(* The oracle output distribution is lossless at every point *)
lemma qro_dout_ll : forall (_ : qdom), is_lossless (dblk `*` dblk).
proof. by move=> _; apply dprod_ll; split; apply dblk_ll. qed.

section QROMSOUND.

declare module D <: QROE.FinRO_Distinguisher {-QRO.RO, -QRO.FRO, -QROE.FunRO}.

(* Lazy sampling and monolithic sampling of the oracle agree *)
lemma pr_lazy_monolithic &m (x : int) (p : bool -> bool) :
  Pr[QRO.MainD(D, QRO.RO).distinguish(x) @ &m : p res]
  = Pr[QRO.MainD(D, QROE.FunRO).distinguish(x) @ &m : p res].
proof.
rewrite (QROE.pr_RO_FinRO_D qro_dout_ll D &m x p).
by rewrite (QROE.pr_FinRO_FunRO_D qro_dout_ll D &m x p).
qed.

end section QROMSOUND.

(* The monolithic oracle answers with the sampled function *)
lemma qro_monolithic_get (f : qdom -> blk * blk) (z : qdom) :
  hoare [ QROE.FunRO.get : QROE.FunRO.f = f /\ x = z ==> res = f z ].
proof. by proc; auto. qed.

(* The monolithic oracle samples the whole function at initialization *)
lemma qro_monolithic_init :
  hoare [ QROE.FunRO.init :
          true ==> QROE.FunRO.f \in QROE.MUniFinFun.dfun (fun (_ : qdom) => dblk `*` dblk) ].
proof. by proc; auto. qed.
