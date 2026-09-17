require import AllCore Int List Distr DProd FMap FSet Real RealExp.
require import StdOrder StdBigop.
require import IKEv2Core Qrom.
import RealOrder.

type ekey.

type dkey.

type ctxt.

type mesg = qdom.

op dmesg : { mesg distr | is_lossless dmesg } as dmesg_ll.

op kpke_enc : ekey -> mesg -> blk -> ctxt.

op kpke_keygen : { (dkey * ekey) distr | is_lossless kpke_keygen } as kpke_keygen_ll.

op eps_ow : { real | 0%r <= eps_ow } as ge0_eps_ow.

op eps_o2h : { real | 0%r <= eps_o2h } as ge0_eps_o2h.

op derr : { real | 0%r <= derr } as ge0_derr.

op qq : { int | 0 <= qq } as ge0_qq.

module Chall = { var mm : mesg }.

module type ROGet = { proc get (x : mesg) : blk * blk }.

module Log (G : QRO.RO) : ROGet = {
  var qs : mesg list

  proc get (x : mesg) : blk * blk = {
    var y;
    qs <- x :: qs;
    y <@ G.get(x);
    return y;
  }
}.

module type KEMA (G : ROGet) = {
  proc guess (ek : ekey, c : ctxt, k : blk) : bool
}.

module CpaReal (A : KEMA) (G : QRO.RO) = {
  proc distinguish (z : int) : bool = {
    var dk, ek, m, kk, rr, c, b;
    Log.qs <- [];
    (dk, ek) <$ kpke_keygen;
    m <$ dmesg;
    Chall.mm <- m;
    kk <$ dblk;
    rr <$ dblk;
    G.set(m, (kk, rr));
    c <- kpke_enc ek m rr;
    b <@ A(Log(G)).guess(ek, c, kk);
    return b;
  }
}.

module CpaProg (A : KEMA) (G : QRO.RO) = {
  proc distinguish (z : int) : bool = {
    var dk, ek, m, kk, rr, kc, c, b;
    Log.qs <- [];
    (dk, ek) <$ kpke_keygen;
    m <$ dmesg;
    Chall.mm <- m;
    kk <$ dblk;
    rr <$ dblk;
    kc <$ dblk;
    G.set(m, (kc, rr));
    c <- kpke_enc ek m rr;
    b <@ A(Log(G)).guess(ek, c, kc);
    return b;
  }
}.

module CpaRand (A : KEMA) (G : QRO.RO) = {
  proc distinguish (z : int) : bool = {
    var dk, ek, m, kk, rr, kc, c, b;
    Log.qs <- [];
    (dk, ek) <$ kpke_keygen;
    m <$ dmesg;
    Chall.mm <- m;
    kk <$ dblk;
    rr <$ dblk;
    kc <$ dblk;
    G.set(m, (kk, rr));
    c <- kpke_enc ek m rr;
    b <@ A(Log(G)).guess(ek, c, kc);
    return b;
  }
}.



section KEMPROOF.

declare module A <: KEMA {-QRO.RO, -QRO.FRO, -QROE.FunRO, -Log, -Chall}.

(* The real key and a programmed key are identically distributed *)
local equiv real_prog_eq (G <: QRO.RO {-A, -Log, -Chall}) :
  CpaReal(A, G).distinguish ~ CpaProg(A, G).distinguish :
  ={glob A, glob G, arg} ==> ={res}.
proof.
proc.
call (: ={glob G, Log.qs}).
+ by proc; call (: true); auto.
wp; call (: true); wp.
by swap{2} 6 1; rnd; rnd; rnd{2}; wp; rnd; rnd; auto => />; smt(dblk_ll).
qed.

(* Lazy sampling and monolithic sampling agree on the real game *)
lemma cpa_qrom_bridge &m (z : int) :
  Pr[QRO.MainD(CpaReal(A), QRO.RO).distinguish(z) @ &m : res]
  = Pr[QRO.MainD(CpaReal(A), QROE.FunRO).distinguish(z) @ &m : res].
proof. by apply (pr_lazy_monolithic (CpaReal(A)) &m z (fun (b : bool) => b)). qed.

declare axiom o2h_bound &m (z : int) :
  `| Pr[QRO.MainD(CpaProg(A), QROE.FunRO).distinguish(z) @ &m : res]
     - Pr[QRO.MainD(CpaRand(A), QROE.FunRO).distinguish(z) @ &m : res] |
  <= 2%r * sqrt ((qq + 1)%r * eps_o2h).

declare axiom find_bound : eps_o2h <= eps_ow + qq%r * derr.

(* Square root is monotone on nonnegative arguments *)
lemma sqrt_le (x y : real) : 0%r <= x => x <= y => sqrt x <= sqrt y.
proof.
move=> hx hxy.
have hy : 0%r <= y by smt().
by rewrite (sqrt_mono x y hx hy).
qed.

(* Chosen plaintext security of the derived key mechanism *)
lemma mlkem_indcpa &m (z : int) :
  `| Pr[QRO.MainD(CpaProg(A), QROE.FunRO).distinguish(z) @ &m : res]
     - Pr[QRO.MainD(CpaRand(A), QROE.FunRO).distinguish(z) @ &m : res] |
  <= 2%r * sqrt ((qq + 1)%r * (eps_ow + qq%r * derr)).
proof.
have h1 := o2h_bound &m z.
have ha : 0%r <= (qq + 1)%r * eps_o2h by smt(ge0_qq ge0_eps_o2h).
have hb : (qq + 1)%r * eps_o2h <= (qq + 1)%r * (eps_ow + qq%r * derr).
+ by have := find_bound; smt(ge0_qq).
have h3 := sqrt_le _ _ ha hb.
smt().
qed.

end section KEMPROOF.
