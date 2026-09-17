require import AllCore Int IntDiv List Distr DList FMap FSet Real.
require import StdOrder StdBigop.
require import IKEv2Core Expansion Segment Cascade.
import RealOrder.

op tlen : { int | 0 <= tlen } as ge0_tlen.

op bind (a k : kmat) : kmat = take tlen (a ++ k ++ nseq tlen witness).

(* The transcript binder has a fixed length *)
lemma size_bind (a k : kmat) : size (bind a k) = tlen.
proof.
rewrite /bind size_take 1:ge0_tlen !size_cat size_nseq.
smt(size_ge0 ge0_tlen).
qed.

(* Writing at a split position concatenates the segments *)
lemma flatten_setk (pr sf : kmat list) (dmv x : kmat) :
  flatten (setk (size pr) x (pr ++ (dmv :: sf)))
  = flatten pr ++ (x ++ flatten sf).
proof. by rewrite setk_cat flatten_cat flatten_cons. qed.

module SPKS : Schedule = {
  proc kdf (ks : kmat list, aux : kmat) : kmat = {
    var sig0, kb0, theta, sg, kb;
    sig0 <- F nonces (0, nth witness ks 0 ++ spis);
    kb0 <@ Expand.fexp([sig0], lb0, olen0);
    theta <- bind aux kb0;
    sg <- F theta (1, flatten ks);
    kb <@ Expand.fexp([sg], lb, olen);
    return kb;
  }
}.

(* Counter mode expansion under equal inputs is deterministic *)
equiv fexp_eq : Expand.fexp ~ Expand.fexp : ={arg} ==> ={res}.
proof. proc; sim. qed.

(* Counter mode expansion has no precondition *)
lemma fexp_true : hoare [Expand.fexp : true ==> true].
proof. proc; while (true); auto. qed.

(* Counter mode expansion terminates *)
lemma fexp_ll : islossless Expand.fexp.
proof. proc; while (true) (u - i); auto; smt(). qed.

module BSpksP (A : DistA) (O : SegO) = {
  proc guess (q : sin) : bool = {
    var sig0, kb0, theta, sg, kb, b;
    sig0 <- F nonces (0, head witness q.`1 ++ spis);
    kb0 <@ Expand.fexp([sig0], lb0, olen0);
    theta <- bind q.`3 kb0;
    sg <@ O.f(theta, 1, flatten q.`1, flatten q.`2);
    kb <@ Expand.fexp([sg], lb, olen);
    b <@ A.guess(kb);
    return b;
  }
}.

section SPKSLATER.

declare module A <: DistA {-PRFR, -PRFI, -SegR, -SegI, -SKPar}.

declare axiom prf_bound (B <: PRFA{-PRFR, -PRFI}) (p : pin) &m :
  `| Pr[PRFR(B).main(p) @ &m : res] - Pr[PRFI(B).main(p) @ &m : res] | <= eps_prf.

declare axiom seg_bound (B <: SegA{-SegR, -SegI}) (ak ap asz aq : int) (q : sin) &m :
  `| Pr[SegR(B).main(ak, ap, asz, aq, q) @ &m : res]
     - Pr[SegI(B).main(ak, ap, asz, aq, q) @ &m : res] | <= eps_seg.

(* The single pass extraction is one segment keyed query *)
local equiv spks_seg_real (pr sf : kmat list) (dmv axv : kmat) (sn : int) :
  SK1R(SPKS, A).main ~ SegR(BSpksP(A)).main :
  ={glob A} /\ arg{1} = (size pr, sn, pr ++ (dmv :: sf), axv)
  /\ arg{2} = (tlen, size (flatten pr), sn, size (flatten sf), (pr, sf, axv))
  /\ pr <> [] ==> ={res}.
proof.
proc; inline SPKS.kdf BSpksP(A, SegR(BSpksP(A)).O).guess SegR(BSpksP(A)).O.f.
wp; call (: true); wp; call fexp_eq; wp; call fexp_eq; wp; rnd.
by auto => />; smt(setk_nth0 flatten_setk size_bind catA).
qed.

(* A fresh segment answer is a uniform combined secret *)
local equiv spks_seg_ideal (pr sf : kmat list) (axv : kmat) (sn : int) :
  SegI(BSpksP(A)).main ~ ExpCR(Lift(A)).main :
  ={glob A}
  /\ arg{1} = (tlen, size (flatten pr), sn, size (flatten sf), (pr, sf, axv))
  /\ arg{2} = (olen, lb, []) ==> ={res}.
proof.
proc; inline SegI(BSpksP(A)).O.f BSpksP(A, SegI(BSpksP(A)).O).guess Lift(A).guess.
rcondt{1} 13; first by auto; call fexp_true; auto; smt(size_bind).
rcondt{1} 13; first by auto; call fexp_true; auto; smt(mem_empty).
wp; call (: true); wp; call fexp_eq; wp; rnd; wp.
by call{1} fexp_ll; auto => />; smt(size_bind get_set_sameE).
qed.

(* The ideal expansion output is the ideal split key answer *)
local equiv expi_sk1i (j sn : int) (ks : kmat list) (axv : kmat) :
  ExpI(Lift(A)).main ~ SK1I(SPKS, A).main :
  ={glob A} /\ arg{1} = (olen, lb, []) /\ arg{2} = (j, sn, ks, axv) ==> ={res}.
proof. by proc; inline Lift(A).guess; wp; call (: true); auto. qed.

(* Split key security of the single pass schedule at a later exchange *)
lemma spks_splitkey_pos (pr sf : kmat list) (dmv axv : kmat) (sn : int) &m :
  pr <> [] =>
  `| Pr[SK1R(SPKS, A).main(size pr, sn, pr ++ (dmv :: sf), axv) @ &m : res]
     - Pr[SK1I(SPKS, A).main(size pr, sn, pr ++ (dmv :: sf), axv) @ &m : res] |
  <= eps_seg + eps_prf.
proof.
move=> hpr.
have e1 : Pr[SK1R(SPKS, A).main(size pr, sn, pr ++ (dmv :: sf), axv) @ &m : res]
        = Pr[SegR(BSpksP(A)).main(tlen, size (flatten pr), sn, size (flatten sf),
                                  (pr, sf, axv)) @ &m : res].
+ by byequiv (spks_seg_real pr sf dmv axv sn).
have e2 := seg_bound (BSpksP(A)) tlen (size (flatten pr)) sn (size (flatten sf))
                     (pr, sf, axv) &m.
have e3 : Pr[SegI(BSpksP(A)).main(tlen, size (flatten pr), sn, size (flatten sf),
                                  (pr, sf, axv)) @ &m : res]
        = Pr[ExpCR(Lift(A)).main(olen, lb, []) @ &m : res].
+ by byequiv (spks_seg_ideal pr sf axv sn).
have e4 := fexp_pseudorandom (Lift(A)) &m (olen, lb, []).
have e5 := prf_bound (BExp(Lift(A))) (olen, lb, []) &m.
have e6 : Pr[ExpI(Lift(A)).main(olen, lb, []) @ &m : res]
        = Pr[SK1I(SPKS, A).main(size pr, sn, pr ++ (dmv :: sf), axv) @ &m : res].
+ by byequiv (expi_sk1i (size pr) sn (pr ++ (dmv :: sf)) axv).
smt().
qed.

end section SPKSLATER.

type prof3 = int * int * int.

op wf2 (q1 q2 : prof3) (k x y : kmat) : bool =
  ((size k, size x, size y) = q1) \/ ((size k, size x, size y) = q2).

module Seg2R (A : SegA) = {
  var xx : kmat
  var r1, r2 : prof3

  module O : SegO = {
    proc f (k : kmat, l : int, x : kmat, y : kmat) : blk = {
      return if wf2 r1 r2 k x y then F k (l, x ++ xx ++ y) else witness;
    }
  }

  proc main (q1 q2 : prof3, sz : int, q : sin) : bool = {
    var b;
    r1 <- q1; r2 <- q2;
    xx <$ dlist dblk sz;
    b <@ A(O).guess(q);
    return b;
  }
}.

module Seg2I (A : SegA) = {
  var mp : (kmat * int * kmat * kmat, blk) fmap
  var r1, r2 : prof3

  module O : SegO = {
    proc f (k : kmat, l : int, x : kmat, y : kmat) : blk = {
      var r;
      if (wf2 r1 r2 k x y) {
        if ((k, l, x, y) \notin mp) { r <$ dblk; mp.[(k, l, x, y)] <- r; }
      }
      return if wf2 r1 r2 k x y then oget mp.[(k, l, x, y)] else witness;
    }
  }

  proc main (q1 q2 : prof3, sz : int, q : sin) : bool = {
    var b;
    r1 <- q1; r2 <- q2; mp <- empty;
    b <@ A(O).guess(q);
    return b;
  }
}.

module BSpks0 (A : DistA) (O : SegO) = {
  proc guess (q : sin) : bool = {
    var sig0, kb0, theta, sg, kb, b;
    sig0 <@ O.f(nonces, 0, [], spis);
    kb0 <@ Expand.fexp([sig0], lb0, olen0);
    theta <- bind q.`3 kb0;
    sg <@ O.f(theta, 1, [], flatten q.`2);
    kb <@ Expand.fexp([sg], lb, olen);
    b <@ A.guess(kb);
    return b;
  }
}.

section SPKSINITIAL.

declare module A <: DistA {-PRFR, -PRFI, -Seg2R, -Seg2I, -SKPar}.

declare axiom prf_bound (B <: PRFA{-PRFR, -PRFI}) (p : pin) &m :
  `| Pr[PRFR(B).main(p) @ &m : res] - Pr[PRFI(B).main(p) @ &m : res] | <= eps_prf.

declare axiom seg2_bound (B <: SegA{-Seg2R, -Seg2I}) (q1 q2 : prof3) (sz : int)
                         (q : sin) &m :
  `| Pr[Seg2R(B).main(q1, q2, sz, q) @ &m : res]
     - Pr[Seg2I(B).main(q1, q2, sz, q) @ &m : res] | <= eps_seg.

(* Both initial extractions are segment keyed queries *)
local equiv spks0_seg_real (sf : kmat list) (dmv axv : kmat) (sn : int) :
  SK1R(SPKS, A).main ~ Seg2R(BSpks0(A)).main :
  ={glob A} /\ arg{1} = (0, sn, dmv :: sf, axv)
  /\ arg{2} = ((size nonces, 0, size spis), (tlen, 0, size (flatten sf)), sn,
                ([], sf, axv)) ==> ={res}.
proof.
proc; inline SPKS.kdf BSpks0(A, Seg2R(BSpks0(A)).O).guess Seg2R(BSpks0(A)).O.f.
wp; call (: true); wp; call fexp_eq; wp; call fexp_eq; wp; rnd.
by auto => />; smt(setk0 size_bind cat0s).
qed.

(* Fresh segment answers give a uniform combined secret *)
local equiv spks0_seg_ideal (sf : kmat list) (axv : kmat) (sn : int) :
  Seg2I(BSpks0(A)).main ~ ExpCR(Lift(A)).main :
  ={glob A}
  /\ arg{1} = ((size nonces, 0, size spis), (tlen, 0, size (flatten sf)), sn,
                ([], sf, axv))
  /\ arg{2} = (olen, lb, []) ==> ={res}.
proof.
proc; inline Seg2I(BSpks0(A)).O.f BSpks0(A, Seg2I(BSpks0(A)).O).guess Lift(A).guess.
rcondt{1} 9; first by auto; smt(wf2).
rcondt{1} 9; first by auto; smt(mem_empty).
rcondt{1} 18; first by auto; call fexp_true; auto; smt(size_bind).
rcondt{1} 18; first by auto; call fexp_true; auto; smt(mem_set mem_empty).
wp; call (: true); wp; call fexp_eq; wp; rnd; wp.
by call{1} fexp_ll; auto => />; smt(size_bind get_setE mem_set).
qed.

(* The ideal expansion output is the ideal split key answer *)
local equiv expi_sk1i0 (j sn : int) (ks : kmat list) (axv : kmat) :
  ExpI(Lift(A)).main ~ SK1I(SPKS, A).main :
  ={glob A} /\ arg{1} = (olen, lb, []) /\ arg{2} = (j, sn, ks, axv) ==> ={res}.
proof. by proc; inline Lift(A).guess; wp; call (: true); auto. qed.

(* Split key security of the single pass schedule at the initial exchange *)
lemma spks_splitkey_zero (sf : kmat list) (dmv axv : kmat) (sn : int) &m :
  `| Pr[SK1R(SPKS, A).main(0, sn, dmv :: sf, axv) @ &m : res]
     - Pr[SK1I(SPKS, A).main(0, sn, dmv :: sf, axv) @ &m : res] |
  <= eps_seg + eps_prf.
proof.
have e1 : Pr[SK1R(SPKS, A).main(0, sn, dmv :: sf, axv) @ &m : res]
        = Pr[Seg2R(BSpks0(A)).main((size nonces, 0, size spis),
                                   (tlen, 0, size (flatten sf)), sn,
                                   ([], sf, axv)) @ &m : res].
+ by byequiv (spks0_seg_real sf dmv axv sn).
have e2 := seg2_bound (BSpks0(A)) (size nonces, 0, size spis)
                      (tlen, 0, size (flatten sf)) sn ([], sf, axv) &m.
have e3 : Pr[Seg2I(BSpks0(A)).main((size nonces, 0, size spis),
                                   (tlen, 0, size (flatten sf)), sn,
                                   ([], sf, axv)) @ &m : res]
        = Pr[ExpCR(Lift(A)).main(olen, lb, []) @ &m : res].
+ by byequiv (spks0_seg_ideal sf axv sn).
have e4 := fexp_pseudorandom (Lift(A)) &m (olen, lb, []).
have e5 := prf_bound (BExp(Lift(A))) (olen, lb, []) &m.
have e6 : Pr[ExpI(Lift(A)).main(olen, lb, []) @ &m : res]
        = Pr[SK1I(SPKS, A).main(0, sn, dmv :: sf, axv) @ &m : res].
+ by byequiv (expi_sk1i0 0 sn (dmv :: sf) axv).
smt().
qed.

end section SPKSINITIAL.
