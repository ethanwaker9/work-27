require import AllCore Int IntDiv List Distr DList FMap FSet Real.
require import StdOrder StdBigop.
require import IKEv2Core Expansion Segment Cascade.
import RealOrder.

module Ppk0R (A : DistA) = {
  proc main (kb : kmat) : bool = {
    var k, r, b;
    k <$ dblk;
    r <- F [k] (1, kb);
    b <@ A.guess([r]);
    return b;
  }
}.

module Ppk0I (A : DistA) = {
  proc main (kb : kmat) : bool = {
    var r, b;
    r <$ dblk;
    b <@ A.guess([r]);
    return b;
  }
}.

module Ppk1R (A : DistA) = {
  proc main (pk : kmat, sn : int) : bool = {
    var kb, r, b;
    kb <$ dlist dblk sn;
    r <- F pk (1, kb);
    b <@ A.guess([r]);
    return b;
  }
}.

module Ppk1I (A : DistA) = {
  proc main (pk : kmat, sn : int) : bool = {
    var r, b;
    r <$ dblk;
    b <@ A.guess([r]);
    return b;
  }
}.

module BPpk0 (A : DistA) (O : PRFO) = {
  proc guess (p : pin) : bool = {
    var r, b;
    r <@ O.f(1, p.`2);
    b <@ A.guess([r]);
    return b;
  }
}.

module BPpk1 (A : DistA) (O : SegO) = {
  proc guess (q : sin) : bool = {
    var r, b;
    r <@ O.f(q.`3, 1, [], []);
    b <@ A.guess([r]);
    return b;
  }
}.

section PRESHAREDKEY.

declare module A <: DistA {-PRFR, -PRFI, -SegR, -SegI}.

declare axiom prf_bound (B <: PRFA{-PRFR, -PRFI}) (p : pin) &m :
  `| Pr[PRFR(B).main(p) @ &m : res] - Pr[PRFI(B).main(p) @ &m : res] | <= eps_prf.

declare axiom seg_bound (B <: SegA{-SegR, -SegI}) (ak ap asz aq : int) (q : sin) &m :
  `| Pr[SegR(B).main(ak, ap, asz, aq, q) @ &m : res]
     - Pr[SegI(B).main(ak, ap, asz, aq, q) @ &m : res] | <= eps_seg.

(* The preshared key occupies the key input at index zero *)
local equiv ppk0_real (kb : kmat) :
  Ppk0R(A).main ~ PRFR(BPpk0(A)).main :
  ={glob A} /\ arg{1} = kb /\ arg{2} = (0, kb, []) ==> ={res}.
proof.
proc; inline PRFR(BPpk0(A)).O.f BPpk0(A, PRFR(BPpk0(A)).O).guess.
by wp; call (: true); auto.
qed.

(* A random function answer is a uniform derived key *)
local equiv ppk0_ideal (kb : kmat) :
  Ppk0I(A).main ~ PRFI(BPpk0(A)).main :
  ={glob A} /\ arg{1} = kb /\ arg{2} = (0, kb, []) ==> ={res}.
proof.
proc; inline PRFI(BPpk0(A)).O.f BPpk0(A, PRFI(BPpk0(A)).O).guess.
rcondt{2} 4; first by auto; smt(mem_empty).
by wp; call (: true); wp; rnd; auto => />; smt(get_set_sameE).
qed.

(* The key exchange block occupies a fixed segment at index one *)
local equiv ppk1_real (pk : kmat) (sn : int) :
  Ppk1R(A).main ~ SegR(BPpk1(A)).main :
  ={glob A} /\ arg{1} = (pk, sn)
  /\ arg{2} = (size pk, 0, sn, 0, ([], [], pk)) ==> ={res}.
proof.
proc; inline SegR(BPpk1(A)).O.f BPpk1(A, SegR(BPpk1(A)).O).guess.
by wp; call (: true); wp; rnd; auto => />; smt(cat0s cats0).
qed.

(* A fresh segment answer is a uniform derived key *)
local equiv ppk1_ideal (pk : kmat) (sn : int) :
  Ppk1I(A).main ~ SegI(BPpk1(A)).main :
  ={glob A} /\ arg{1} = (pk, sn)
  /\ arg{2} = (size pk, 0, sn, 0, ([], [], pk)) ==> ={res}.
proof.
proc; inline SegI(BPpk1(A)).O.f BPpk1(A, SegI(BPpk1(A)).O).guess.
rcondt{2} 10; first by auto; rewrite /wfseg.
rcondt{2} 10; first by auto; smt(mem_empty).
by wp; call (: true); wp; rnd; auto => />; smt(get_set_sameE).
qed.

(* The preshared key mixing is split key pseudorandom at index zero *)
lemma ppk_splitkey_zero (kb : kmat) &m :
  `| Pr[Ppk0R(A).main(kb) @ &m : res] - Pr[Ppk0I(A).main(kb) @ &m : res] |
  <= eps_prf.
proof.
have -> : Pr[Ppk0R(A).main(kb) @ &m : res] = Pr[PRFR(BPpk0(A)).main(0, kb, []) @ &m : res].
+ by byequiv (ppk0_real kb).
have -> : Pr[Ppk0I(A).main(kb) @ &m : res] = Pr[PRFI(BPpk0(A)).main(0, kb, []) @ &m : res].
+ by byequiv (ppk0_ideal kb).
by apply (prf_bound (BPpk0(A)) (0, kb, []) &m).
qed.

(* The preshared key mixing is split key pseudorandom at index one *)
lemma ppk_splitkey_one (pk : kmat) (sn : int) &m :
  `| Pr[Ppk1R(A).main(pk, sn) @ &m : res] - Pr[Ppk1I(A).main(pk, sn) @ &m : res] |
  <= eps_seg.
proof.
have -> : Pr[Ppk1R(A).main(pk, sn) @ &m : res]
        = Pr[SegR(BPpk1(A)).main(size pk, 0, sn, 0, ([], [], pk)) @ &m : res].
+ by byequiv (ppk1_real pk sn).
have -> : Pr[Ppk1I(A).main(pk, sn) @ &m : res]
        = Pr[SegI(BPpk1(A)).main(size pk, 0, sn, 0, ([], [], pk)) @ &m : res].
+ by byequiv (ppk1_ideal pk sn).
by apply (seg_bound (BPpk1(A)) (size pk) 0 sn 0 ([], [], pk) &m).
qed.

end section PRESHAREDKEY.
