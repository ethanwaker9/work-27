require import AllCore Int IntDiv List Distr DList FMap FSet Real.
require import StdOrder StdBigop.
require import IKEv2Core.
import RealOrder.

clone import DList.Program as DLB with
  type t <- blk,
  op d <- dblk.

module Expand = {
  proc prfp (k : kmat, s : kmat, u : int) : kmat = {
    var i, t, acc;
    i <- 0; t <- witness; acc <- [];
    while (i < u) {
      t <- F k (i + 1, if i = 0 then s else t :: s);
      acc <- acc ++ [t];
      i <- i + 1;
    }
    return acc;
  }

  proc fexp (k : kmat, l : kmat, u : int) : kmat = {
    var i, acc;
    i <- 0; acc <- [];
    while (i < u) {
      acc <- acc ++ [F k (i + 1, l)];
      i <- i + 1;
    }
    return acc;
  }
}.

module ExpPR (A : PDistA) = {
  proc main (p : pin) : bool = {
    var k, r, b;
    k <$ dblk;
    r <@ Expand.prfp([k], p.`2, p.`1);
    b <@ A.guess(p, r);
    return b;
  }
}.

module ExpCR (A : PDistA) = {
  proc main (p : pin) : bool = {
    var k, r, b;
    k <$ dblk;
    r <@ Expand.fexp([k], p.`2, p.`1);
    b <@ A.guess(p, r);
    return b;
  }
}.

module ExpI (A : PDistA) = {
  proc main (p : pin) : bool = {
    var r, b;
    r <$ dlist dblk p.`1;
    b <@ A.guess(p, r);
    return b;
  }
}.

module ExpIC (A : PDistA) = {
  proc main (p : pin) : bool = {
    var rest, k, b;
    rest <$ dlist dblk (p.`1 - 1);
    k <$ dblk;
    b <@ A.guess(p, k :: rest);
    return b;
  }
}.

module BPlus (A : PDistA) (O : PRFO) = {
  proc guess (p : pin) : bool = {
    var i, t, acc, b;
    i <- 0; t <- witness; acc <- [];
    while (i < p.`1) {
      t <@ O.f(i + 1, if i = 0 then p.`2 else t :: p.`2);
      acc <- acc ++ [t];
      i <- i + 1;
    }
    b <@ A.guess(p, acc);
    return b;
  }
}.

module BExp (A : PDistA) (O : PRFO) = {
  proc guess (p : pin) : bool = {
    var i, t, acc, b;
    i <- 0; t <- witness; acc <- [];
    while (i < p.`1) {
      t <@ O.f(i + 1, p.`2);
      acc <- acc ++ [t];
      i <- i + 1;
    }
    b <@ A.guess(p, acc);
    return b;
  }
}.

section EXPANSION.

declare module A <: PDistA {-PRFR, -PRFI}.

local module SamI (A : PDistA) = {
  proc main (p : pin) : bool = {
    var r, b;
    r <@ DLB.Sample.sample(p.`1);
    b <@ A.guess(p, r);
    return b;
  }
}.

local module SamC (A : PDistA) = {
  proc main (p : pin) : bool = {
    var r, b;
    r <@ DLB.SampleCons.sample(p.`1);
    b <@ A.guess(p, r);
    return b;
  }
}.

local module LoopI (A : PDistA) = {
  proc main (p : pin) : bool = {
    var r, b;
    r <@ DLB.LoopSnoc.sample(p.`1);
    b <@ A.guess(p, r);
    return b;
  }
}.

(* The chained expansion matches its pseudorandom function reduction *)
local equiv plus_real_eq :
  ExpPR(A).main ~ PRFR(BPlus(A)).main : ={glob A, arg} ==> ={res}.
proof.
proc; inline PRFR(BPlus(A)).O.f BPlus(A, PRFR(BPlus(A)).O).guess Expand.prfp.
wp; call (: true); wp.
while (={i, t, acc} /\ u{1} = p0{2}.`1 /\ k0{1} = [PRFR.k{2}] /\ s{1} = p0{2}.`2).
+ by auto.
by auto.
qed.

(* The counter mode expansion matches its reduction *)
local equiv exp_real_eq :
  ExpCR(A).main ~ PRFR(BExp(A)).main : ={glob A, arg} ==> ={res}.
proof.
proc; inline PRFR(BExp(A)).O.f BExp(A, PRFR(BExp(A)).O).guess Expand.fexp.
wp; call (: true); wp.
while (={i, acc} /\ u{1} = p0{2}.`1 /\ k0{1} = [PRFR.k{2}] /\ l{1} = p0{2}.`2).
+ by auto.
by auto.
qed.

(* The lazily sampled chain is a fresh uniform list *)
local equiv plus_ideal_eq :
  LoopI(A).main ~ PRFI(BPlus(A)).main : ={glob A, arg} ==> ={res}.
proof.
proc; inline PRFI(BPlus(A)).O.f BPlus(A, PRFI(BPlus(A)).O).guess
             DLB.LoopSnoc.sample.
wp; call (: true); wp.
while (={i} /\ l{1} = acc{2} /\ n{1} = p0{2}.`1 /\ 0 <= i{1}
       /\ (forall (m : msg), m \in PRFI.mp{2} => m.`1 <= i{2})).
+ rcondt{2} 2; first by auto; smt().
  by auto => />; smt(get_setE mem_set).
by auto => />; smt(mem_empty).
qed.

(* The lazily sampled counter mode is a fresh uniform list *)
local equiv exp_ideal_eq :
  LoopI(A).main ~ PRFI(BExp(A)).main : ={glob A, arg} ==> ={res}.
proof.
proc; inline PRFI(BExp(A)).O.f BExp(A, PRFI(BExp(A)).O).guess
             DLB.LoopSnoc.sample.
wp; call (: true); wp.
while (={i} /\ l{1} = acc{2} /\ n{1} = p0{2}.`1 /\ 0 <= i{1}
       /\ (forall (m : msg), m \in PRFI.mp{2} => m.`1 <= i{2})).
+ rcondt{2} 2; first by auto; smt().
  by auto => />; smt(get_setE mem_set).
by auto => />; smt(mem_empty).
qed.

(* Monolithic list sampling equals its procedural form *)
local equiv sami_eq : ExpI(A).main ~ SamI(A).main : ={glob A, arg} ==> ={res}.
proof. by proc; call (: true); inline*; auto. qed.

(* Loop sampling and monolithic list sampling agree *)
local equiv loop_sample_eq : SamI(A).main ~ LoopI(A).main : ={glob A, arg} ==> ={res}.
proof. by proc; call (: true); call DLB.Sample_LoopSnoc_eq; auto. qed.

(* Consed sampling and monolithic list sampling agree *)
local equiv samc_eq :
  SamI(A).main ~ SamC(A).main : ={glob A, arg} /\ 0 < p{1}.`1 ==> ={res}.
proof. by proc; call (: true); call DLB.Sample_SampleCons_eq; auto. qed.

(* Consed sampling is the head and tail form *)
local equiv expic_eq : SamC(A).main ~ ExpIC(A).main : ={glob A, arg} ==> ={res}.
proof. by proc; call (: true); inline*; auto. qed.

(* The ideal list game equals its loop form *)
local equiv expi_loop_eq : ExpI(A).main ~ LoopI(A).main : ={glob A, arg} ==> ={res}.
proof.
transitivity SamI(A).main (={glob A, arg} ==> ={res}) (={glob A, arg} ==> ={res}).
+ by move=> &1 &2 h; exists (glob A){2} arg{2}.
+ by [].
+ by conseq sami_eq.
by conseq loop_sample_eq.
qed.

(* Chained expansion under a uniform key is pseudorandom *)
lemma prfp_pseudorandom &m (p : pin) :
  `| Pr[ExpPR(A).main(p) @ &m : res] - Pr[ExpI(A).main(p) @ &m : res] |
  = `| Pr[PRFR(BPlus(A)).main(p) @ &m : res]
       - Pr[PRFI(BPlus(A)).main(p) @ &m : res] |.
proof.
have -> : Pr[ExpPR(A).main(p) @ &m : res] = Pr[PRFR(BPlus(A)).main(p) @ &m : res].
+ by byequiv plus_real_eq.
have -> : Pr[ExpI(A).main(p) @ &m : res] = Pr[PRFI(BPlus(A)).main(p) @ &m : res].
+ rewrite (: Pr[ExpI(A).main(p) @ &m : res] = Pr[LoopI(A).main(p) @ &m : res]).
  + by byequiv expi_loop_eq.
  by byequiv plus_ideal_eq.
done.
qed.

(* Counter mode expansion under a uniform key is pseudorandom *)
lemma fexp_pseudorandom &m (p : pin) :
  `| Pr[ExpCR(A).main(p) @ &m : res] - Pr[ExpI(A).main(p) @ &m : res] |
  = `| Pr[PRFR(BExp(A)).main(p) @ &m : res]
       - Pr[PRFI(BExp(A)).main(p) @ &m : res] |.
proof.
have -> : Pr[ExpCR(A).main(p) @ &m : res] = Pr[PRFR(BExp(A)).main(p) @ &m : res].
+ by byequiv exp_real_eq.
have -> : Pr[ExpI(A).main(p) @ &m : res] = Pr[PRFI(BExp(A)).main(p) @ &m : res].
+ rewrite (: Pr[ExpI(A).main(p) @ &m : res] = Pr[LoopI(A).main(p) @ &m : res]).
  + by byequiv expi_loop_eq.
  by byequiv exp_ideal_eq.
done.
qed.

(* The ideal block equals a fresh head with an independent tail *)
lemma expi_expic &m (p : pin) :
  0 < p.`1 => Pr[ExpI(A).main(p) @ &m : res] = Pr[ExpIC(A).main(p) @ &m : res].
proof.
move=> hu.
have -> : Pr[ExpI(A).main(p) @ &m : res] = Pr[SamI(A).main(p) @ &m : res].
+ by byequiv sami_eq.
have -> : Pr[SamI(A).main(p) @ &m : res] = Pr[SamC(A).main(p) @ &m : res].
+ by byequiv samc_eq.
by byequiv expic_eq.
qed.

end section EXPANSION.
