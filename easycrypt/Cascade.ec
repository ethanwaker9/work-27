require import AllCore Int IntDiv List Distr DList FMap FSet Real.
require import StdOrder StdBigop.
require import IKEv2Core Expansion Segment.
import RealOrder.

op eps_prf : real.

op eps_seg : real.

module Tail = {
  proc run (sd : blk, p : pin) : kmat = {
    var kb, ss;
    ss <- p.`3;
    kb <@ Expand.prfp([sd], p.`2, p.`1);
    while (ss <> []) {
      sd <- F (skd kb) (0, head witness ss ++ nonces);
      kb <@ Expand.prfp([sd], p.`2, p.`1);
      ss <- behead ss;
    }
    return kb;
  }
}.

module CReal (A : DistA) = {
  proc main (p : pin) : bool = {
    var sd, kb, b;
    sd <$ dblk;
    kb <@ Tail.run(sd, p);
    b <@ A.guess(kb);
    return b;
  }
}.

module CIdeal (A : DistA) = {
  proc main (p : pin) : bool = {
    var kb, b;
    kb <$ dlist dblk p.`1;
    b <@ A.guess(kb);
    return b;
  }
}.

module D1 (A : DistA) : PDistA = {
  proc guess (p : pin, kb0 : kmat) : bool = {
    var sd, kb, b;
    sd <- F (skd kb0) (0, head witness p.`3 ++ nonces);
    kb <@ Tail.run(sd, (p.`1, p.`2, behead p.`3));
    b <@ A.guess(kb);
    return b;
  }
}.

module D2 (A : DistA) (O : PRFO) = {
  proc guess (p : pin) : bool = {
    var sd, kb, b;
    sd <@ O.f(0, head witness p.`3 ++ nonces);
    kb <@ Tail.run(sd, (p.`1, p.`2, behead p.`3));
    b <@ A.guess(kb);
    return b;
  }
}.

(* Expansion under equal inputs is deterministic *)
equiv prfp_eq : Expand.prfp ~ Expand.prfp : ={arg} ==> ={res}.
proof. proc; sim. qed.

(* Expansion has no precondition *)
lemma prfp_true : hoare [Expand.prfp : true ==> true].
proof. proc; while (true); auto. qed.

(* The cascade tail under equal inputs is deterministic *)
equiv tail_eq : Tail.run ~ Tail.run : ={arg} ==> ={res}.
proof.
proc.
while (={ss, kb, sd, p}).
+ by wp; call prfp_eq; auto.
by call prfp_eq; auto.
qed.

(* The chaining key is the head of the key block *)
lemma skd_cons (k : blk) (r : kmat) : skd (k :: r) = [k].
proof. by rewrite /skd /= take0. qed.


(* The chained expansion terminates *)
lemma prfp_ll : islossless Expand.prfp.
proof. proc; while (true) (u - i); auto; smt(). qed.

(* The cascade tail has no precondition *)
lemma tail_true : hoare [Tail.run : true ==> true].
proof.
proc; while (true).
+ by wp; call prfp_true; auto.
by call prfp_true; auto.
qed.

(* The cascade tail terminates *)
lemma tail_ll : islossless Tail.run.
proof.
proc; while (true) (size ss).
+ by move=> z; wp; call prfp_ll; auto; smt(size_behead size_eq0 size_ge0).
by call prfp_ll; auto; smt(size_ge0).
qed.

(* The head of a nonempty concatenation is the head of its first part *)
lemma head_cat (s1 s2 : kmat list) :
  s1 <> [] => head witness (s1 ++ s2) = head witness s1.
proof. by case: s1. qed.

(* The tail of a nonempty concatenation extends its first part *)
lemma behead_cat (s1 s2 : kmat list) :
  s1 <> [] => behead (s1 ++ s2) = behead s1 ++ s2.
proof. by case: s1. qed.

(* The split guard tracks the remaining prefix *)
lemma split_guard (t l : kmat list) (z : kmat) :
  ((t ++ (z :: l)) <> [] /\ size l + 1 < size (t ++ (z :: l))) <=> t <> [].
proof. rewrite size_cat /=; smt(size_ge0). qed.

(* The first component of a split write is the original head *)
lemma setk_nth0 (pre suf : kmat list) (dm x : kmat) :
  pre <> [] =>
  nth witness (setk (size pre) x (pre ++ (dm :: suf))) 0 = head witness pre.
proof. by move=> h; rewrite setk_cat nth0_head head_cat. qed.

(* The remaining components of a split write carry the secret *)
lemma setk_drop1 (pre suf : kmat list) (dm x : kmat) :
  pre <> [] =>
  drop 1 (setk (size pre) x (pre ++ (dm :: suf))) = behead pre ++ (x :: suf).
proof. by move=> h; rewrite setk_cat drop1 behead_cat. qed.

(* Writing at the initial index prepends the secret *)
lemma setk0 (suf : kmat list) (dm x : kmat) : setk 0 x (dm :: suf) = x :: suf.
proof. by rewrite /setk take0 cat0s /= drop0. qed.

module TailSplit = {
  proc run (sd : blk, p : pin, x : kmat, l2 : kmat list) : kmat = {
    var kb, sd2;
    kb <@ Tail.run(sd, p);
    sd2 <- F (skd kb) (0, x ++ nonces);
    kb <@ Tail.run(sd2, (p.`1, p.`2, l2));
    return kb;
  }
}.

(* The cascade splits at the round that absorbs a secret *)
equiv tail_split (la lb : kmat list) (xz : kmat) :
  Tail.run ~ TailSplit.run :
  sd{1} = sd{2} /\ p{1}.`1 = p{2}.`1 /\ p{1}.`2 = p{2}.`2
  /\ p{1}.`3 = la ++ (xz :: lb) /\ p{2}.`3 = la /\ x{2} = xz /\ l2{2} = lb
  ==> ={res}.
proof.
proc; inline Tail.run.
splitwhile{1} 3 : (size lb + 1 < size ss).
splitwhile{1} 4 : (size lb < size ss).
unroll{1} 4.
rcondt{1} 4.
+ auto.
+ while (size lb < size ss).
  + by wp; call prfp_true; auto; smt(size_behead).
  by call prfp_true; auto => />; smt(size_cat size_ge0).
rcondf{1} 7.
+ auto.
+ wp; call prfp_true; wp.
  while (size lb < size ss).
  + by wp; call prfp_true; auto; smt(size_behead).
  by call prfp_true; auto => />; smt(size_cat size_behead size_ge0).
seq 2 4 : (ss{1} = ss{2} ++ (x{2} :: l2{2}) /\ kb{1} = kb0{2}
           /\ p{1}.`1 = p{2}.`1 /\ p{1}.`2 = p{2}.`2
           /\ p0{2} = p{2} /\ x{2} = xz /\ l2{2} = lb).
+ by wp; call prfp_eq; auto.
seq 1 1 : (ss{1} = x{2} :: l2{2} /\ kb{1} = kb0{2}
           /\ p{1}.`1 = p{2}.`1 /\ p{1}.`2 = p{2}.`2).
+ while (ss{1} = ss{2} ++ (x{2} :: l2{2}) /\ kb{1} = kb0{2}
         /\ p{1}.`1 = p{2}.`1 /\ p{1}.`2 = p{2}.`2
         /\ p0{2} = p{2} /\ x{2} = xz /\ l2{2} = lb).
  + by wp; call prfp_eq; auto => />; smt(head_cat behead_cat size_cat size_ge0 size_eq0).
  by auto => />; smt(split_guard cat0s size_cat size_ge0 size_eq0).
wp.
while (ss{1} = ss0{2} /\ kb{1} = kb1{2}
       /\ p{1}.`1 = p1{2}.`1 /\ p{1}.`2 = p1{2}.`2).
+ by wp; call prfp_eq; auto.
by wp; call prfp_eq; auto => />.
qed.

module KSc : Schedule = {
  proc kdf (ks : kmat list, aux : kmat) : kmat = {
    var sd, kb;
    sd <- F nonces (0, nth witness ks 0);
    kb <@ Tail.run(sd, (olen, ctx, drop 1 ks));
    return kb;
  }
}.

module BSeg0 (A : DistA) (O : SegO) = {
  proc guess (q : sin) : bool = {
    var sd, kb, b;
    sd <@ O.f(nonces, 0, [], []);
    kb <@ Tail.run(sd, (olen, ctx, q.`2));
    b <@ A.guess(kb);
    return b;
  }
}.

module BSegP (A : DistA) (O : SegO) = {
  proc guess (q : sin) : bool = {
    var kb, sd, b;
    kb <@ Tail.run(F nonces (0, head witness q.`1), (olen, ctx, behead q.`1));
    sd <@ O.f(skd kb, 0, [], nonces);
    kb <@ Tail.run(sd, (olen, ctx, q.`2));
    b <@ A.guess(kb);
    return b;
  }
}.

module SK1RSplitP (A : DistA) = {
  proc main (pre : kmat list, suf : kmat list, sl : int) : bool = {
    var xj, sd, kb, b;
    xj <$ dlist dblk sl;
    sd <- F nonces (0, head witness pre);
    kb <@ TailSplit.run(sd, (olen, ctx, behead pre), xj, suf);
    b <@ A.guess(kb);
    return b;
  }
}.

section CASCADE.

declare module A <: DistA {-PRFR, -PRFI, -SegR, -SegI, -SKPar}.

declare axiom prf_bound (B <: PRFA{-PRFR, -PRFI}) (p : pin) &m :
  `| Pr[PRFR(B).main(p) @ &m : res] - Pr[PRFI(B).main(p) @ &m : res] | <= eps_prf.

declare axiom seg_bound (B <: SegA{-SegR, -SegI}) (ak ap asz aq : int) (q : sin) &m :
  `| Pr[SegR(B).main(ak, ap, asz, aq, q) @ &m : res]
     - Pr[SegI(B).main(ak, ap, asz, aq, q) @ &m : res] | <= eps_seg.

(* The empty cascade is the chained expansion *)
local equiv creal_nil :
  CReal(A).main ~ ExpPR(Lift(A)).main :
  ={glob A, arg} /\ arg{1}.`3 = [] ==> ={res}.
proof.
proc; inline Tail.run Lift(A).guess.
rcondf{1} 6; first by auto; call prfp_true; auto.
wp; call (: true); wp; call prfp_eq; auto.
qed.

(* One round of the cascade is one expansion and one extraction *)
local equiv creal_cons :
  CReal(A).main ~ ExpPR(D1(A)).main :
  ={glob A, arg} /\ arg{1}.`3 <> [] ==> ={res}.
proof.
proc; inline Tail.run D1(A).guess.
unroll{1} 6; rcondt{1} 6; first by auto; call prfp_true; auto.
wp; call (: true); wp.
while (={ss} /\ kb0{1} = kb1{2} /\ p0{1}.`1 = p1{2}.`1 /\ p0{1}.`2 = p1{2}.`2).
+ by wp; call prfp_eq; auto.
wp; call prfp_eq; wp; call prfp_eq; auto.
qed.

(* The uniform key block keys the next extraction *)
local equiv expic_d2_eq :
  ExpIC(D1(A)).main ~ PRFR(D2(A)).main :
  ={glob A, arg} /\ 0 < arg{1}.`1 ==> ={res}.
proof.
proc; inline D1(A).guess PRFR(D2(A)).O.f D2(A, PRFR(D2(A)).O).guess.
wp; call (: true); wp; call tail_eq; wp.
rnd; rnd{1}; skip => />; smt(skd_cons dlist_blk_ll).
qed.

(* A fresh extraction output is a uniform seed *)
local equiv d2_creal_eq :
  PRFI(D2(A)).main ~ CReal(A).main :
  ={glob A} /\ arg{2} = (arg{1}.`1, arg{1}.`2, behead arg{1}.`3) ==> ={res}.
proof.
proc; inline PRFI(D2(A)).O.f D2(A, PRFI(D2(A)).O).guess.
rcondt{1} 4; first by auto; smt(mem_empty).
by wp; call (: true); wp; call tail_eq; wp; rnd; auto => />; smt(get_set_sameE).
qed.

(* The ideal block is the ideal expansion output *)
local equiv cideal_expi :
  CIdeal(A).main ~ ExpI(Lift(A)).main : ={glob A, arg} ==> ={res}.
proof. by proc; inline Lift(A).guess; wp; call (: true); auto. qed.

(* The ideal block does not depend on the secrets *)
local equiv cideal_len :
  CIdeal(A).main ~ CIdeal(A).main :
  ={glob A} /\ arg{1}.`1 = arg{2}.`1 ==> ={res}.
proof. proc; call (: true); auto => />; smt(). qed.

(* The cascade output is pseudorandom given a uniform seed *)
lemma tail_bound (u : int) (sstr : kmat) &m (ss : kmat list) :
  0 < u =>
  `| Pr[CReal(A).main(u, sstr, ss) @ &m : res]
     - Pr[CIdeal(A).main(u, sstr, ss) @ &m : res] |
  <= (2 * size ss + 1)%r * eps_prf.
proof.
elim: ss => [|s t ih] hu.
+ have -> : Pr[CReal(A).main(u, sstr, []) @ &m : res]
          = Pr[ExpPR(Lift(A)).main(u, sstr, []) @ &m : res].
  + by byequiv creal_nil.
  have -> : Pr[CIdeal(A).main(u, sstr, []) @ &m : res]
          = Pr[ExpI(Lift(A)).main(u, sstr, []) @ &m : res].
  + by byequiv cideal_expi.
  rewrite (prfp_pseudorandom (Lift(A)) &m (u, sstr, [])).
  have := prf_bound (BPlus(Lift(A))) (u, sstr, []) &m.
  by smt().
have e1 : Pr[CReal(A).main(u, sstr, s :: t) @ &m : res]
        = Pr[ExpPR(D1(A)).main(u, sstr, s :: t) @ &m : res].
+ by byequiv creal_cons.
have e2 : `| Pr[ExpPR(D1(A)).main(u, sstr, s :: t) @ &m : res]
             - Pr[ExpI(D1(A)).main(u, sstr, s :: t) @ &m : res] | <= eps_prf.
+ rewrite (prfp_pseudorandom (D1(A)) &m (u, sstr, s :: t)).
  by apply (prf_bound (BPlus(D1(A))) (u, sstr, s :: t) &m).
have e3 : Pr[ExpI(D1(A)).main(u, sstr, s :: t) @ &m : res]
        = Pr[ExpIC(D1(A)).main(u, sstr, s :: t) @ &m : res].
+ by apply (expi_expic (D1(A)) &m (u, sstr, s :: t)).
have e4 : Pr[ExpIC(D1(A)).main(u, sstr, s :: t) @ &m : res]
        = Pr[PRFR(D2(A)).main(u, sstr, s :: t) @ &m : res].
+ by byequiv expic_d2_eq.
have e5 : `| Pr[PRFR(D2(A)).main(u, sstr, s :: t) @ &m : res]
             - Pr[PRFI(D2(A)).main(u, sstr, s :: t) @ &m : res] | <= eps_prf.
+ by apply (prf_bound (D2(A)) (u, sstr, s :: t) &m).
have e6 : Pr[PRFI(D2(A)).main(u, sstr, s :: t) @ &m : res]
        = Pr[CReal(A).main(u, sstr, t) @ &m : res].
+ by byequiv d2_creal_eq.
have e7 : Pr[CIdeal(A).main(u, sstr, s :: t) @ &m : res]
        = Pr[CIdeal(A).main(u, sstr, t) @ &m : res].
+ by byequiv cideal_len.
have e8 := ih hu.
have : 0 <= size t by apply size_ge0.
by smt().
qed.

(* The initial extraction is one segment keyed query *)
local equiv sk0_seg_real (suf : kmat list) (dm ax : kmat) (sl : int) :
  SK1R(KSc, A).main ~ SegR(BSeg0(A)).main :
  ={glob A} /\ arg{1} = (0, sl, dm :: suf, ax)
  /\ arg{2} = (size nonces, 0, sl, 0, ([], suf, ax)) ==> ={res}.
proof.
proc; inline KSc.kdf BSeg0(A, SegR(BSeg0(A)).O).guess SegR(BSeg0(A)).O.f.
wp; call (: true); wp; call tail_eq; auto => />; smt(setk0 drop1 cats0 cat0s).
qed.

(* A fresh segment answer is a uniform seed *)
local equiv sk0_seg_ideal (suf : kmat list) (ax : kmat) (sl : int) :
  SegI(BSeg0(A)).main ~ CReal(A).main :
  ={glob A} /\ arg{1} = (size nonces, 0, sl, 0, ([], suf, ax))
  /\ arg{2} = (olen, ctx, suf) ==> ={res}.
proof.
proc; inline SegI(BSeg0(A)).O.f BSeg0(A, SegI(BSeg0(A)).O).guess.
rcondt{1} 10; first by auto; rewrite /wfseg.
rcondt{1} 10; first by auto; smt(mem_empty).
wp; call (: true); wp; call tail_eq; wp; rnd; auto => />; smt(get_set_sameE).
qed.

(* The ideal block is the ideal split key answer *)
local equiv cideal_sk1i (j sl : int) (ks : kmat list) (ax : kmat) (suf : kmat list) :
  CIdeal(A).main ~ SK1I(KSc, A).main :
  ={glob A} /\ arg{1} = (olen, ctx, suf) /\ arg{2} = (j, sl, ks, ax) ==> ={res}.
proof. by proc; call (: true); auto. qed.

(* Split key security of the cascade at the initial exchange *)
lemma ksc_splitkey_zero (suf : kmat list) (dm ax : kmat) (sl : int) &m :
  `| Pr[SK1R(KSc, A).main(0, sl, dm :: suf, ax) @ &m : res]
     - Pr[SK1I(KSc, A).main(0, sl, dm :: suf, ax) @ &m : res] |
  <= eps_seg + (2 * size suf + 1)%r * eps_prf.
proof.
have e1 : Pr[SK1R(KSc, A).main(0, sl, dm :: suf, ax) @ &m : res]
        = Pr[SegR(BSeg0(A)).main(size nonces, 0, sl, 0, ([], suf, ax)) @ &m : res].
+ by byequiv (sk0_seg_real suf dm ax sl).
have e2 := seg_bound (BSeg0(A)) (size nonces) 0 sl 0 ([], suf, ax) &m.
have e3 : Pr[SegI(BSeg0(A)).main(size nonces, 0, sl, 0, ([], suf, ax)) @ &m : res]
        = Pr[CReal(A).main(olen, ctx, suf) @ &m : res].
+ by byequiv (sk0_seg_ideal suf ax sl).
have e4 := tail_bound olen ctx &m suf gt0_olen.
have e5 : Pr[CIdeal(A).main(olen, ctx, suf) @ &m : res]
        = Pr[SK1I(KSc, A).main(0, sl, dm :: suf, ax) @ &m : res].
+ by byequiv (cideal_sk1i 0 sl (dm :: suf) ax suf).
smt().
qed.

(* The cascade splits at the round of a later exchange *)
local equiv skp_split_eq (pr sf : kmat list) (dmv axv : kmat) (sn : int) :
  SK1R(KSc, A).main ~ SK1RSplitP(A).main :
  ={glob A} /\ arg{1} = (size pr, sn, pr ++ (dmv :: sf), axv)
  /\ arg{2} = (pr, sf, sn) /\ pr <> [] ==> ={res}.
proof.
proc; inline KSc.kdf.
seq 7 2 : (={glob A} /\ sd{1} = sd{2} /\ pre{2} = pr /\ suf{2} = sf
           /\ drop 1 ks0{1} = behead pr ++ (xj{2} :: sf)).
+ by auto => />; smt(setk_nth0 setk_drop1).
call (: true); wp.
exists* xj{2}; elim* => xv.
call (tail_split (behead pr) sf xv).
by auto => />.
qed.

(* The later extraction is one segment keyed query *)
local equiv skp_seg_real (pr sf : kmat list) (axv : kmat) (sn : int) :
  SK1RSplitP(A).main ~ SegR(BSegP(A)).main :
  ={glob A} /\ arg{1} = (pr, sf, sn)
  /\ arg{2} = (1, 0, sn, size nonces, (pr, sf, axv)) ==> ={res}.
proof.
proc; inline TailSplit.run BSegP(A, SegR(BSegP(A)).O).guess SegR(BSegP(A)).O.f.
wp; call (: true); wp; call tail_eq; wp; call tail_eq; wp; rnd.
by auto => />; smt(size_skd cat0s).
qed.

(* A fresh later segment answer is a uniform seed *)
local equiv skp_seg_ideal (pr sf : kmat list) (axv : kmat) (sn : int) :
  SegI(BSegP(A)).main ~ CReal(A).main :
  ={glob A} /\ arg{1} = (1, 0, sn, size nonces, (pr, sf, axv))
  /\ arg{2} = (olen, ctx, sf) ==> ={res}.
proof.
proc; inline SegI(BSegP(A)).O.f BSegP(A, SegI(BSegP(A)).O).guess.
rcondt{1} 11; first by auto; call tail_true; auto; smt(size_skd).
rcondt{1} 11; first by auto; call tail_true; auto; smt(mem_empty).
wp; call (: true); wp; call tail_eq; wp; rnd; wp.
by call{1} tail_ll; auto => />; smt(get_set_sameE).
qed.

(* Split key security of the cascade at a later exchange *)
lemma ksc_splitkey_pos (pr sf : kmat list) (dmv axv : kmat) (sn : int) &m :
  pr <> [] =>
  `| Pr[SK1R(KSc, A).main(size pr, sn, pr ++ (dmv :: sf), axv) @ &m : res]
     - Pr[SK1I(KSc, A).main(size pr, sn, pr ++ (dmv :: sf), axv) @ &m : res] |
  <= eps_seg + (2 * size sf + 1)%r * eps_prf.
proof.
move=> hpr.
have e1 : Pr[SK1R(KSc, A).main(size pr, sn, pr ++ (dmv :: sf), axv) @ &m : res]
        = Pr[SK1RSplitP(A).main(pr, sf, sn) @ &m : res].
+ by byequiv (skp_split_eq pr sf dmv axv sn).
have e2 : Pr[SK1RSplitP(A).main(pr, sf, sn) @ &m : res]
        = Pr[SegR(BSegP(A)).main(1, 0, sn, size nonces, (pr, sf, axv)) @ &m : res].
+ by byequiv (skp_seg_real pr sf axv sn).
have e3 := seg_bound (BSegP(A)) 1 0 sn (size nonces) (pr, sf, axv) &m.
have e4 : Pr[SegI(BSegP(A)).main(1, 0, sn, size nonces, (pr, sf, axv)) @ &m : res]
        = Pr[CReal(A).main(olen, ctx, sf) @ &m : res].
+ by byequiv (skp_seg_ideal pr sf axv sn).
have e5 := tail_bound olen ctx &m sf gt0_olen.
have e6 : Pr[CIdeal(A).main(olen, ctx, sf) @ &m : res]
        = Pr[SK1I(KSc, A).main(size pr, sn, pr ++ (dmv :: sf), axv) @ &m : res].
+ by byequiv (cideal_sk1i (size pr) sn (pr ++ (dmv :: sf)) axv sf).
smt().
qed.

end section CASCADE.
