require import AllCore Int IntDiv List Distr DList FMap FSet Real.
require import StdOrder StdBigop.
import RealOrder.

type blk.

op [lossless uniform full] dblk : blk distr.

type kmat = blk list.

type msg = int * kmat.

op F : kmat -> msg -> blk.

op olen : { int | 0 < olen } as gt0_olen.

op olen0 : { int | 0 < olen0 } as gt0_olen0.

op ctx : kmat.

op lb : kmat.

op lb0 : kmat.

op nonces : kmat.

op spis : kmat.

op nadd : { int | 0 <= nadd } as ge0_nadd.

op skd (kb : kmat) : kmat = take 1 (kb ++ [witness]).

op pblk : real = mu1 dblk witness.

type pin = int * kmat * kmat list.

module type DistA = { proc guess (r : kmat) : bool }.

module type PDistA = { proc guess (p : pin, r : kmat) : bool }.

module Lift (A : DistA) : PDistA = {
  proc guess (p : pin, r : kmat) : bool = {
    var b;
    b <@ A.guess(r);
    return b;
  }
}.

module type PRFO = { proc f (m : msg) : blk }.

module type PRFA (O : PRFO) = { proc guess (p : pin) : bool }.

module PRFR (A : PRFA) = {
  var k : blk

  module O : PRFO = {
    proc f (m : msg) : blk = { return F [k] m; }
  }

  proc main (p : pin) : bool = {
    var b;
    k <$ dblk;
    b <@ A(O).guess(p);
    return b;
  }
}.

module PRFI (A : PRFA) = {
  var mp : (msg, blk) fmap

  module O : PRFO = {
    proc f (m : msg) : blk = {
      var r;
      if (m \notin mp) { r <$ dblk; mp.[m] <- r; }
      return oget mp.[m];
    }
  }

  proc main (p : pin) : bool = {
    var b;
    mp <- empty;
    b <@ A(O).guess(p);
    return b;
  }
}.

module type SegO = { proc f (k : kmat, l : int, x : kmat, y : kmat) : blk }.

type sin = kmat list * kmat list * kmat.

module type SegA (O : SegO) = { proc guess (q : sin) : bool }.

op wfseg (nk np nq : int) (k x y : kmat) : bool =
  size k = nk /\ size x = np /\ size y = nq.

module SegR (A : SegA) = {
  var xx : kmat
  var nk, np, nq : int

  module O : SegO = {
    proc f (k : kmat, l : int, x : kmat, y : kmat) : blk = {
      return if wfseg nk np nq k x y then F k (l, x ++ xx ++ y) else witness;
    }
  }

  proc main (ak ap asz aq : int, q : sin) : bool = {
    var b;
    nk <- ak; np <- ap; nq <- aq;
    xx <$ dlist dblk asz;
    b <@ A(O).guess(q);
    return b;
  }
}.

module SegI (A : SegA) = {
  var mp : (kmat * int * kmat * kmat, blk) fmap
  var nk, np, nq : int

  module O : SegO = {
    proc f (k : kmat, l : int, x : kmat, y : kmat) : blk = {
      var r;
      if (wfseg nk np nq k x y) {
        if ((k, l, x, y) \notin mp) { r <$ dblk; mp.[(k, l, x, y)] <- r; }
      }
      return if wfseg nk np nq k x y then oget mp.[(k, l, x, y)] else witness;
    }
  }

  proc main (ak ap asz aq : int, q : sin) : bool = {
    var b;
    nk <- ak; np <- ap; nq <- aq;
    mp <- empty;
    b <@ A(O).guess(q);
    return b;
  }
}.

type hnd = kmat list * kmat.

module type MPRFO = { proc f (h : hnd, m : msg) : blk }.

module type MPRFA (O : MPRFO) = { proc guess () : bool }.

module MPRFR (A : MPRFA) = {
  var ks : (hnd, blk) fmap

  module O : MPRFO = {
    proc f (h : hnd, m : msg) : blk = {
      var k;
      if (h \notin ks) { k <$ dblk; ks.[h] <- k; }
      return F [oget ks.[h]] m;
    }
  }

  proc main () : bool = {
    var b;
    ks <- empty;
    b <@ A(O).guess();
    return b;
  }
}.

module MPRFI (A : MPRFA) = {
  var mp : (hnd * msg, blk) fmap

  module O : MPRFO = {
    proc f (h : hnd, m : msg) : blk = {
      var r;
      if ((h, m) \notin mp) { r <$ dblk; mp.[(h, m)] <- r; }
      return oget mp.[(h, m)];
    }
  }

  proc main () : bool = {
    var b;
    mp <- empty;
    b <@ A(O).guess();
    return b;
  }
}.

module type Schedule = { proc kdf (ks : kmat list, aux : kmat) : kmat }.

module type SKO = { proc f (ks : kmat list, aux : kmat) : kmat }.

module type SKA (O : SKO) = { proc guess () : bool }.

op setk (j : int) (x : kmat) (ks : kmat list) : kmat list =
  take j ks ++ (x :: drop (j + 1) ks).

module SKPar = { var j : int

  var ks : kmat list

  var aux : kmat }.

module SKR (S : Schedule, A : SKA) = {
  var xj : kmat
  var jj : int

  module O : SKO = {
    proc f (ks : kmat list, aux : kmat) : kmat = {
      var r;
      r <@ S.kdf (setk jj xj ks, aux);
      return r;
    }
  }

  proc main (j sl : int) : bool = {
    var b;
    jj <- j;
    SKPar.j <- j;
    xj <$ dlist dblk sl;
    b <@ A(O).guess();
    return b;
  }
}.

module SKI (S : Schedule, A : SKA) = {
  var mp : (kmat list * kmat, kmat) fmap

  module O : SKO = {
    proc f (ks : kmat list, aux : kmat) : kmat = {
      var r;
      if ((ks, aux) \notin mp) { r <$ dlist dblk olen; mp.[(ks, aux)] <- r; }
      return oget mp.[(ks, aux)];
    }
  }

  proc main (j sl : int) : bool = {
    var b;
    SKPar.j <- j;
    mp <- empty;
    b <@ A(O).guess();
    return b;
  }
}.

module SK1R (S : Schedule, A : DistA) = {
  proc main (j : int, sl : int, ks : kmat list, aux : kmat) : bool = {
    var xj, kb, b;
    SKPar.j <- j;
    SKPar.ks <- ks;
    SKPar.aux <- aux;
    xj <$ dlist dblk sl;
    kb <@ S.kdf(setk j xj ks, aux);
    b <@ A.guess(kb);
    return b;
  }
}.

module SK1I (S : Schedule, A : DistA) = {
  proc main (j : int, sl : int, ks : kmat list, aux : kmat) : bool = {
    var kb, b;
    SKPar.j <- j;
    SKPar.ks <- ks;
    SKPar.aux <- aux;
    kb <$ dlist dblk olen;
    b <@ A.guess(kb);
    return b;
  }
}.

module BOne (A : DistA) (O : SKO) = {
  proc guess () : bool = {
    var kb, b;
    kb <@ O.f(SKPar.ks, SKPar.aux);
    b <@ A.guess(kb);
    return b;
  }
}.

(* The block distribution is lossless uniform and full *)
lemma dblk_props : is_lossless dblk /\ is_uniform dblk /\ is_full dblk.
proof. by rewrite dblk_ll dblk_uni dblk_fu. qed.

(* Fixed size block lists are sampled losslessly *)
lemma dlist_blk_ll (n : int) : 0 <= n => is_lossless (dlist dblk n).
proof. by move=> hn; apply/dlist_ll/dblk_ll. qed.

(* Sampled block lists have the requested size *)
lemma dlist_blk_size (n : int) (l : kmat) :
  0 <= n => l \in dlist dblk n => size l = n.
proof. by move=> hn /(supp_dlist dblk n l hn) [] ->. qed.

(* Writing one component preserves the list length *)
lemma size_setk (j : int) (x : kmat) (ks : kmat list) :
  0 <= j < size ks => size (setk j x ks) = size ks.
proof.
move=> h; rewrite /setk size_cat /= size_takel 1:/# size_drop 1:/#.
by smt(size_ge0).
qed.

(* Writing one component stores it at that index *)
lemma nth_setk (j : int) (x : kmat) (ks : kmat list) :
  0 <= j < size ks => nth witness (setk j x ks) j = x.
proof.
move=> h.
have hs : size (take j ks) = j by rewrite size_takel /#.
rewrite /setk nth_cat hs.
have -> : (j < j) = false by smt().
have -> : j - j = 0 by ring.
by simplify.
qed.

(* Writing one component leaves the others intact *)
lemma nth_setk_neq (j i : int) (x : kmat) (ks : kmat list) :
  0 <= j < size ks => 0 <= i < size ks => i <> j =>
  nth witness (setk j x ks) i = nth witness ks i.
proof.
move=> hj hi hne.
have hs : size (take j ks) = j by rewrite size_takel /#.
rewrite /setk nth_cat hs.
case: (i < j) => [hlt|hge].
+ by rewrite nth_take /#.
have -> : i - j = (i - j - 1) + 1 by ring.
by simplify; rewrite nth_drop 1:/# 1:/# /#.
qed.

(* Writing at the boundary of a split list is concatenation *)
lemma setk_cat (pre suf : kmat list) (dm x : kmat) :
  setk (size pre) x (pre ++ (dm :: suf)) = pre ++ (x :: suf).
proof.
rewrite /setk (take_size_cat (size pre)) //.
have -> : drop (size pre + 1) (pre ++ (dm :: suf)) = suf.
+ have -> : pre ++ (dm :: suf) = (pre ++ [dm]) ++ suf by rewrite -catA cat1s.
  by apply (drop_size_cat (size pre + 1)); rewrite size_cat.
done.
qed.

(* Every block has the same sampling probability *)
lemma mu1_dblk (x : blk) : mu1 dblk x = pblk.
proof. by rewrite /pblk; apply dblk_uni; apply dblk_fu. qed.

(* The chaining key is one block long *)
lemma size_skd (kb : kmat) : size (skd kb) = 1.
proof. rewrite /skd size_take // size_cat /=; smt(size_ge0). qed.

(* Dropping one element is taking the tail *)
lemma drop1 (s : kmat list) : drop 1 s = behead s.
proof. by case: s => [|x l] //=; rewrite drop0. qed.

section SINGLECHALLENGE.

declare module S <: Schedule {-SKR, -SKI, -SKPar}.

declare module A <: DistA {-SKR, -SKI, -SKPar, -S}.

(* One query suffices for the real split key game *)
lemma sk1_real_eq :
  equiv [ SK1R(S, A).main ~ SKR(S, BOne(A)).main :
          ={glob S, glob A} /\ arg{1}.`1 = arg{2}.`1 /\ arg{1}.`2 = arg{2}.`2
          /\ SKPar.ks{2} = arg{1}.`3 /\ SKPar.aux{2} = arg{1}.`4 ==> ={res} ].
proof.
proc; inline SKR(S, BOne(A)).O.f BOne(A, SKR(S, BOne(A)).O).guess.
by wp; call (: true); wp; call (: true); wp; rnd; auto.
qed.

(* One query suffices for the ideal split key game *)
lemma sk1_ideal_eq :
  equiv [ SK1I(S, A).main ~ SKI(S, BOne(A)).main :
          ={glob A} /\ arg{1}.`1 = arg{2}.`1 /\ arg{1}.`2 = arg{2}.`2 ==> ={res} ].
proof.
proc; inline SKI(S, BOne(A)).O.f BOne(A, SKI(S, BOne(A)).O).guess.
rcondt{2} 5; first by auto; smt(mem_empty).
by wp; call (: true); wp; rnd; auto => />; smt(get_set_sameE).
qed.

end section SINGLECHALLENGE.
