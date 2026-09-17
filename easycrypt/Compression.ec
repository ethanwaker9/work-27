require import AllCore Int List Distr DList Dexcepted FMap FSet Real.
require import StdOrder StdBigop Mu_mem FelTactic.
require import IKEv2Core Segment.
require (*--*) BitWord.
import RealOrder Bigreal BRA.

clone import BitWord as CV with op n <- 256
proof gt0_n by done.

type cv = CV.word.

op dcv : cv distr = DWord.dunifin.

op E : kmat -> cv -> cv.

op h (v : cv) (bk : kmat) : cv = E bk v +^ v.

op pcv : real = mu1 dcv witness.

op qq : { int | 0 <= qq } as ge0_qq.

(* Every chaining value has the same sampling probability *)
lemma mu1_dcv (x : cv) : mu1 dcv x = pcv.
proof. by rewrite /pcv /dcv; apply DWord.dunifin_uni; apply DWord.dunifin_fu. qed.

(* Every chaining value is in the support *)
lemma dcv_fu (x : cv) : x \in dcv.
proof. by rewrite /dcv; apply DWord.dunifin_fu. qed.

(* The chaining value distribution is lossless *)
lemma dcv_ll : is_lossless dcv.
proof. by apply DWord.dunifin_ll. qed.

(* Masking by a fixed value is an involution on chaining values *)
lemma xor_inv (a b : cv) : (a +^ b) +^ b = a.
proof. by rewrite -xorwA xorwK xorw0. qed.

(* A used image set is hit with probability at most its size *)
lemma mu_hit (s : cv fset) : mu dcv (mem s) <= (card s)%r * pcv.
proof. by apply mu_mem_le => x _; rewrite mu1_dcv. qed.

(* Adding one element grows a set by at most one *)
lemma fcard_add (s : cv fset) (r : cv) : card (s `|` fset1 r) <= card s + 1.
proof. by rewrite fcardU fcard1; smt(fcard_ge0). qed.

module type RkaO = { proc f (x y : kmat, v : cv) : cv }.

module type RkaA (O : RkaO) = { proc guess () : bool }.

module RkaPrfR (A : RkaA) = {
  var xx : kmat

  module O : RkaO = {
    proc f (x y : kmat, v : cv) : cv = { return h v (ins x xx y); }
  }

  proc main (asz : int) : bool = {
    var b;
    xx <$ dlist dblk asz;
    b <@ A(O).guess();
    return b;
  }
}.

module RkaPrfI (A : RkaA) = {
  var mp : (kmat * kmat * cv, cv) fmap

  module O : RkaO = {
    proc f (x y : kmat, v : cv) : cv = {
      var r;
      if ((x, y, v) \notin mp) { r <$ dcv; mp.[(x, y, v)] <- r; }
      return oget mp.[(x, y, v)];
    }
  }

  proc main (asz : int) : bool = {
    var b;
    mp <- empty;
    b <@ A(O).guess();
    return b;
  }
}.

module RkaPrpR (A : RkaA) = {
  var xx : kmat

  module O : RkaO = {
    proc f (x y : kmat, v : cv) : cv = { return E (ins x xx y) v; }
  }

  proc main (asz : int) : bool = {
    var b;
    xx <$ dlist dblk asz;
    b <@ A(O).guess();
    return b;
  }
}.

module Flag = { var bad : bool }.

module RkaPrpI (A : RkaA) = {
  var mp  : (kmat * kmat * cv, cv) fmap
  var img : (kmat * kmat, cv fset) fmap
  var qs  : int

  module O : RkaO = {
    proc f (x y : kmat, v : cv) : cv = {
      var r, s;
      if ((x, y, v) \notin mp) {
        s <- odflt fset0 img.[(x, y)];
        r <$ dcv;
        Flag.bad <- Flag.bad \/ (r \in s);
        r <$ (if r \in s /\ card s < qq then dcv \ (mem s) else dunit r);
        mp.[(x, y, v)] <- r;
        img.[(x, y)] <- s `|` fset1 r;
      }
      qs <- qs + 1;
      return oget mp.[(x, y, v)];
    }
  }

  proc main (asz : int) : bool = {
    var b;
    mp <- empty; img <- empty; Flag.bad <- false; qs <- 0;
    b <@ A(O).guess();
    return b;
  }
}.

module RkaPrpB (A : RkaA) = {
  var mp  : (kmat * kmat * cv, cv) fmap
  var img : (kmat * kmat, cv fset) fmap
  var qs  : int

  module O : RkaO = {
    proc f (x y : kmat, v : cv) : cv = {
      var r, s;
      if ((x, y, v) \notin mp) {
        s <- odflt fset0 img.[(x, y)];
        r <$ dcv;
        Flag.bad <- Flag.bad \/ (r \in s);
        mp.[(x, y, v)] <- r;
        img.[(x, y)] <- s `|` fset1 r;
      }
      qs <- qs + 1;
      return oget mp.[(x, y, v)];
    }
  }

  proc main (asz : int) : bool = {
    var b;
    mp <- empty; img <- empty; Flag.bad <- false; qs <- 0;
    b <@ A(O).guess();
    return b;
  }
}.

module RkaPrfM (A : RkaA) = {
  var mp : (kmat * kmat * cv, cv) fmap

  module O : RkaO = {
    proc f (x y : kmat, v : cv) : cv = {
      var r;
      if ((x, y, v) \notin mp) { r <$ dcv; mp.[(x, y, v)] <- r +^ v; }
      return oget mp.[(x, y, v)];
    }
  }

  proc main (asz : int) : bool = {
    var b;
    mp <- empty;
    b <@ A(O).guess();
    return b;
  }
}.

module BDm (A : RkaA) (O : RkaO) = {
  module Op : RkaO = {
    proc f (x y : kmat, v : cv) : cv = {
      var r;
      r <@ O.f(x, y, v);
      return r +^ v;
    }
  }

  proc guess () : bool = {
    var b;
    b <@ A(Op).guess();
    return b;
  }
}.

section SWITCHING.

declare module A <: RkaA {-RkaPrfR, -RkaPrfI, -RkaPrfM, -RkaPrpR, -RkaPrpI, -RkaPrpB, -Flag}.

declare axiom A_ll (O <: RkaO{-A}) : islossless O.f => islossless A(O).guess.

declare axiom qq_small : qq%r * pcv < 1%r.

declare axiom A_qbound :
  hoare [ BDm(A, RkaPrpB(BDm(A)).O).guess :
          RkaPrpB.qs = 0 ==> RkaPrpB.qs <= qq ].

(* Davies Meyer answers are the cipher outputs masked by the plaintext *)
local equiv dm_real_eq :
  RkaPrfR(A).main ~ RkaPrpR(BDm(A)).main : ={glob A, arg} ==> ={res}.
proof.
proc; inline BDm(A, RkaPrpR(BDm(A)).O).guess; wp.
call (: RkaPrfR.xx{1} = RkaPrpR.xx{2}).
+ by proc; inline RkaPrpR(BDm(A)).O.f; auto => />; rewrite /h.
by auto.
qed.

(* The masked table and the plain table answer alike *)
local equiv prpb_prfm_eq :
  RkaPrpB(BDm(A)).main ~ RkaPrfM(A).main : ={glob A, arg} ==> ={res}.
proof.
proc; inline BDm(A, RkaPrpB(BDm(A)).O).guess; wp.
call (: (forall k, (k \in RkaPrfM.mp{2}) = (k \in RkaPrpB.mp{1}))
        /\ (forall a b c, (a, b, c) \in RkaPrpB.mp{1} =>
              oget RkaPrfM.mp{2}.[(a, b, c)]
              = oget RkaPrpB.mp{1}.[(a, b, c)] +^ c)).
+ proc; inline RkaPrpB(BDm(A)).O.f.
  sp 3 0; if.
  + smt().
  + by auto => /> *; smt(@FMap).
  by auto => /> *; smt().
by auto => />; smt(mem_empty).
qed.

(* Masking a uniform table entry keeps it uniform *)
local equiv prfm_prfi_eq :
  RkaPrfM(A).main ~ RkaPrfI(A).main : ={glob A, arg} ==> ={res}.
proof.
proc.
call (: RkaPrfM.mp{1} = RkaPrfI.mp{2}).
+ proc; if; 1: by move=> &1 &2 />.
  + by wp; rnd (fun (r : cv) => r +^ v{1}); auto => /> *;
        smt(xor_inv mu1_dcv dcv_fu).
  by auto.
by auto.
qed.

(* The reduction turns the random function family into the ideal game *)
local lemma prpb_prfi &m (asz : int) :
  Pr[RkaPrpB(BDm(A)).main(asz) @ &m : res] = Pr[RkaPrfI(A).main(asz) @ &m : res].
proof.
have -> : Pr[RkaPrpB(BDm(A)).main(asz) @ &m : res]
        = Pr[RkaPrfM(A).main(asz) @ &m : res].
+ by byequiv prpb_prfm_eq.
by byequiv prfm_prfi_eq.
qed.

(* A small image set leaves room for a fresh value *)
lemma excepted_ok (s : cv fset) : card s < qq => is_lossless (dcv \ (mem s)).
proof.
move=> hs; apply dexcepted_ll; first by apply dcv_ll.
have h1 := mu_hit s.
have h2 : (card s)%r * pcv <= qq%r * pcv.
+ by apply ler_wpmul2r; [rewrite /pcv; apply ge0_mu | smt()].
have := qq_small.
smt().
qed.

(* The permutation game and the flagged game agree until a collision *)
local lemma prpi_prpb &m (asz : int) :
  `| Pr[RkaPrpI(BDm(A)).main(asz) @ &m : res]
     - Pr[RkaPrpB(BDm(A)).main(asz) @ &m : res] |
  <= Pr[RkaPrpB(BDm(A)).main(asz) @ &m : Flag.bad].
proof.
byequiv: Flag.bad => //=; 2: smt().
proc; inline BDm(A, RkaPrpI(BDm(A)).O).guess BDm(A, RkaPrpB(BDm(A)).O).guess.
wp.
call (_: Flag.bad,
         ! Flag.bad{2} /\ ={Flag.bad}
         /\ ={mp, img, qs}(RkaPrpI, RkaPrpB),
         ={Flag.bad}).
+ exact A_ll.
+ proc; inline RkaPrpI(BDm(A)).O.f RkaPrpB(BDm(A)).O.f.
  sp 3 3; if; 1: by auto.
  + seq 3 3 : (={x, y, v, x0, y0, v0, s, r0} /\ ={mp, img, qs}(RkaPrpI, RkaPrpB)
               /\ ={Flag.bad}
               /\ Flag.bad{2} = (r0{2} \in s{2})).
    + by auto => /> /#.
    wp; rnd{1}; auto => /> *; smt(excepted_ok dunit_ll supp_dunit).
  by auto => /> /#.
+ move=> &2 bd; proc; inline*; sp; if; last by auto.
  by auto => /> *; smt(excepted_ok dcv_ll dunit_ll).
+ move=> &1; proc; inline*; sp; if; last by auto.
  by auto => /> *; smt(dcv_ll).
by auto => /> /#.
qed.

(* A collision happens rarely on a bounded number of queries *)
local lemma pr_bad_bounded &m (asz : int) :
  Pr[RkaPrpB(BDm(A)).main(asz) @ &m : RkaPrpB.qs <= qq /\ Flag.bad]
  <= (qq * (qq - 1))%r / 2%r * pcv.
proof.
fel 4 RkaPrpB.qs (fun i => i%r * pcv) qq Flag.bad
    [BDm(A, RkaPrpB(BDm(A)).O).Op.f : (RkaPrpB.qs < qq)]
    (forall xy, card (odflt fset0 RkaPrpB.img.[xy]) <= RkaPrpB.qs).
+ by rewrite -Bigreal.BRA.mulr_suml Bigreal.sumidE 1:ge0_qq.
+ by move=> &m0; smt().
+ by auto => />; move=> *; rewrite emptyE /= fcards0.
+ proc; if; last by hoare; auto => />; smt(ge0_mu).
  sp 1; wp; rnd (mem s); skip => /> &hr h1 h2 h3 h4 h5.
  apply (ler_trans ((card (odflt fset0 RkaPrpB.img{hr}.[(x{hr}, y{hr})]))%r * pcv)).
  + by apply mu_hit.
  apply ler_wpmul2r; first by rewrite /pcv; apply ge0_mu.
  by have := h4 (x{hr}, y{hr}); smt().
+ by move=> c; proc; if; auto => />; smt(fcard_add get_setE).
by move=> b c; proc; if; auto => /> /#.
qed.

(* A bounded adversary never exceeds the query counter *)
local lemma pr_bad_eq &m (asz : int) :
  Pr[RkaPrpB(BDm(A)).main(asz) @ &m : Flag.bad]
  = Pr[RkaPrpB(BDm(A)).main(asz) @ &m : RkaPrpB.qs <= qq /\ Flag.bad].
proof.
byequiv (_: ={glob A, arg} ==> ={Flag.bad, RkaPrpB.qs} /\ RkaPrpB.qs{2} <= qq) => //=.
conseq (_: _ ==> ={Flag.bad, RkaPrpB.qs}) _ (_: _ ==> RkaPrpB.qs <= qq) => //=;
  2: by sim.
by proc; call A_qbound; auto.
qed.

(* Related key pseudorandomness of the Davies Meyer construction *)
lemma dm_rka_prf (asz : int) &m :
  `| Pr[RkaPrfR(A).main(asz) @ &m : res]
     - Pr[RkaPrfI(A).main(asz) @ &m : res] |
  <= `| Pr[RkaPrpR(BDm(A)).main(asz) @ &m : res]
        - Pr[RkaPrpI(BDm(A)).main(asz) @ &m : res] |
     + (qq * (qq - 1))%r / 2%r * pcv.
proof.
have e1 : Pr[RkaPrfR(A).main(asz) @ &m : res]
        = Pr[RkaPrpR(BDm(A)).main(asz) @ &m : res].
+ by byequiv dm_real_eq.
have e2 := prpb_prfi &m asz.
have e3 := prpi_prpb &m asz.
have e4 := pr_bad_bounded &m asz.
have e5 := pr_bad_eq &m asz.
smt().
qed.

end section SWITCHING.

op iv : cv.

op kin : kmat -> kmat.

op kout : kmat -> kmat.

op bpre : kmat -> kmat.

op bsuf : kmat -> kmat -> kmat.

op prefixb : kmat -> kmat list.

op suffb : kmat -> kmat -> kmat list.

op outblock : cv -> kmat.

op mdc (v : cv) (bs : kmat list) : cv =
  with bs = []     => v
  with bs = b :: t => mdc (h v b) t.

op hmacseg (k x y : kmat) (xx : kmat) : cv =
  mdc (h iv (kout k))
      [outblock (mdc (h (mdc (h iv (kin k)) (prefixb x))
                        (ins (bpre x) xx (bsuf x y)))
                     (suffb x y))].

(* Merkle Damgard chaining splits along message blocks *)
lemma mdc_cat (v : cv) (b1 b2 : kmat list) :
  mdc v (b1 ++ b2) = mdc (mdc v b1) b2.
proof. by elim: b1 v => //= b t ih v; apply ih. qed.

module type HSegO = { proc f (k x y : kmat) : cv }.

module type HSegA (O : HSegO) = { proc guess () : bool }.

module HSegR (A : HSegA) = {
  var xx : kmat

  module O : HSegO = {
    proc f (k x y : kmat) : cv = { return hmacseg k x y xx; }
  }

  proc main (asz : int) : bool = {
    var b;
    xx <$ dlist dblk asz;
    b <@ A(O).guess();
    return b;
  }
}.

module HSegP (A : HSegA) = {
  var mp : (kmat * kmat * cv, cv) fmap

  module O : HSegO = {
    proc f (k x y : kmat) : cv = {
      var u, w;
      u <- mdc (h iv (kin k)) (prefixb x);
      if ((bpre x, bsuf x y, u) \notin mp) {
        w <$ dcv;
        mp.[(bpre x, bsuf x y, u)] <- w;
      }
      w <- oget mp.[(bpre x, bsuf x y, u)];
      return mdc (h iv (kout k)) [outblock (mdc w (suffb x y))];
    }
  }

  proc main (asz : int) : bool = {
    var b;
    mp <- empty;
    b <@ A(O).guess();
    return b;
  }
}.

module HSegI (A : HSegA) = {
  var mp : (kmat * kmat * kmat, cv) fmap

  module O : HSegO = {
    proc f (k x y : kmat) : cv = {
      var r;
      if ((k, x, y) \notin mp) { r <$ dcv; mp.[(k, x, y)] <- r; }
      return oget mp.[(k, x, y)];
    }
  }

  proc main (asz : int) : bool = {
    var b;
    mp <- empty;
    b <@ A(O).guess();
    return b;
  }
}.

module BHmac (A : HSegA) (O : RkaO) = {
  module Op : HSegO = {
    proc f (k x y : kmat) : cv = {
      var u, w;
      u <- mdc (h iv (kin k)) (prefixb x);
      w <@ O.f(bpre x, bsuf x y, u);
      return mdc (h iv (kout k)) [outblock (mdc w (suffb x y))];
    }
  }

  proc guess () : bool = {
    var b;
    b <@ A(Op).guess();
    return b;
  }
}.

section HMACSWAP.

declare module A <: HSegA {-RkaPrfR, -RkaPrfI, -HSegR, -HSegP, -HSegI}.

(* The inner compression on the secret block is a related key query *)
local equiv hmac_real_eq :
  HSegR(A).main ~ RkaPrfR(BHmac(A)).main : ={glob A, arg} ==> ={res}.
proof.
proc; inline BHmac(A, RkaPrfR(BHmac(A)).O).guess; wp.
call (: HSegR.xx{1} = RkaPrfR.xx{2}).
+ by proc; inline RkaPrfR(BHmac(A)).O.f; auto => />; rewrite /hmacseg.
by auto.
qed.

(* Replacing that compression gives a random inner value *)
local equiv hmac_punct_eq :
  RkaPrfI(BHmac(A)).main ~ HSegP(A).main : ={glob A, arg} ==> ={res}.
proof.
proc; inline BHmac(A, RkaPrfI(BHmac(A)).O).guess; wp.
call (: RkaPrfI.mp{1} = HSegP.mp{2}).
+ by proc; inline RkaPrfI(BHmac(A)).O.f; sp; if; auto.
by auto.
qed.

(* The inner step of the segment keyed swap proof for HMAC *)
lemma hmac_inner (asz : int) &m :
  `| Pr[HSegR(A).main(asz) @ &m : res] - Pr[HSegP(A).main(asz) @ &m : res] |
  = `| Pr[RkaPrfR(BHmac(A)).main(asz) @ &m : res]
       - Pr[RkaPrfI(BHmac(A)).main(asz) @ &m : res] |.
proof.
have -> : Pr[HSegR(A).main(asz) @ &m : res]
        = Pr[RkaPrfR(BHmac(A)).main(asz) @ &m : res].
+ by byequiv hmac_real_eq.
have -> : Pr[HSegP(A).main(asz) @ &m : res]
        = Pr[RkaPrfI(BHmac(A)).main(asz) @ &m : res].
+ by rewrite eq_sym; byequiv hmac_punct_eq.
done.
qed.

(* The remaining steps of the segment keyed swap proof for HMAC *)
lemma hmac_segment (asz : int) (eps_out eps_rka : real) &m :
  `| Pr[HSegP(A).main(asz) @ &m : res] - Pr[HSegI(A).main(asz) @ &m : res] |
  <= eps_out =>
  `| Pr[RkaPrfR(BHmac(A)).main(asz) @ &m : res]
     - Pr[RkaPrfI(BHmac(A)).main(asz) @ &m : res] | <= eps_rka =>
  `| Pr[HSegR(A).main(asz) @ &m : res] - Pr[HSegI(A).main(asz) @ &m : res] |
  <= eps_rka + eps_out.
proof.
move=> h1 h2; have := hmac_inner asz &m.
smt().
qed.

end section HMACSWAP.
