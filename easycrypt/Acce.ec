require import AllCore Int IntDiv List Distr DList FMap FSet Real.
require import StdOrder StdBigop Mu_mem FelTactic.
require import IKEv2Core Expansion Segment Cascade Spks.
require (*--*) PlugAndPray.
import RealOrder Bigreal BRA.

type role = [ RoleI | RoleR ].

type pkey.

type skey.

type sgn.

type ekey.

type dkey.

type ctxt.

op dkeys : { (skey * pkey) distr | is_lossless dkeys } as dkeys_ll.

op sign : skey -> kmat -> sgn.

op vrfy : pkey -> kmat -> sgn -> bool.

op kemkg : { (dkey * ekey) distr | is_lossless kemkg } as kemkg_ll.

op kemenc : ekey -> (ctxt * blk) distr.

op kemdec : dkey -> ctxt -> blk.

op aenc : kmat -> int -> kmat -> kmat -> kmat.

op adec : kmat -> int -> kmat -> kmat -> kmat option.

op nP : { int | 0 < nP } as gt0_nP.

op nS : { int | 0 < nS } as gt0_nS.

op mkI0 : blk -> blk -> ekey -> kmat.

op mkR0 : blk -> blk -> ctxt -> kmat.

op mkKEi : ekey -> kmat.

op mkKEr : ctxt -> kmat.

op pI0 : kmat -> (blk * blk * ekey) option.

op pR0 : kmat -> (blk * blk * ctxt) option.

op pKEi : kmat -> ekey option.

op pKEr : kmat -> ctxt option.

op idpay : int -> kmat.

op iachain : kmat -> kmat.

op authmsg (t n idp ia : kmat) : kmat = t ++ (n ++ (idp ++ ia)).

op labQ : bool.

type state = {
  srl   : role;
  spid  : int;
  sacc  : int;
  sstep : int;
  sni   : blk;
  snr   : blk;
  sspi  : blk;
  sspr  : blk;
  sdk   : dkey;
  sek   : ekey;
  sshs  : blk list;
  slab  : bool list;
  ssid  : kmat;
  skb   : kmat;
  sbit  : bool;
  ste   : int;
  std   : int
}.

op st0 (r : role) (v : int) : state =
  {| srl = r; spid = v; sacc = 0; sstep = 0; sni = witness; snr = witness;
     sspi = witness; sspr = witness; sdk = witness; sek = witness;
     sshs = []; slab = []; ssid = []; skb = []; sbit = false;
     ste = 0; std = 0 |}.

op quantum (s : state) : bool = has (fun (b : bool) => b) s.`slab.

op partner (s t : state) (u v : int) : bool =
  s.`ssid = t.`ssid /\ s.`srl <> t.`srl /\ s.`spid = v /\ t.`spid = u.

op fresh (s : state) (cor : int fset) : bool =
  ! (s.`spid \in cor) /\ quantum s.

op harvestable (s : state) (j : int) : bool =
  s.`sacc <> 0 /\ 0 <= j < size s.`slab /\ ! nth false s.`slab j.

module type ACCEO = {
  proc newsess (u v : int, r : role) : int
  proc send (u i : int, m : kmat) : kmat
  proc corrupt (u : int) : skey
  proc harv (u i j : int) : blk
  proc enc (u i : int, m0 m1 ad : kmat) : kmat
  proc dec (u i : int, c ad : kmat) : kmat option
}.

module type ACCEA (O : ACCEO) = {
  proc guess () : int * int * bool
}.

module Acce (S : Schedule, A : ACCEA) = {
  var sks   : (int, skey) fmap
  var pks   : (int, pkey) fmap
  var cor   : int fset
  var st    : (int * int, state) fmap
  var cnt   : (int, int) fmap
  var nlist : blk list
  var tst   : int * int

  module O : ACCEO = {
    proc newsess (u v : int, r : role) : int = {
      var i, ni, spv, dk, ek;
      i <- odflt 0 cnt.[u];
      if (size nlist < nP * nS) {
        ni <$ dblk;
        nlist <- ni :: nlist;
        spv <$ dblk;
        (dk, ek) <$ kemkg;
        if (0 <= u < nP /\ 0 <= v < nP /\ i < nS) {
          cnt.[u] <- i + 1;
          st.[(u, i)] <-
            {| (st0 r v) with sni = ni; sspi = spv; sdk = dk; sek = ek |};
        }
      }
      return i;
    }

    proc send (u i : int, m : kmat) : kmat = {
      var s, out, c, ks, kb, e, dk, ek, t0, t1, t2, t3;
      out <- [];
      if ((u, i) \in st) {
        s <- oget st.[(u, i)];
        if (s.`sacc = 0 /\ s.`srl = RoleI /\ s.`sstep = 0) {
          out <- mkI0 s.`sspi s.`sni s.`sek;
          st.[(u, i)] <- {| s with sstep = 1; ssid = out |};
        }
        if (s.`sacc = 0 /\ s.`srl = RoleR /\ s.`sstep = 0) {
          t0 <- pI0 m;
          if (t0 <> None) {
            (c, ks) <$ kemenc (oget t0).`3;
            out <- mkR0 s.`sspr s.`sni c;
            st.[(u, i)] <-
              {| s with sstep = 1; snr = (oget t0).`2;
                        sshs = [ks]; slab = [labQ]; ssid = m ++ out |};
          }
        }
        if (s.`sacc = 0 /\ s.`srl = RoleI /\ s.`sstep = 1) {
          t1 <- pR0 m;
          if (t1 <> None) {
            (dk, ek) <$ kemkg;
            out <- mkKEi ek;
            st.[(u, i)] <-
              {| s with sstep = 2; snr = (oget t1).`2;
                        sshs = [kemdec s.`sdk (oget t1).`3];
                        slab = [labQ]; sdk = dk;
                        ssid = s.`ssid ++ (m ++ out) |};
          }
        }
        if (s.`sacc = 0 /\ s.`srl = RoleR /\ s.`sstep = 1) {
          t2 <- pKEi m;
          if (t2 <> None) {
            (c, ks) <$ kemenc (oget t2);
            out <- mkKEr c;
            st.[(u, i)] <-
              {| s with sstep = 2; sshs = s.`sshs ++ [ks];
                        slab = s.`slab ++ [labQ];
                        ssid = s.`ssid ++ (m ++ out) |};
          }
        }
        if (s.`sacc = 0 /\ s.`sstep = 2) {
          t3 <- pKEr m;
          if (s.`srl = RoleI /\ t3 <> None) {
            e <- s.`sshs ++ [kemdec s.`sdk (oget t3)];
            st.[(u, i)] <-
              {| s with sstep = 3; sshs = e;
                        slab = s.`slab ++ [labQ];
                        ssid = s.`ssid ++ m |};
          } else {
            st.[(u, i)] <- {| s with sstep = 3 |};
          }
        }
        if (s.`sacc = 0 /\ s.`sstep = 3) {
          kb <@ S.kdf(map (fun (b : blk) => [b]) s.`sshs, ctx);
          out <- authmsg s.`ssid [s.`sni] (idpay u) (iachain s.`ssid);
          st.[(u, i)] <- {| s with sstep = 4; sacc = 1; skb = kb |};
        }
      }
      return out;
    }

    proc corrupt (u : int) : skey = {
      cor <- cor `|` fset1 u;
      return oget sks.[u];
    }

    proc harv (u i j : int) : blk = {
      var s, r;
      r <- witness;
      if ((u, i) \in st) {
        s <- oget st.[(u, i)];
        if (harvestable s j) { r <- nth witness s.`sshs j; }
      }
      return r;
    }

    proc enc (u i : int, m0 m1 ad : kmat) : kmat = {
      var s, r;
      r <- [];
      if ((u, i) \in st) {
        s <- oget st.[(u, i)];
        if (s.`sacc = 1 /\ size m0 = size m1) {
          r <- aenc s.`skb s.`ste ad (if s.`sbit then m1 else m0);
          st.[(u, i)] <- {| s with ste = s.`ste + 1 |};
        }
      }
      return r;
    }

    proc dec (u i : int, c ad : kmat) : kmat option = {
      var s, r;
      r <- None;
      if ((u, i) \in st) {
        s <- oget st.[(u, i)];
        if (s.`sacc = 1 /\ ! s.`sbit) {
          r <- adec s.`skb s.`std ad c;
          st.[(u, i)] <- {| s with std = s.`std + 1 |};
        }
      }
      return r;
    }
  }

  proc setup () : unit = {
    var u, sk, pk;
    sks <- empty; pks <- empty; cor <- fset0; st <- empty; cnt <- empty;
    nlist <- [];
    u <- 0;
    while (u < nP) {
      (sk, pk) <$ dkeys;
      sks.[u] <- sk; pks.[u] <- pk;
      u <- u + 1;
    }
  }

  proc main (z : int) : (int * int) * bool = {
    var u, i, b, s, w;
    setup();
    (u, i, b) <@ A(O).guess();
    tst <- if (0 <= u < nP /\ 0 <= i < nS) then (u, i) else (0, 0);
    w <- false;
    if ((u, i) \in st) {
      s <- oget st.[(u, i)];
      w <- s.`sacc = 1 /\ fresh s cor /\ b = s.`sbit;
    }
    return (tst, w);
  }
}.

section COLLISION.

declare module S <: Schedule {-Acce}.

declare module A <: ACCEA {-Acce, -S}.

(* Distinct sessions draw distinct nonces except with small probability *)
lemma pr_nonce_coll &m :
  Pr[Acce(S, A).main(0) @ &m : ! uniq Acce.nlist]
  <= ((nP * nS) * (nP * nS - 1))%r / 2%r * pblk.
proof.
fel 1 (size Acce.nlist) (fun i => i%r * pblk) (nP * nS) (! uniq Acce.nlist)
    [Acce(S, A).O.newsess : (size Acce.nlist < nP * nS)]
    (size Acce.nlist <= nP * nS).
+ by rewrite -mulr_suml sumidE; smt(gt0_nP gt0_nS).
+ by move=> &m0; smt(size_ge0).
+ by inline*; wp; while (true); auto; smt(size_ge0 gt0_nP gt0_nS).
+ proc; sp 1; if; last by hoare; auto; smt(ge0_mu).
  seq 2 : (! uniq Acce.nlist) ((size Acce.nlist)%r * pblk) 1%r 1%r 0%r => //.
  + wp; rnd (mem Acce.nlist); skip => /> &hr *.
    apply (mu_mem_le_size Acce.nlist{hr} dblk pblk).
    by move=> x _; rewrite mu1_dblk.
  by hoare; auto.
+ by move=> c; proc; sp; if; auto => /> /#.
by move=> b c; proc; sp; if; auto => /> /#.
qed.

end section COLLISION.

op allidx : (int * int) list =
  allpairs (fun (u i : int) => (u, i)) (iota_ 0 nP) (iota_ 0 nS).

(* The session index space is nonempty *)
lemma allidx_nonempty : allidx <> [].
proof.
have : size allidx = nP * nS.
+ by rewrite /allidx size_allpairs !size_iota; smt(gt0_nP gt0_nS).
by smt(gt0_nP gt0_nS size_eq0).
qed.

(* The session index space has no repetitions *)
lemma allidx_uniq : uniq allidx.
proof.
rewrite /allidx; apply allpairs_uniq; 1,2: by apply iota_uniq.
by move=> x1 x2 y1 y2 _ _ _ _.
qed.

(* Every clamped index belongs to the session index space *)
lemma allidx_mem (u i : int) :
  0 <= u < nP => 0 <= i < nS => (u, i) \in allidx.
proof.
move=> hu hi; rewrite /allidx; apply allpairsP.
by exists (u, i); rewrite /= !mem_iota /#.
qed.

(* The session index space has one entry per session *)
lemma allidx_size : size (undup allidx) = nP * nS.
proof.
by rewrite undup_id 1:allidx_uniq /allidx size_allpairs !size_iota;
   smt(gt0_nP gt0_nS).
qed.

clone import PlugAndPray as PP with
  type tval  <- int * int,
  op   indices <- allidx,
  type tin   <- int,
  type tres  <- (int * int) * bool
proof indices_not_nil by apply allidx_nonempty.

section GUESSING.

declare module S <: Schedule {-Acce}.

declare module A <: ACCEA {-Acce, -S}.

(* The reported index is always a valid session index *)
local lemma main_idx : hoare [ Acce(S, A).main : true ==> res.`1 \in allidx ].
proof.
proc; wp; conseq (: _ ==> true) => //.
by move=> &hr *; smt(allidx_mem gt0_nP gt0_nS).
qed.

(* Winning implies that the reported index is a session index *)
local lemma pr_idx &m :
  Pr[Acce(S, A).main(0) @ &m : res.`2]
  = Pr[Acce(S, A).main(0) @ &m : res.`2 /\ res.`1 \in allidx].
proof.
byequiv (_: ={glob A, glob S, arg} ==> ={res} /\ res{2}.`1 \in allidx) => //=.
conseq (_: _ ==> ={res}) _ (_: _ ==> res.`1 \in allidx) => //=; 2: by sim.
by conseq main_idx.
qed.

(* Guessing the tested session costs the number of sessions *)
lemma pr_guess &m :
  Pr[Acce(S, A).main(0) @ &m : res.`2]
  = (nP * nS)%r
    * Pr[PP.Guess(Acce(S, A)).main(0) @ &m :
           (res.`2.`2 /\ res.`2.`1 \in allidx) /\ res.`1 = res.`2.`1].
proof.
rewrite (pr_idx &m).
have -> := PBound_mult (Acce(S, A))
             (fun (g : glob Acce(S, A)) (r : (int * int) * bool) =>
                r.`2 /\ r.`1 \in allidx)
             (fun (g : glob Acce(S, A)) (r : (int * int) * bool) => r.`1)
             0 &m _.
+ by move=> gG o /= [] _.
+ by rewrite allidx_size.
qed.

end section GUESSING.

(* The session identifier and the identity determine the signed string *)
lemma authmsg_inj (t n idp ia t' n' idp' ia' : kmat) :
  size t = size t' => size n = size n' => size idp = size idp' =>
  authmsg t n idp ia = authmsg t' n' idp' ia' =>
  t = t' /\ n = n' /\ idp = idp' /\ ia = ia'.
proof.
rewrite /authmsg => h1 h2 h3 heq.
have e1 := eqseq_cat t t' (n ++ (idp ++ ia)) (n' ++ (idp' ++ ia')) h1.
have e2 := eqseq_cat n n' (idp ++ ia) (idp' ++ ia') h2.
have e3 := eqseq_cat idp idp' ia ia' h3.
smt().
qed.

(* Distinct session identifiers are signed differently *)
lemma sid_distinguishes (t n idp ia t' n' idp' ia' : kmat) :
  size t = size t' => size n = size n' => size idp = size idp' =>
  t <> t' => authmsg t n idp ia <> authmsg t' n' idp' ia'.
proof.
move=> h1 h2 h3 hne.
have hc : authmsg t n idp ia = authmsg t' n' idp' ia' => t = t'.
+ by move=> heq; have := authmsg_inj t n idp ia t' n' idp' ia' h1 h2 h3 heq.
smt().
qed.

op strip (s : state) : state = {| s with skb = [] |}.

op steq (m1 m2 : (int * int, state) fmap) : bool =
  forall k, omap strip m1.[k] = omap strip m2.[k].

(* The cascade schedule terminates *)
lemma ksc_ll : islossless KSc.kdf.
proof. by proc; call tail_ll; auto. qed.

(* The single pass schedule terminates *)
lemma spks_ll : islossless SPKS.kdf.
proof. by proc; call fexp_ll; wp; call fexp_ll; auto. qed.

section SCHEDULESWAP.

declare module A <: ACCEA {-Acce}.

(* Replacing the schedule changes no protocol message *)
local equiv send_same :
  Acce(KSc, A).O.send ~ Acce(SPKS, A).O.send :
  ={arg, glob Acce} ==> ={res} /\ steq Acce.st{1} Acce.st{2}.
proof.
proc; sp; if.
+ by move=> &1 &2 />.
+ sp 1 1.
  seq 5 5 : (={u, i, m, out, s} /\ ={glob Acce}); first by sim.
  if.
  + by move=> &1 &2 />.
  + wp; call{1} ksc_ll; call{2} spks_ll; auto => />.
    by move=> *; rewrite /steq /strip /=; smt(get_setE).
  by auto => />; rewrite /steq.
by auto => />; rewrite /steq.
qed.

end section SCHEDULESWAP.

op eps_sig : { real | 0%r <= eps_sig } as ge0_eps_sig.

op eps_ae : { real | 0%r <= eps_ae } as ge0_eps_ae.

op eps_kem : { real | 0%r <= eps_kem } as ge0_eps_kem.

op eps_sk : { real | 0%r <= eps_sk } as ge0_eps_sk.

op accebnd (ekem esk : real) : real =
  nP%r * eps_sig + (nP * nS)%r * (nP * nS)%r * pblk
  + (nP * nS)%r * (nP * nS)%r * (ekem + esk + eps_ae).

(* The channel bound is monotone in the primitive terms *)
lemma accebnd_mono (e e' f f' : real) :
  e <= e' => f <= f' => accebnd e f <= accebnd e' f'.
proof.
move=> h1 h2; rewrite /accebnd.
have hn : 0%r <= (nP * nS)%r * (nP * nS)%r by smt(gt0_nP gt0_nS).
smt().
qed.

section PROTOCOL.

declare module S <: Schedule {-Acce}.

declare module A <: ACCEA {-Acce, -S}.

(* The tested session is guessed at the cost of one factor *)
lemma acce_guessing (pg : real) &m :
  Pr[PP.Guess(Acce(S, A)).main(0) @ &m :
       (res.`2.`2 /\ res.`2.`1 \in allidx) /\ res.`1 = res.`2.`1] <= pg =>
  Pr[Acce(S, A).main(0) @ &m : res.`2] <= (nP * nS)%r * pg.
proof.
move=> h; rewrite (pr_guess S A &m).
by apply ler_wpmul2l; smt(gt0_nP gt0_nS).
qed.

(* The channel advantage of the protocol follows from the game sequence *)
lemma acce_channel (p1 p2 p3 : real) &m :
  Pr[PP.Guess(Acce(S, A)).main(0) @ &m :
       (res.`2.`2 /\ res.`2.`1 \in allidx) /\ res.`1 = res.`2.`1]
  <= p1 + eps_kem =>
  p1 <= p2 + eps_sk =>
  p2 <= p3 + eps_ae =>
  (nP * nS)%r * p3 <= nP%r * eps_sig
                      + ((nP * nS) * (nP * nS - 1))%r / 2%r * pblk =>
  Pr[Acce(S, A).main(0) @ &m : res.`2] <= accebnd eps_kem eps_sk.
proof.
move=> h1 h2 h3 h4.
have hq : 1%r <= (nP * nS)%r by smt(gt0_nP gt0_nS).
have hb := acce_guessing (p1 + eps_kem) &m h1.
have hn : 0%r <= pblk by rewrite /pblk; apply ge0_mu.
have e1 : p1 + eps_kem <= p3 + (eps_kem + eps_sk + eps_ae) by smt().
have e2 : (nP * nS)%r * (p1 + eps_kem)
          <= (nP * nS)%r * (p3 + (eps_kem + eps_sk + eps_ae)).
+ by apply ler_wpmul2l; smt().
have e3 : ((nP * nS) * (nP * nS - 1))%r / 2%r * pblk
          <= (nP * nS)%r * (nP * nS)%r * pblk.
+ by apply ler_wpmul2r; smt().
have e4 : (nP * nS)%r * (eps_kem + eps_sk + eps_ae)
          <= (nP * nS)%r * (nP * nS)%r * (eps_kem + eps_sk + eps_ae).
+ by apply ler_wpmul2r; smt(ge0_eps_kem ge0_eps_sk ge0_eps_ae).
rewrite /accebnd.
smt().
qed.

(* Chosen plaintext security of the mechanism suffices *)
lemma acce_cpa_sufficient (ecpa : real) &m :
  eps_kem <= ecpa =>
  Pr[Acce(S, A).main(0) @ &m : res.`2] <= accebnd eps_kem eps_sk =>
  Pr[Acce(S, A).main(0) @ &m : res.`2] <= accebnd ecpa eps_sk.
proof.
move=> h1 h2.
have := accebnd_mono eps_kem ecpa eps_sk eps_sk h1 _; first by [].
smt().
qed.

(* The single pass schedule preserves the channel bound *)
lemma acce_spks_transfer (espks : real) &m :
  espks <= eps_sk =>
  Pr[Acce(S, A).main(0) @ &m : res.`2] <= accebnd eps_kem espks =>
  Pr[Acce(S, A).main(0) @ &m : res.`2] <= accebnd eps_kem eps_sk.
proof.
move=> h1 h2.
have := accebnd_mono eps_kem eps_kem espks eps_sk _ h1; first by [].
smt().
qed.

end section PROTOCOL.
