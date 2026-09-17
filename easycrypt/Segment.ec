require import AllCore Int IntDiv List Distr DList FMap FSet Real.
require import StdOrder StdBigop.
require import IKEv2Core.
import RealOrder.

type prof = int * int * int * int.

op pkap (p : prof) : int = p.`1.

op ppre (p : prof) : int = p.`2.

op psec (p : prof) : int = p.`3.

op psuf (p : prof) : int = p.`4.

op wfprof (p : prof) : bool =
  0 <= pkap p /\ 0 <= ppre p /\ 0 < psec p /\ 0 <= psuf p.

op ins (x z y : kmat) : kmat = x ++ (z ++ y).

op cut (ls : int list) (z : kmat) : kmat list =
  with ls = []      => []
  with ls = n :: t  => take n z :: cut t (drop n z).

op slen : { int | 0 <= slen } as ge0_slen.

op padk : kmat -> kmat.

op k1 : kmat.

op k2 : kmat.

op xfix : kmat.

op yfix : kmat.

module type FixO = { proc f (k : kmat, x : kmat, y : kmat) : blk }.

module type FixA (O : FixO) = { proc guess () : bool }.

module FixR (A : FixA) = {
  var xx : kmat

  module O : FixO = {
    proc f (k : kmat, x : kmat, y : kmat) : blk = {
      return F (padk k) (0, ins x xx y);
    }
  }

  proc main () : bool = {
    var b;
    xx <$ dlist dblk slen;
    b <@ A(O).guess();
    return b;
  }
}.

module FixI (A : FixA) = {
  var mp : (kmat * kmat * kmat, blk) fmap

  module O : FixO = {
    proc f (k : kmat, x : kmat, y : kmat) : blk = {
      var r;
      if ((k, x, y) \notin mp) { r <$ dblk; mp.[(k, x, y)] <- r; }
      return oget mp.[(k, x, y)];
    }
  }

  proc main () : bool = {
    var b;
    mp <- empty;
    b <@ A(O).guess();
    return b;
  }
}.

module DFix (O : FixO) = {
  proc guess () : bool = {
    var r1, r2;
    r1 <@ O.f(k1, xfix, yfix);
    r2 <@ O.f(k2, xfix, yfix);
    return r1 = r2;
  }
}.

(* Sums of nonnegative lengths are nonnegative *)
lemma sumz_cons (n : int) (t : int list) : sumz (n :: t) = n + sumz t.
proof. by rewrite /sumz. qed.

(* Nonnegative length vectors have nonnegative total length *)
lemma sumz_ge0 (ls : int list) : all (fun n => 0 <= n) ls => 0 <= sumz ls.
proof.
elim: ls => [|n t ih] /=; first by rewrite /sumz.
by rewrite sumz_cons; smt().
qed.

(* Insertion at a fixed profile is injective *)
lemma ins_inj (p l : int) (x z y x' z' y' : kmat) :
  size x = p => size x' = p => size z = l => size z' = l =>
  ins x z y = ins x' z' y' => x = x' /\ z = z' /\ y = y'.
proof.
rewrite /ins => hx hx' hz hz' heq.
have hsx : size x = size x' by rewrite hx hx'.
have hsz : size z = size z' by rewrite hz hz'.
have h1 := eqseq_cat x x' (z ++ y) (z' ++ y') hsx.
have h2 := eqseq_cat z z' y y' hsz.
smt().
qed.

(* Cutting a string yields the prescribed segment lengths *)
lemma size_cut (ls : int list) (z : kmat) :
  all (fun n => 0 <= n) ls => sumz ls = size z =>
  map size (cut ls z) = ls.
proof.
move: z; elim: ls => [|n t ih] z.
+ by move=> _ _ /=.
move=> /= [hn ht]; rewrite sumz_cons => hsum.
have hs0 : 0 <= sumz t by apply sumz_ge0.
have -> : size (take n z) = n by rewrite size_take 1:hn; smt().
have hd : sumz t = size (drop n z) by rewrite size_drop 1:hn; smt().
by rewrite (ih (drop n z) ht hd).
qed.

(* Cutting is inverted by concatenation *)
lemma flatten_cut (ls : int list) (z : kmat) :
  all (fun n => 0 <= n) ls => sumz ls = size z =>
  flatten (cut ls z) = z.
proof.
move: z; elim: ls => [|n t ih] z.
+ move=> _ hs; have hz : z = [] by smt(size_eq0).
  by rewrite hz /=.
move=> /= [hn ht]; rewrite sumz_cons => hsum.
have hs0 : 0 <= sumz t by apply sumz_ge0.
have hd : sumz t = size (drop n z) by rewrite size_drop 1:hn; smt().
by rewrite flatten_cons (ih (drop n z) ht hd) cat_take_drop.
qed.

(* Distinct total lengths make the segmentation unambiguous *)
lemma seg_unambiguous (ls ls' : int list) (z z' : kmat) :
  all (fun n => 0 <= n) ls => all (fun n => 0 <= n) ls' =>
  sumz ls = size z => sumz ls' = size z' =>
  (sumz ls = sumz ls' => ls = ls') =>
  flatten (cut ls z) = flatten (cut ls' z') =>
  ls = ls' /\ cut ls z = cut ls' z'.
proof.
move=> h1 h2 h3 h4 hinj.
rewrite (flatten_cut ls z) // (flatten_cut ls' z') // => hzz.
have hll : ls = ls' by apply hinj; rewrite h3 h4 hzz.
by rewrite hll hzz.
qed.

(* Equal total lengths make two segmentations collide *)
lemma seg_ambiguous (ls ls' : int list) (z : kmat) :
  all (fun n => 0 <= n) ls => all (fun n => 0 <= n) ls' =>
  sumz ls = size z => sumz ls' = size z => ls <> ls' =>
  cut ls z <> cut ls' z /\
  flatten (cut ls z) = flatten (cut ls' z).
proof.
move=> h1 h2 h3 h4 hne; split; last first.
+ by rewrite (flatten_cut ls z) // (flatten_cut ls' z).
have h : map size (cut ls z) <> map size (cut ls' z).
+ by rewrite (size_cut ls z) // (size_cut ls' z).
smt().
qed.

section FIXEDLENGTH.

declare axiom padk_coll : padk k1 = padk k2.

declare axiom keys_distinct : k1 <> k2.

local module GIdeal = {
  proc main () : bool = {
    var r1, r2;
    r1 <$ dblk;
    r2 <$ dblk;
    return r2 = r1;
  }
}.

(* Two independent blocks agree with block probability *)
local lemma pr_gideal &m : Pr[GIdeal.main() @ &m : res] = pblk.
proof.
byphoare => //; proc.
seq 1 : true 1%r pblk 0%r 0%r => //.
+ by rnd; skip => />; apply dblk_ll.
rnd; skip => /> &hr.
have -> : (fun (r2 : blk) => r2 = r1{hr}) = pred1 r1{hr} by done.
by rewrite mu1_dblk.
qed.

(* The ideal oracle answers the two queries independently *)
local equiv fix_ideal_eq :
  FixI(DFix).main ~ GIdeal.main : true ==> ={res}.
proof.
proc; inline*.
rcondt{1} 5; first by auto; rewrite mem_empty.
rcondt{1} 11; first by auto => />; smt(mem_set keys_distinct).
by auto => />; smt(get_setE mem_set keys_distinct).
qed.

(* Colliding key padding is always detected on the real oracle *)
local lemma fix_real &m : Pr[FixR(DFix).main() @ &m : res] = 1%r.
proof.
byphoare => //; proc; inline*; wp; rnd; skip => />.
rewrite padk_coll /=.
have -> : (fun (_ : kmat) => true) = predT by done.
by apply (dlist_blk_ll slen ge0_slen).
qed.

(* Two key lengths break segment keyed swap security *)
lemma fixedlen_necessary &m :
  `| Pr[FixR(DFix).main() @ &m : res] - Pr[FixI(DFix).main() @ &m : res] |
  = 1%r - pblk.
proof.
rewrite (fix_real &m).
have -> : Pr[FixI(DFix).main() @ &m : res] = Pr[GIdeal.main() @ &m : res].
+ by byequiv fix_ideal_eq.
rewrite (pr_gideal &m).
have h0 : 0%r <= pblk by rewrite /pblk; apply ge0_mu.
have h1 : pblk <= 1%r by rewrite /pblk; apply le1_mu1.
by smt().
qed.

end section FIXEDLENGTH.
