require import AllCore Int IntDiv List Real.
require import StdOrder StdBigop.
import IntOrder.

op cdiv (a b : int) : int = (a + b - 1) %/ b.

op blen : int = 64.

op clen : int = 32.

op lamH : int = 8.

op lzero : int = 136.

op lfull : int = 168.

op mabs0 : int = 48.

op mabs : int = 112.

op cmin (mu : int) : int = 3 + cdiv (mu + 1 + lamH) blen.

op ninv (nb0 nb : int) : int = nb0 + nb + 2.

op ncomp (nb0 nb m0 m1 : int) : int =
  4 * (nb0 + nb) + cmin m0 + cmin m1.

op twolayer (nb0 nb m0 m1 : int) : bool =
  cdiv lzero clen <= nb0 /\ cdiv lfull clen <= nb /\ mabs0 <= m0 /\ mabs <= m1.

(* Ceiling division is monotone in its numerator *)
lemma cdiv_mono (a a' b : int) : 0 < b => a <= a' => cdiv a b <= cdiv a' b.
proof. by move=> hb h; rewrite /cdiv; smt(leq_div2r). qed.

(* The minimal invocation cost is monotone in the message length *)
lemma cmin_mono (m m' : int) : m <= m' => cmin m <= cmin m'.
proof. by move=> h; rewrite /cmin; smt(cdiv_mono). qed.

(* Every two layer schedule needs this many invocations *)
lemma opt_invocations (nb0 nb m0 m1 : int) :
  twolayer nb0 nb m0 m1 =>
  cdiv lzero clen + cdiv lfull clen + 2 <= ninv nb0 nb.
proof. by rewrite /twolayer /ninv; smt(). qed.

(* Every two layer schedule needs this many compression calls *)
lemma opt_compressions (nb0 nb m0 m1 : int) :
  twolayer nb0 nb m0 m1 =>
  4 * (cdiv lzero clen + cdiv lfull clen) + cmin mabs0 + cmin mabs
  <= ncomp nb0 nb m0 m1.
proof.
rewrite /twolayer /ncomp => [#] h0 h1 h2 h3.
have c0 := cmin_mono mabs0 m0 h2.
have c1 := cmin_mono mabs m1 h3.
smt().
qed.

(* The single pass schedule attains the invocation bound *)
lemma spks_invocations :
  ninv (cdiv lzero clen) (cdiv lfull clen)
  = cdiv lzero clen + cdiv lfull clen + 2.
proof. by rewrite /ninv. qed.

(* The single pass schedule attains the compression bound *)
lemma spks_compressions :
  ncomp (cdiv lzero clen) (cdiv lfull clen) mabs0 mabs = 53.
proof. by rewrite /ncomp /cmin /cdiv /lzero /lfull /clen /blen /lamH /mabs0 /mabs /=. qed.

(* The concrete block counts of the single pass schedule *)
lemma spks_blocks : cdiv lzero clen = 5 /\ cdiv lfull clen = 6.
proof. by rewrite /cdiv /lzero /lfull /clen /=. qed.
