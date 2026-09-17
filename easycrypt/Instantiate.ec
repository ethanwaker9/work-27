require import AllCore Int IntDiv List Real.
require import IKEv2Core Segment Optimality.

op cbytes : int = 32.

op bbytes : int = 64.

op nubytes : int = 32.

op sibytes : int = 8.

op lamHb : int = 8.

op lblock : int = 168.

op lblock0 : int = 136.

op shsC : int = 32.

op shsK1 : int = 32.

op shsK2 : int = 16.

op shsK3 : int = 32.

op lvec : int list = [shsC; shsK1; shsK2; shsK3].

op prof0c : prof = (2 * nubytes, 0, shsC, 0).

op profjc (j : int) : prof = (cbytes, 0, nth 0 lvec j, 2 * nubytes).

op prof0s : prof = (2 * nubytes, 0, shsC, 2 * sibytes).

op profjs (j : int) : prof =
  (2 * cbytes, sumz (take j lvec), nth 0 lvec j, sumz (drop (j + 1) lvec)).

(* The negotiated suite fixes the derivation parameters *)
lemma inst_sizes :
  cbytes = 32 /\ bbytes = 64 /\ lamHb = 8 /\ lblock = 168 /\ lblock0 = 136.
proof. by rewrite /cbytes /bbytes /lamHb /lblock /lblock0. qed.

(* The key blocks occupy this many pseudorandom function outputs *)
lemma inst_blocks : cdiv lblock0 cbytes = 5 /\ cdiv lblock cbytes = 6.
proof. by rewrite /cdiv /lblock0 /lblock /cbytes. qed.

(* The shared secret lengths of the negotiated sequence *)
lemma inst_lvec : sumz lvec = 112.
proof. by rewrite /lvec /sumz /shsC /shsK1 /shsK2 /shsK3. qed.

(* The cascade profiles of the negotiated sequence are well formed *)
lemma inst_prof0c : wfprof prof0c.
proof. by rewrite /wfprof /prof0c /pkap /ppre /psec /psuf /nubytes /shsC. qed.

(* The later cascade profiles are well formed *)
lemma inst_profjc (j : int) :
  0 <= j < size lvec => wfprof (profjc j).
proof.
move=> h; rewrite /wfprof /profjc /pkap /ppre /psec /psuf /cbytes /nubytes.
by rewrite /lvec /=; smt(size_ge0).
qed.

(* The initial single pass profile is well formed *)
lemma inst_prof0s : wfprof prof0s.
proof. by rewrite /wfprof /prof0s /pkap /ppre /psec /psuf /nubytes /sibytes /shsC. qed.

(* The single pass profiles cover the whole concatenation *)
lemma inst_profjs (j : int) :
  0 <= j < size lvec =>
  ppre (profjs j) + psec (profjs j) + psuf (profjs j) = sumz lvec.
proof.
move=> h; rewrite /profjs /ppre /psec /psuf /=.
have := size_cut (take j lvec) [].
by rewrite /lvec /sumz /=; smt().
qed.

(* The single pass schedule attains the counting bound of the suite *)
lemma inst_cost : ncomp (cdiv lzero clen) (cdiv lfull clen) mabs0 mabs = 53.
proof. by apply spks_compressions. qed.
