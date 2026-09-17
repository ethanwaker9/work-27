import hmac
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ikev2pq.combiners import (
    Context,
    DEFERRED_COMBINERS,
    rfc9370,
    spks,
    spks_stage0,
    stage0_protection,
)
from ikev2pq.costs import COST_TABLE, spks_stage0_cost, stage0_full, stage0_partial
from ikev2pq.params import KEM_SIZES, SUITES
from ikev2pq.prf import CostCounter, Prf, hmac_compressions
from ikev2pq.kex import get_kem

LADDER = [
    "x25519",
    "ml-kem-768",
    "frodokem-640-aes",
    "ml-kem-1024",
    "ml-kem-512",
    "frodokem-976-aes",
    "ecp256",
    "ml-kem-768",
]


def check_hmac():
    for hn in ("sha256", "sha384", "sha512"):
        p = Prf(hn)
        for kl in (1, 16, 32, 48, 64, 65, 128, 200):
            k = os.urandom(kl)
            for ml in (0, 1, 31, 64, 113, 1000):
                m = os.urandom(ml)
                assert p(k, m) == hmac.digest(k, m, hn)
    print("ok   HMAC implementation matches the standard library")


def check_prf_plus():
    p = Prf("sha256")
    key = os.urandom(32)
    seed = os.urandom(80)
    out = p.plus(key, seed, 168)
    ref = b""
    prev = b""
    for i in range(1, 7):
        prev = hmac.digest(key, prev + seed + bytes((i,)), "sha256")
        ref += prev
    assert out == ref[:168]
    print("ok   prf+ matches RFC 7296")


def check_cost_model():
    for suite_key, suite in SUITES.items():
        for n_add in range(1, 8):
            kems = LADDER[: n_add + 1]
            ss_lens = [KEM_SIZES[k]["ss"] for k in kems]
            ct_lens = [KEM_SIZES[k]["ct"] for k in kems]
            pk_lens = [KEM_SIZES[k]["pk"] for k in kems]
            secrets = [os.urandom(x) for x in ss_lens]
            ctx = Context(
                ni=os.urandom(suite.nonce_len),
                nr=os.urandom(suite.nonce_len),
                spii=os.urandom(suite.spi_len),
                spir=os.urandom(suite.spi_len),
                cts=[os.urandom(x) for x in ct_lens],
                pks=[os.urandom(x) for x in pk_lens],
                theta=os.urandom(2 * suite.out),
            )
            for method, fn in COST_TABLE.items():
                counter = CostCounter()
                prf = Prf(suite.prf_hash, counter)
                if method == "RFC 9370":
                    rfc9370(secrets, ctx, suite, prf)
                elif method == "SPKS":
                    spks_stage0(secrets[0], ctx, suite, prf)
                    spks(secrets, ctx, suite, prf)
                else:
                    stage0_protection(secrets[0], ctx, suite, prf)
                    DEFERRED_COMBINERS[method](secrets, ctx, suite, prf)
                model = fn(suite, ss_lens, ct_lens, pk_lens)
                assert counter.compressions == model["comp"], (
                    suite_key,
                    n_add,
                    method,
                    counter.compressions,
                    model["comp"],
                )
    print("ok   analytic cost model matches the instrumented count for all suites")


def check_agreement():
    suite = SUITES["gcm256-sha256"]
    for names in (["x25519", "ml-kem-768"], ["x25519", "ml-kem-768", "frodokem-640-aes"]):
        secrets_i, secrets_r, cts, pks = [], [], [], []
        for name in names:
            kem = get_kem(name)
            pk, sk = kem.keygen()
            ct, ss_r = kem.encaps(pk)
            ss_i = kem.decaps(sk, ct)
            assert ss_i == ss_r
            secrets_i.append(ss_i)
            secrets_r.append(ss_r)
            cts.append(ct)
            pks.append(pk)
        ctx = Context(
            ni=os.urandom(32),
            nr=os.urandom(32),
            spii=os.urandom(8),
            spir=os.urandom(8),
            cts=cts,
            pks=pks,
            theta=os.urandom(64),
        )
        a = spks(secrets_i, ctx, suite, Prf(suite.prf_hash))
        b = spks(secrets_r, ctx, suite, Prf(suite.prf_hash))
        assert a == b and len(a) == suite.keymat_len
        c, _ = rfc9370(secrets_i, ctx, suite, Prf(suite.prf_hash))
        d, _ = rfc9370(secrets_r, ctx, suite, Prf(suite.prf_hash))
        assert c == d and len(c) == suite.keymat_len
        assert a != c
    print("ok   both schedules agree between the two peers on real key exchanges")


def check_split_key():
    suite = SUITES["gcm256-sha256"]
    ss = [os.urandom(32), os.urandom(32)]
    ctx = Context(
        ni=os.urandom(32),
        nr=os.urandom(32),
        spii=os.urandom(8),
        spir=os.urandom(8),
        cts=[os.urandom(32), os.urandom(1088)],
        pks=[os.urandom(32), os.urandom(1184)],
        theta=os.urandom(64),
    )
    base = spks(ss, ctx, suite, Prf(suite.prf_hash))
    for j in range(len(ss)):
        alt = list(ss)
        alt[j] = os.urandom(32)
        assert spks(alt, ctx, suite, Prf(suite.prf_hash)) != base
    print("ok   the output of SPKS changes with each shared secret")


def check_handshake_costs():
    suite = SUITES["gcm256-sha256"]
    ss_lens = [32, 32]
    a = stage0_full(suite, 32)
    b = stage0_partial(suite, 32)
    c = spks_stage0_cost(suite, 32)
    assert a == 34 and b == 29 and c == 24, (a, b, c)
    assert COST_TABLE["RFC 9370"](suite, ss_lens, [32, 1088], [32, 1184])["comp"] == 69
    assert COST_TABLE["SPKS"](suite, ss_lens, [32, 1088], [32, 1184])["comp"] == 53
    assert hmac_compressions(64, 32, "sha256") == 4
    print("ok   the cost expressions of the paper reproduce")


def main():
    check_hmac()
    check_prf_plus()
    check_cost_model()
    check_agreement()
    check_split_key()
    check_handshake_costs()
    print("all checks passed")


if __name__ == "__main__":
    main()
