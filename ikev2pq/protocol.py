import os
import time
from dataclasses import dataclass, field
from typing import Dict, List

from cryptography.hazmat.primitives.ciphers.aead import AESGCM

from .combiners import Context, rfc9370, spks, spks_stage0, _split_keys
from .kex import get_kem, OqsSig
from .params import Suite, SUITE_GCM256_SHA256
from .prf import CostCounter, Prf

IKE_HDR = 28
GEN_HDR = 4
KE_EXTRA = 4
NOTIFY = 8
SA_PAYLOAD = 4 + 8 + 5 * 8
ENC_OVERHEAD = GEN_HDR + 8 + 16 + 1
ID_PAYLOAD = 4 + 4 + 16


def _pad16(n: int) -> int:
    return (16 - (n % 16)) % 16


@dataclass
class HandshakeStats:
    method: str
    profile: str
    n_add: int
    messages: int = 0
    round_trips: int = 0
    wire_bytes: int = 0
    init_time: float = 0.0
    resp_time: float = 0.0
    ks_time: float = 0.0
    ks_compressions: int = 0
    ks_prf_calls: int = 0
    ks_keymat_bytes: int = 0
    ks_depth: int = 0
    ia_compressions: int = 0
    live_key_bytes: int = 0


class Ikev2Handshake:
    def __init__(self, kem_names: List[str], suite: Suite = SUITE_GCM256_SHA256,
                 method: str = "rfc9370", sig_mechanism: str = "ML-DSA-65"):
        self.kem_names = kem_names
        self.suite = suite
        self.method = method
        self.kems = [get_kem(k) for k in kem_names]
        self.sig = OqsSig(sig_mechanism)

    def run(self) -> HandshakeStats:
        suite = self.suite
        counter = CostCounter()
        prf = Prf(suite.prf_hash, counter)
        ia_counter = CostCounter()
        prf_ia = Prf(suite.prf_hash, ia_counter)
        st = HandshakeStats(method=self.method,
                            profile="+".join(self.kem_names),
                            n_add=len(self.kems) - 1)

        rpk, rsk = self.sig.keygen()

        ti = 0.0
        tr = 0.0
        tks = 0.0

        spii = os.urandom(suite.spi_len)
        spir = os.urandom(suite.spi_len)
        ni = os.urandom(suite.nonce_len)
        nr = os.urandom(suite.nonce_len)

        t0 = time.perf_counter()
        pk0, sk0 = self.kems[0].keygen()
        ti += time.perf_counter() - t0

        msg1 = IKE_HDR + SA_PAYLOAD + (GEN_HDR + KE_EXTRA + len(pk0)) + (GEN_HDR + len(ni)) + NOTIFY
        st.wire_bytes += msg1
        st.messages += 1

        t0 = time.perf_counter()
        ct0, ss0_r = self.kems[0].encaps(pk0)
        tr += time.perf_counter() - t0

        msg2 = IKE_HDR + SA_PAYLOAD + (GEN_HDR + KE_EXTRA + len(ct0)) + (GEN_HDR + len(nr)) + NOTIFY
        st.wire_bytes += msg2
        st.messages += 1

        t0 = time.perf_counter()
        ss0 = self.kems[0].decaps(sk0, ct0)
        ti += time.perf_counter() - t0

        ctx = Context(ni=ni, nr=nr, spii=spii, spir=spir, cts=[ct0], pks=[pk0])

        secrets = [ss0]
        cts = [ct0]
        pks = [pk0]

        t0 = time.perf_counter()
        if self.method == "rfc9370":
            skeyseed = prf(ctx.salt, ss0)
            km = prf.plus(skeyseed, ctx.seed, suite.keymat_len)
            keys = _split_keys(km, suite)
            live = suite.keymat_len + prf.out
        else:
            pm = spks_stage0(ss0, ctx, suite, prf)
            keys = _split_keys(bytes(suite.sk_d) + pm, suite)
            live = suite.protect_len + prf.out
        dt = time.perf_counter() - t0
        tks += dt
        ti += dt
        tr += dt

        intauth_i = b""
        intauth_r = b""

        for j in range(1, len(self.kems)):
            t0 = time.perf_counter()
            pkj, skj = self.kems[j].keygen()
            ti += time.perf_counter() - t0

            inner_i = GEN_HDR + KE_EXTRA + len(pkj)
            body_i = IKE_HDR + GEN_HDR + 8 + inner_i
            total_i = body_i + _pad16(inner_i + 1) + 1 + 16
            st.wire_bytes += total_i
            st.messages += 1

            aad_i = os.urandom(IKE_HDR + GEN_HDR)
            plain_i = os.urandom(inner_i)
            aes = AESGCM(keys["sk_ei"][:32])
            t0 = time.perf_counter()
            ct_msg = aes.encrypt(keys["sk_ei"][32:36] + b"\x00" * 8, plain_i, aad_i)
            ti += time.perf_counter() - t0
            t0 = time.perf_counter()
            aes.decrypt(keys["sk_ei"][32:36] + b"\x00" * 8, ct_msg, aad_i)
            tr += time.perf_counter() - t0

            t0 = time.perf_counter()
            ctj, ssj_r = self.kems[j].encaps(pkj)
            tr += time.perf_counter() - t0

            inner_r = GEN_HDR + KE_EXTRA + len(ctj)
            body_r = IKE_HDR + GEN_HDR + 8 + inner_r
            total_r = body_r + _pad16(inner_r + 1) + 1 + 16
            st.wire_bytes += total_r
            st.messages += 1

            aad_r = os.urandom(IKE_HDR + GEN_HDR)
            plain_r = os.urandom(inner_r)
            aes2 = AESGCM(keys["sk_er"][:32])
            t0 = time.perf_counter()
            ct_msg2 = aes2.encrypt(keys["sk_er"][32:36] + b"\x00" * 8, plain_r, aad_r)
            tr += time.perf_counter() - t0
            t0 = time.perf_counter()
            aes2.decrypt(keys["sk_er"][32:36] + b"\x00" * 8, ct_msg2, aad_r)
            ti += time.perf_counter() - t0

            t0 = time.perf_counter()
            ssj = self.kems[j].decaps(skj, ctj)
            ti += time.perf_counter() - t0

            secrets.append(ssj)
            cts.append(ctj)
            pks.append(pkj)

            t0 = time.perf_counter()
            intauth_i = prf_ia(keys["sk_pi"], intauth_i + aad_i + plain_i)
            intauth_r = prf_ia(keys["sk_pr"], intauth_r + aad_r + plain_r)
            dt = time.perf_counter() - t0
            tks += dt
            ti += dt
            tr += dt

            if self.method == "rfc9370":
                t0 = time.perf_counter()
                skeyseed = prf(keys["sk_d"], ssj + ni + nr)
                km = prf.plus(skeyseed, ctx.seed, suite.keymat_len)
                keys = _split_keys(km, suite)
                dt = time.perf_counter() - t0
                tks += dt
                ti += dt
                tr += dt
                live = max(live, 2 * suite.keymat_len + prf.out)

        ctx = Context(ni=ni, nr=nr, spii=spii, spir=spir, cts=cts, pks=pks,
                      theta=intauth_i + intauth_r)

        if self.method != "rfc9370":
            t0 = time.perf_counter()
            km = spks(secrets, ctx, suite, prf)
            keys = _split_keys(km, suite)
            dt = time.perf_counter() - t0
            tks += dt
            ti += dt
            tr += dt
            live = max(live, suite.protect_len + suite.keymat_len + prf.out)

        signed_i = os.urandom(msg1) + nr + prf_ia(keys["sk_pi"], b"IDi")
        signed_r = os.urandom(msg2) + ni + prf_ia(keys["sk_pr"], b"IDr")
        signed_i += intauth_i + intauth_r + b"\x00\x00\x00\x01"
        signed_r += intauth_i + intauth_r + b"\x00\x00\x00\x01"

        t0 = time.perf_counter()
        auth_i = self.sig.sign(rsk, signed_i)
        ti += time.perf_counter() - t0

        t0 = time.perf_counter()
        auth_r = self.sig.sign(rsk, signed_r)
        tr += time.perf_counter() - t0

        inner3 = ID_PAYLOAD + (GEN_HDR + 1 + self.sig.pk_len) + (GEN_HDR + 4 + len(auth_i)) + SA_PAYLOAD + 2 * 16
        st.wire_bytes += IKE_HDR + GEN_HDR + 8 + inner3 + _pad16(inner3 + 1) + 1 + 16
        st.messages += 1
        inner4 = ID_PAYLOAD + (GEN_HDR + 1 + self.sig.pk_len) + (GEN_HDR + 4 + len(auth_r)) + SA_PAYLOAD + 2 * 16
        st.wire_bytes += IKE_HDR + GEN_HDR + 8 + inner4 + _pad16(inner4 + 1) + 1 + 16
        st.messages += 1

        t0 = time.perf_counter()
        assert self.sig.verify(rpk, signed_i, auth_i)
        tr += time.perf_counter() - t0
        t0 = time.perf_counter()
        assert self.sig.verify(rpk, signed_r, auth_r)
        ti += time.perf_counter() - t0

        st.round_trips = st.messages // 2
        st.init_time = ti
        st.resp_time = tr
        st.ks_time = tks
        snap = counter.snapshot()
        st.ks_compressions = snap["compressions"]
        st.ks_prf_calls = snap["prf_calls"]
        st.ks_keymat_bytes = snap["keymat_bytes"]
        st.ks_depth = snap["depth"]
        st.ia_compressions = ia_counter.snapshot()["compressions"]
        st.live_key_bytes = live
        return st
