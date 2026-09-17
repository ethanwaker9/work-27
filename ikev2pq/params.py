from dataclasses import dataclass, field
from typing import Dict, List


HASH_PARAMS = {
    "sha256": {"block": 64, "out": 32, "len_field": 8},
    "sha384": {"block": 128, "out": 48, "len_field": 16},
    "sha512": {"block": 128, "out": 64, "len_field": 16},
}


@dataclass(frozen=True)
class Suite:
    name: str
    prf_hash: str
    nonce_len: int = 32
    spi_len: int = 8
    sk_d: int = 32
    sk_ai: int = 0
    sk_ar: int = 0
    sk_ei: int = 36
    sk_er: int = 36
    sk_pi: int = 32
    sk_pr: int = 32

    @property
    def block(self) -> int:
        return HASH_PARAMS[self.prf_hash]["block"]

    @property
    def out(self) -> int:
        return HASH_PARAMS[self.prf_hash]["out"]

    @property
    def len_field(self) -> int:
        return HASH_PARAMS[self.prf_hash]["len_field"]

    @property
    def keymat_len(self) -> int:
        return (
            self.sk_d
            + self.sk_ai
            + self.sk_ar
            + self.sk_ei
            + self.sk_er
            + self.sk_pi
            + self.sk_pr
        )

    @property
    def protect_len(self) -> int:
        return self.sk_ai + self.sk_ar + self.sk_ei + self.sk_er + self.sk_pi + self.sk_pr

    @property
    def context_len(self) -> int:
        return 2 * self.nonce_len + 2 * self.spi_len


SUITE_GCM256_SHA256 = Suite(
    name="AES-GCM-16-256 / PRF-HMAC-SHA2-256",
    prf_hash="sha256",
)

SUITE_CBC256_SHA256 = Suite(
    name="AES-CBC-256 + HMAC-SHA2-256-128 / PRF-HMAC-SHA2-256",
    prf_hash="sha256",
    sk_ai=32,
    sk_ar=32,
    sk_ei=32,
    sk_er=32,
)

SUITE_GCM256_SHA384 = Suite(
    name="AES-GCM-16-256 / PRF-HMAC-SHA2-384",
    prf_hash="sha384",
    nonce_len=48,
    sk_d=48,
    sk_pi=48,
    sk_pr=48,
)

SUITES = {
    "gcm256-sha256": SUITE_GCM256_SHA256,
    "cbc256-sha256": SUITE_CBC256_SHA256,
    "gcm256-sha384": SUITE_GCM256_SHA384,
}


@dataclass(frozen=True)
class KexProfile:
    label: str
    kem_ids: List[str]
    ss_lens: List[int]
    ct_lens: List[int]
    pk_lens: List[int]


KEM_SIZES = {
    "x25519": {"ss": 32, "ct": 32, "pk": 32},
    "ecp256": {"ss": 32, "ct": 64, "pk": 64},
    "ml-kem-512": {"ss": 32, "ct": 768, "pk": 800},
    "ml-kem-768": {"ss": 32, "ct": 1088, "pk": 1184},
    "ml-kem-1024": {"ss": 32, "ct": 1568, "pk": 1568},
    "frodokem-640-aes": {"ss": 16, "ct": 9720, "pk": 9616},
    "frodokem-976-aes": {"ss": 24, "ct": 15744, "pk": 15632},
}


def profile(kem_ids: List[str], label: str = "") -> KexProfile:
    return KexProfile(
        label=label or "+".join(kem_ids),
        kem_ids=list(kem_ids),
        ss_lens=[KEM_SIZES[k]["ss"] for k in kem_ids],
        ct_lens=[KEM_SIZES[k]["ct"] for k in kem_ids],
        pk_lens=[KEM_SIZES[k]["pk"] for k in kem_ids],
    )


DEFAULT_PROFILES = {
    1: profile(["x25519", "ml-kem-768"]),
    2: profile(["x25519", "ml-kem-768", "frodokem-640-aes"]),
    3: profile(["x25519", "ml-kem-768", "frodokem-640-aes", "ml-kem-1024"]),
}
