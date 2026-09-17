import os

from cryptography.hazmat.primitives.asymmetric.x25519 import (
    X25519PrivateKey,
    X25519PublicKey,
)
from cryptography.hazmat.primitives.serialization import (
    Encoding,
    PublicFormat,
)

try:
    import oqs

    HAVE_OQS = True
except Exception:
    HAVE_OQS = False


class X25519Kem:
    name = "x25519"
    pk_len = 32
    ct_len = 32
    ss_len = 32

    def keygen(self):
        sk = X25519PrivateKey.generate()
        pk = sk.public_key().public_bytes(Encoding.Raw, PublicFormat.Raw)
        return pk, sk

    def encaps(self, pk: bytes):
        e = X25519PrivateKey.generate()
        ct = e.public_key().public_bytes(Encoding.Raw, PublicFormat.Raw)
        ss = e.exchange(X25519PublicKey.from_public_bytes(pk))
        return ct, ss

    def decaps(self, sk, ct: bytes):
        return sk.exchange(X25519PublicKey.from_public_bytes(ct))


class OqsKem:
    def __init__(self, mechanism: str, alias: str = None):
        if not HAVE_OQS:
            raise RuntimeError("liboqs-python is required")
        self.mechanism = mechanism
        self.name = alias or mechanism.lower()
        with oqs.KeyEncapsulation(mechanism) as k:
            d = k.details
        self.pk_len = d["length_public_key"]
        self.ct_len = d["length_ciphertext"]
        self.ss_len = d["length_shared_secret"]

    def keygen(self):
        k = oqs.KeyEncapsulation(self.mechanism)
        pk = k.generate_keypair()
        return pk, k

    def encaps(self, pk: bytes):
        with oqs.KeyEncapsulation(self.mechanism) as k:
            ct, ss = k.encap_secret(pk)
        return ct, ss

    def decaps(self, sk, ct: bytes):
        return sk.decap_secret(ct)


REGISTRY = {}


def get_kem(name: str):
    if name in REGISTRY:
        return REGISTRY[name]
    if name == "x25519":
        REGISTRY[name] = X25519Kem()
    else:
        table = {
            "ml-kem-512": "ML-KEM-512",
            "ml-kem-768": "ML-KEM-768",
            "ml-kem-1024": "ML-KEM-1024",
            "frodokem-640-aes": "FrodoKEM-640-AES",
            "frodokem-976-aes": "FrodoKEM-976-AES",
        }
        REGISTRY[name] = OqsKem(table[name], alias=name)
    return REGISTRY[name]


class OqsSig:
    def __init__(self, mechanism: str):
        if not HAVE_OQS:
            raise RuntimeError("liboqs-python is required")
        self.mechanism = mechanism
        with oqs.Signature(mechanism) as s:
            d = s.details
        self.pk_len = d["length_public_key"]
        self.sig_len = d["length_signature"]

    def keygen(self):
        s = oqs.Signature(self.mechanism)
        pk = s.generate_keypair()
        return pk, s

    def sign(self, sk, msg: bytes):
        return sk.sign(msg)

    def verify(self, pk: bytes, msg: bytes, sig: bytes):
        with oqs.Signature(self.mechanism) as v:
            return v.verify(msg, sig, pk)
