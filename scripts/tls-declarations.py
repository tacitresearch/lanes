#!/usr/bin/env python3
"""Checks the OpenSSL declarations of `native/tls.c`, `native/verify.c`, `native/sign.c` and
`native/lanes.c` against the system's OpenSSL headers.

The OpenSSL that these files link is the one Lean's toolchain ships, which has no headers, so
each file declares what it calls. This compiles each with the system's headers included first
and its constants turned into assertions: a function declared otherwise than OpenSSL declares
it, or a constant of another value, does not compile. It needs a C compiler and OpenSSL's
headers (`libssl-dev`, or Homebrew's `openssl@3` found through pkg-config); CI runs it on Linux.
Run from the repository root.
"""
import os
import re
import subprocess
import sys
import tempfile

HEADERS = ("#include <openssl/ssl.h>\n#include <openssl/x509v3.h>\n#include <openssl/err.h>\n"
           "#include <openssl/evp.h>\n#include <openssl/x509.h>\n#include <openssl/pem.h>\n"
           "#include <openssl/sha.h>\n#include <openssl/hmac.h>\n#include <openssl/crypto.h>\n"
           "#include <openssl/kdf.h>\n#include <openssl/param_build.h>\n")
lean = subprocess.run(["lean", "--print-prefix"], capture_output=True, text=True, check=True)
flags = subprocess.run(["pkg-config", "--cflags", "openssl"], capture_output=True, text=True)
for name in ["native/tls.c", "native/verify.c", "native/sign.c", "native/lanes.c"]:
    source = open(name).read()
    pairs = []
    if "enum {" in source:
        start = source.index("enum {")
        end = source.index("};", start) + 2
        pairs = re.findall(r"(\w+) = (0x[0-9a-fA-F]+|\d+)", source[start:end])
        asserts = "\n".join(f'_Static_assert({k} == {v}, "{k}");' for k, v in pairs)
        source = source[:start] + asserts + source[end:]
    with tempfile.TemporaryDirectory() as scratch:
        path = os.path.join(scratch, "check.c")
        open(path, "w").write(HEADERS + source)
        result = subprocess.run(["cc", "-fsyntax-only", "-Wall", "-Werror",
                                 "-I", os.path.join(lean.stdout.strip(), "include"),
                                 *flags.stdout.split(), path])
    if result.returncode != 0:
        sys.exit(f"{name} declares OpenSSL otherwise than its headers do")
    print(f"{name}: its declarations and {len(pairs)} constants agree with OpenSSL's headers")
