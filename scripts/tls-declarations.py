#!/usr/bin/env python3
"""Checks the OpenSSL declarations of `native/tls.c` against the system's OpenSSL headers.

The OpenSSL that `native/tls.c` links is the one Lean's toolchain ships, which has no headers,
so the file declares what it calls. This compiles the file with the system's headers included
first and its constants turned into assertions: a function declared otherwise than OpenSSL
declares it, or a constant of another value, does not compile. It needs a C compiler and
OpenSSL's headers (`libssl-dev`, or Homebrew's `openssl@3` found through pkg-config); CI runs
it on Linux. Run from the repository root.
"""
import os
import re
import subprocess
import sys
import tempfile

source = open("native/tls.c").read()
start = source.index("enum {")
end = source.index("};", start) + 2
pairs = re.findall(r"(\w+) = (0x[0-9a-fA-F]+|\d+)", source[start:end])
asserts = "\n".join(f'_Static_assert({k} == {v}, "{k}");' for k, v in pairs)
checked = ("#include <openssl/ssl.h>\n#include <openssl/x509v3.h>\n#include <openssl/err.h>\n"
           + source[:start] + asserts + source[end:])
lean = subprocess.run(["lean", "--print-prefix"], capture_output=True, text=True, check=True)
flags = subprocess.run(["pkg-config", "--cflags", "openssl"], capture_output=True, text=True)
with tempfile.TemporaryDirectory() as scratch:
    path = os.path.join(scratch, "tls-check.c")
    open(path, "w").write(checked)
    result = subprocess.run(["cc", "-fsyntax-only", "-Wall", "-Werror",
                             "-I", os.path.join(lean.stdout.strip(), "include"),
                             *flags.stdout.split(), path])
if result.returncode != 0:
    sys.exit("native/tls.c declares OpenSSL otherwise than its headers do")
print(f"native/tls.c: its declarations and {len(pairs)} constants agree with OpenSSL's headers")
