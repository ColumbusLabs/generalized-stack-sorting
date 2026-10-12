"""Check the exact final pullback from the immutable quintic certificate."""
from pathlib import Path
import argparse
import hashlib
import json
import sympy as sp

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("certificate", type=Path)
args = parser.parse_args()
raw = args.certificate.read_bytes()
expected = "744a7670f06b52d38147c90059a9db57628ca5a13d18f08eaa35637e4c5179fe"
assert hashlib.sha256(raw).hexdigest() == expected, "Unexpected certificate bytes"
receipt = json.loads(raw)
x, z, F = sp.symbols("x z F")
symbols = {"x": x, "z": z, "F": F}
P = sp.sympify(receipt["polynomial"], locals=symbols)
R = sp.sympify(receipt["kernel_root_polynomial"], locals=symbols)
d = 1 + x*z*z - x*z
assert sp.cancel(R - d**5 * P.subs(F, z/d)) == 0
print(json.dumps({"status": "passed", "identity": "R10(x,z) = (1+x*z^2-x*z)^5 * P(x,z/(1+x*z^2-x*z))", "certificate_sha256": expected, "sympy_version": sp.__version__}, indent=2))
