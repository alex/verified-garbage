/-!
# Numeral exponents are natural numbers

Untrusted: this only changes how terms are elaborated, not what they are.

In `x ^ 26` the type of the numeral `26` is only fixed by default instances,
which Lean tries last, once for every numeral still pending in the whole
term: elaborating a statement with many powers of numerals (`h0 < 2 ^ 26 → … →
x = (y + z / 2 ^ 26) % 2 ^ 64`) takes time quadratic in their number, up to
seconds for one theorem header. `open VG.PowLit` elaborates `x ^ 26` as
`x ^ (26 : Nat)`, which is the same term (the exponent's default type is `Nat`),
without the search.
-/

namespace VG.PowLit

/-- A numeral exponent is a `Nat`. -/
scoped macro_rules | `($x ^ $n:num) => `($x ^ ($n : Nat))

end VG.PowLit
