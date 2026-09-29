/-!
# Index bounds by `decide`

Untrusted: this only changes how proofs are found.

`xs[i]` proves `i < n` with `get_elem_tactic`, which after `assumption` tries
the rules of `get_elem_tactic_extensible`, the most recent first. The ones
of Lean core rewrite every hypothesis (for the polymorphic ranges) and then
run `omega`: in a proof with many hypotheses, a tenth of a second or more for
every `v[1]` of a hash value, which is most of the time of some proofs. A
literal index is in bounds by `decide`, tried first here; for any other
index `decide` fails at once and the other rules run as before.
-/

macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| decide)
