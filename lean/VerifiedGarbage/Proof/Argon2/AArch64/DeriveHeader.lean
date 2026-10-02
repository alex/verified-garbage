import VerifiedGarbage.Proof.Argon2.AArch64.DeriveWords

/-! H₀ hashes the original requested memory cost and the exact reviewed parameters. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

theorem private_header {s t : State} (words : DeriveWords s t) :
    Initial.headerBytes t = Proof.Argon2.initialHeader (abiParams s) := by
  have headerWords : (List.range 6).map (Initial.headerValue t) =
      [BitVec.ofNat 32 (abiParams s).lanes, BitVec.ofNat 32 (abiParams s).tagLen,
        BitVec.ofNat 32 (abiParams s).memory, BitVec.ofNat 32 (abiParams s).passes,
        19#32, BitVec.ofNat 32 (abiParams s).variant.code] := by
    change [(Initial.wordAt t 184).setWidth 32, (Initial.wordAt t 264).setWidth 32,
      (Initial.wordAt t 176).setWidth 32, (Initial.wordAt t 72).setWidth 32, 19#32,
      (Initial.wordAt t 112).setWidth 32] = _
    rw [words.lanes, words.tagLength, words.memory, words.passes, words.kind]
    simp only [BitVec.setWidth_ofNat_of_le (show 32 ≤ 64 by decide)]
  unfold Initial.headerBytes
  rw [← List.flatMap_map, headerWords]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ← List.append_assoc,
    Proof.Argon2.initialHeader, Spec.Argon2.le32]

end VG.Proof.Argon2.AArch64.Derive
