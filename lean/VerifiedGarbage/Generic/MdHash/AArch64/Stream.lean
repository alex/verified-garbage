import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant

/-! Streaming wrappers emitted for every registered compression backend. -/

namespace VG.Generic.MdHash.AArch64.Stream

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact := v.stream

end VG.Generic.MdHash.AArch64.Stream
