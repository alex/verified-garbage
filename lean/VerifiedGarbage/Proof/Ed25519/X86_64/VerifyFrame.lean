import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch

/-! Untrusted: verification preserves input buffers and its saved pointers. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside)

theorem tableFrame_work {base : Addr} {o n : Nat} {m m' : Mem}
    (h : TableFrame base o n m m') (ho : o ≤ 64) (hn : 768 ≤ o + n) : Outside base o n m m' :=
  fun p hp => h p (by omega) hp

theorem outside_bytes {base p : Addr} {o n len : Nat} {m m' : Mem}
    (h : Outside base o n m m') (hn : o + n ≤ 8192)
    (hf : ∀ i < len, 8192 ≤ ofs base (off p i)) :
    Spec.Ed25519.bytesAt m' p len = Spec.Ed25519.bytesAt m p len := by
  apply List.map_congr_left
  intro i hi
  apply h
  change ofs base (off p i) < o ∨ o + n ≤ ofs base (off p i)
  have := hf i (List.mem_range.mp hi)
  omega

theorem PowersKeep.header {base : Addr} {o n d : Nat} {s t : State}
    (h : PowersKeep base o n s t) (hd : 7936 ≤ d) (hb : d + 8 ≤ 8192) (hn : o + n ≤ 7936) :
    t.mem.readW (off base d) 64 = s.mem.readW (off base d) 64 :=
  h.mem.word (by omega) (Or.inr (by omega)) (by omega)

end VG.Proof.Ed25519.X86_64
