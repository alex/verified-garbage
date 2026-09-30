import VerifiedGarbage.Impl.Ed25519.X86_64.PointFromScalar
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Ed25519.X86_64.Bits

/-! Untrusted: both the 256-bit signature scalar and the full 512-bit challenge. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs)

theorem pointFromScalarPrepare_ok {s : State} {base k : Addr} (hs : Scratch s base) (hp : s.gpr .rsi = k)
    (count : Nat) (hn0 : 0 < count) (hn : count ≤ 32)
    (hr : ∀ q < 2 * count, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 2 * count, 8192 ≤ ofs base (off k q)) :
    WP isa (pointFromScalarPrepare count) s fun t => PowersKeep base 56 7368 s t ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      env t.mem base 16 = Spec.Ed25519.d ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k (2 * count)) < 2 ^ (16 * count) ∧
      ∀ i < 16 * count, t.mem (off base (768 + i)) =
        BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k (2 * count)) / 2 ^ i) % 2) := by
  rw [pointFromScalarPrepare]
  refine WP.seq (WP.mono (expandScalarBits_ok hs hp (2 * count) (by omega) (by omega) hr hd)
    fun a ⟨ka, abits⟩ => ?_)
  have kap : PowersKeep base 56 7368 s a := by
    refine ⟨fun r hb _ hr => ka.gpr r (fun hm => ?_), ka.rd, ka.wr,
      (TableFrame.table ka.mem).mono (by decide) (by omega)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact hr (by decide)
    · exact hr (by decide)
    · exact hb rfl
  have ae : env a.mem base = env s.mem base := table_env ka.mem (by decide)
  refine WP.mono (constFieldWide_ok (ka.scratch hs) 16 Spec.Ed25519.d) fun b ⟨kb, vb⟩ => ?_
  have bd : env b.mem base 16 = Spec.Ed25519.d := by rw [vb]; rfl
  have bp : point (env b.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by rw [vb, ae]; rfl
  have hscalar : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k (2 * count)) < 2 ^ (16 * count) := by
    have h := decodeLE_lt (Spec.Ed25519.bytesAt s.mem k (2 * count))
    have hl : (Spec.Ed25519.bytesAt s.mem k (2 * count)).length = 2 * count := by
      simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
    rw [hl, show 256 = 2 ^ 8 by decide, ← Nat.pow_mul, show 8 * (2 * count) = 16 * count by omega] at h
    exact h
  have bbits : ∀ i < 16 * count, b.mem (off base (768 + i)) =
      BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k (2 * count)) / 2 ^ i) % 2) := by
    intro i hi
    rw [kb.bit _ (by omega)]
    exact abits i (by omega)
  exact ⟨kap.trans (PowersKeep.of_keep kb), bp, bd, hscalar, bbits⟩

theorem pointFromScalar_ok {s : State} {base k : Addr} (hs : Scratch s base) (hp : s.gpr .rsi = k)
    (count : Nat) (hn0 : 0 < count) (hn : count ≤ 32)
    (hr : ∀ q < 2 * count, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 2 * count, 8192 ≤ ofs base (off k q)) :
    WP isa (pointFromScalar count) s fun t => PowersKeep base 56 7368 s t ∧
      point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k (2 * count)))
          (point (env s.mem base) 0 1 2 3) ∧ env t.mem base 16 = Spec.Ed25519.d := by
  rw [pointFromScalar]
  refine WP.seq (WP.mono (pointFromScalarPrepare_ok hs hp count hn0 hn hr hd)
    fun a ⟨ka, ap, ad, ab, av⟩ => ?_)
  refine WP.mono (pointMultiply_ok (ka.scratch hs) count _ hn0 hn ab ad av) fun t ⟨tv, td, kt⟩ => ?_
  exact ⟨ka.trans kt, (by rw [tv, ap]), td⟩

end VG.Proof.Ed25519.X86_64
