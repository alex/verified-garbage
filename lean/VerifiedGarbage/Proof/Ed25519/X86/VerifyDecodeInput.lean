import VerifiedGarbage.Impl.Ed25519.X86.Verify
import VerifiedGarbage.Proof.Ed25519.X86.VerifyContract
import VerifiedGarbage.Proof.Ed25519.X86.PointDecode
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
import VerifiedGarbage.Proof.Ed25519.Decode

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem decodeNumber_spec (bs : List Byte) (hl : bs.length = 32) :
    decodeNumber (Spec.Ed25519.decodeLE bs) = Spec.Ed25519.decodePoint bs := by
  rw [decodePoint32 bs hl]
  by_cases hy : Spec.Ed25519.decodeLE bs % 2 ^ 255 < Spec.X25519.P
  · rw [decodeNumber, dite_eq_left hy, ite_eq_left hy, toFe_of_lt _ hy]
    rfl
  · rw [decodeNumber, dite_eq_right hy, ite_eq_right hy]

def inputPoint (s : State) (i : Nat) : Option Spec.Ed25519.Point :=
  Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem ((arg s i + BitVec.ofNat 32 0).setWidth 64) 32)

theorem decodeInput_number_ok {s₀ s : State} {i : Nat} (hp : ScratchPre s₀ 3 4)
    (hi : SlicePre s₀ 3 (arg s₀ i + BitVec.ofNat 32 0) 32)
    (hs : Saved s₀ (arg s₀ 3) s) (hia : i < 4) :
    WP isa (.seq (.block (inputSliceWords i 0 96 8)) pointDecode) s fun t =>
      Saved s₀ (arg s₀ 3) t ∧ Frame [sub (arg s₀ 3) 24 7144] s.mem t.mem ∧
      DecodeResult (arg s₀ 3) (decodeNumber (fe s₀.mem (arg s₀ i + BitVec.ofNat 32 0) 0)) t := by
  refine WP.seq (WP.mono (inputSliceWords_ok hp hi hs hia (by decide) (by decide) (by decide))
    fun a ⟨ha, wa, fa⟩ => ?_)
  refine WP.mono (pointDecode_ok (ha.ctx hp.fit hp.wr)) fun t ht => ?_
  have kt := ht.1
  refine ⟨ha.mulkeep hp.fit kt, (frameWiden fa hp.fit (by decide) (by decide) (by decide)).trans kt.frame, ?_⟩
  have value : fe a.mem (arg s₀ 3) 96 = fe s₀.mem (arg s₀ i + BitVec.ofNat 32 0) 0 := by
    apply num_congr
    intro k hk
    simp only [Nat.zero_add]
    exact congrArg BitVec.toNat (wa k hk)
  with_reducible exact Eq.mp (congrArg (fun n => DecodeResult (arg s₀ 3) (decodeNumber n) t) value) ht.2

theorem inputPoint_number {s : State} {i : Nat} (hi : SlicePre s 3 (arg s i + BitVec.ofNat 32 0) 32) :
    decodeNumber (fe s.mem (arg s i + BitVec.ofNat 32 0) 0) = inputPoint s i := by
  have hv : fe s.mem (arg s i + BitVec.ofNat 32 0) 0 = Spec.Ed25519.decodeLE
      (Spec.Ed25519.bytesAt s.mem ((arg s i + BitVec.ofNat 32 0).setWidth 64) 32) := by
    rw [← addr_zero (arg s i + BitVec.ofNat 32 0)]
    exact (decode_words s.mem 8 (by have := hi.fit; omega_using [this])).symm
  exact (congrArg decodeNumber hv).trans (decodeNumber_spec _
    (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]))

theorem decodeInput_ok {s₀ s : State} {i : Nat} (hp : ScratchPre s₀ 3 4)
    (hi : SlicePre s₀ 3 (arg s₀ i + BitVec.ofNat 32 0) 32)
    (hs : Saved s₀ (arg s₀ 3) s) (hia : i < 4) :
    WP isa (.seq (.block (inputSliceWords i 0 96 8)) pointDecode) s fun t =>
      Saved s₀ (arg s₀ 3) t ∧ Frame [sub (arg s₀ 3) 24 7144] s.mem t.mem ∧
      DecodeResult (arg s₀ 3) (inputPoint s₀ i) t := by
  refine WP.mono (decodeInput_number_ok hp hi hs hia) fun t ht => ⟨ht.1, ht.2.1, ?_⟩
  with_reducible exact Eq.mp (congrArg (fun p => DecodeResult (arg s₀ 3) p t) (inputPoint_number hi)) ht.2.2

theorem decodedThen_ok {s₀ s : State} {p : Option Spec.Ed25519.Point} {next : Prog isa} {P : State → Prop}
    (hs : Saved s₀ (arg s₀ 3) s) (hr : DecodeResult (arg s₀ 3) p s)
    (hn : ∀ t, Saved s₀ (arg s₀ 3) t → t.mem = s.mem → p = none → WP isa recoverInvalid t P)
    (hy : ∀ t a, Saved s₀ (arg s₀ 3) t → t.mem = s.mem → p = some a →
      point (env t.mem (arg s₀ 3)) 0 1 2 3 = a → WP isa next t P) :
    WP isa (decodedThen next) s P := by
  refine WP.seq (Wp.wp_test fun t ht zt => WP.block_nil ?_)
  have ht' : Saved s₀ (arg s₀ 3) t := ⟨by rw [ht.gpr]; exact hs.edi,
    by rw [ht.gpr]; exact hs.esp, ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    by rw [ht.mem]; exact hs.frame, by rw [ht.mem]; exact hs.saved⟩
  cases he : p with
  | none =>
    rw [he] at hr
    change s.gpr .eax = 0 at hr
    apply WP.ite false (by show t.zf.map (!·) = _; rw [zt, BitVec.and_self, hr]; rfl)
    · intro h; contradiction
    · intro _; exact hn t ht' ht.mem he
  | some a =>
    rw [he] at hr
    apply WP.ite true (by show t.zf.map (!·) = _; rw [zt, BitVec.and_self, hr.1]; rfl)
    · intro _; exact hy t a ht' ht.mem he (by rw [ht.mem]; exact hr.2)
    · intro h; contradiction

end VG.Proof.Ed25519.X86
