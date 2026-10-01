import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTBytes
import VerifiedGarbage.Proof.Ed25519.X86.VerifyDecodeInput

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem inputSliceValue_ok {s₀ s : State} {i : Nat} (hp : ScratchPre s₀ 3 4)
    (hi : SlicePre s₀ 3 (arg s₀ i + BitVec.ofNat 32 0) 32)
    (hs : Saved s₀ (arg s₀ 3) s) (hia : i < 4) :
    WP isa (.block (inputSliceWords i 0 96 8)) s fun t => Saved s₀ (arg s₀ 3) t ∧
      fe t.mem (arg s₀ 3) 96 = Spec.Ed25519.decodeLE
        (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i + BitVec.ofNat 32 0).setWidth 64) 32) := by
  refine WP.mono (inputSliceWords_ok hp hi hs hia (by decide) (by decide) (by decide)) fun t ⟨ht, wt, _⟩ => ?_
  refine ⟨ht, ?_⟩
  rw [← addr_zero (arg s₀ i + BitVec.ofNat 32 0), decode_words s₀.mem 8 (by have := hi.fit; omega_using [this])]
  apply num_congr
  intro k hk
  simp only [Nat.zero_add]
  exact congrArg BitVec.toNat (wt k hk)

theorem decodeInput_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (i : Nat) (hi : i ≤ 2)
    (is : SlicePre s₀ 3 (arg s₀ i + BitVec.ofNat 32 0) 32)
    (it : SlicePre t₀ 3 (arg t₀ i + BitVec.ofNat 32 0) 32)
    (hb : Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i + BitVec.ofNat 32 0).setWidth 64) 32 =
      Spec.Ed25519.bytesAt t₀.mem ((arg t₀ i + BitVec.ofNat 32 0).setWidth 64) 32) :
    RelCT isa (VerifySaved s₀ t₀) (.seq (.block (inputSliceWords i 0 96 8)) pointDecode) (fun _ _ => True) := by
  have hh := (inputSlice96_ct h i hi).wp (fun _ _ hp =>
    ⟨inputSliceValue_ok (verify_pre h.left).scratch is hp.1 (by omega),
      inputSliceValue_ok (verify_pre h.right).scratch it hp.2 (by omega)⟩)
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_)
    (pointDecode_ct (arg s₀ 3) (Spec.Ed25519.decodeLE
      (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i + BitVec.ofNat 32 0).setWidth 64) 32)))
  intro s t hp
  have hs := hp.2.1
  have ht := hp.2.2
  have left : DecodeCTPre (arg s₀ 3) _ s :=
    ⟨hs.1.ctx (verify_pre h.left).scratch.fit (verify_pre h.left).scratch.wr, hs.2⟩
  have right : DecodeCTPre (arg t₀ 3) (Spec.Ed25519.decodeLE
      (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i + BitVec.ofNat 32 0).setWidth 64) 32)) t :=
    ⟨ht.1.ctx (verify_pre h.right).scratch.fit (verify_pre h.right).scratch.wr,
      ht.2.trans (congrArg Spec.Ed25519.decodeLE hb.symm)⟩
  exact ⟨left, Eq.mp (congrArg (fun base => DecodeCTPre base
    (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i + BitVec.ofNat 32 0).setWidth 64) 32)) t)
    (h.args 3 (by decide)).symm) right⟩

end VG.Proof.Ed25519.X86
