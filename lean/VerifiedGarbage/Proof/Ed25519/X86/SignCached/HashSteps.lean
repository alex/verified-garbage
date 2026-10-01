import VerifiedGarbage.Proof.Ed25519.X86.SignCached.HashPreserve

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem update_input (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (source count : Nat) (hsource : source < 6) (hi : Input L (L.value source) 32)
    {prev : List Byte} (hcount : (BitVec.ofNat 32 count).toNat = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (update (inputArgs source count)) s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt s.mem ((L.value source).setWidth 64) 32) := by
  refine update_step hc hL ha (by simp) (by simp [Whole.valid, hsource]) ?_ hi hcount hr
  intro t ht
  have h := update_args hL count (.caller source 0) (.const 32) ht
  change UpdateArgs L (BitVec.ofNat 32 count) (L.value source) (32#32) t
  simpa only [value, BitVec.add_zero] using h

theorem update_prefix (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) []) :
    WP isa (update prefixArgs) s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 64) 32) := by
  have e : (L.E + 64).setWidth 64 = L.E.setWidth 64 + 64 :=
    addr_eq (x := L.E) (k := 64) (by have := hL.top; omega)
  refine WP.mono (update_step hc hL ha (c := 0#32) (by decide) (by simp [Whole.valid]) ?_
    (prefix_input hL) (prev := []) (by decide) hr) fun t ⟨ht, hf, hp⟩ => ⟨ht, hf, ?_⟩
  · intro t ht
    exact update_args hL 0 (.frame 64) (.const 32) ht
  · simpa only [List.nil_append, e, show (32 : BitVec 32).toNat = 32 from rfl] using hp

theorem update_message (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (count : Nat) {prev : List Byte} (hcount : (BitVec.ofNat 32 count).toNat = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (update (messageArgs count)) s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.mono (update_step hc hL ha (by simp) (by simp [Whole.valid]) ?_
    (message_input hL) hcount hr) fun t ⟨ht, hf, hp⟩ => ⟨ht, hf, ?_⟩
  · intro t ht
    have h := update_args hL count (.caller 3 0) (.caller 4 0) ht
    simpa only [value, Lay.value, BitVec.add_zero] using h
  · rw [hc.input_bytes hL (r := L.MSG) (by simp [Lay.inputs]) (by have := L.len.isLt; change L.len.toNat ≤ 2 ^ 64; omega)] at hp
    exact hp

end VG.Proof.Ed25519.X86.SignCached
