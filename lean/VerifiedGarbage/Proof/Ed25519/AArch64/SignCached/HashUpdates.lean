import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.HashInputs

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

variable {L : Lay} {g : Reg → BitVec 64} {vec : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem update_input (v : Backend) (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (source count : Nat) (hj : source < 6) (hc16 : count < 65536) (hi : Input L (L.value source) 32)
    {prev : List Byte} (hcount : count = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr prev) :
    WP isa (update v.code v.suffix (inputArgs source count)) s fun t => Ctx L g vec m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt s.mem (L.value source) 32) := by
  have inp : Input L (value L (.caller source 0)) (value L (.const 32)) := by
    change Input L (L.value source + 0#64) 32#64
    rw [BitVec.add_zero]
    exact hi
  refine WP.mono (update_step v hc hL ha count (.caller source 0) (.const 32) hc16
    ⟨hj, by decide⟩ (by simp [Whole.valid]) inp hcount hr) fun t ⟨ht, hf, hh⟩ => ⟨ht, hf, ?_⟩
  change Spec.Sha512.Repr _ t.mem _ (prev ++ Spec.Ed25519.bytesAt s.mem (L.value source + 0#64) 32) at hh
  rw [BitVec.add_zero] at hh
  exact hh

theorem update_prefix (v : Backend) (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr []) :
    WP isa (update v.code v.suffix prefixArgs) s fun t => Ctx L g vec m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (Spec.Ed25519.bytesAt s.mem (L.E + 64) 32) := by
  refine WP.mono (update_step v hc hL ha 0 (.frame 64) (.const 32) (by decide)
    (by simp [Whole.valid]) (by simp [Whole.valid]) (prefix_input hL) rfl hr) fun t ⟨ht, hf, hh⟩ => ⟨ht, hf, ?_⟩
  change Spec.Sha512.Repr _ t.mem _ ([] ++ Spec.Ed25519.bytesAt s.mem (L.E + 64) 32) at hh
  rw [List.nil_append] at hh
  exact hh

theorem update_message (v : Backend) (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (count : Nat) (hc16 : count < 65536) {prev : List Byte} (hcount : count = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr prev) :
    WP isa (update v.code v.suffix (messageArgs count)) s fun t => Ctx L g vec m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat) := by
  have inp : Input L (value L (.caller 3 0)) (value L (.caller 4 0)) := by
    simpa only [value, Lay.value, BitVec.add_zero] using message_input hL
  refine WP.mono (update_step v hc hL ha count (.caller 3 0) (.caller 4 0) hc16
    (by simp [Whole.valid]) (by simp [Whole.valid]) inp hcount hr) fun t ⟨ht, hf, hh⟩ => ⟨ht, hf, ?_⟩
  simp only [value, Lay.value, BitVec.add_zero] at hh
  rw [hc.input_bytes hL (r := L.MSG) (by simp [Lay.inputs]) (Nat.le_of_lt L.len.isLt)] at hh
  exact hh

end VG.Proof.Ed25519.AArch64.SignCached
