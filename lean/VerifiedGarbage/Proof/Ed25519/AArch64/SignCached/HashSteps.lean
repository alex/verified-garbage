import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Hash

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached

variable {L : Lay} {g : Reg → BitVec 64} {vec : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem update_step (b : Backend) (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (count : Nat) (p n : Value) (hc16 : count < 65536) (hp : Whole.valid p) (hn : Whole.valid n)
    (hi : Input L (value L p) (value L n)) {prev : List Byte}
    (hcount : count = prev.length) (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr prev) :
    WP isa (update b.code b.suffix (setup [(.x0, .caller 5 0), (.x1, .const count),
      (.x2, p), (.x3, n), (.x4, .caller 5 192)])) s fun t => Ctx L g vec m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt s.mem (value L p) (value L n).toNat) := by
  have hv : ∀ (x : Reg × Value), x ∈ [(.x0, .caller 5 0), (.x1, .const count), (.x2, p), (.x3, n), (.x4, .caller 5 192)] →
      Whole.valid x.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl | rfl)
    · simp [Whole.valid]
    · exact hc16
    · exact hp
    · exact hn
    · simp [Whole.valid]
  refine WP.seq (WP.mono (args_ok hc hL ha (by simp) hv (by simp [preserved]))
    fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.x0, .caller 5 0) (by simp)
  have a1 := hs (.x1, .const count) (by simp)
  have a2 := hs (.x2, p) (by simp)
  have a3 := hs (.x3, n) (by simp)
  have a4 := hs (.x4, .caller 5 192) (by simp)
  change u.gpr .x0 = L.scr + 0#64 at a0
  rw [BitVec.add_zero] at a0
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  have huRepr : Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem L.scr prev := by rw [hm]; exact hr
  refine WP.mono (Whole.update_call b hu (Whole.update_pre a0 a2 a3 a4 hi.scratch
    (by rw [hu.sp]; exact hL.e16) (by rw [hu.sp]; exact hL.cc) (by rw [hu.sp]; exact hi.ck hL))
    (update_covers hi) hw a0 a2 a3 (by rw [a1]; exact congrArg (BitVec.ofNat 64) hcount) huRepr)
    fun t ⟨ht, hf, hrepr⟩ => ⟨ht, ?_, ?_⟩
  · rw [hm] at hf; exact update_frame hf
  · rw [hm] at hrepr; exact hrepr

theorem finalize_count (L : Lay) (n : Nat) (b : Bool) :
    value L (if b then Value.caller 4 n else .const n) =
      BitVec.ofNat 64 ((if b then L.len.toNat else 0) + n) := by
  cases b <;> simp [value, Lay.value, BitVec.ofNat_add]

theorem finalize_step (v : Backend) (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (n : Nat) (hn : n < 4096) (b : Bool) {msg : List Byte}
    (hlen : msg.length < 2 ^ 64) (hcount : (if b then L.len.toNat else 0) + n = msg.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr msg) :
    WP isa (finalize v.code v.suffix n b) s fun t => Ctx L g vec m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 192) 64 = Spec.Sha512.sha512 msg := by
  have hv : ∀ (x : Reg × Value), x ∈ [(.x0, .caller 5 0), (.x1, if b then .caller 4 n else .const n),
      (.x2, .frame 192), (.x3, .caller 5 192)] → Whole.valid x.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl)
    · simp [Whole.valid]
    · cases b <;> simp [Whole.valid] <;> omega
    · simp [Whole.valid]
    · simp [Whole.valid]
  refine WP.seq (WP.mono (args_ok hc hL ha (by simp) hv (by simp [preserved]))
    fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.x0, .caller 5 0) (by simp)
  have a1 := hs (.x1, if b then .caller 4 n else .const n) (by simp)
  have a2 := hs (.x2, .frame 192) (by simp)
  have a3 := hs (.x3, .caller 5 192) (by simp)
  change u.gpr .x0 = L.scr + 0#64 at a0
  rw [BitVec.add_zero] at a0
  have countEq : u.gpr .x1 = BitVec.ofNat 64 msg.length := by
    rw [a1, finalize_count, hcount]
  have huRepr : Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem L.scr msg := by rw [hm]; exact hr
  have hw := final_writes L
  refine WP.mono (Whole.finalize_call v hu (Whole.finalize_pre a0 a2 a3
    (hL.kc.sub_left (digestWithin L).sub) (by rw [hu.sp]; exact hL.e16) (by rw [hu.sp]; exact hL.cc)
    (by rw [hu.sp]; exact Whole.ck_frame (by decide : 192 + 64 ≤ 304)))
    (Whole.covers_writes hw) hw a0 a2 countEq huRepr hlen)
    fun t ⟨ht, hf, hh⟩ => ⟨ht, ?_, hh⟩
  rw [hm] at hf
  exact finalize_frame hf

end VG.Proof.Ed25519.AArch64.SignCached
