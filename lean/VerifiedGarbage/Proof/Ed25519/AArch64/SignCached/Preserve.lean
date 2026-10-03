import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Args
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.HashPre

/-! Merged from `Proof.Ed25519.AArch64.SignCached.Calls`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

variable {L : Lay}

def field (L : Lay) (d : Nat) : Region := ⟨L.E + BitVec.ofNat 64 d, 32⟩
def digest (L : Lay) : Region := ⟨L.E + BitVec.ofNat 64 192, 64⟩
def baseOut (L : Lay) : Region := ⟨L.out, 32⟩
def half (L : Lay) : Region := ⟨L.out + BitVec.ofNat 64 32, 32⟩

theorem fieldWithin (L : Lay) {d : Nat} (hd : d + 32 ≤ 256) : Whole.Within (field L d) L.FR :=
  ⟨d, rfl, hd⟩
theorem digestWithin (L : Lay) : Whole.Within (digest L) L.FR := ⟨192, rfl, by change 192 + 64 ≤ 256; decide⟩
theorem baseWithin (L : Lay) : Whole.Within (baseOut L) L.OUT := ⟨0, by simp [baseOut], by change 0 + 32 ≤ 64; decide⟩
theorem halfWithin (L : Lay) : Whole.Within (half L) L.OUT := ⟨32, rfl, by change 32 + 32 ≤ 64; decide⟩
theorem scratchWithin (L : Lay) : Whole.Within L.SCR L.SCR := ⟨0, by simp, by simp⟩

theorem covers {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r L.FR ∨ ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R) :
    Covers rs (L.inputs ++ L.FR :: L.outputs) := by
  apply Covers.of_sub
  intro r hr
  rcases h r hr with hf | ⟨R, hR, hsub⟩
  · exact ⟨L.FR, List.mem_append_right _ List.mem_cons_self, hf⟩
  · refine ⟨R, ?_, hsub⟩
    rcases List.mem_append.mp hR with hi | ho
    · exact List.mem_append_left _ hi
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ ho)

theorem scratch_covered (L : Lay) : ∃ R ∈ L.inputs ++ L.outputs, Whole.Within L.SCR R :=
  ⟨L.SCR, by simp [Lay.outputs], scratchWithin L⟩

theorem output_covered {r : Region} (h : Whole.Within r L.OUT) :
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R :=
  ⟨L.OUT, by simp [Lay.outputs], h⟩

theorem writes {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r L.FR ∨ Whole.Within r L.OUT ∨ Whole.Within r L.SCR) :
    ∀ r ∈ rs, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  rcases h r hr with hf | ho | hs
  · exact .inl hf
  · exact .inr ⟨L.OUT, by simp [Lay.outputs], ho⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], hs⟩

theorem field_scr (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256) :
    (field L d).Disjoint L.SCR := hL.kc.sub_left (fieldWithin L hd).sub

theorem field_mem {m n : Mem} (hm : n = m) (d : Nat) :
    Spec.Ed25519.bytesAt n (L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (L.E + BitVec.ofNat 64 d) 32 := by rw [hm]

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.Hashes`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.SignCached.HashSteps`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.SignCached.Hash`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

abbrev Backend := Whole.Backend
def hashWrites (L : Lay) : List Region := [L.SCR, digest L, L.CK]

theorem hash_frame {L : Lay} {m n : Mem} {ws : List Region} (hf : Frame ws m n)
    (hw : ∀ r ∈ ws, Region.Sub r L.SCR ∨ Region.Sub r (digest L) ∨ Region.Sub r L.CK) :
    Frame (hashWrites L) m n := by
  refine Frame.sub hf fun r hr => ?_
  rcases hw r hr with hs | hd | hk
  · exact ⟨L.SCR, by simp [hashWrites], hs⟩
  · exact ⟨digest L, by simp [hashWrites], hd⟩
  · exact ⟨L.CK, by simp [hashWrites], hk⟩

theorem init_frame {L : Lay} {m n : Mem} (hf : Frame (Whole.initWr L.scr) m n) :
    Frame (hashWrites L) m n := by
  apply hash_frame hf
  intro r hr; rw [List.mem_singleton.mp hr]
  exact .inl (Whole.sha_sub L.scr)

theorem update_frame {L : Lay} {m n : Mem} (hf : Frame (Whole.hashWr L.scr ++ [L.CK]) m n) :
    Frame (hashWrites L) m n := by
  apply hash_frame hf
  simp only [Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inl (Whole.sha_sub L.scr)
  · exact .inl (Whole.work_sub L.scr)
  · exact .inr (.inr fun _ h => h)

theorem finalize_frame {L : Lay} {m n : Mem}
    (hf : Frame (Whole.finalizeWr L.scr (L.E + 192) ++ [L.CK]) m n) : Frame (hashWrites L) m n := by
  apply hash_frame hf
  simp only [Whole.finalizeWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact .inl (Whole.sha_sub L.scr)
  · exact .inr (.inl fun _ h => h)
  · exact .inl (Whole.work_sub L.scr)
  · exact .inr (.inr fun _ h => h)

theorem final_writes (L : Lay) :
    ∀ r ∈ Whole.finalizeWr L.scr (L.E + 192),
      Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, by simp, by change 0+192≤8192; decide⟩
  · exact .inl (digestWithin L)
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 192, rfl, by change 192+688≤8192; decide⟩

variable {L : Lay} {g : Reg → BitVec 64} {vec : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem init_step (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa init s fun t => Ctx L g vec m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr [] := by
  refine WP.seq (WP.mono (args_ok hc hL ha (args := [(.x0, .caller 5 0)])
    (by decide) (by simp [Whole.valid]) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.x0, .caller 5 0) (by simp)
  change u.gpr .x0 = L.scr + 0#64 at a0
  rw [BitVec.add_zero] at a0
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  refine WP.mono (Whole.init_call hu (Whole.init_pre a0) (Whole.covers_writes hw) hw a0)
    fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, hp⟩
  rw [hm] at hf
  exact init_frame hf

structure Input (L : Lay) (p n : Addr) : Prop where
  cover : Whole.Within ⟨p, n.toNat⟩ L.FR ∨ ∃ R ∈ L.inputs ++ L.outputs, Whole.Within ⟨p,n.toNat⟩ R
  scratch : Region.Disjoint ⟨p,n.toNat⟩ L.SCR

/-- A hashed input is outside the frame of the hash function's calls. -/
theorem Input.ck {p n : Addr} (hL : L.Ok) (hi : Input L p n) : L.CK.Disjoint ⟨p, n.toNat⟩ := by
  rcases hi.cover with ⟨off, hb, hl⟩ | ⟨R, hR, hw⟩
  · simp only at hb hl
    rw [hb]
    exact Whole.ck_frame (by change off + n.toNat ≤ 256 at hl; omega)
  · refine Region.Disjoint.sub_right ?_ hw.sub
    simp only [Lay.outputs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with hR | rfl | rfl
    · exact hL.ck R hR
    · exact hL.co
    · exact hL.cc

theorem update_covers {p n : Addr} (hi : Input L p n) :
    Covers (Whole.updateRd p n ++ Whole.hashWr L.scr) (L.inputs ++ L.FR :: L.outputs) := by
  apply covers
  simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hi.cover
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, by simp, by change 0+192≤8192; decide⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 192, rfl, by change 192+688≤8192; decide⟩

end VG.Proof.Ed25519.AArch64.SignCached
end

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
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.HashUpdates`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.SignCached.HashInputs`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64

variable {L : Lay}

theorem input_self {r : Region} (hr : r ∈ L.inputs) :
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R :=
  ⟨r, List.mem_append_left _ hr, 0, by simp, by simp⟩

theorem seed_input (hL : L.Ok) : Input L L.seed 32 :=
  ⟨.inr (input_self (r := L.SEED) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs])⟩
theorem key_input (hL : L.Ok) : Input L L.pk 32 :=
  ⟨.inr (input_self (r := L.PK) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs])⟩
theorem message_input (hL : L.Ok) : Input L L.msg L.len :=
  ⟨.inr (input_self (r := L.MSG) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs])⟩
theorem point_input (hL : L.Ok) : Input L L.out 32 :=
  ⟨.inr (output_covered (baseWithin L)), hL.oc.sub_left (baseWithin L).sub⟩
theorem prefix_input (hL : L.Ok) : Input L (L.E + 64) 32 :=
  ⟨.inl (fieldWithin L (by decide)), field_scr hL (by decide)⟩

theorem frame_bytes {m n : Mem} {ws : List Region} (hf : Frame ws m n) (r : Region)
    (hd : ∀ w ∈ ws, r.Disjoint w) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt n r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  exact Frame.bytes hf hd hn (List.mem_range.mp hi)

theorem hash_field_bytes {m n : Mem} (hL : L.Ok) (hf : Frame (hashWrites L) m n)
    {d : Nat} (hd : d + 32 ≤ 192) :
    Spec.Ed25519.bytesAt n (L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (L.E + BitVec.ofNat 64 d) 32 := by
  apply frame_bytes hf (field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact field_scr hL (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by decide)
  · exact (Whole.ck_frame (by omega)).symm

theorem hash_out_bytes {m n : Mem} (hL : L.Ok) (hf : Frame (hashWrites L) m n) :
    Spec.Ed25519.bytesAt n L.out 32 = Spec.Ed25519.bytesAt m L.out 32 := by
  apply frame_bytes hf (baseOut L) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.oc.sub_left (baseWithin L).sub
  · exact (hL.ko.sub_right (baseWithin L).sub).symm.sub_right (digestWithin L).sub
  · exact (hL.co.sub_right (baseWithin L).sub).symm

theorem bytes_length (m : Mem) (p : Addr) (n : Nat) :
    (Spec.Ed25519.bytesAt m p n).length = n := by simp [Spec.Ed25519.bytesAt]

end VG.Proof.Ed25519.AArch64.SignCached
end

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
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

variable {L : Lay} {g : Reg → BitVec 64} {vec : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem hashSeed_ok (b : Backend) (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (hashSeed b.code b.suffix) s fun t => Ctx L g vec m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ (L.seed) 32) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (update_input b hu hL ha 1 0 (by decide) (by decide) (seed_input hL)
    (by decide) ru) fun v ⟨hv, fv, rv⟩ => ?_)
  have hs := hu.input_bytes hL (r := L.SEED) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  change Spec.Ed25519.bytesAt u.mem (L.seed) 32 = Spec.Ed25519.bytesAt m₀ (L.seed) 32 at hs
  change Spec.Sha512.Repr _ v.mem _ ([] ++ Spec.Ed25519.bytesAt u.mem (L.seed) 32) at rv
  rw [List.nil_append, hs] at rv
  refine WP.mono (finalize_step b hv hL ha 32 (by decide) false
    (by rw [bytes_length]; decide) (by rw [bytes_length]; rfl) rv)
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans ft), hd⟩

theorem hashNonce_ok (b : Backend) (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (hashNonce b.code b.suffix) s fun t => Ctx L g vec m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (L.E + 64) 32 ++
          Spec.Ed25519.bytesAt m₀ (L.msg) L.len.toNat) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (update_prefix b hu hL ha ru) fun v ⟨hv, fv, rv⟩ => ?_)
  have keep := hash_field_bytes hL fu (d := 64) (by decide)
  change Spec.Ed25519.bytesAt u.mem (L.E + (64 : BitVec 64)) 32 = Spec.Ed25519.bytesAt s.mem (L.E + (64 : BitVec 64)) 32 at keep
  rw [keep] at rv
  refine WP.seq (WP.mono (update_message b hv hL ha 32 (by decide) (by rw [bytes_length]) rv)
    fun w ⟨hw, fw, rw'⟩ => ?_)
  refine WP.mono (finalize_step b hw hL ha 32 (by decide) true ?_ ?_ rw')
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans (fw.trans ft)), hd⟩
  · rw [List.length_append, bytes_length, bytes_length]
    have := hL.message_bound; omega
  · rw [List.length_append, bytes_length, bytes_length]
    simp only [ite_true]; omega

theorem hashChallenge_ok (b : Backend) (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (hashChallenge b.code b.suffix) s fun t => Ctx L g vec m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (L.out) 32 ++
          Spec.Ed25519.bytesAt m₀ (L.pk) 32 ++
          Spec.Ed25519.bytesAt m₀ (L.msg) L.len.toNat) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (update_input b hu hL ha 0 0 (by decide) (by decide) (point_input hL)
    (by decide) ru) fun v ⟨hv, fv, rv⟩ => ?_)
  change Spec.Sha512.Repr _ v.mem _ ([] ++ Spec.Ed25519.bytesAt u.mem (L.out) 32) at rv
  rw [List.nil_append, hash_out_bytes hL fu] at rv
  refine WP.seq (WP.mono (update_input b hv hL ha 2 32 (by decide) (by decide) (key_input hL)
    (by rw [bytes_length]) rv) fun w ⟨hw, fw, rw'⟩ => ?_)
  have hk := hv.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  change Spec.Ed25519.bytesAt v.mem (L.pk) 32 = Spec.Ed25519.bytesAt m₀ (L.pk) 32 at hk
  change Spec.Sha512.Repr _ w.mem _ (_ ++ Spec.Ed25519.bytesAt v.mem (L.pk) 32) at rw'
  rw [hk] at rw'
  refine WP.seq (WP.mono (update_message b hw hL ha 64 (by decide) (by rw [List.length_append, bytes_length, bytes_length])
    rw') fun z ⟨hz, fz, rz⟩ => ?_)
  refine WP.mono (finalize_step b hz hL ha 64 (by decide) true ?_ ?_ rz)
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans (fw.trans (fz.trans ft))), hd⟩
  · rw [List.length_append, List.length_append, bytes_length, bytes_length, bytes_length]
    have := hL.message_bound; omega
  · rw [List.length_append, List.length_append, bytes_length, bytes_length, bytes_length]
    simp only [ite_true]; omega

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.Reduce`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached
open VG.Impl.Ed25519.AArch64 (scalarReduce)

def reduceRd (L : Lay) : List Region := [digest L]
def reduceWr (L : Lay) (d : Nat) : List Region := [field L d, L.SCR]
def ReduceArgs (L : Lay) (d : Nat) (s : State) : Prop :=
  s.gpr .x0 = L.E + BitVec.ofNat 64 d ∧ s.gpr .x1 = L.E + 192 ∧ s.gpr .x2 = L.scr

theorem reduce_noFrames : scalarReduce.noFrames = true := by lit_decide

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem reduce_pre (hL : L.Ok) {d : Nat} (ha : ReduceArgs L d s) :
    scalarReduceLocal.pre (s.callEntry.withRegions (reduceRd L) (reduceWr L d)) := by
  simp only [scalarReduceLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), ha.1, ha.2.1, ha.2.2]
  exact ⟨rfl, rfl, hL.kc.sub_left (digestWithin L).sub⟩

theorem reduce_call (hc : Ctx L g v m₀ s) (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256)
    (ha : ReduceArgs L d s) :
    WP isa (.call "vg_ed25519_scalar_reduce" scalarReduce) s fun t => Ctx L g v m₀ t ∧
      Frame (reduceWr L d) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + BitVec.ofNat 64 d) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E + 192) 64) := by
  have cov : Covers (reduceRd L ++ reduceWr L d) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (digestWithin L)
    · exact .inl (fieldWithin L hd)
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ reduceWr L d, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (fieldWithin L hd)
    · exact .inr (.inr (scratchWithin L))
  refine Whole.call_ok hc scalarReduce_ok reduce_noFrames (reduce_pre hL ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  simpa only [scalarReduceLocal, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), ha.1, ha.2.1] using hp

theorem reduce_step (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (d : Nat) (hd : d + 32 ≤ 256) :
    WP isa (reduce d) s fun t => Ctx L g v m₀ t ∧ Frame (reduceWr L d) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + BitVec.ofNat 64 d) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E + 192) 64) := by
  refine WP.seq (WP.mono (args_ok hc hL ha
    (args := [(.x0, .frame d), (.x1, .frame 192), (.x2, .caller 5 0)])
    (by simp) (by simp [Whole.valid]; omega) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.x0, .frame d) (by simp)
  have a1 := hs (.x1, .frame 192) (by simp)
  have a2 := hs (.x2, .caller 5 0) (by simp)
  change u.gpr .x2 = L.scr + 0#64 at a2
  rw [BitVec.add_zero] at a2
  refine WP.mono (reduce_call hu hL hd ⟨a0, a1, a2⟩) fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, ?_⟩
  · rw [hm] at hf; exact hf
  · rw [hm] at hp; exact hp

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.Base`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached
open VG.Impl.Ed25519.AArch64 (scalarBase)
open VG.Impl.Ed25519.AArch64.Whole (callWith)

def baseRd (L : Lay) : List Region := [field L 96]
def baseWr (L : Lay) : List Region := [baseOut L, L.SCR]
def BaseArgs (L : Lay) (s : State) : Prop :=
  s.gpr .x0 = L.out ∧ s.gpr .x1 = L.E + 96 ∧ s.gpr .x2 = L.scr

theorem base_noFrames : scalarBase.noFrames = true := by lit_decide

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem base_pre (hL : L.Ok) (ha : BaseArgs L s) :
    scalarBaseLocal.pre (s.callEntry.withRegions (baseRd L) (baseWr L)) := by
  simp only [scalarBaseLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), ha.1, ha.2.1, ha.2.2]
  exact ⟨rfl, rfl, field_scr hL (by decide), hL.nc⟩

theorem base_call (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : BaseArgs L s) :
    WP isa (.call "vg_ed25519_scalar_base" scalarBase) s fun t => Ctx L g v m₀ t ∧
      Frame (baseWr L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem L.out 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem (L.E + 96) 32) := by
  have cov : Covers (baseRd L ++ baseWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [baseRd, baseWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (fieldWithin L (by decide))
    · exact .inr (output_covered (baseWithin L))
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ baseWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [baseWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (.inl (baseWithin L))
    · exact .inr (.inr (scratchWithin L))
  refine Whole.call_ok hc scalarBase_ok base_noFrames (base_pre hL ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  simpa only [scalarBaseLocal, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), ha.1, ha.2.1] using hp

theorem base_step (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith baseArgs "vg_ed25519_scalar_base" scalarBase) s fun t =>
      Ctx L g v m₀ t ∧ Frame (baseWr L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem L.out 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem (L.E + 96) 32) := by
  refine WP.seq (WP.mono (args_ok hc hL ha
    (args := [(.x0, .caller 0 0), (.x1, .frame 96), (.x2, .caller 5 0)])
    (by decide) (by simp [Whole.valid]) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.x0, .caller 0 0) (by simp)
  have a1 := hs (.x1, .frame 96) (by simp)
  have a2 := hs (.x2, .caller 5 0) (by simp)
  change u.gpr .x0 = L.out + 0#64 at a0
  change u.gpr .x2 = L.scr + 0#64 at a2
  rw [BitVec.add_zero] at a0 a2
  refine WP.mono (base_call hu hL ⟨a0, a1, a2⟩) fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, ?_⟩
  · rw [hm] at hf; exact hf
  · rw [hm] at hp; exact hp

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.MulAdd`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached
open VG.Impl.Ed25519.AArch64 (scalarMulAdd)
open VG.Impl.Ed25519.AArch64.Whole (callWith)

def mulRd (L : Lay) : List Region := [field L 96, field L 128, field L 32]
def mulWr (L : Lay) : List Region := [half L, L.SCR]
def MulArgs (L : Lay) (s : State) : Prop :=
  s.gpr .x0 = L.out + 32 ∧ s.gpr .x1 = L.E + 96 ∧ s.gpr .x2 = L.E + 128 ∧
    s.gpr .x3 = L.E + 32 ∧ s.gpr .x4 = L.scr

theorem mul_noFrames : scalarMulAdd.noFrames = true := by lit_decide

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem mul_pre (hL : L.Ok) (ha : MulArgs L s) :
    scalarMulAddLocal.pre (s.callEntry.withRegions (mulRd L) (mulWr L)) := by
  simp only [scalarMulAddLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs),
    ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2]
  exact ⟨rfl, rfl, field_scr hL (by decide), field_scr hL (by decide), field_scr hL (by decide), hL.nc⟩

theorem mul_call (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : MulArgs L s) :
    WP isa (.call "vg_ed25519_scalar_mul_add" scalarMulAdd) s fun t => Ctx L g v m₀ t ∧
      Frame (mulWr L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.out + 32) 32 = Spec.Ed25519.scalarMulAdd
        (Spec.Ed25519.bytesAt s.mem (L.E + 96) 32) (Spec.Ed25519.bytesAt s.mem (L.E + 128) 32)
        (Spec.Ed25519.bytesAt s.mem (L.E + 32) 32) := by
  have cov : Covers (mulRd L ++ mulWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [mulRd, mulWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact .inl (fieldWithin L (by decide))
    · exact .inl (fieldWithin L (by decide))
    · exact .inl (fieldWithin L (by decide))
    · exact .inr (output_covered (halfWithin L))
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ mulWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [mulWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (.inl (halfWithin L))
    · exact .inr (.inr (scratchWithin L))
  refine Whole.call_ok hc scalarMulAdd_ok mul_noFrames (mul_pre hL ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  simpa only [scalarMulAddLocal, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1] using hp

theorem mul_step (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith mulAddArgs "vg_ed25519_scalar_mul_add" scalarMulAdd) s fun t =>
      Ctx L g v m₀ t ∧ Frame (mulWr L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.out + 32) 32 = Spec.Ed25519.scalarMulAdd
        (Spec.Ed25519.bytesAt s.mem (L.E + 96) 32) (Spec.Ed25519.bytesAt s.mem (L.E + 128) 32)
        (Spec.Ed25519.bytesAt s.mem (L.E + 32) 32) := by
  refine WP.seq (WP.mono (args_ok hc hL ha
    (args := [(.x0, .caller 0 32), (.x1, .frame 96), (.x2, .frame 128), (.x3, .frame 32), (.x4, .caller 5 0)])
    (by decide) (by simp [Whole.valid]) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.x0, .caller 0 32) (by simp)
  have a1 := hs (.x1, .frame 96) (by simp)
  have a2 := hs (.x2, .frame 128) (by simp)
  have a3 := hs (.x3, .frame 32) (by simp)
  have a4 := hs (.x4, .caller 5 0) (by simp)
  change u.gpr .x4 = L.scr + 0#64 at a4
  rw [BitVec.add_zero] at a4
  refine WP.mono (mul_call hu hL ⟨a0, a1, a2, a3, a4⟩) fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, ?_⟩
  · rw [hm] at hf; exact hf
  · rw [hm] at hp; exact hp

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64
variable {L : Lay} {m n : Mem}

theorem single_frame_bytes {d e k : Nat} (hf : Frame [⟨L.E + BitVec.ofNat 64 e, k⟩] m n)
    (hd : d + 32 ≤ 256) (he : e + k ≤ 256) (hs : d + 32 ≤ e ∨ e + k ≤ d) :
    Spec.Ed25519.bytesAt n (L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (L.E + BitVec.ofNat 64 d) 32 := by
  apply frame_bytes hf (field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ hs (by omega) (by omega)

theorem reduce_field_bytes (hL : L.Ok) {d out : Nat} (hf : Frame (reduceWr L out) m n)
    (hd : d + 32 ≤ 256) (ho : out + 32 ≤ 256) (hs : d + 32 ≤ out ∨ out + 32 ≤ d) :
    Spec.Ed25519.bytesAt n (L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (L.E + BitVec.ofNat 64 d) 32 := by
  apply frame_bytes hf (field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Offset.disjoint _ hs (by omega) (by omega)
  · exact field_scr hL hd

theorem base_field_bytes (hL : L.Ok) (hf : Frame (baseWr L) m n) {d : Nat} (hd : d + 32 ≤ 256) :
    Spec.Ed25519.bytesAt n (L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (L.E + BitVec.ofNat 64 d) 32 := by
  apply frame_bytes hf (field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [baseWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact (hL.ko.sub_left (fieldWithin L hd).sub).sub_right (baseWithin L).sub
  · exact field_scr hL hd

theorem reduce_out_bytes (hL : L.Ok) {d : Nat} (hf : Frame (reduceWr L d) m n) (hd : d + 32 ≤ 256) :
    Spec.Ed25519.bytesAt n L.out 32 = Spec.Ed25519.bytesAt m L.out 32 := by
  apply frame_bytes hf (baseOut L) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact ((hL.ko.sub_left (fieldWithin L hd).sub).sub_right (baseWithin L).sub).symm
  · exact hL.oc.sub_left (baseWithin L).sub

theorem mul_out_bytes (hL : L.Ok) (hf : Frame (mulWr L) m n) :
    Spec.Ed25519.bytesAt n L.out 32 = Spec.Ed25519.bytesAt m L.out 32 := by
  apply frame_bytes hf (baseOut L) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [mulWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Offset.base_disjoint _ (by decide) (by decide)
  · exact hL.oc.sub_left (baseWithin L).sub

end VG.Proof.Ed25519.AArch64.SignCached
