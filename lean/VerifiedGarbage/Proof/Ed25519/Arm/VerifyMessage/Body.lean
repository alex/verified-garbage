import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Calls
import VerifiedGarbage.Proof.Sha512.Stream
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.HashPre
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Args
import VerifiedGarbage.Impl.Ed25519.Arm.VerifyMessage
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wipe
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Equation

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.HashSteps`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.HashReady`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.HashInputs`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.HashFrame`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm
variable {L : Lay}

def slots (L : Lay) : Region := ⟨State.addr L.E, 24⟩
def hashWrites (L : Lay) : List Region := [L.SCR, slots L, digest L]

theorem setup_frame {m n : Mem} (hf : Frame [slots L] m n) : Frame (hashWrites L) m n :=
  hf.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨slots L, by simp [hashWrites], fun _ h => h⟩

theorem hash_frame {m n : Mem} {rs : List Region} (hf : Frame rs m n)
    (hw : ∀ r ∈ rs, Whole.Within r L.SCR ∨ Whole.Within r (digest L)) : Frame (hashWrites L) m n := by
  refine hf.sub fun r hr => ?_
  rcases hw r hr with hc | hd
  · exact ⟨L.SCR, by simp [hashWrites], hc.sub⟩
  · exact ⟨digest L, by simp [hashWrites], hd.sub⟩

theorem frame_bytes {m n : Mem} {ws : List Region} (hf : Frame ws m n) (r : Region)
    (hd : ∀ w ∈ ws, r.Disjoint w) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt n r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  exact Frame.bytes hf hd hn (List.mem_range.mp hi)

theorem setup_field_bytes {m n : Mem} (hf : Frame [slots L] m n)
    {d : Nat} (hd : d + 32 ≤ 248) (hmin : 24 ≤ d) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by
  apply frame_bytes hf (field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  exact Offset.disjoint_base _ hmin (by omega)

theorem setup_repr {m n : Mem} (hL : L.Ok) (hf : Frame [slots L] m n) {msg : List Byte}
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 m (State.addr L.scr) msg) :
    Spec.Sha512.Repr Spec.Sha512.H0_512 n (State.addr L.scr) msg := by
  refine Proof.Sha512.Stream.repr_congr (mem := m) ?_ hr
  intro i hi
  exact hf.bytes (R := ⟨State.addr L.scr, 192⟩) (by
    rintro r hm; rw [List.mem_singleton.mp hm]
    exact (hL.kc.sub_left (Region.sub_prefix (by decide))).symm.sub_left (Region.sub_prefix (by decide)))
    (by change 192 ≤ 2 ^ 64; decide) hi

theorem hash_field_bytes {m n : Mem} (hL : L.Ok) (hf : Frame (hashWrites L) m n)
    {d : Nat} (hd : d + 32 ≤ 184) (hmin : 24 ≤ d) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by
  apply frame_bytes hf (field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact field_scr hL (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by decide)

theorem bytes_length (m : Mem) (p : Addr) (n : Nat) :
    (Spec.Ed25519.bytesAt m p n).length = n := by simp [Spec.Ed25519.bytesAt]

end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm
variable {L : Lay}

structure Input (L : Lay) (p n : BitVec 32) : Prop where
  cover : Whole.Within ⟨State.addr p, n.toNat⟩ L.FR ∨
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within ⟨State.addr p, n.toNat⟩ R
  scratch : Region.Disjoint ⟨State.addr p, n.toNat⟩ L.SCR
  args : Region.Disjoint ⟨State.addr p, n.toNat⟩ (slots L)
  fit : p.toNat + n.toNat ≤ 2 ^ 32

theorem input_self {r : Region} (hr : r ∈ L.inputs) :
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R :=
  ⟨r, List.mem_append_left _ hr, 0, by simp, by simp⟩

theorem input_slots (hL : L.Ok) {r : Region} (hr : r ∈ L.inputs) : r.Disjoint (slots L) :=
  (hL.ks _ hr).symm.sub_right (Region.sub_prefix (by decide))

theorem key_input (hL : L.Ok) : Input L L.pk 32 :=
  ⟨.inr (input_self (r := L.PK) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs]),
    input_slots hL (by simp [Lay.inputs]), hL.np⟩

theorem message_input (hL : L.Ok) : Input L L.msg L.len :=
  ⟨.inr (input_self (r := L.MSG) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs]),
    input_slots hL (by simp [Lay.inputs]), hL.nm⟩

theorem signature_input (hL : L.Ok) : Input L L.sig 32 := by
  have sub : Region.Sub ⟨State.addr L.sig,32⟩ L.SIG := Region.sub_prefix (by decide)
  exact ⟨.inr ⟨L.SIG,by simp [Lay.inputs],0,by simp,by change 0+32≤64; decide⟩,
    (hL.sc _ (by simp [Lay.inputs])).sub_left sub,
    (input_slots hL (by simp [Lay.inputs])).sub_left sub,by have := hL.ns; change L.sig.toNat+32≤2^32; omega⟩

end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm
variable {L : Lay}

theorem shaWithin (L : Lay) : Whole.Within (Whole.SHA L.scr) L.SCR :=
  ⟨0, by simp, by change 0 + 192 ≤ 8192; decide⟩
theorem workWithin (L : Lay) : Whole.Within (Whole.WORK L.scr) L.SCR :=
  ⟨192, rfl, by change 192 + 272 ≤ 8192; decide⟩
theorem argsWithin (L : Lay) {n : Nat} (hn : n ≤ 248) :
    Whole.Within (Whole.CALLARGS L.E n) L.FR := ⟨0, by simp, by change 0 + n ≤ 248; omega⟩

theorem init_frame {m n : Mem} (hf : Frame (Whole.initWr L.scr) m n) : Frame (hashWrites L) m n := by
  apply hash_frame hf
  intro r hr; rw [List.mem_singleton.mp hr]
  exact .inl (shaWithin L)

theorem update_frame {m n : Mem} (hf : Frame (Whole.hashWr L.scr) m n) : Frame (hashWrites L) m n := by
  apply hash_frame hf
  simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inl (shaWithin L)
  · exact .inl (workWithin L)

theorem final_addr (hL : L.Ok) : State.addr (L.E + 184) = State.addr L.E + 184 :=
  frame_addr hL (d := 184) (by decide)

theorem finalize_frame (hL : L.Ok) {m n : Mem} (hf : Frame (Whole.finalizeWr L.scr (L.E + 184)) m n) :
    Frame (hashWrites L) m n := by
  apply hash_frame hf
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inl (shaWithin L)
  · exact .inr ⟨0, by rw [final_addr hL]; simp [digest], by change 0 + 64 ≤ 64; decide⟩
  · exact .inl (workWithin L)

theorem final_writes (hL : L.Ok) : ∀ r ∈ Whole.finalizeWr L.scr (L.E + 184),
    Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  apply writes
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inr (shaWithin L)
  · exact .inl ⟨184, final_addr hL, by change 184 + 64 ≤ 248; decide⟩
  · exact .inr (workWithin L)

theorem update_covers {p n : BitVec 32} (hi : Input L p n) :
    Covers (Whole.updateRd L.E p n ++ Whole.hashWr L.scr) (L.inputs ++ L.FR :: L.outputs) := by
  apply covers
  simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hi.cover
  · exact .inl (argsWithin L (by decide))
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], shaWithin L⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], workWithin L⟩

theorem finalize_covers (hL : L.Ok) :
    Covers (Whole.finalizeRd L.E ++ Whole.finalizeWr L.scr (L.E + 184)) (L.inputs ++ L.FR :: L.outputs) := by
  apply covers
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    exact .inl (argsWithin L (by decide))
  · rcases final_writes hL r hr with hf | ⟨R, hR, hw⟩
    · exact .inl hf
    · exact .inr ⟨R, List.mem_append_right _ hR, hw⟩

def UpdateArgs (L : Lay) (count p n : BitVec 32) (t : State) : Prop :=
  t.gpr .r0 = L.scr ∧ t.gpr .r2 = count ∧ t.gpr .r3 = 0 ∧
    stackArg t 0 = p ∧ stackArg t 1 = n ∧ stackArg t 2 = L.scr + 192

def FinalArgs (L : Lay) (count : BitVec 32) (t : State) : Prop :=
  t.gpr .r0 = L.scr ∧ t.gpr .r2 = count ∧ t.gpr .r3 = 0 ∧
    stackArg t 0 = L.E + 184 ∧ stackArg t 1 = L.scr + 192

theorem update_pre {t : State} (hL : L.Ok) (he : t.sp = L.E)
    {count p n : BitVec 32} (ha : UpdateArgs L count p n t) (hi : Input L p n) :
    Proof.Sha512.updateArm.pre (t.callEntry.withRegions (Whole.updateRd L.E p n) (Whole.hashWr L.scr)) :=
  Whole.update_pre he ha.1 ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.2.2.2 hi.scratch
    (hL.kc.sub_left (Region.sub_prefix (by decide))) hL.nc hi.fit (by have := hL.top; omega)

theorem finalize_pre {t : State} (hL : L.Ok) (he : t.sp = L.E)
    {count : BitVec 32} (ha : FinalArgs L count t) :
    Proof.Sha512.finalizeArm.pre (t.callEntry.withRegions (Whole.finalizeRd L.E) (Whole.finalizeWr L.scr (L.E + 184))) := by
  refine Whole.finalize_pre he ha.1 ha.2.2.2.1 ha.2.2.2.2 ?_
    (hL.kc.sub_left (Region.sub_prefix (by decide))) ?_ hL.nc
    (frame_fit hL (d := 184) (by decide)) (by have := hL.top; omega)
  · rw [final_addr hL]
    exact hL.kc.sub_left (digestWithin L).sub
  · rw [final_addr hL]
    exact Offset.base_disjoint _ (by decide) (by decide)

theorem count_zero_high (x : BitVec 32) : (0#32) ++ x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt, Nat.shiftLeft_eq]
  have hx := x.isLt
  simp only [BitVec.toNat_ofNat]
  change 0 * 2 ^ 32 + x.toNat = x.toNat % 2 ^ 64
  omega

end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem init_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa init s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr) [] := by
  refine WP.seq (WP.mono (args_regs_ok hc hL ha (args := [(.r0, .caller 4 0)])
    (by decide) (by simp [valid]) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.r0, .caller 4 0) (by simp)
  change u.gpr .r0 = L.scr + 0#32 at a0
  rw [BitVec.add_zero] at a0
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  refine WP.mono (Whole.init_call hu (Whole.init_pre a0 hL.nc) (Whole.covers_writes hw) hw a0)
    fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, hp⟩
  rw [hm] at hf
  exact init_frame hf

theorem update_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (count : Nat) (p n : Value) (hc16 : count < 65536) (hp : valid p) (hn : valid n)
    (hi : Input L (value L p) (value L n)) {prev : List Byte}
    (hcount : count = prev.length) (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (State.addr L.scr) prev) :
    WP isa (update (setup [(.r0, .caller 4 0), (.r2, .const count), (.r3, .const 0)]
      [p, n, .caller 4 192])) s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr)
        (prev ++ Spec.Ed25519.bytesAt s.mem (State.addr (value L p)) (value L n).toNat) := by
  have hv : ∀ (x : Reg × Value), x ∈ [(.r0, .caller 4 0), (.r2, .const count), (.r3, .const 0)] →
      valid x.2 := by simp [valid, hc16]
  have hvs : ∀ v ∈ [p, n, Value.caller 4 192], valid v := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl)
    · exact hp
    · exact hn
    · simp [valid]
  refine WP.seq (WP.mono (args_ok hc hL ha (by simp) hv (by simp) hvs (by simp [preserved]))
    fun u ⟨hu, hf, hs, hstack⟩ => ?_)
  have a0 := hs (.r0, .caller 4 0) (by simp)
  have a2 : u.gpr .r2 = BitVec.ofNat 32 count := hs (.r2, .const count) (by simp)
  have a3 : u.gpr .r3 = 0#32 := hs (.r3, .const 0) (by simp)
  have d0 := hstack 0 (by simp)
  have d1 := hstack 1 (by simp)
  have d2 := hstack 2 (by simp)
  change u.gpr .r0 = L.scr + 0#32 at a0
  rw [BitVec.add_zero] at a0
  have args : UpdateArgs L (BitVec.ofNat 32 count) (value L p) (value L n) u := ⟨a0,a2,a3,d0,d1,d2⟩
  have ce : Proof.Sha512.countArm u = BitVec.ofNat 64 prev.length := by
    unfold Proof.Sha512.countArm
    rw [a3,a2,count_zero_high]
    change BitVec.ofNat 64 (count % 2^32) = _
    rw [Nat.mod_eq_of_lt (by omega),hcount]
  have huRepr := setup_repr hL hf hr
  have heq : Spec.Ed25519.bytesAt u.mem (State.addr (value L p)) (value L n).toNat =
      Spec.Ed25519.bytesAt s.mem (State.addr (value L p)) (value L n).toNat :=
    frame_bytes hf ⟨State.addr (value L p), (value L n).toNat⟩
      (by simp only [List.mem_singleton]; intro r he; subst r; exact hi.args)
      (by have := (value L n).isLt; change (value L n).toNat ≤ 2^64; omega)
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  refine WP.mono (Whole.update_call hu (update_pre hL hu.sp args hi) (update_covers hi) hw
    a0 d0 d1 ce huRepr) fun t ⟨ht, hf', hrepr⟩ => ⟨ht, (setup_frame hf).trans (update_frame hf'), ?_⟩
  change Spec.Sha512.Repr _ t.mem _ (prev ++ Spec.Ed25519.bytesAt u.mem (State.addr (value L p)) (value L n).toNat) at hrepr
  rw [heq] at hrepr
  exact hrepr

theorem finalize_count (L : Lay) (n : Nat) (b : Bool) :
    value L (if b then Value.caller 2 n else .const n) =
      BitVec.ofNat 32 ((if b then L.len.toNat else 0) + n) := by
  cases b <;> simp [value, Lay.value, BitVec.ofNat_add]

theorem finalize_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (n : Nat) (hn : n < 256) (b : Bool) {msg : List Byte}
    (hlen : msg.length < 2^32) (hcount : (if b then L.len.toNat else 0) + n = msg.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (State.addr L.scr) msg) :
    WP isa (finalize n b) s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64 = Spec.Sha512.sha512 msg := by
  have hv : ∀ (x : Reg × Value), x ∈ [(.r0, .caller 4 0),
      (.r2, if b then .caller 2 n else .const n), (.r3, .const 0)] → valid x.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl)
    · simp [valid]
    · cases b <;> simp [valid] <;> omega
    · simp [valid]
  refine WP.seq (WP.mono (args_ok hc hL ha (by simp) hv (by simp)
    (by simp [valid]) (by simp [preserved])) fun u ⟨hu,hf,hs,hstack⟩ => ?_)
  have a0 := hs (.r0, .caller 4 0) (by simp)
  have a2 := hs (.r2, if b then .caller 2 n else .const n) (by simp)
  have a3 : u.gpr .r3 = 0#32 := hs (.r3, .const 0) (by simp)
  have d0 := hstack 0 (by simp)
  have d1 := hstack 1 (by simp)
  change u.gpr .r0 = L.scr + 0#32 at a0
  rw [BitVec.add_zero] at a0
  rw [finalize_count,hcount] at a2
  have args : FinalArgs L (BitVec.ofNat 32 msg.length) u := ⟨a0,a2,a3,d0,d1⟩
  have ce : Proof.Sha512.countArm u = BitVec.ofNat 64 msg.length := by
    unfold Proof.Sha512.countArm
    rw [a3,a2,count_zero_high]
    change BitVec.ofNat 64 (msg.length % 2^32) = _
    rw [Nat.mod_eq_of_lt hlen]
  refine WP.mono (Whole.finalize_call hu (finalize_pre hL hu.sp args) (finalize_covers hL)
    (final_writes hL) a0 d0 ce (setup_repr hL hf hr) (by omega))
    fun t ⟨ht,hf',hh⟩ => ⟨ht,(setup_frame hf).trans (finalize_frame hL hf'),?_⟩
  change Spec.Ed25519.bytesAt t.mem (State.addr (L.E + 184)) 64 = _ at hh
  rw [final_addr hL] at hh
  exact hh

end VG.Proof.Ed25519.Arm.VerifyMessage
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.HashPipeline`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.HashUpdates`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem update_input (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (source count : Nat) (hj : source < 5) (hc16 : count < 65536) (hi : Input L (L.value source) 32)
    {prev : List Byte} (hcount : count = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (State.addr L.scr) prev) :
    WP isa (update (prefixArgs source count)) s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr)
        (prev ++ Spec.Ed25519.bytesAt s.mem (State.addr (L.value source)) 32) := by
  have inp : Input L (value L (.caller source 0)) (value L (.const 32)) := by
    change Input L (L.value source + 0#32) 32#32
    rw [BitVec.add_zero]
    exact hi
  refine WP.mono (update_step hc hL ha count (.caller source 0) (.const 32) hc16
    ⟨hj, by decide⟩ (by simp [valid]) inp hcount hr) fun t ⟨ht, hf, hh⟩ => ⟨ht, hf, ?_⟩
  change Spec.Sha512.Repr _ t.mem _ (prev ++ Spec.Ed25519.bytesAt s.mem (State.addr (L.value source + 0#32)) 32) at hh
  rw [BitVec.add_zero] at hh
  exact hh

theorem update_message (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (count : Nat) (hc16 : count < 65536) {prev : List Byte} (hcount : count = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (State.addr L.scr) prev) :
    WP isa (update (messageArgs count)) s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr)
        (prev ++ Spec.Ed25519.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  have inp : Input L (value L (.caller 1 0)) (value L (.caller 2 0)) := by
    simpa only [value, Lay.value, BitVec.add_zero] using message_input hL
  refine WP.mono (update_step hc hL ha count (.caller 1 0) (.caller 2 0) hc16
    (by simp [valid]) (by simp [valid]) inp hcount hr) fun t ⟨ht, hf, hh⟩ => ⟨ht, hf, ?_⟩
  simp only [value, Lay.value, BitVec.add_zero] at hh
  rw [hc.input_bytes hL (r := L.MSG) (by simp [Lay.inputs]) (by have := L.len.isLt; change L.len.toNat ≤ 2^64; omega)] at hh
  exact hh

end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def hashInput (L : Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.bytesAt m (State.addr L.sig) 32 ++
    Spec.Ed25519.bytesAt m (State.addr L.pk) 32 ++
    Spec.Ed25519.bytesAt m (State.addr L.msg) L.len.toNat

theorem sig_prefix_same (hc : Ctx L g m₀ s) (hL : L.Ok) :
    Spec.Ed25519.bytesAt s.mem (State.addr L.sig) 32 = Spec.Ed25519.bytesAt m₀ (State.addr L.sig) 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  exact hc.frame.bytes (R := L.SIG) (by
    intro r hr
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.sc _ (by simp [Lay.inputs])
    · exact (hL.ks _ (by simp [Lay.inputs])).symm)
    (by change 64 ≤ 2 ^ 64; decide) (by change i < 64; have := List.mem_range.mp hi; omega)

theorem hash_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa VG.Impl.Ed25519.Arm.VerifyMessage.hash s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E+184) 64 = Spec.Sha512.sha512 (hashInput L m₀) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun t ⟨ht,_,hinit⟩ => ?_)
  refine WP.seq (WP.mono (update_input ht hL ha 3 0 (by decide) (by decide)
    (signature_input hL) rfl hinit) fun u ⟨hu,_,hsig⟩ => ?_)
  change Spec.Sha512.Repr _ u.mem _ ([] ++ Spec.Ed25519.bytesAt t.mem (State.addr L.sig) 32) at hsig
  rw [List.nil_append,sig_prefix_same ht hL] at hsig
  refine WP.seq (WP.mono (update_input hu hL ha 0 32 (by decide) (by decide)
    (key_input hL) (bytes_length _ _ _).symm hsig) fun w ⟨hw,_,hpk⟩ => ?_)
  change Spec.Sha512.Repr _ w.mem _ (_ ++ Spec.Ed25519.bytesAt u.mem (State.addr L.pk) 32) at hpk
  rw [hu.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32≤2^64; decide)] at hpk
  have hpkl : (Spec.Ed25519.bytesAt m₀ (State.addr L.sig) 32 ++ Spec.Ed25519.bytesAt m₀ (State.addr L.pk) 32).length = 64 := by
    rw [List.length_append,bytes_length,bytes_length]
  refine WP.seq (WP.mono (update_message hw hL ha 64 (by decide) hpkl.symm hpk) fun z ⟨hz,_,hmsg⟩ => ?_)
  have hlen : (hashInput L m₀).length = 64+L.len.toNat := by
    simp only [hashInput,List.length_append,bytes_length]
  refine WP.mono (finalize_step hz hL ha 64 (by decide) true (msg := hashInput L m₀)
    (by rw [hlen]; exact hL.message_bound) (by simp only [ite_true]; rw [hlen]; omega) hmsg)
    fun t ⟨ht,_,hh⟩ => ⟨ht,hh⟩

end VG.Proof.Ed25519.Arm.VerifyMessage
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.Challenge`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.Reduce`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm
open VG.Impl.Ed25519.Arm (scalarReduce)

def reduceRd (L : Lay) : List Region := [digest L]
def reduceWr (L : Lay) (d : Nat) : List Region := [field L d, L.SCR]
def ReduceArgs (L : Lay) (d : Nat) (s : State) : Prop :=
  s.gpr .r0 = L.E + BitVec.ofNat 32 d ∧ s.gpr .r1 = L.E + 184 ∧ s.gpr .r2 = L.scr

theorem reduce_noFrames : scalarReduce.noFrames = true := by lit_decide

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem reduce_pre (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 184) (ha : ReduceArgs L d s) :
    scalarReduceLocal.pre (s.callEntry.withRegions (reduceRd L) (reduceWr L d)) := by
  have ad := frame_addr hL (d := d) (by omega)
  have a184 : State.addr (L.E + 184) = State.addr L.E + 184 := frame_addr hL (d := 184) (by decide)
  simp only [scalarReduceLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), ha.1, ha.2.1, ha.2.2, ad, a184]
  have sep : (field L d).Disjoint (digest L) := Offset.disjoint _ (by omega) (by omega) (by decide)
  exact ⟨rfl, rfl, sep,
    field_scr hL (by omega), hL.kc.sub_left (digestWithin L).sub,
    frame_fit hL (by omega), frame_fit hL (by decide), hL.nc⟩

theorem reduce_call (hc : Ctx L g m₀ s) (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 184)
    (ha : ReduceArgs L d s) :
    WP isa (.call "vg_ed25519_scalar_reduce" scalarReduce) s fun t => Ctx L g m₀ t ∧
      Frame (reduceWr L d) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 d) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 184) 64) := by
  have cov : Covers (reduceRd L ++ reduceWr L d) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (digestWithin L)
    · exact .inl (fieldWithin L (by omega))
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ reduceWr L d, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (fieldWithin L (by omega))
    · exact .inr (scratchWithin L)
  refine Whole.call_ok hc scalarReduce_ok reduce_noFrames (reduce_pre hL hd ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  change Spec.Ed25519.bytesAt t.mem (State.addr (s.callEntry.gpr .r0)) 32 =
    Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r1)) 64) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), ha.1, ha.2.1] at hp
  have ad := frame_addr hL (d := d) (by omega)
  have a184 : State.addr (L.E + 184) = State.addr L.E + 184 := frame_addr hL (d := 184) (by decide)
  rw [ad, a184] at hp
  exact hp

theorem reduce_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.Arm.Whole.callWith VG.Impl.Ed25519.Arm.VerifyMessage.reduceArgs "vg_ed25519_scalar_reduce" scalarReduce) s
      fun t => Ctx L g m₀ t ∧ Frame (reduceWr L 120) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E+120) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (State.addr L.E+184) 64) := by
  refine WP.seq (WP.mono (args_regs_ok hc hL ha
    (args := [(.r0,.frame 120),(.r1,.frame 184),(.r2,.caller 4 0)])
    (by simp) (by simp [valid]) (by simp [preserved])) fun u ⟨hu,hm,hs⟩ => ?_)
  have a0 := hs (.r0,.frame 120) (by simp)
  have a1 := hs (.r1,.frame 184) (by simp)
  have a2 := hs (.r2,.caller 4 0) (by simp)
  change u.gpr .r2 = L.scr+0#32 at a2
  rw [BitVec.add_zero] at a2
  refine WP.mono (reduce_call hu hL (d := 120) (by decide) ⟨a0,a1,a2⟩) fun t ⟨ht,hf,hp⟩ => ⟨ht,?_,?_⟩
  · rw [hm] at hf; exact hf
  · rw [hm] at hp; exact hp

end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem encodeLE_eq (n x : Nat) : Spec.Ed25519.encodeLE n x = Proof.X25519.leBytes n x := by
  unfold Spec.Ed25519.encodeLE Proof.X25519.leBytes
  apply congrArg (List.map · (List.range n))
  funext i
  rw [Nat.shiftRight_eq_div_pow,show 256^i=2^(8*i) by rw [Nat.pow_mul]]

theorem reduced_challenge (digest : List Byte) :
    Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) =
      Spec.Ed25519.scalarReduce digest ++ Spec.Ed25519.encodeLE 32 0 := by
  simp only [Spec.Ed25519.scalarReduce, encodeLE_eq]
  rw [show (64 : Nat) = 32 + 32 from rfl, Proof.X25519.leBytes_add]
  have hL : Spec.Ed25519.L ≤ 256 ^ 32 := by decide
  have hpos : 0 < Spec.Ed25519.L := by decide
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpos) hL)]

theorem extend_step (hc : Ctx L g m₀ s) (hL : L.Ok) {digest : List Byte}
    (hd : Spec.Ed25519.bytesAt s.mem (State.addr L.E + 120) 32 = Spec.Ed25519.scalarReduce digest) :
    WP isa (.block extendChallenge) s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 64 =
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) := by
  refine WP.mono (Whole.Ctx.zeroWords hc (by have := hL.top; omega) (start := 38) (count := 8) (by decide)) fun t ⟨ht, hf, hz⟩ => ⟨ht, ?_⟩
  have low : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 32 =
      Spec.Ed25519.bytesAt s.mem (State.addr L.E + 120) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (R := ⟨State.addr L.E + 120, 32⟩) (by
      rintro r hr; rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by decide) (by decide) (by decide)) (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  have high : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 152) 32 = Spec.Ed25519.encodeLE 32 0 := by
    rw [encodeLE_eq]
    have word (j : Nat) (hj : j < 8) : t.mem.readW (State.addr L.E + 152 + BitVec.ofNat 64 (4*j)) 32 = 0 := by
      have z := hz j hj
      have e : State.addr L.E + BitVec.ofNat 64 (4*(38+j)) = State.addr L.E + 152 + BitVec.ofNat 64 (4*j) := by
        rw [show 4*(38+j)=152+4*j by omega, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      rw [e] at z
      exact z
    apply Proof.X25519.bytesAt_leBytes_words32
    intro j hj
    simpa using congrArg BitVec.toNat (word j hj)
  change Spec.X25519.bytesAt t.mem (State.addr L.E + 120) (32 + 32) = _
  rw [Proof.X25519.bytesAt_add]
  change Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 32 ++
    Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120 + 32) 32 = _
  rw [show State.addr L.E + 120 + 32 = State.addr L.E + 152 by rw [BitVec.add_assoc]; rfl,
    low, hd, high, reduced_challenge]

end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem hashInput_eq (L : Lay) (m : Mem) : hashInput L m =
    (Spec.Ed25519.bytesAt m (State.addr L.sig) 64).take 32 ++
      Spec.Ed25519.bytesAt m (State.addr L.pk) 32 ++
      Spec.Ed25519.bytesAt m (State.addr L.msg) L.len.toNat := by
  have e : (Spec.Ed25519.bytesAt m (State.addr L.sig) 64).take 32 =
      Spec.Ed25519.bytesAt m (State.addr L.sig) 32 := by
    unfold Spec.Ed25519.bytesAt
    rw [← List.map_take, List.take_range]
    rfl
  rw [e]
  rfl

theorem body_ok (hc : Ctx L g m₀ s) (hL : L.Ok)
    (ha : Arguments L m₀) :
    WP isa body s fun t => Ctx L g m₀ t ∧
      t.gpr .r0 = signWord (Spec.Ed25519.verify (Spec.Ed25519.bytesAt m₀ (State.addr L.pk) 32)
        (Spec.Ed25519.bytesAt m₀ (State.addr L.msg) L.len.toNat) (Spec.Ed25519.bytesAt m₀ (State.addr L.sig) 64)) := by
  refine WP.seq (WP.mono (hash_ok hc hL ha) fun t ⟨ht,hh⟩ => ?_)
  refine WP.seq (WP.mono (reduce_step ht hL ha) fun u ⟨hu,_,hr⟩ => ?_)
  rw [hh] at hr
  refine WP.seq (WP.mono (extend_step hu hL hr) fun w ⟨hw,he⟩ => ?_)
  rw [hashInput_eq] at he
  refine WP.mono (equation_step hw hL ha) fun z ⟨hz,eq⟩ => ⟨hz,?_⟩
  rw [hw.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32≤2^64; decide),
    hw.input_bytes hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64≤2^64; decide),he] at eq
  exact eq

theorem body_noFrames : body.noFrames = true := by
  have hu := Whole.update_noFrames
  have hf := Whole.finalize_noFrames
  simp only [body,Impl.Ed25519.Arm.VerifyMessage.hash,init,update,finalize,Impl.Ed25519.Arm.Whole.callWith,
    Code.noFrames,Impl.Sha512.Arm.Stream.init,hu,hf,Bool.and_self]
  rw [reduce_noFrames,equation_noFrames]
  rfl

end VG.Proof.Ed25519.Arm.VerifyMessage
