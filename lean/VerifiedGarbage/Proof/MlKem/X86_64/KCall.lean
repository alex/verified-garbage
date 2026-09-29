import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Squeeze
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-KEM on x86-64: calling the SHA-3 sponge

Untrusted: everything here is checked by Lean. Calls of
`vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` from their
proofs (`WP.call`): the callee's precondition on entry (`absorb_pre`,
`pad_pre`, `squeeze_pre`, which the constant-time proofs of callers use
too), and what holds when it returns (`absorb_call`, `pad_call`,
`squeeze_call`). A caller gives each call 16 bytes of stack below `rsp`
(the return address and that of the permutation's call).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64
open VG.Spec.Sha3 (stateAt bytesAt absorb pad rates squeezeFrom)

/-! ## The stack of a call -/

theorem sub_ret (sp : Addr) : Region.Sub ⟨sp - 8, 8⟩ (below sp 16) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (sp - BitVec.ofNat 64 16) = (x - (sp - 8)) + 8 by bv_omega, BitVec.toNat_add]
  have : (8 : BitVec 64).toNat = 8 := rfl
  omega

theorem sub_stk (sp : Addr) : Region.Sub ⟨sp - 8 - 8, 8⟩ (below sp 16) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (sp - BitVec.ofNat 64 16) = x - (sp - 8 - 8) by bv_omega]
  omega

theorem sub_b8 (sp : Addr) : Region.Sub (below sp 8) (below sp 16) := below_sub (by omega) (by omega)

/-- A region apart from the 16 bytes below `rsp` reads the same on entry to a callee. -/
theorem callEntry_bytes (s : State) {R : Region} (hd : (below (s.gpr .rsp) 16).Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    s.callEntry.mem (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [below (s.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega)))
    (by simpa using (hd.sub_left (sub_b8 _)).symm) hR hi

theorem callEntry_stateAt (s : State) {p : Addr} (hd : (below (s.gpr .rsp) 16).Disjoint ⟨p, 200⟩) :
    stateAt s.callEntry.mem p = stateAt s.mem p :=
  Proof.Sha3.stateAt_congr fun _ hi => callEntry_bytes s (R := ⟨p, 200⟩) hd (by simp) hi

theorem callEntry_bytesAt (s : State) {p : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (hd : (below (s.gpr .rsp) 16).Disjoint ⟨p, n⟩) : bytesAt s.callEntry.mem p n = bytesAt s.mem p n :=
  bytesAt_congr fun _ hi => callEntry_bytes s (R := ⟨p, n⟩) hd (by simp; omega) hi

theorem callEntry_repr (s : State) {p : Addr} (hd : (below (s.gpr .rsp) 16).Disjoint ⟨p, 200⟩)
    {rate : Nat} {msg : List Byte} : Spec.Sha3.Repr s.callEntry.mem p rate msg ↔ Spec.Sha3.Repr s.mem p rate msg := by
  unfold Spec.Sha3.Repr; rw [callEntry_stateAt s hd]

theorem ce_gpr (s : State) {r : Reg} (h : r ≠ .rsp) : s.callEntry.gpr r = s.gpr r := State.callEntry_gpr _ h

/-! ## The callees' registers and stack -/

theorem absorb_nosp : NoSp Impl.Sha3.X86_64.Stream.absorb := by
  have : ((instrs Impl.Sha3.X86_64.Stream.absorb).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem pad_nosp : NoSp Impl.Sha3.X86_64.Stream.pad := by
  have : ((instrs Impl.Sha3.X86_64.Stream.pad).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem squeeze_nosp : NoSp Impl.Sha3.X86_64.Stream.squeeze := by
  have : ((instrs Impl.Sha3.X86_64.Stream.squeeze).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem absorb_depth : Impl.Sha3.X86_64.Stream.absorb.depth = 1 := by decide +kernel
theorem pad_depth : Impl.Sha3.X86_64.Stream.pad.depth = 1 := by decide +kernel
theorem squeeze_depth : Impl.Sha3.X86_64.Stream.squeeze.depth = 1 := by decide +kernel

/-! ## `vg_keccak_absorb` -/

section
variable {s : State} {st dp scr : Addr} {rate pos len : Nat}

/-- The facts a call of `vg_keccak_absorb(st, rate, pos, dp, len, scr)` needs. -/
structure AbsorbArgs (s : State) (st dp scr : Addr) (rate pos len : Nat) : Prop where
  rdi : s.gpr .rdi = st
  rsi : s.gpr .rsi = BitVec.ofNat 64 rate
  rdx : s.gpr .rdx = BitVec.ofNat 64 pos
  rcx : s.gpr .rcx = dp
  r8 : s.gpr .r8 = BitVec.ofNat 64 len
  r9 : s.gpr .r9 = scr
  hrate : rate ∈ rates
  hpos : pos < rate
  hlen : len < 2 ^ 64
  st_scr : Region.Disjoint ⟨st, 200⟩ ⟨scr, 640⟩
  d_st : Region.Disjoint ⟨dp, len⟩ ⟨st, 200⟩
  d_scr : Region.Disjoint ⟨dp, len⟩ ⟨scr, 640⟩
  k_st : (below (s.gpr .rsp) 16).Disjoint ⟨st, 200⟩
  k_d : (below (s.gpr .rsp) 16).Disjoint ⟨dp, len⟩
  k_scr : (below (s.gpr .rsp) 16).Disjoint ⟨scr, 640⟩

theorem rate_lt {rate : Nat} (h : rate ∈ rates) : rate < 2 ^ 64 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem ofNat_toNat' {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem absorb_pre (h : AbsorbArgs s st dp scr rate pos len) :
    Proof.Sha3.absorbX86_64.pre (s.callEntry.withRegions [⟨dp, len⟩] [⟨st, 200⟩, ⟨scr, 640⟩]) := by
  have hr := rate_lt h.hrate
  simp only [Proof.Sha3.absorbX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, ce_gpr s (by decide : Reg.rdi ≠ .rsp), ce_gpr s (by decide : Reg.rsi ≠ .rsp),
    ce_gpr s (by decide : Reg.rdx ≠ .rsp), ce_gpr s (by decide : Reg.rcx ≠ .rsp),
    ce_gpr s (by decide : Reg.r8 ≠ .rsp), ce_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx,
    h.r8, h.r9, ofNat_toNat' h.hlen, ofNat_toNat' hr, ofNat_toNat' (Nat.lt_trans h.hpos hr)]
  exact ⟨trivial, trivial, h.st_scr, h.d_st, h.d_scr, h.k_st.sub_left (sub_ret _), h.k_scr.sub_left (sub_ret _),
    h.k_st.sub_left (sub_stk _), h.k_d.sub_left (sub_stk _), h.k_scr.sub_left (sub_stk _), h.hrate, h.hpos⟩

theorem absorb_call (h : AbsorbArgs s st dp scr rate pos len)
    (hc : Covers ([⟨dp, len⟩] ++ [⟨st, 200⟩, ⟨scr, 640⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨scr, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨scr, 640⟩, below (s.gpr .rsp) 16] s.mem s'.mem →
      (∀ msg, Spec.Sha3.Repr s.mem st rate msg → pos = msg.length % rate →
        Spec.Sha3.Repr s'.mem st rate (msg ++ bytesAt s.mem dp len)) →
      (s'.gpr .rax).toNat = (pos + len) % rate → Q s') :
    WP isa (.call "vg_keccak_absorb" Impl.Sha3.X86_64.Stream.absorb) s Q := by
  have hr := rate_lt h.hrate
  refine WP.call (k := Proof.Sha3.absorbX86_64) Proof.Sha3.X86_64.Stream.Absorb.absorb_correct absorb_nosp
    (by rw [absorb_depth]; decide) (absorb_pre h) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost, hrax⟩
  simp only [State.withRegions_gpr, State.withRegions_mem, ce_gpr s (by decide : Reg.rdi ≠ .rsp),
    ce_gpr s (by decide : Reg.rsi ≠ .rsp), ce_gpr s (by decide : Reg.rdx ≠ .rsp),
    ce_gpr s (by decide : Reg.rcx ≠ .rsp), ce_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx,
    h.r8, hm₂, ofNat_toNat' h.hlen, ofNat_toNat' hr, ofNat_toNat' (Nat.lt_trans h.hpos hr)] at hpost hrax
  refine hQ s' hrd hwr hcs (by rw [absorb_depth] at hf; simpa using hf) (fun msg hm hp => ?_)
    (by rw [← hg₂ _ (by decide)]; exact hrax)
  have := hpost msg ((callEntry_repr s h.k_st).mpr hm) hp
  rwa [callEntry_bytesAt s h.hlen h.k_d] at this

end

/-! ## `vg_keccak_pad` -/

section
variable {s : State} {st scr : Addr} {rate pos : Nat} {suffix : BitVec 64}

/-- The facts a call of `vg_keccak_pad(st, rate, pos, suffix, scr)` needs. -/
structure PadArgs (s : State) (st scr : Addr) (rate pos : Nat) : Prop where
  rdi : s.gpr .rdi = st
  rsi : s.gpr .rsi = BitVec.ofNat 64 rate
  rdx : s.gpr .rdx = BitVec.ofNat 64 pos
  r8 : s.gpr .r8 = scr
  hrate : rate ∈ rates
  hpos : pos < rate
  st_scr : Region.Disjoint ⟨st, 200⟩ ⟨scr, 640⟩
  k_st : (below (s.gpr .rsp) 16).Disjoint ⟨st, 200⟩
  k_scr : (below (s.gpr .rsp) 16).Disjoint ⟨scr, 640⟩

theorem pad_pre (h : PadArgs s st scr rate pos) :
    Proof.Sha3.padX86_64.pre (s.callEntry.withRegions [] [⟨st, 200⟩, ⟨scr, 640⟩]) := by
  have hr := rate_lt h.hrate
  simp only [Proof.Sha3.padX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, ce_gpr s (by decide : Reg.rdi ≠ .rsp), ce_gpr s (by decide : Reg.rsi ≠ .rsp),
    ce_gpr s (by decide : Reg.rdx ≠ .rsp), ce_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.r8,
    ofNat_toNat' hr, ofNat_toNat' (Nat.lt_trans h.hpos hr)]
  exact ⟨trivial, trivial, h.st_scr, h.k_st.sub_left (sub_ret _), h.k_scr.sub_left (sub_ret _),
    h.k_st.sub_left (sub_stk _), h.k_scr.sub_left (sub_stk _), h.hrate, h.hpos⟩

theorem pad_call (h : PadArgs s st scr rate pos)
    (hc : Covers ([] ++ [⟨st, 200⟩, ⟨scr, 640⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨scr, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨scr, 640⟩, below (s.gpr .rsp) 16] s.mem s'.mem →
      (∀ msg, Spec.Sha3.Repr s.mem st rate msg → pos = msg.length % rate →
        stateAt s'.mem st = absorb rate (pad rate ((s.gpr .rcx).setWidth 8) msg)) → Q s') :
    WP isa (.call "vg_keccak_pad" Impl.Sha3.X86_64.Stream.pad) s Q := by
  have hr := rate_lt h.hrate
  refine WP.call (k := Proof.Sha3.padX86_64) Proof.Sha3.X86_64.Stream.Pad.pad_correct pad_nosp
    (by rw [pad_depth]; decide) (pad_pre h) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩
  simp only [Proof.Sha3.padX86_64, State.withRegions_gpr, State.withRegions_mem, ce_gpr s (by decide : Reg.rdi ≠ .rsp),
    ce_gpr s (by decide : Reg.rsi ≠ .rsp), ce_gpr s (by decide : Reg.rdx ≠ .rsp),
    ce_gpr s (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rsi, h.rdx, hm₂, ofNat_toNat' hr,
    ofNat_toNat' (Nat.lt_trans h.hpos hr)] at hpost
  exact hQ s' hrd hwr hcs (by rw [pad_depth] at hf; simpa using hf)
    (fun msg hm hp => hpost msg ((callEntry_repr s h.k_st).mpr hm) hp)

end

/-! ## `vg_keccak_squeeze` -/

section
variable {s : State} {st out scr : Addr} {rate pos len : Nat}

/-- The facts a call of `vg_keccak_squeeze(st, rate, pos, out, len, scr)` needs. -/
structure SqueezeArgs (s : State) (st out scr : Addr) (rate pos len : Nat) : Prop where
  rdi : s.gpr .rdi = st
  rsi : s.gpr .rsi = BitVec.ofNat 64 rate
  rdx : s.gpr .rdx = BitVec.ofNat 64 pos
  rcx : s.gpr .rcx = out
  r8 : s.gpr .r8 = BitVec.ofNat 64 len
  r9 : s.gpr .r9 = scr
  hrate : rate ∈ rates
  hpos : pos ≤ rate
  hlen : len < 2 ^ 64
  st_out : Region.Disjoint ⟨st, 200⟩ ⟨out, len⟩
  st_scr : Region.Disjoint ⟨st, 200⟩ ⟨scr, 640⟩
  out_scr : Region.Disjoint ⟨out, len⟩ ⟨scr, 640⟩
  k_st : (below (s.gpr .rsp) 16).Disjoint ⟨st, 200⟩
  k_out : (below (s.gpr .rsp) 16).Disjoint ⟨out, len⟩
  k_scr : (below (s.gpr .rsp) 16).Disjoint ⟨scr, 640⟩

theorem squeeze_pre (h : SqueezeArgs s st out scr rate pos len) :
    Proof.Sha3.squeezeX86_64.pre (s.callEntry.withRegions [] [⟨st, 200⟩, ⟨out, len⟩, ⟨scr, 640⟩]) := by
  have hr := rate_lt h.hrate
  simp only [Proof.Sha3.squeezeX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, ce_gpr s (by decide : Reg.rdi ≠ .rsp), ce_gpr s (by decide : Reg.rsi ≠ .rsp),
    ce_gpr s (by decide : Reg.rdx ≠ .rsp), ce_gpr s (by decide : Reg.rcx ≠ .rsp),
    ce_gpr s (by decide : Reg.r8 ≠ .rsp), ce_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx,
    h.r8, h.r9, ofNat_toNat' h.hlen, ofNat_toNat' hr, ofNat_toNat' (Nat.lt_of_le_of_lt h.hpos hr)]
  exact ⟨trivial, trivial, h.st_out, h.st_scr, h.out_scr, h.k_st.sub_left (sub_ret _), h.k_out.sub_left (sub_ret _),
    h.k_scr.sub_left (sub_ret _), h.k_st.sub_left (sub_stk _), h.k_out.sub_left (sub_stk _),
    h.k_scr.sub_left (sub_stk _), h.hrate, h.hpos⟩

theorem squeeze_call (h : SqueezeArgs s st out scr rate pos len)
    (hc : Covers ([] ++ [⟨st, 200⟩, ⟨out, len⟩, ⟨scr, 640⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨out, len⟩, ⟨scr, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨out, len⟩, ⟨scr, 640⟩, below (s.gpr .rsp) 16] s.mem s'.mem →
      bytesAt s'.mem out len = squeezeFrom rate (stateAt s.mem st) pos len → Q s') :
    WP isa (.call "vg_keccak_squeeze" Impl.Sha3.X86_64.Stream.squeeze) s Q := by
  have hr := rate_lt h.hrate
  refine WP.call (k := Proof.Sha3.squeezeX86_64) Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct squeeze_nosp
    (by rw [squeeze_depth]; decide) (squeeze_pre h) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost, _⟩
  simp only [State.withRegions_gpr, State.withRegions_mem, ce_gpr s (by decide : Reg.rdi ≠ .rsp),
    ce_gpr s (by decide : Reg.rsi ≠ .rsp), ce_gpr s (by decide : Reg.rdx ≠ .rsp),
    ce_gpr s (by decide : Reg.rcx ≠ .rsp), ce_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx,
    h.r8, hm₂, ofNat_toNat' h.hlen, ofNat_toNat' hr, ofNat_toNat' (Nat.lt_of_le_of_lt h.hpos hr)] at hpost
  refine hQ s' hrd hwr hcs (by rw [squeeze_depth] at hf; simpa using hf) ?_
  rw [hpost, callEntry_stateAt s h.k_st]

end

end VG.Proof.MlKem.X86_64
