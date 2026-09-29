import VerifiedGarbage.Proof.MlKem.X86.Piece
import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Proof.Sha3.X86.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.X86.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.X86.Call
import VerifiedGarbage.Impl.MlKem.X86.Basic

/-!
# ML-KEM on x86 (32-bit): calling the Keccak streaming functions

Untrusted: everything here is checked by Lean. What a call of
`vg_keccak_absorb`, `vg_keccak_pad` or `vg_keccak_squeeze` (with their
per-target contracts, `Proof/Sha3/X86/Contract.lean`) needs of the state
it is made from (`CallPre`), with the arguments in `eax`, `ecx`, `edx`,
`ebx`, (`ebp`,) `edi`, pushed in a frame of their own (`rs6`, `rs5`); and
what holds when it returns. Each call uses the 40 bytes below `esp`: its
arguments (24 bytes), the return address, and the 12 bytes the callee's own
calls use.

The pieces `absorb_piece`, `pad_piece` and `squeeze_piece` (`Piece.lean`)
make the calls from a state satisfying `AbsorbAt`, `PadAt` or `SqueezeAt`,
whose pointers are functions of the entry state, public when the entry
states' pointers agree.
-/

namespace VG.Proof.MlKem.X86

open VG VG.X86
open VG.Proof.Sha3.X86 (reg32 within)
open VG.Spec.Sha3 (stateAt Repr bytesAt rates squeezeFrom absorb pad)

/-- The registers of the arguments of a call with six. -/
abbrev rs6 : List Reg := [.edi, .ebp, .ebx, .edx, .ecx, .eax]

/-- The registers of the arguments of a call with five. -/
abbrev rs5 : List Reg := [.edi, .ebx, .edx, .ecx, .eax]

theorem absorb_nosp : NoSp Impl.Sha3.X86.Stream.absorb := NoSp.of_all (by decide +kernel)
theorem pad_nosp : NoSp Impl.Sha3.X86.Stream.pad := NoSp.of_all (by decide +kernel)
theorem squeeze_nosp : NoSp Impl.Sha3.X86.Stream.squeeze := NoSp.of_all (by decide +kernel)

theorem absorb_stack : stackUse Impl.Sha3.X86.Stream.absorb = 12 := by decide +kernel
theorem pad_stack : stackUse Impl.Sha3.X86.Stream.pad = 12 := by decide +kernel
theorem squeeze_stack : stackUse Impl.Sha3.X86.Stream.squeeze = 12 := by decide +kernel

/-- The stack a call uses, below `E`: its arguments' frame, its return
address and the 12 bytes below it. -/
theorem stack_parts {E : BitVec 32} (hE : 40 ≤ E.toNat) :
    Region.Sub (below E 24) (below E 40) ∧
      Region.Sub ⟨(E - BitVec.ofNat 32 28).setWidth 64, 4⟩ (below E 40) ∧
      Region.Sub ⟨(E - BitVec.ofNat 32 28).setWidth 64 - 12, 12⟩ (below E 40) ∧
      Region.Sub (below E 20) (below E 40) ∧
      Region.Sub ⟨(E - BitVec.ofNat 32 24).setWidth 64, 4⟩ (below E 40) ∧
      Region.Sub ⟨(E - BitVec.ofNat 32 24).setWidth 64 - 12, 12⟩ (below E 40) := by
  have r1 : ∀ k, k + 4 ≤ 40 → Region.Sub ⟨(E - BitVec.ofNat 32 (k + 4)).setWidth 64, 4⟩ (below E 40) :=
    fun k hk => by
      have := below_inner (sp := E) (a := 4) (b := 40) (k := k) (by omega) hE
      have e : (⟨(E - BitVec.ofNat 32 (k + 4)).setWidth 64, 4⟩ : Region) = below (E - BitVec.ofNat 32 k) 4 := by
        simp only [below]; congr 2; bv_omega
      rw [e]; exact this
  have r2 : ∀ k, k + 12 ≤ 40 → Region.Sub ⟨(E - BitVec.ofNat 32 k).setWidth 64 - 12, 12⟩ (below E 40) :=
    fun k hk => by
      have := below_inner (sp := E) (a := 12) (b := 40) (k := k) (by omega) hE
      have e : (⟨(E - BitVec.ofNat 32 k).setWidth 64 - 12, 12⟩ : Region) = below (E - BitVec.ofNat 32 k) 12 := by
        simp only [below]
        rw [Taint.sub_setWidth (show 12 ≤ (E - BitVec.ofNat 32 k).toNat by rw [sub_toNat (by omega)]; omega)]
        rfl
      rw [e]; exact this
  exact ⟨below_sub (by omega) hE, r1 24 (by omega), r2 28 (by omega), below_sub (by omega) hE, r1 20 (by omega),
    r2 24 (by omega)⟩

/-- Where the state `S` and working space `W` of a Keccak call are, with `esp = E`. -/
structure KBufs (E S W : BitVec 32) : Prop where
  hE : 40 ≤ E.toNat
  fS : S.toNat + 200 ≤ 2 ^ 32
  fW : W.toNat + 640 ≤ 2 ^ 32
  dSW : (reg32 S 200).Disjoint (reg32 W 640)
  bS : (below E 40).Disjoint (reg32 S 200)
  bW : (below E 40).Disjoint (reg32 W 640)

/-- A region within one of `rs`. -/
def Within (r : Region) (rs : List Region) : Prop :=
  ∃ r' ∈ rs, ∃ o, r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len

theorem entry_frame {s : State} {E : BitVec 32} (hesp : s.gpr .esp = E) (hE : 40 ≤ E.toNat) {rs : List Reg}
    (hrs : Reg.esp ∉ rs) (hl : rs.length ≤ 6) :
    Frame [below E 40] s.mem (pushed rs s).callEntry.mem :=
  (callEntry_frame (by rw [hesp]; omega) hrs).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by rw [hesp]; exact below_sub (by omega) hE⟩

/-! ## `vg_keccak_absorb` -/

/-- `absorb(S, rate, pos, D, len, W)`'s arguments. -/
structure AbsArgs (s : State) (S D W : BitVec 32) (rate pos len : Nat) : Prop where
  eax : s.gpr .eax = S
  ecx : s.gpr .ecx = BitVec.ofNat 32 rate
  edx : s.gpr .edx = BitVec.ofNat 32 pos
  ebx : s.gpr .ebx = D
  ebp : s.gpr .ebp = BitVec.ofNat 32 len
  edi : s.gpr .edi = W

theorem absorb_pre {s : State} {E S D W : BitVec 32} {rate pos len : Nat} (hesp : s.gpr .esp = E)
    (ha : AbsArgs s S D W rate pos len) (hk : KBufs E S W) (fD : D.toNat + len ≤ 2 ^ 32)
    (dDS : (reg32 D len).Disjoint (reg32 S 200)) (dDW : (reg32 D len).Disjoint (reg32 W 640))
    (bD : (below E 40).Disjoint (reg32 D len)) (hr : rate ∈ rates) (hp : pos < rate) (hlen : len < 2 ^ 32)
    (cD : Within (reg32 D len) (s.rd ++ s.wr)) (cS : Within (reg32 S 200) s.wr)
    (cW : Within (reg32 W 640) s.wr) :
    CallPre Proof.Sha3.absorbX86 rs6 [reg32 D len] [reg32 S 200, reg32 W 640, below E 24] s := by
  have hE := hk.hE
  have fit : 4 * rs6.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrate : rate < 2 ^ 32 := by simp [rates] at hr; omega
  have a0 : arg (pushed rs6 s).callEntry 0 = S := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.eax
  have a1 : arg (pushed rs6 s).callEntry 1 = BitVec.ofNat 32 rate := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ecx
  have a2 : arg (pushed rs6 s).callEntry 2 = BitVec.ofNat 32 pos := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edx
  have a3 : arg (pushed rs6 s).callEntry 3 = D := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebx
  have a4 : arg (pushed rs6 s).callEntry 4 = BitVec.ofNat 32 len := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebp
  have a5 : arg (pushed rs6 s).callEntry 5 = W := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edi
  have eA : argAddr (pushed rs6 s).callEntry 0 = (E - BitVec.ofNat 32 24).setWidth 64 := by
    rw [callEntry_argAddr0, hesp]; rfl
  have eSp : (pushed rs6 s).callEntry.gpr .esp = E - BitVec.ofNat 32 28 := by rw [callEntry_esp', hesp]; rfl
  have t1 : (BitVec.ofNat 32 rate).toNat = rate := toNat_ofNat32 hrate
  have t2 : (BitVec.ofNat 32 pos).toNat = pos := toNat_ofNat32 (by omega)
  have t4 : (BitVec.ofNat 32 len).toNat = len := toNat_ofNat32 hlen
  obtain ⟨p24, pr, pst, -, -, -⟩ := stack_parts hE
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Sha3.absorbX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, eA, eSp, t1, t2, t4]
    refine ⟨trivial, trivial, hk.dSW, dDS, dDW, hk.bS.sub_left p24, bD.sub_left p24, hk.bW.sub_left p24,
      hk.bS.sub_left pr, bD.sub_left pr, hk.bW.sub_left pr, hk.bS.sub_left pst, bD.sub_left pst,
      hk.bW.sub_left pst, hk.fS, fD, hk.fW, by rw [sub_toNat (by omega)]; omega,
      by rw [sub_toNat (by omega)]; have := E.isLt; omega, hr, hp⟩
  · refine Covers.of_sub fun r hr' => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr'', o, hb, hl⟩ := cD
      refine ⟨r', ?_, o, hb, hl⟩
      rcases List.mem_append.mp hr'' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    · obtain ⟨r', hr'', o, hb, hl⟩ := cS
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr''), o, hb, hl⟩
    · obtain ⟨r', hr'', o, hb, hl⟩ := cW
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr''), o, hb, hl⟩
    · exact within (below (s.gpr .esp) (4 * rs6.length)) (by simp) 0 (by rw [hesp]; simp) (by simp)
  · refine Covers.of_sub fun r hr' => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · obtain ⟨r', hr'', o, hb, hl⟩ := cS
      exact ⟨r', List.mem_cons_of_mem _ hr'', o, hb, hl⟩
    · obtain ⟨r', hr'', o, hb, hl⟩ := cW
      exact ⟨r', List.mem_cons_of_mem _ hr'', o, hb, hl⟩
    · exact within (below (s.gpr .esp) (4 * rs6.length)) (by simp) 0 (by rw [hesp]; simp) (by simp)

theorem absorb_post {s s' : State} {E S D W : BitVec 32} {rate pos len : Nat} (hesp : s.gpr .esp = E)
    (ha : AbsArgs s S D W rate pos len) (hE : 40 ≤ E.toNat) (hlen : len < 2 ^ 32) (hrate : rate < 2 ^ 32)
    (hpos : pos < 2 ^ 32) (bS : (below E 40).Disjoint (reg32 S 200)) (bD : (below E 40).Disjoint (reg32 D len))
    {rd wr : List Region}
    (h : ∃ s₂ : State, s₂.mem = s'.mem ∧
      Proof.Sha3.absorbX86.post ((pushed rs6 s).callEntry.withRegions rd wr) s₂) :
    ∀ msg, Repr s.mem (S.setWidth 64) rate msg → pos = msg.length % rate →
      Repr s'.mem (S.setWidth 64) rate (msg ++ bytesAt s.mem (D.setWidth 64) len) := by
  obtain ⟨s₂, m₂, post, -⟩ := h
  have fit : 4 * rs6.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have a0 : arg (pushed rs6 s).callEntry 0 = S := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.eax
  have a1 : arg (pushed rs6 s).callEntry 1 = BitVec.ofNat 32 rate := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ecx
  have a2 : arg (pushed rs6 s).callEntry 2 = BitVec.ofNat 32 pos := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edx
  have a3 : arg (pushed rs6 s).callEntry 3 = D := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebx
  have a4 : arg (pushed rs6 s).callEntry 4 = BitVec.ofNat 32 len := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebp
  have fr := entry_frame hesp hE (rs := rs6) (by decide) (by decide)
  simp only [arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, toNat_ofNat32 hlen,
    toNat_ofNat32 hrate, toNat_ofNat32 hpos, m₂] at post
  intro msg hm hp
  have eS : stateAt (pushed rs6 s).callEntry.mem (S.setWidth 64) = stateAt s.mem (S.setWidth 64) :=
    Proof.Sha3.stateAt_congr fun i hi => fr.bytes (R := reg32 S 200) (by simpa using bS.symm) (by simp) hi
  have eD : bytesAt (pushed rs6 s).callEntry.mem (D.setWidth 64) len = bytesAt s.mem (D.setWidth 64) len :=
    bytesAt_frame fr (by simpa using bD.symm) (by omega)
  have := post msg (by unfold Spec.Sha3.Repr; rw [eS]; exact hm) hp
  rwa [eD] at this

/-! ## `vg_keccak_pad` -/

/-- `pad(S, rate, pos, suffix, W)`'s arguments. -/
structure PadArgs (s : State) (S W : BitVec 32) (rate pos sfx : Nat) : Prop where
  eax : s.gpr .eax = S
  ecx : s.gpr .ecx = BitVec.ofNat 32 rate
  edx : s.gpr .edx = BitVec.ofNat 32 pos
  ebx : s.gpr .ebx = BitVec.ofNat 32 sfx
  edi : s.gpr .edi = W

theorem pad_pre {s : State} {E S W : BitVec 32} {rate pos sfx : Nat} (hesp : s.gpr .esp = E)
    (ha : PadArgs s S W rate pos sfx) (hk : KBufs E S W) (hr : rate ∈ rates) (hp : pos < rate)
    (cS : Within (reg32 S 200) s.wr) (cW : Within (reg32 W 640) s.wr) :
    CallPre Proof.Sha3.padX86 rs5 [] [reg32 S 200, reg32 W 640, below E 20] s := by
  have hE := hk.hE
  have fit : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrate : rate < 2 ^ 32 := by simp [rates] at hr; omega
  have a0 : arg (pushed rs5 s).callEntry 0 = S := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.eax
  have a1 : arg (pushed rs5 s).callEntry 1 = BitVec.ofNat 32 rate := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ecx
  have a2 : arg (pushed rs5 s).callEntry 2 = BitVec.ofNat 32 pos := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edx
  have a4 : arg (pushed rs5 s).callEntry 4 = W := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edi
  have eA : argAddr (pushed rs5 s).callEntry 0 = (E - BitVec.ofNat 32 20).setWidth 64 := by
    rw [callEntry_argAddr0, hesp]; rfl
  have eSp : (pushed rs5 s).callEntry.gpr .esp = E - BitVec.ofNat 32 24 := by rw [callEntry_esp', hesp]; rfl
  have t1 : (BitVec.ofNat 32 rate).toNat = rate := toNat_ofNat32 hrate
  have t2 : (BitVec.ofNat 32 pos).toNat = pos := toNat_ofNat32 (by omega)
  obtain ⟨-, -, -, p20, pr, pst⟩ := stack_parts hE
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Sha3.padX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a4, eA, eSp, t1, t2]
    refine ⟨trivial, trivial, hk.dSW, hk.bS.sub_left p20, hk.bW.sub_left p20, hk.bS.sub_left pr,
      hk.bW.sub_left pr, hk.bS.sub_left pst, hk.bW.sub_left pst, hk.fS, hk.fW,
      by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := E.isLt; omega, hr, hp⟩
  · refine Covers.of_sub fun r hr' => ?_
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · obtain ⟨r', hr'', o, hb, hl⟩ := cS
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr''), o, hb, hl⟩
    · obtain ⟨r', hr'', o, hb, hl⟩ := cW
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr''), o, hb, hl⟩
    · exact within (below (s.gpr .esp) (4 * rs5.length)) (by simp) 0 (by rw [hesp]; simp) (by simp)
  · refine Covers.of_sub fun r hr' => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · obtain ⟨r', hr'', o, hb, hl⟩ := cS
      exact ⟨r', List.mem_cons_of_mem _ hr'', o, hb, hl⟩
    · obtain ⟨r', hr'', o, hb, hl⟩ := cW
      exact ⟨r', List.mem_cons_of_mem _ hr'', o, hb, hl⟩
    · exact within (below (s.gpr .esp) (4 * rs5.length)) (by simp) 0 (by rw [hesp]; simp) (by simp)

theorem pad_post {s s' : State} {E S W : BitVec 32} {rate pos sfx : Nat} (hesp : s.gpr .esp = E)
    (ha : PadArgs s S W rate pos sfx) (hE : 40 ≤ E.toNat) (hrate : rate < 2 ^ 32) (hpos : pos < 2 ^ 32)
    (bS : (below E 40).Disjoint (reg32 S 200)) {rd wr : List Region}
    (h : ∃ s₂ : State, s₂.mem = s'.mem ∧
      Proof.Sha3.padX86.post ((pushed rs5 s).callEntry.withRegions rd wr) s₂) :
    ∀ msg, Repr s.mem (S.setWidth 64) rate msg → pos = msg.length % rate →
      stateAt s'.mem (S.setWidth 64) = absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8) msg) := by
  obtain ⟨s₂, m₂, post⟩ := h
  have fit : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have a0 : arg (pushed rs5 s).callEntry 0 = S := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.eax
  have a1 : arg (pushed rs5 s).callEntry 1 = BitVec.ofNat 32 rate := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ecx
  have a2 : arg (pushed rs5 s).callEntry 2 = BitVec.ofNat 32 pos := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edx
  have a3 : arg (pushed rs5 s).callEntry 3 = BitVec.ofNat 32 sfx := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebx
  have fr := entry_frame hesp hE (rs := rs5) (by decide) (by decide)
  simp only [Proof.Sha3.padX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, toNat_ofNat32 hrate,
    toNat_ofNat32 hpos, m₂] at post
  intro msg hm hp
  have eS : stateAt (pushed rs5 s).callEntry.mem (S.setWidth 64) = stateAt s.mem (S.setWidth 64) :=
    Proof.Sha3.stateAt_congr fun i hi => fr.bytes (R := reg32 S 200) (by simpa using bS.symm) (by simp) hi
  exact post msg (by unfold Spec.Sha3.Repr; rw [eS]; exact hm) hp

/-! ## `vg_keccak_squeeze` -/

theorem squeeze_pre {s : State} {E S O W : BitVec 32} {rate pos len : Nat} (hesp : s.gpr .esp = E)
    (ha : AbsArgs s S O W rate pos len) (hk : KBufs E S W) (fO : O.toNat + len ≤ 2 ^ 32)
    (dSO : (reg32 S 200).Disjoint (reg32 O len)) (dOW : (reg32 O len).Disjoint (reg32 W 640))
    (bO : (below E 40).Disjoint (reg32 O len)) (hr : rate ∈ rates) (hp : pos ≤ rate) (hlen : len < 2 ^ 32)
    (cS : Within (reg32 S 200) s.wr) (cO : Within (reg32 O len) s.wr) (cW : Within (reg32 W 640) s.wr) :
    CallPre Proof.Sha3.squeezeX86 rs6 [] [reg32 S 200, reg32 O len, reg32 W 640, below E 24] s := by
  have hE := hk.hE
  have fit : 4 * rs6.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrate : rate < 2 ^ 32 := by simp [rates] at hr; omega
  have a0 : arg (pushed rs6 s).callEntry 0 = S := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.eax
  have a1 : arg (pushed rs6 s).callEntry 1 = BitVec.ofNat 32 rate := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ecx
  have a2 : arg (pushed rs6 s).callEntry 2 = BitVec.ofNat 32 pos := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edx
  have a3 : arg (pushed rs6 s).callEntry 3 = O := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebx
  have a4 : arg (pushed rs6 s).callEntry 4 = BitVec.ofNat 32 len := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebp
  have a5 : arg (pushed rs6 s).callEntry 5 = W := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edi
  have eA : argAddr (pushed rs6 s).callEntry 0 = (E - BitVec.ofNat 32 24).setWidth 64 := by
    rw [callEntry_argAddr0, hesp]; rfl
  have eSp : (pushed rs6 s).callEntry.gpr .esp = E - BitVec.ofNat 32 28 := by rw [callEntry_esp', hesp]; rfl
  have t1 : (BitVec.ofNat 32 rate).toNat = rate := toNat_ofNat32 hrate
  have t2 : (BitVec.ofNat 32 pos).toNat = pos := toNat_ofNat32 (by omega)
  have t4 : (BitVec.ofNat 32 len).toNat = len := toNat_ofNat32 hlen
  obtain ⟨p24, pr, pst, -, -, -⟩ := stack_parts hE
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Sha3.squeezeX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, eA, eSp, t1, t2, t4]
    refine ⟨trivial, trivial, dSO, hk.dSW, dOW, hk.bS.sub_left p24, bO.sub_left p24, hk.bW.sub_left p24,
      hk.bS.sub_left pr, bO.sub_left pr, hk.bW.sub_left pr, hk.bS.sub_left pst, bO.sub_left pst,
      hk.bW.sub_left pst, hk.fS, fO, hk.fW, by rw [sub_toNat (by omega)]; omega,
      by rw [sub_toNat (by omega)]; have := E.isLt; omega, hr, hp⟩
  · refine Covers.of_sub fun r hr' => ?_
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr'', o, hb, hl⟩ := cS
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr''), o, hb, hl⟩
    · obtain ⟨r', hr'', o, hb, hl⟩ := cO
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr''), o, hb, hl⟩
    · obtain ⟨r', hr'', o, hb, hl⟩ := cW
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr''), o, hb, hl⟩
    · exact within (below (s.gpr .esp) (4 * rs6.length)) (by simp) 0 (by rw [hesp]; simp) (by simp)
  · refine Covers.of_sub fun r hr' => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr'', o, hb, hl⟩ := cS
      exact ⟨r', List.mem_cons_of_mem _ hr'', o, hb, hl⟩
    · obtain ⟨r', hr'', o, hb, hl⟩ := cO
      exact ⟨r', List.mem_cons_of_mem _ hr'', o, hb, hl⟩
    · obtain ⟨r', hr'', o, hb, hl⟩ := cW
      exact ⟨r', List.mem_cons_of_mem _ hr'', o, hb, hl⟩
    · exact within (below (s.gpr .esp) (4 * rs6.length)) (by simp) 0 (by rw [hesp]; simp) (by simp)

theorem squeeze_post {s s' : State} {E S O W : BitVec 32} {rate pos len : Nat} (hesp : s.gpr .esp = E)
    (ha : AbsArgs s S O W rate pos len) (hE : 40 ≤ E.toNat) (hlen : len < 2 ^ 32) (hrate : rate < 2 ^ 32)
    (hpos : pos < 2 ^ 32) (bS : (below E 40).Disjoint (reg32 S 200)) {rd wr : List Region}
    (h : ∃ s₂ : State, s₂.mem = s'.mem ∧
      Proof.Sha3.squeezeX86.post ((pushed rs6 s).callEntry.withRegions rd wr) s₂) :
    bytesAt s'.mem (O.setWidth 64) len = squeezeFrom rate (stateAt s.mem (S.setWidth 64)) pos len ∧
      ∃ pos' ≤ rate, ∀ d, squeezeFrom rate (stateAt s'.mem (S.setWidth 64)) pos' d =
        squeezeFrom rate (stateAt s.mem (S.setWidth 64)) (pos + len) d := by
  obtain ⟨s₂, m₂, post⟩ := h
  have fit : 4 * rs6.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have a0 : arg (pushed rs6 s).callEntry 0 = S := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.eax
  have a1 : arg (pushed rs6 s).callEntry 1 = BitVec.ofNat 32 rate := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ecx
  have a2 : arg (pushed rs6 s).callEntry 2 = BitVec.ofNat 32 pos := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edx
  have a3 : arg (pushed rs6 s).callEntry 3 = O := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebx
  have a4 : arg (pushed rs6 s).callEntry 4 = BitVec.ofNat 32 len := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebp
  have fr := entry_frame hesp hE (rs := rs6) (by decide) (by decide)
  simp only [Proof.Sha3.squeezeX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4,
    toNat_ofNat32 hlen, toNat_ofNat32 hrate, toNat_ofNat32 hpos, m₂] at post
  have eS : stateAt (pushed rs6 s).callEntry.mem (S.setWidth 64) = stateAt s.mem (S.setWidth 64) :=
    Proof.Sha3.stateAt_congr fun i hi => fr.bytes (R := reg32 S 200) (by simpa using bS.symm) (by simp) hi
  rw [eS] at post
  exact ⟨post.1, _, post.2.1, post.2.2⟩

/-! ## The calls, as pieces -/

theorem rate_lt {rate : Nat} (hr : rate ∈ rates) : rate < 2 ^ 32 := by simp [rates] at hr; omega

/-- Everything a call of `vg_keccak_absorb` needs of the state it is made from. -/
structure AbsorbAt (s : State) (E S D W : BitVec 32) (rate pos len : Nat) : Prop where
  esp : s.gpr .esp = E
  args : AbsArgs s S D W rate pos len
  bufs : KBufs E S W
  fD : D.toNat + len ≤ 2 ^ 32
  dDS : (reg32 D len).Disjoint (reg32 S 200)
  dDW : (reg32 D len).Disjoint (reg32 W 640)
  bD : (below E 40).Disjoint (reg32 D len)
  cD : Within (reg32 D len) (s.rd ++ s.wr)
  cS : Within (reg32 S 200) s.wr
  cW : Within (reg32 W 640) s.wr

/-- Everything a call of `vg_keccak_pad` needs of the state it is made from. -/
structure PadAt (s : State) (E S W : BitVec 32) (rate pos sfx : Nat) : Prop where
  esp : s.gpr .esp = E
  args : PadArgs s S W rate pos sfx
  bufs : KBufs E S W
  cS : Within (reg32 S 200) s.wr
  cW : Within (reg32 W 640) s.wr

/-- Everything a call of `vg_keccak_squeeze` needs of the state it is made from. -/
structure SqueezeAt (s : State) (E S O W : BitVec 32) (rate pos len : Nat) : Prop where
  esp : s.gpr .esp = E
  args : AbsArgs s S O W rate pos len
  bufs : KBufs E S W
  fO : O.toNat + len ≤ 2 ^ 32
  dSO : (reg32 S 200).Disjoint (reg32 O len)
  dOW : (reg32 O len).Disjoint (reg32 W 640)
  bO : (below E 40).Disjoint (reg32 O len)
  cS : Within (reg32 S 200) s.wr
  cO : Within (reg32 O len) s.wr
  cW : Within (reg32 W 640) s.wr

/-- Two runs that push the same six registers pass the same arguments. -/
theorem args6_eq {s s' : State} (hE : 40 ≤ (s.gpr .esp).toNat) (hsp : s.gpr .esp = s'.gpr .esp)
    (hr : ∀ r ∈ rs6, s.gpr r = s'.gpr r) (rd wr : List Region) :
    ((pushed rs6 s).callEntry.withRegions rd wr).gpr .esp = ((pushed rs6 s').callEntry.withRegions rd wr).gpr .esp ∧
      ∀ i < 6, arg ((pushed rs6 s).callEntry.withRegions rd wr) i =
        arg ((pushed rs6 s').callEntry.withRegions rd wr) i := by
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', hsp], fun i hi => ?_⟩
  simp only [arg_withRegions]
  exact callEntry_arg_eq (by decide) (by simp only [List.length_cons, List.length_nil]; omega) hsp hr
    (by simpa using hi)

/-- Two runs that push the same five registers pass the same arguments. -/
theorem args5_eq {s s' : State} (hE : 40 ≤ (s.gpr .esp).toNat) (hsp : s.gpr .esp = s'.gpr .esp)
    (hr : ∀ r ∈ rs5, s.gpr r = s'.gpr r) (rd wr : List Region) :
    ((pushed rs5 s).callEntry.withRegions rd wr).gpr .esp = ((pushed rs5 s').callEntry.withRegions rd wr).gpr .esp ∧
      ∀ i < 5, arg ((pushed rs5 s).callEntry.withRegions rd wr) i =
        arg ((pushed rs5 s').callEntry.withRegions rd wr) i := by
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', hsp], fun i hi => ?_⟩
  simp only [arg_withRegions]
  exact callEntry_arg_eq (by decide) (by simp only [List.length_cons, List.length_nil]; omega) hsp hr
    (by simpa using hi)

theorem absArgs_eq {s s' : State} {S D W : BitVec 32} {rate pos len : Nat} (h : AbsArgs s S D W rate pos len)
    (h' : AbsArgs s' S D W rate pos len) : ∀ r ∈ rs6, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [rs6, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.edi, h'.edi]
  · rw [h.ebp, h'.ebp]
  · rw [h.ebx, h'.ebx]
  · rw [h.edx, h'.edx]
  · rw [h.ecx, h'.ecx]
  · rw [h.eax, h'.eax]

theorem padArgs_eq {s s' : State} {S W : BitVec 32} {rate pos sfx : Nat} (h : PadArgs s S W rate pos sfx)
    (h' : PadArgs s' S W rate pos sfx) : ∀ r ∈ rs5, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [rs5, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.edi, h'.edi]
  · rw [h.ebx, h'.ebx]
  · rw [h.edx, h'.edx]
  · rw [h.ecx, h'.ecx]
  · rw [h.eax, h'.eax]

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {A B : State → State → Prop}

/-- A call of `vg_keccak_absorb`. -/
theorem absorb_piece (E S D W : State → BitVec 32) (rate pos len : Nat) (hr : rate ∈ rates) (hp : pos < rate)
    (hlen : len < 2 ^ 32) (hA : ∀ s₀ s, Pre s₀ → A s₀ s → AbsorbAt s (E s₀) (S s₀) (D s₀) (W s₀) rate pos len)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' →
      E s₀ = E s₀' ∧ S s₀ = S s₀' ∧ D s₀ = D s₀' ∧ W s₀ = W s₀')
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [reg32 (S s₀) 200, reg32 (W s₀) 640, below (E s₀) 40] s.mem s'.mem →
      (∀ msg, Repr s.mem ((S s₀).setWidth 64) rate msg → pos = msg.length % rate →
        Repr s'.mem ((S s₀).setWidth 64) rate (msg ++ bytesAt s.mem ((D s₀).setWidth 64) len)) → B s₀ s') :
    Piece Pre Pub A B (Impl.MlKem.X86.callWith rs6 "vg_keccak_absorb" Impl.Sha3.X86.Stream.absorb) := by
  refine Piece.callWith Proof.Sha3.X86.Stream.Absorb.absorb_verified.1
    Proof.Sha3.X86.Stream.Absorb.absorb_verified.2.1 absorb_nosp (by decide) (by decide)
    (fun s₀ => [reg32 (D s₀) len]) (fun s₀ => [reg32 (S s₀) 200, reg32 (W s₀) 640, below (E s₀) 24])
    (fun s₀ s h₀ ha => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s₀' s s' h₀ h₀' hq ha ha' => ?_)
    (fun s₀ s s' h₀ ha e₁ e₂ e₃ fr post => ?_)
  · have h := hA s₀ s h₀ ha
    have := h.bufs.hE
    rw [absorb_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega
  · have h := hA s₀ s h₀ ha
    exact absorb_pre h.esp h.args h.bufs h.fD h.dDS h.dDW h.bD hr hp hlen h.cD h.cS h.cW
  · obtain ⟨e₁, e₂, e₃, e₄⟩ := hpub s₀ s₀' h₀ h₀' hq
    have h := hA s₀ s h₀ ha
    have h' := hA s₀' s' h₀' ha'
    rw [← e₁, ← e₂, ← e₃, ← e₄] at h'
    have hsp : s.gpr .esp = s'.gpr .esp := h.esp.trans h'.esp.symm
    exact ⟨by rw [e₃], by rw [e₁, e₂, e₄], hsp,
      args6_eq (by rw [h.esp]; exact h.bufs.hE) hsp (absArgs_eq h.args h'.args) _ _⟩
  · have h := hA s₀ s h₀ ha
    have hE := h.bufs.hE
    refine hQ s₀ s s' h₀ ha e₁ e₂ e₃ (fr.sub fun r hr' => ?_)
      (absorb_post h.esp h.args hE hlen (rate_lt hr) (by have := rate_lt hr; omega) h.bufs.bS h.bD post)
    rw [absorb_stack, h.esp] at hr'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, below_sub (by omega) hE⟩
    · exact ⟨_, by simp, below_sub (by simp) hE⟩

/-- A call of `vg_keccak_pad`. -/
theorem pad_piece (E S W : State → BitVec 32) (rate pos sfx : Nat) (hr : rate ∈ rates) (hp : pos < rate)
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → PadAt s (E s₀) (S s₀) (W s₀) rate pos sfx)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → E s₀ = E s₀' ∧ S s₀ = S s₀' ∧ W s₀ = W s₀')
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [reg32 (S s₀) 200, reg32 (W s₀) 640, below (E s₀) 40] s.mem s'.mem →
      (∀ msg, Repr s.mem ((S s₀).setWidth 64) rate msg → pos = msg.length % rate →
        stateAt s'.mem ((S s₀).setWidth 64) = absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8) msg)) →
      B s₀ s') :
    Piece Pre Pub A B (Impl.MlKem.X86.callWith rs5 "vg_keccak_pad" Impl.Sha3.X86.Stream.pad) := by
  refine Piece.callWith Proof.Sha3.X86.Stream.Pad.pad_verified.1
    Proof.Sha3.X86.Stream.Pad.pad_verified.2.1 pad_nosp (by decide) (by decide)
    (fun _ => []) (fun s₀ => [reg32 (S s₀) 200, reg32 (W s₀) 640, below (E s₀) 20])
    (fun s₀ s h₀ ha => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s₀' s s' h₀ h₀' hq ha ha' => ?_)
    (fun s₀ s s' h₀ ha e₁ e₂ e₃ fr post => ?_)
  · have h := hA s₀ s h₀ ha
    have := h.bufs.hE
    rw [pad_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega
  · have h := hA s₀ s h₀ ha
    exact pad_pre h.esp h.args h.bufs hr hp h.cS h.cW
  · obtain ⟨e₁, e₂, e₃⟩ := hpub s₀ s₀' h₀ h₀' hq
    have h := hA s₀ s h₀ ha
    have h' := hA s₀' s' h₀' ha'
    rw [← e₁, ← e₂, ← e₃] at h'
    have hsp : s.gpr .esp = s'.gpr .esp := h.esp.trans h'.esp.symm
    exact ⟨rfl, by rw [e₁, e₂, e₃], hsp,
      args5_eq (by rw [h.esp]; exact h.bufs.hE) hsp (padArgs_eq h.args h'.args) _ _⟩
  · have h := hA s₀ s h₀ ha
    have hE := h.bufs.hE
    refine hQ s₀ s s' h₀ ha e₁ e₂ e₃ (fr.sub fun r hr' => ?_)
      (pad_post h.esp h.args hE (rate_lt hr) (by have := rate_lt hr; omega) h.bufs.bS post)
    rw [pad_stack, h.esp] at hr'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, below_sub (by omega) hE⟩
    · exact ⟨_, by simp, below_sub (by simp) hE⟩

/-- A call of `vg_keccak_squeeze`. -/
theorem squeeze_piece (E S O W : State → BitVec 32) (rate pos len : Nat) (hr : rate ∈ rates) (hp : pos ≤ rate)
    (hlen : len < 2 ^ 32) (hA : ∀ s₀ s, Pre s₀ → A s₀ s → SqueezeAt s (E s₀) (S s₀) (O s₀) (W s₀) rate pos len)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' →
      E s₀ = E s₀' ∧ S s₀ = S s₀' ∧ O s₀ = O s₀' ∧ W s₀ = W s₀')
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [reg32 (S s₀) 200, reg32 (O s₀) len, reg32 (W s₀) 640, below (E s₀) 40] s.mem s'.mem →
      bytesAt s'.mem ((O s₀).setWidth 64) len = squeezeFrom rate (stateAt s.mem ((S s₀).setWidth 64)) pos len →
      (∃ pos' ≤ rate, ∀ d, squeezeFrom rate (stateAt s'.mem ((S s₀).setWidth 64)) pos' d =
        squeezeFrom rate (stateAt s.mem ((S s₀).setWidth 64)) (pos + len) d) → B s₀ s') :
    Piece Pre Pub A B (Impl.MlKem.X86.callWith rs6 "vg_keccak_squeeze" Impl.Sha3.X86.Stream.squeeze) := by
  refine Piece.callWith Proof.Sha3.X86.Stream.Squeeze.squeeze_verified.1
    Proof.Sha3.X86.Stream.Squeeze.squeeze_verified.2.1 squeeze_nosp (by decide) (by decide)
    (fun _ => []) (fun s₀ => [reg32 (S s₀) 200, reg32 (O s₀) len, reg32 (W s₀) 640, below (E s₀) 24])
    (fun s₀ s h₀ ha => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s₀' s s' h₀ h₀' hq ha ha' => ?_)
    (fun s₀ s s' h₀ ha e₁ e₂ e₃ fr post => ?_)
  · have h := hA s₀ s h₀ ha
    have := h.bufs.hE
    rw [squeeze_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega
  · have h := hA s₀ s h₀ ha
    exact squeeze_pre h.esp h.args h.bufs h.fO h.dSO h.dOW h.bO hr hp hlen h.cS h.cO h.cW
  · obtain ⟨e₁, e₂, e₃, e₄⟩ := hpub s₀ s₀' h₀ h₀' hq
    have h := hA s₀ s h₀ ha
    have h' := hA s₀' s' h₀' ha'
    rw [← e₁, ← e₂, ← e₃, ← e₄] at h'
    have hsp : s.gpr .esp = s'.gpr .esp := h.esp.trans h'.esp.symm
    exact ⟨rfl, by rw [e₁, e₂, e₃, e₄], hsp,
      args6_eq (by rw [h.esp]; exact h.bufs.hE) hsp (absArgs_eq h.args h'.args) _ _⟩
  · have h := hA s₀ s h₀ ha
    have hE := h.bufs.hE
    obtain ⟨r₁, r₂⟩ := squeeze_post h.esp h.args hE hlen (rate_lt hr) (by have := rate_lt hr; omega)
      h.bufs.bS post
    refine hQ s₀ s s' h₀ ha e₁ e₂ e₃ (fr.sub fun r hr' => ?_) r₁ r₂
    rw [squeeze_stack, h.esp] at hr'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, below_sub (by omega) hE⟩
    · exact ⟨_, by simp, below_sub (by simp) hE⟩

end

end VG.Proof.MlKem.X86
