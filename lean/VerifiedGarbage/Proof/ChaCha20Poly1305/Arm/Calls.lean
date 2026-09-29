import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Common
import VerifiedGarbage.Proof.Poly1305.Arm.Shared

/-!
# ChaCha20-Poly1305 on ARMv7: the calls

Untrusted: everything here is checked by Lean. Each call of a verified
function, from its proof of `Verified` (with `WP.call`): what it needs of the
state it is called from, and what holds when it returns. A call (`bl`)
stores nothing in memory, so the callee changes memory only within the
regions it may write; the frame around `vg_poly1305_finalize` also stores
its stack arguments below the stack pointer.
-/

namespace VG.Proof.ChaCha20Poly1305.Arm

open VG VG.Arm
open VG.Spec.Poly1305 (Repr Buffered bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-! ## Memory -/

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- A Poly1305 state outside a frame is unchanged. -/
theorem Repr.frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr}
    (hd : ∀ r ∈ rs, (⟨P, 128⟩ : Region).Disjoint r) {key msg : List Byte} (h : Repr m P key msg) :
    Repr m' P key msg := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · rw [show (P + 24 : Addr) = P + BitVec.ofNat 64 24 from rfl,
      bytesAt_frame hf (n := 32) (fun r hr => (hd r hr).sub_left (sub_off P (a := 24) (by omega)))
      (by omega)]
    exact h2
  · rw [bytesAt_frame hf (n := 24) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by omega)))
      (by omega)]
    exact h3

/-- A ChaCha20 state outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p :=
  VG.Proof.ChaCha20.Arm.Xor.stateAt_frame hf hd

/-! ## Registers the callees keep -/

theorem keeps {c : Prog isa} {r : Reg} (h : ((instrs c).all fun i => dstOf i != some r) = true) :
    ∀ i ∈ instrs c, dstOf i ≠ some r := by
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem init_keeps_r0 : ∀ i ∈ instrs Impl.Poly1305.Arm.init, dstOf i ≠ some .r0 :=
  keeps (by rw [← Code.allInstrs_eq]; decide +kernel)

theorem blocks_keeps_r0 : ∀ i ∈ instrs Impl.Poly1305.Arm.blocks, dstOf i ≠ some .r0 :=
  keeps (by rw [← Code.allInstrs_eq]; decide +kernel)

theorem init_noCalls : Impl.Poly1305.Arm.init.noCalls = true := by decide +kernel
theorem blocks_noCalls : Impl.Poly1305.Arm.blocks.noCalls = true := by decide +kernel
theorem finalize_noCalls : Impl.Poly1305.Arm.finalize.noCalls = true := by decide +kernel
theorem block_noCalls : Impl.ChaCha20.Arm.block.noCalls = true := by decide +kernel
theorem xor_noFrames : Impl.ChaCha20.Arm.Xor.xor.noFrames = true := by decide +kernel

/-! ## `vg_chacha20_block` -/

theorem block_call {s : State} {S B : BitVec 32} (h0 : s.gpr .r0 = S) (h1 : s.gpr .r1 = B)
    (hdj : (⟨State.addr B, 256⟩ : Region).Disjoint ⟨State.addr S, 64⟩)
    (hS : S.toNat + 64 ≤ 2 ^ 32) (hB : B.toNat + 256 ≤ 2 ^ 32)
    (hc : Covers ([⟨State.addr S, 64⟩] ++ [⟨State.addr B, 256⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr B, 256⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨State.addr B, 256⟩] s s' → s'.gpr .r1 = B →
      stateAt s'.mem (State.addr B) = Spec.ChaCha20.block (stateAt s.mem (State.addr S)) → Q s') :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.Arm.block) s Q := by
  refine WP.call (k := Proof.ChaCha20.blockArm) Proof.ChaCha20.Arm.block_correct
    (rd := [⟨State.addr S, 64⟩]) (wr := [⟨State.addr B, 256⟩]) ?_ hc hw ?_ block_noCalls
  · simp only [Proof.ChaCha20.blockArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), h0, h1]
    exact ⟨trivial, trivial, hdj, hS, hB⟩
  · intro s' hrd hwr hsp hf hcs hkeep hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩
      (by rw [hkeep .r1 Proof.ChaCha20.Arm.Xor.block_keeps_r1 (by decide), h1]) ?_
    simpa only [Proof.ChaCha20.blockArm, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), h0, h1] using hpost

/-! ## `vg_chacha20_xor` -/

/-- `vg_chacha20_xor`'s contract, with what its proof shows of `r0` and `r1`
on return. -/
def xorK : Contract isa :=
  { Proof.ChaCha20.xorArm with
    post := fun s s' => Proof.ChaCha20.xorArm.post s s' ∧ s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r3 }

theorem xor_call {s : State} {S D B : BitVec 32} {n : Nat} (h0 : s.gpr .r0 = S) (h1 : s.gpr .r1 = D)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 n) (h3 : s.gpr .r3 = B) (hn : n < 2 ^ 32)
    (hSD : (⟨State.addr S, 64⟩ : Region).Disjoint ⟨State.addr D, n⟩)
    (hSB : (⟨State.addr S, 64⟩ : Region).Disjoint ⟨State.addr B, 320⟩)
    (hDB : (⟨State.addr D, n⟩ : Region).Disjoint ⟨State.addr B, 320⟩)
    (hS : S.toNat + 64 ≤ 2 ^ 32) (hD : D.toNat + n ≤ 2 ^ 32) (hB : B.toNat + 320 ≤ 2 ^ 32)
    (hc : Covers ([] ++ [⟨State.addr S, 64⟩, ⟨State.addr D, n⟩, ⟨State.addr B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr S, 64⟩, ⟨State.addr D, n⟩, ⟨State.addr B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨State.addr S, 64⟩, ⟨State.addr D, n⟩, ⟨State.addr B, 320⟩] s s' → s'.gpr .r1 = B →
      Spec.ChaCha20.bytesAt s'.mem (State.addr D) n =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem (State.addr D) n)
          (keystream (stateAt s.mem (State.addr S)) n) → Q s') :
    WP isa (.call "vg_chacha20_xor" Impl.ChaCha20.Arm.Xor.xor) s Q := by
  have hn' : (BitVec.ofNat 32 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  refine WP.callCalls (k := xorK) (fun s hs => Proof.ChaCha20.Arm.Xor.xor_regs s hs)
    (rd := []) (wr := [⟨State.addr S, 64⟩, ⟨State.addr D, n⟩, ⟨State.addr B, 320⟩]) ?_ hc hw ?_
    xor_noFrames
  · simp only [xorK, Proof.ChaCha20.xorArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r2 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs), h0, h1, h2, h3, hn']
    exact ⟨trivial, trivial, hSD, hSB, hDB, hS, hD, hB⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [xorK, Proof.ChaCha20.xorArm, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r2 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs), h0, h1, h2, h3, hn'] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hpost.2.2 hpost.1

/-! ## `vg_poly1305_init` -/

theorem init_call {s : State} {P K : BitVec 32} (h0 : s.gpr .r0 = P) (h1 : s.gpr .r1 = K)
    (hdj : (⟨State.addr P, 128⟩ : Region).Disjoint ⟨State.addr K, 32⟩)
    (hP : P.toNat + 128 ≤ 2 ^ 32) (hK : K.toNat + 32 ≤ 2 ^ 32)
    (hc : Covers ([⟨State.addr K, 32⟩] ++ [⟨State.addr P, 128⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr P, 128⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨State.addr P, 128⟩] s s' → s'.gpr .r0 = P →
      Repr s'.mem (State.addr P) (bytesAt s.mem (State.addr K) 32) [] → Q s') :
    WP isa (.call "vg_poly1305_init" Impl.Poly1305.Arm.init) s Q := by
  refine WP.call (k := Proof.Poly1305.initArm) Proof.Poly1305.Arm.init_verified.1
    (rd := [⟨State.addr K, 32⟩]) (wr := [⟨State.addr P, 128⟩]) ?_ hc hw ?_ init_noCalls
  · simp only [Proof.Poly1305.initArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), h0, h1]
    exact ⟨trivial, trivial, hdj, hP, hK⟩
  · intro s' hrd hwr hsp hf hcs hkeep hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ (by rw [hkeep .r0 init_keeps_r0 (by decide), h0]) ?_
    simpa only [Proof.Poly1305.initArm, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), h0, h1] using hpost

/-! ## `vg_poly1305_blocks` -/

theorem blocks_call {s : State} {P p : BitVec 32} {n : Nat} (h0 : s.gpr .r0 = P) (h1 : s.gpr .r1 = p)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 n) (hn : 16 * n < 2 ^ 32)
    (hdj : (⟨State.addr P, 128⟩ : Region).Disjoint ⟨State.addr p, 16 * n⟩)
    (hP : P.toNat + 128 ≤ 2 ^ 32) (hp : p.toNat + 16 * n ≤ 2 ^ 32)
    (hc : Covers ([⟨State.addr p, 16 * n⟩] ++ [⟨State.addr P, 128⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr P, 128⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨State.addr P, 128⟩] s s' → s'.gpr .r0 = P →
      (∀ key msg, Repr s.mem (State.addr P) key msg →
        Repr s'.mem (State.addr P) key (msg ++ bytesAt s.mem (State.addr p) (16 * n))) → Q s') :
    WP isa (.call "vg_poly1305_blocks" Impl.Poly1305.Arm.blocks) s Q := by
  have hn' : (BitVec.ofNat 32 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine WP.call (k := Proof.Poly1305.blocksArm) Proof.Poly1305.Arm.blocks_verified.1
    (rd := [⟨State.addr p, 16 * n⟩]) (wr := [⟨State.addr P, 128⟩]) ?_ hc hw ?_ blocks_noCalls
  · simp only [Proof.Poly1305.blocksArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r2 ∉ linkRegs),
      h0, h1, h2, hn']
    exact ⟨trivial, trivial, hdj, hP, hp⟩
  · intro s' hrd hwr hsp hf hcs hkeep hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ (by rw [hkeep .r0 blocks_keeps_r0 (by decide), h0])
      fun key msg hr => ?_
    simp only [Proof.Poly1305.blocksArm, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r2 ∉ linkRegs),
      h0, h1, h2, hn'] at hpost
    exact hpost key msg hr

/-! ## `vg_poly1305_finalize`, in its frame -/

theorem storeWords_two (m : Mem) (a : BitVec 32) (x y : BitVec 32) :
    storeWords m a [x, y] = (m.writeW (State.addr a) x).writeW (State.addr (a + 4)) y := rfl

/-- The 8 bytes below `sp`, as the frame's push computes them. -/
theorem addr_below {sp : BitVec 32} (h : 8 ≤ sp.toNat) :
    State.addr (sp - BitVec.ofNat 32 (4 * [Reg.r1, Reg.r12].length)) = State.addr sp - 8 := by
  have e : BitVec.ofNat 32 (4 * [Reg.r1, Reg.r12].length) = 8 := rfl
  rw [e]; simp only [State.addr]; bv_omega

/-- What the frame around `vg_poly1305_finalize` needs of the state it is
entered in: the state at `P`, `out` at `O` and `scratch` at `Sc` in `r0`,
`r1` and `r12`, disjoint, writable, and disjoint from the 8 bytes of stack the
frame pushes. -/
structure FinArgs (s : State) (P O Sc : BitVec 32) : Prop where
  h0 : s.gpr .r0 = P
  h1 : s.gpr .r1 = O
  h12 : s.gpr .r12 = Sc
  hsp : 8 ≤ s.sp.toNat
  hPO : (⟨State.addr P, 128⟩ : Region).Disjoint ⟨State.addr O, 16⟩
  hPS : (⟨State.addr P, 128⟩ : Region).Disjoint ⟨State.addr Sc, 128⟩
  hOS : (⟨State.addr O, 16⟩ : Region).Disjoint ⟨State.addr Sc, 128⟩
  hbP : (⟨State.addr s.sp - 8, 8⟩ : Region).Disjoint ⟨State.addr P, 128⟩
  hbO : (⟨State.addr s.sp - 8, 8⟩ : Region).Disjoint ⟨State.addr O, 16⟩
  hbS : (⟨State.addr s.sp - 8, 8⟩ : Region).Disjoint ⟨State.addr Sc, 128⟩
  hP : P.toNat + 128 ≤ 2 ^ 32
  hO : O.toNat + 16 ≤ 2 ^ 32
  hS : Sc.toNat + 128 ≤ 2 ^ 32
  hw : Covers [⟨State.addr P, 128⟩, ⟨State.addr O, 16⟩, ⟨State.addr Sc, 128⟩] s.wr

/-- The regions `vg_poly1305_finalize` is called with. -/
abbrev finRd (s : State) : List Region := [⟨State.addr s.sp - 8, 8⟩]
abbrev finWr (P O Sc : BitVec 32) : List Region := [⟨State.addr P, 128⟩, ⟨State.addr O, 16⟩, ⟨State.addr Sc, 128⟩]

/-- The state `vg_poly1305_finalize` runs from, with the permissions it is
given. -/
abbrev finView (s : State) (P O Sc : BitVec 32) : State :=
  (pushed [.r1, .r12] s).callEntry.withRegions (finRd s) (finWr P O Sc)

theorem e8 : BitVec.ofNat 32 (4 * [Reg.r1, Reg.r12].length) = 8 := rfl

theorem fin_asp (s : State) : (pushed [.r1, .r12] s).sp = s.sp - 8 := by rw [pushed_sp, e8]

theorem fin_nsp (s : State) (P O Sc : BitVec 32) : (finView s P O Sc).sp = s.sp - 8 := fin_asp s


theorem fin_ng (s : State) (P O Sc : BitVec 32) (r : Reg) (hr : r ∉ linkRegs) :
    (finView s P O Sc).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

namespace FinArgs
variable {s : State} {P O Sc : BitVec 32} (h : FinArgs s P O Sc)
include h

theorem hA : State.addr (s.sp - 8) = State.addr s.sp - 8 := by
  have := addr_below h.hsp; rwa [e8] at this

theorem hA4 : State.addr (s.sp - 8 + BitVec.ofNat 32 4) = State.addr s.sp - 8 + 4 := by
  have := h.hsp; simp only [State.addr]; bv_omega

theorem hspA : (s.sp - 8).toNat = s.sp.toNat - 8 := by have := h.hsp; bv_omega

theorem amem : (pushed [.r1, .r12] s).mem =
    (s.mem.writeW (State.addr s.sp - 8) O).writeW (State.addr s.sp - 8 + 4) Sc := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [Reg.r1, Reg.r12].length)) [s.gpr .r1, s.gpr .r12] = _
  rw [e8, storeWords_two, h.hA, show (s.sp - 8 + 4 : BitVec 32) = s.sp - 8 + BitVec.ofNat 32 4 from rfl, h.hA4,
    h.h1, h.h12]

theorem sa0 (t : State) (ht : t.sp = s.sp - 8) : stackArgAddr t 0 = State.addr s.sp - 8 := by
  unfold stackArgAddr; rw [ht, show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 by bv_omega, h.hA]

theorem arg0 (t : State) (ht : t.sp = s.sp - 8) (hm : t.mem = (pushed [.r1, .r12] s).mem) : stackArg t 0 = O := by
  have := h.hsp
  rw [stackArg, h.sa0 t ht, hm, h.amem, Mem.readW_writeW_sep (fun x h₁ h₂ => by bv_omega) (by decide),
    Mem.readW_writeW_self32]

theorem arg1 (t : State) (ht : t.sp = s.sp - 8) (hm : t.mem = (pushed [.r1, .r12] s).mem) : stackArg t 1 = Sc := by
  rw [stackArg, show stackArgAddr t 1 = State.addr s.sp - 8 + 4 by unfold stackArgAddr; rw [ht]; exact h.hA4, hm,
    h.amem, Mem.readW_writeW_self32]

theorem fA : Frame [⟨State.addr s.sp - 8, 8⟩] s.mem (pushed [.r1, .r12] s).mem := by
  rw [h.amem]
  refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [Region.Contains]
    rw [show State.addr s.sp - 8 + 4 - (State.addr s.sp - 8) = 4 by bv_omega]; decide

theorem pre : Proof.Poly1305.finalizeArm.pre (finView s P O Sc) := by
  simp only [Proof.Poly1305.finalizeArm, h.arg0 _ (fin_nsp s P O Sc) rfl, h.arg1 _ (fin_nsp s P O Sc) rfl, h.sa0 _ (fin_nsp s P O Sc),
    fin_ng s P O Sc .r0 (by decide), h.h0, State.withRegions_rd, State.withRegions_wr]
  refine ⟨trivial, trivial, h.hPO, h.hPS, h.hOS, h.hbP, h.hbO, h.hbS, h.hP, h.hO, h.hS, ?_⟩
  rw [fin_nsp s P O Sc, h.hspA]; omega

/-- The stack arguments are the frame. -/
theorem cov : Covers (finRd s ++ finWr P O Sc) ((pushed [.r1, .r12] s).rd ++ (pushed [.r1, .r12] s).wr) := by
  intro x n' ⟨r, hr, hc⟩
  rcases List.mem_append.mp hr with hr | hr
  · simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_self ..), ?_⟩
    rwa [e8, h.hA]
  · obtain ⟨r', hr', hc'⟩ := h.hw x n' ⟨r, hr, hc⟩
    exact ⟨r', List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr'), hc'⟩

theorem covW : Covers (finWr P O Sc) (pushed [.r1, .r12] s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h.hw x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

end FinArgs

theorem finalize_ok {s : State} {P O Sc : BitVec 32} (h : FinArgs s P O Sc) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨State.addr P, 128⟩, ⟨State.addr O, 16⟩, ⟨State.addr Sc, 128⟩,
        ⟨State.addr s.sp - 8, 8⟩] s s' →
      (∀ key msg, Repr s.mem (State.addr P) key msg →
        Proof.Poly1305.countArm s = BitVec.ofNat 64 msg.length →
        bytesAt s'.mem (State.addr O) 16 = mac key msg) → Q s') :
    WP isa Impl.ChaCha20Poly1305.Arm.finalize s Q := by
  refine WP.frame (rs := [.r1, .r12]) (r := .r1) rfl (by simpa using h.hsp) (by decide) ?_
  have hbw : ∀ r ∈ [⟨State.addr s.sp - 8, 8⟩], (⟨State.addr P, 128⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact h.hbP.symm
  refine WP.call (k := Proof.Poly1305.finalizeArm) Proof.Poly1305.Arm.Fin.finalize_verified.1
    (rd := finRd s) (wr := finWr P O Sc) h.pre h.cov h.covW ?_ finalize_noCalls
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  have hcnt : Proof.Poly1305.countArm (finView s P O Sc) = Proof.Poly1305.countArm s := by
    simp only [Proof.Poly1305.countArm, fin_ng s P O Sc .r2 (by decide), fin_ng s P O Sc .r3 (by decide)]
  simp only [Proof.Poly1305.finalizeArm, fin_ng s P O Sc .r0 (by decide), h.h0, hcnt, h.arg0 _ (fin_nsp s P O Sc) rfl,
    State.withRegions_mem] at hpost
  refine hQ _ ⟨fun r hr hl => ?_, ?_, ?_, ?_, ?_⟩ fun key msg hr hc => ?_
  · have hr1 : r ≠ .r1 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr hr1, hcs r hr hl, pushed_gpr]
  · rw [popped_sp, hsp₂, fin_asp s, e8]
    exact BitVec.sub_add_cancel _ _
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_mem]
    refine (h.fA.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (hf.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem]
    exact hpost key msg (Proof.Poly1305.Repr.buffered (Repr.frame h.fA hbw hr)) hc

end VG.Proof.ChaCha20Poly1305.Arm
