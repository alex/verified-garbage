import VerifiedGarbage.Proof.AesGcm.Arm.Tag

/-!
# AES-GCM on ARMv7: the pre-counter block (`j0`)

Untrusted: everything here is checked by Lean. `j0` writes `J₀` for the
`r5`-byte nonce at `r4` to the state: its words and `0x00000001` for a
12-byte nonce (`j012_ok`), and otherwise GHASH of the nonce padded with
zeros and the lengths block, with `absorb`, `flush` and `lens` on the
accumulator at the state's first block (`j0hash_ok`), the nonce's length
kept in `r7`. `initState` then zeroes the accumulator and writes the first
counter block `inc₃₂(J₀)` (`initState_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes inc32)
open VG.Proof.Gcm (Absorbed lensBlock)
open VG.Proof.Cmac (le4 store4)

theorem inc32_words (a b c d : BitVec 32) : inc32 (a ++ b ++ c ++ d) = a ++ b ++ c ++ (d + 1) := by
  have h₁ : (a ++ b ++ c ++ d).extractLsb' 32 96 = a ++ b ++ c := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
    simp only [show ¬ (32 + i < 32) by omega, ite_false, show 32 + i - 32 = i by omega]
  have h₂ : (a ++ b ++ c ++ d).extractLsb' 0 32 = d := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]; simp [hi]
  simp only [inc32, h₁, h₂]

theorem le4_one : le4 (BitVec.ofNat 32 0x01000000) = [0, 0, 0, 1] := by decide

/-- A block from the bytes of its four little-endian words. -/
theorem ofBytes_le4 (a b c d : BitVec 32) :
    ofBytes (le4 a ++ le4 b ++ le4 c ++ le4 d) = byteRev32 a ++ byteRev32 b ++ byteRev32 c ++ byteRev32 d := by
  have h := Cmac.le4_rev4 (byteRev32 a) (byteRev32 b) (byteRev32 c) (byteRev32 d)
  rw [Cmac.byteRev32_byteRev32, Cmac.byteRev32_byteRev32, Cmac.byteRev32_byteRev32,
    Cmac.byteRev32_byteRev32] at h
  rw [h, Cmac.ofBytes_toBytes]

/-- The regions `j0` writes. -/
abbrev j0Frame (st w sp : BitVec 32) : List Region :=
  [⟨State.addr st, 80⟩, ⟨State.addr w + BitVec.ofNat 64 96, 16⟩, ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, below sp]

/-- Before `j0`: the `n`-byte nonce at `Np`. -/
structure J0In (c st w sp k7 k8 : BitVec 32) (H : Block) (Np : BitVec 32) (n : Nat) (s : State) : Prop where
  env : Env c st w sp k7 k8 s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  r4 : s.gpr .r4 = Np
  r5 : s.gpr .r5 = BitVec.ofNat 32 n
  data : DataOk st w sp s Np n

/-- `J₀` written, from `m₀`, with some value of `r7`. -/
structure J0Mid (c st w sp k8 : BitVec 32) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : ∃ k7, Env c st w sp k7 k8 s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem (State.addr st) = Spec.Gcm.j0 H iv
  frame : Frame (j0Frame st w sp) m₀ s.mem

/-- After `j0`: `J₀`, the accumulator zeroed and the first counter block. -/
structure J0Out (c st w sp k8 : BitVec 32) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : ∃ k7, Env c st w sp k7 k8 s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem (State.addr st) = Spec.Gcm.j0 H iv
  y : blockAt s.mem (State.addr st + BitVec.ofNat 64 16) = 0
  cb : blockAt s.mem (State.addr st + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  frame : Frame (j0Frame st w sp) m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

theorem ctx_j0Frame : ∀ r ∈ j0Frame st w sp, (⟨State.addr c + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.cs.sub_left (Lay.ctxSub (by decide))
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

omit L in
theorem st_j0Frame {m m' : Mem} {d k : Nat} (h : Frame [⟨State.addr st + BitVec.ofNat 64 d, k⟩] m m')
    (hk : d + k ≤ 80) : Frame (j0Frame st w sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Lay.stSub hk⟩

/-- `J₀` of a 12-byte nonce. -/
theorem j012_ok {H : Block} {Np : BitVec 32} {s : State} (h : J0In c st w sp k7 k8 H Np 12 s) :
    WP isa (.block j012) s (J0Mid c st w sp k8 H (bytesAt s.mem (State.addr Np) 12) s.mem) := by
  have he := h.env
  have h10 := he.r10
  have hd := h.data
  have a₁ := hd.addr (j := 4) (by decide)
  have a₂ := hd.addr (j := 8) (by decide)
  have r₀ := in_off hd.rd (show 0 + 4 ≤ 12 by decide) (by decide)
  have r₁ := in_off hd.rd (show 4 + 4 ≤ 12 by decide) (by decide)
  have r₂ := in_off hd.rd (show 8 + 4 ≤ 12 by decide) (by decide)
  simp only [add_ofNat_zero] at r₀
  have w₀ := he.perm.stW (show 0 + 4 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 4 + 4 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 8 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 12 + 4 ≤ 80 by decide)
  simp only [add_ofNat_zero] at w₀
  have h4 := h.r4
  obtain ⟨s', run, hm, hg, hrd, hwr, hsp⟩ : ∃ s', runBlock isa j012 s = some s' ∧
      s'.mem = store4 s.mem (State.addr st) (s.mem.readW (State.addr Np) 32)
        (s.mem.readW (State.addr Np + BitVec.ofNat 64 4) 32) (s.mem.readW (State.addr Np + BitVec.ofNat 64 8) 32)
        (BitVec.ofNat 32 0x01000000) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
    refine ⟨_, by simp only [j012]; arun [h4, h10, add_ofNat_zero, a₁, a₂, L.stA, r₀, r₁, r₂, w₀, w₁, w₂, w₃],
      ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, store4_eq]
    · intro r a b d e; simp [gpr_setReg, a, b, d, e]
    all_goals rfl
  refine WP.of_runBlock ⟨s', run, ?_⟩
  have f : Frame [⟨State.addr st + BitVec.ofNat 64 0, 16⟩] s.mem s'.mem := by
    rw [hm]; simpa using Cmac.frame_store4 (m := s.mem) (State.addr st) _ _ _ _
  refine ⟨⟨k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide) (by decide))
      hsp hrd hwr⟩, ?_, ?_, st_j0Frame f (by decide)⟩
  · rw [blockAt_frame f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide), h.hH]
  · have hb : bytesAt s.mem (State.addr Np) 12 = bytesAt s.mem (State.addr Np) 4 ++
        bytesAt s.mem (State.addr Np + BitVec.ofNat 64 4) 4 ++ bytesAt s.mem (State.addr Np + BitVec.ofNat 64 8) 4 := by
      rw [show (12 : Nat) = 4 + 8 from rfl, bytesAt_add, show (8 : Nat) = 4 + 4 from rfl, bytesAt_add,
        add_ofNat_assoc, List.append_assoc]
    rw [Proof.Gcm.j0_12 _ (length_bytesAt _ _ _), blockAt, hm, Cmac.bytesAt_store4, Cmac.le4_readW,
      Cmac.le4_readW, Cmac.le4_readW, le4_one, hb]

/-- The first counter block, and the accumulator zeroed. -/
theorem initState_ok {H : Block} {iv : List Byte} {m₀ : Mem} {s : State} (h : J0Mid c st w sp k8 H iv m₀ s) :
    WP isa (.block initState) s (J0Out c st w sp k8 H iv m₀) := by
  obtain ⟨k7', he⟩ := h.env
  have h10 := he.r10
  have r₀ := he.perm.stR (show 0 + 4 ≤ 80 by decide)
  have r₁ := he.perm.stR (show 4 + 4 ≤ 80 by decide)
  have r₂ := he.perm.stR (show 8 + 4 ≤ 80 by decide)
  have r₃ := he.perm.stR (show 12 + 4 ≤ 80 by decide)
  simp only [add_ofNat_zero] at r₀
  have w₀ := he.perm.stW (show 48 + 4 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 52 + 4 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 56 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 60 + 4 ≤ 80 by decide)
  have z₀ := he.perm.stW (show 16 + 4 ≤ 80 by decide)
  have z₁ := he.perm.stW (show 20 + 4 ≤ 80 by decide)
  have z₂ := he.perm.stW (show 24 + 4 ≤ 80 by decide)
  have z₃ := he.perm.stW (show 28 + 4 ≤ 80 by decide)
  generalize hw : s.mem.readW (State.addr st + BitVec.ofNat 64 12) 32 = w3
  have split : initState =
      [.ldr .r0 .r10 0, .ldr .r1 .r10 4, .ldr .r2 .r10 8, .ldr .r3 .r10 12, .rev .r3 .r3, addI .r3 .r3 1,
        .rev .r3 .r3, .str .r0 .r10 48, .str .r1 .r10 52, .str .r2 .r10 56, .str .r3 .r10 60] ++
      [.mov .r0 (imm 0), .str .r0 .r10 16, .str .r0 .r10 20, .str .r0 .r10 24, .str .r0 .r10 28] := rfl
  obtain ⟨s₁, run₁, hm₁, hg₁, hrd₁, hwr₁, hsp₁⟩ : ∃ s₁, runBlock isa
      [.ldr .r0 .r10 0, .ldr .r1 .r10 4, .ldr .r2 .r10 8, .ldr .r3 .r10 12, .rev .r3 .r3, addI .r3 .r3 1,
        .rev .r3 .r3, .str .r0 .r10 48, .str .r1 .r10 52, .str .r2 .r10 56, .str .r3 .r10 60] s = some s₁ ∧
      s₁.mem = store4 s.mem (State.addr st + BitVec.ofNat 64 48) (s.mem.readW (State.addr st) 32)
        (s.mem.readW (State.addr st + BitVec.ofNat 64 4) 32) (s.mem.readW (State.addr st + BitVec.ofNat 64 8) 32)
        (byteRev32 (byteRev32 w3 + BitVec.ofNat 32 1)) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      s₁.sp = s.sp := by
    refine ⟨_, by arun [h10, add_ofNat_zero, L.stA, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, store4_eq, add_ofNat_assoc,
        rev_eq, hw, Nat.reduceAdd]
    · intro r a b d e; simp [gpr_setReg, a, b, d, e]
    all_goals rfl
  have h10' : s₁.gpr .r10 = st := by rw [hg₁ _ (by decide) (by decide) (by decide) (by decide), h10]
  rw [← hwr₁] at z₀ z₁ z₂ z₃
  obtain ⟨s', run, hm, hg, hrd, hwr, hsp⟩ : ∃ s', runBlock isa
      [.mov .r0 (imm 0), .str .r0 .r10 16, .str .r0 .r10 20, .str .r0 .r10 24, .str .r0 .r10 28] s₁ = some s' ∧
      s'.mem = store4 s₁.mem (State.addr st + BitVec.ofNat 64 16) 0 0 0 0 ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s₁.gpr r) ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr ∧ s'.sp = s₁.sp := by
    refine ⟨_, by arun [h10', L.stA, z₀, z₁, z₂, z₃], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc, Nat.reduceAdd]; rfl
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  rw [split]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s', run, ?_⟩⟩)
  have f₄ : Frame [⟨State.addr st + BitVec.ofNat 64 48, 16⟩] s.mem s₁.mem := by
    rw [hm₁]; exact Cmac.frame_store4 _ _ _ _ _
  have fz : Frame [⟨State.addr st + BitVec.ofNat 64 16, 16⟩] s₁.mem s'.mem := by
    rw [hm]; exact Cmac.frame_store4 _ _ _ _ _
  have dz : (⟨State.addr st + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint ⟨State.addr st + BitVec.ofNat 64 16, 16⟩ :=
    Lay.st_st (.inr (by decide)) (by decide) (by decide)
  have ff : Frame [⟨State.addr st + BitVec.ofNat 64 0, 80⟩] s.mem s'.mem := by
    refine (f₄.sub fun r hr => ?_).trans (fz.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr <;>
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hJ : blockAt s'.mem (State.addr st) = blockAt s.mem (State.addr st) := by
    rw [blockAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simpa using Lay.st_st (st := st) (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide)
          (by decide)),
      blockAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simpa using Lay.st_st (st := st) (a := 0) (n := 16) (d := 48) (k := 16) (.inl (by decide)) (by decide)
          (by decide))]
  refine ⟨⟨k7', he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        rw [hg _ (by decide), hg₁ _ (by decide) (by decide) (by decide) (by decide)])
      (hsp.trans hsp₁) (hrd.trans hrd₁) (hwr.trans hwr₁)⟩, ?_, by rw [hJ, h.j0], ?_, ?_,
    h.frame.trans (st_j0Frame ff (by decide))⟩
  · rw [blockAt_frame ff (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide)), h.hH]
  · rw [blockAt, hm, Cmac.bytesAt_store4, Cmac.le4_zero]; decide
  · rw [blockAt, bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dz) (by decide),
      hm₁, Cmac.bytesAt_store4, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, ← h.j0, blockAt,
      Cmac.ofBytes_rev4, ← Cmac.le4_readW s.mem (State.addr st), ← Cmac.le4_readW, ← Cmac.le4_readW, ofBytes_le4, hw,
      Cmac.byteRev32_byteRev32, inc32_words]
    rfl

end

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

omit L in
theorem abs_j0Frame {m m' : Mem} (h : Frame (absFrame st w sp 0) m m') : Frame (j0Frame st w sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

omit L in
theorem t_j0Frame {m m' : Mem} (h : Frame (tFrame st w sp 0) m m') : Frame (j0Frame st w sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- The first block of `j0hash`: the accumulator at the state zeroed, the
nonce's length kept in `r7`. -/
theorem j0zero_ok {H : Block} {Np : BitVec 32} {n : Nat} {s : State} (h : J0In c st w sp k7 k8 H Np n s) :
    WP isa (.block [.mov .r0 (imm 0), .str .r0 .r10 0, .str .r0 .r10 4, .str .r0 .r10 8, .str .r0 .r10 12,
      .mov .r7 (.reg .r5), .mov .r6 (imm 0)]) s
      (fun s' => AbsIn c st w sp (BitVec.ofNat 32 n) k8 0 H [] Np n s' ∧
        blockAt s'.mem (State.addr st + BitVec.ofNat 64 0) = 0 ∧
        bytesAt s'.mem (State.addr Np) n = bytesAt s.mem (State.addr Np) n ∧
        Frame [⟨State.addr st, 16⟩] s.mem s'.mem) := by
  have he := h.env
  have hd := h.data
  have h10 := he.r10
  have z₀ := he.perm.stW (show 0 + 4 ≤ 80 by decide)
  have z₁ := he.perm.stW (show 4 + 4 ≤ 80 by decide)
  have z₂ := he.perm.stW (show 8 + 4 ≤ 80 by decide)
  have z₃ := he.perm.stW (show 12 + 4 ≤ 80 by decide)
  simp only [add_ofNat_zero] at z₀
  obtain ⟨s₁, run₁, hm₁, h6, h7, hg₁, hrd₁, hwr₁, hsp₁⟩ : ∃ s₁, runBlock isa [.mov .r0 (imm 0), .str .r0 .r10 0,
      .str .r0 .r10 4, .str .r0 .r10 8, .str .r0 .r10 12, .mov .r7 (.reg .r5), .mov .r6 (imm 0)] s = some s₁ ∧
      s₁.mem = store4 s.mem (State.addr st) 0 0 0 0 ∧ s₁.gpr .r6 = BitVec.ofNat 32 0 ∧
      s₁.gpr .r7 = BitVec.ofNat 32 n ∧ (∀ r, r ≠ .r0 → r ≠ .r6 → r ≠ .r7 → s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp := by
    refine ⟨_, by arun [h10, add_ofNat_zero, L.stA, z₀, z₁, z₂, z₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq]; rfl
    · simp [gpr_setReg]
    · simp [gpr_setReg, h.r5]
    · intro r a b d; simp [gpr_setReg, a, b, d]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have he₁ := he.set7 h7 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hsp₁ hrd₁ hwr₁
  have f₁ : Frame [⟨State.addr st, 16⟩] s.mem s₁.mem := by rw [hm₁]; exact Cmac.frame_store4 _ _ _ _ _
  have dD : ∀ r ∈ [(⟨State.addr st, 16⟩ : Region)], (⟨State.addr Np, n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hd.st.sub_right (Region.sub_prefix (by decide))
  refine ⟨⟨he₁, by rw [hg₁ _ (by decide) (by decide) (by decide), h.r4],
    by rw [hg₁ _ (by decide) (by decide) (by decide), h.r5], h6, hd.of_eq hrd₁ hwr₁, ?_⟩, ?_,
    bytesAt_frame f₁ dD (by have := hd.lt; omega), f₁⟩
  · rw [blockAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using L.ctx_st (a := 240) (n := 16) (d := 0) (k := 16) (by decide) (by decide)), h.hH]
  · rw [add_ofNat_zero, blockAt, hm₁, Cmac.bytesAt_store4, Cmac.le4_zero]; decide

/-- `J₀` of a nonce of any length but 12: GHASH of the nonce padded and of
the lengths block. -/
theorem j0hash_ok {H : Block} {Np : BitVec 32} {n : Nat} {s : State} (h : J0In c st w sp k7 k8 H Np n s)
    (hn : n ≠ 12) :
    WP isa j0hash s (J0Mid c st w sp k8 H (bytesAt s.mem (State.addr Np) n) s.mem) := by
  have hd := h.data
  have hlt := hd.lt32
  refine WP.seq (WP.mono (j0zero_ok L h) fun s₁ ⟨hai, hY₁, hiv, f₁⟩ => ?_)
  refine WP.seq (WP.mono (absorb_ok L (yo := 0) (.inl rfl) hai) fun s₂ ho => ?_)
  rw [List.nil_append, hiv] at ho
  have hab₂ := ho.abs (Proof.Gcm.absorbed_nil H hY₁)
  have he₂ := ho.env
  have hH₂ : blockAt s₂.mem (State.addr c + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ho.frame (ctx_absFrame L (.inl rfl)), hai.hH]
  obtain ⟨s₃, run₃, h6₃, hg₃, hk₃⟩ : ∃ s₃, runBlock isa [.dp .and .r6 .r7 (imm 15)] s₂ = some s₃ ∧
      s₃.gpr .r6 = BitVec.ofNat 32 (n % 16) ∧ (∀ r, r ≠ .r6 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    have hand := and15 (BitVec.ofNat 32 n)
    rw [toNat32 hlt] at hand
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, he₂.r7, hand]
    · intro r a; simp [gpr_setReg, a]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hk₃.sp hk₃.rd hk₃.wr
  refine WP.seq (WP.mono (flush_ok L (yo := 0) (.inl rfl) (x := bytesAt s.mem (State.addr Np) n) ⟨he₃, by
    rw [hk₃.mem, hH₂]⟩ (by rw [h6₃, length_bytesAt])) fun s₄ hf => ?_)
  have he₄ := hf.env
  obtain ⟨s₅, run₅, h4₅, h5₅, h6₅, h7₅, hg₅, hk₅⟩ : ∃ s₅, runBlock isa [.mov .r4 (imm 0), .mov .r5 (imm 0),
      .mov .r6 (.reg .r7), .mov .r7 (imm 0)] s₄ = some s₅ ∧
      s₅.gpr .r4 = 0 ∧ s₅.gpr .r5 = 0 ∧ s₅.gpr .r6 = BitVec.ofNat 32 n ∧ s₅.gpr .r7 = 0 ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg, he₄.r7]
    · simp [gpr_setReg]
    · intro r a b d e; simp [gpr_setReg, a, b, d, e]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := he₄.set7 h7₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide) (by decide) (by decide))
    hk₅.sp hk₅.rd hk₅.wr
  refine WP.mono (lens_ok L (yo := 0) (.inl rfl) (H := H) he₅ (by rw [hk₅.mem]; exact hf.hH))
    fun s₆ ⟨he₆, hH₆, hY₆, f₆⟩ => ?_
  refine ⟨⟨_, he₆⟩, hH₆, ?_, ?_⟩
  · have hw := (hf.abs (by rw [hk₃.mem]; exact hab₂)).whole_eq (by
      simp only [List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod n)
    rw [length_bytesAt] at hw
    rw [h4₅, h5₅, h6₅, h7₅, show ((0 : BitVec 32) ++ (0 : BitVec 32)).toNat = 0 from rfl,
      show ((0 : BitVec 32) ++ BitVec.ofNat 32 n).toNat = n by
        rw [Proof.Gcm.toNat_append, toNat32 hlt]; simp, hk₅.mem, hw] at hY₆
    rw [Proof.Gcm.j0_eq H (by rw [length_bytesAt]; exact hn), length_bytesAt, ← hY₆, add_ofNat_zero]
  · have g₁ : Frame (j0Frame st w sp) s.mem s₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    have g₄ := t_j0Frame hf.frame
    have g₆ := t_j0Frame f₆
    rw [hk₃.mem] at g₄
    rw [hk₅.mem] at g₆
    exact ((g₁.trans (abs_j0Frame ho.frame)).trans g₄).trans g₆

/-- `j0`: the streaming state's `J₀`, accumulator and first counter block. -/
theorem j0_ok {H : Block} {Np : BitVec 32} {n : Nat} {s : State} (h : J0In c st w sp k7 k8 H Np n s) :
    WP isa j0 s (J0Out c st w sp k8 H (bytesAt s.mem (State.addr Np) n) s.mem) := by
  have hlt := h.data.lt32
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmpk_ok s .r5 h.r5 hlt (k := 12) (by decide) (by decide)
  have h₁ : J0In c st w sp k7 k8 H Np n s₁ :=
    ⟨h.env.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁, by rw [hm₁]; exact h.hH, by rw [hg₁]; exact h.r4,
      by rw [hg₁]; exact h.r5, h.data.of_eq hrd₁ hwr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  rw [← hm₁]
  refine WP.seq (WP.ite (decide (n = 12)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_))
  · have h12 : n = 12 := by simpa using ht
    subst h12
    exact WP.mono (j012_ok L h₁) fun _ hm => initState_ok L hm
  · exact WP.mono (j0hash_ok L h₁ (by simpa using hf)) fun _ hm => initState_ok L hm

end

end VG.Proof.AesGcm.Arm
