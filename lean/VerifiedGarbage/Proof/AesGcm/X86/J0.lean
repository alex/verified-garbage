import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.Cmac.Dbl32

/-!
# AES-GCM on x86: the pre-counter block (`j0`)

Untrusted: everything here is checked by Lean. `j0` writes `J₀` for the
`nO`-byte nonce at `dO` to the state: its words and `0x00000001` for a
12-byte nonce (`j012_pc`), and otherwise GHASH of the nonce padded with
zeros and the lengths block, with `absorb`, `flush` and `lens` on the
accumulator at the state's first block (`j0hash_pc`). `initState` then
zeroes the accumulator and writes the first counter block `inc₃₂(J₀)`
(`initState_pc`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
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
abbrev j0Frame (St W SP : BitVec 32) (K : Nat) : List Region :=
  [⟨w64 St, 80⟩, ⟨w64 W + BitVec.ofNat 64 96, 16⟩, wsR W, below SP K]

/-- Before `j0`: the `n`-byte nonce at `D`. -/
structure J0In (Ctx St W SP : BitVec 32) (K : Nat) (D : BitVec 32) (n : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  dO : slotv s.mem W dO = D
  nO : slotv s.mem W nO = BitVec.ofNat 32 n
  nl : slotv s.mem W nlO = BitVec.ofNat 32 n
  z : slotv s.mem W zO = 0
  nlt : n < 2 ^ 32
  data : DataOk St W SP K s D n

/-- `J₀` written, from `m₀`. -/
structure J0Mid (Ctx St W SP : BitVec 32) (K : Nat) (D : BitVec 32) (n : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  j0 : blockAt s.mem (w64 St) = Spec.Gcm.j0 (Hk m₀ Ctx) (bytesAt m₀ (w64 D) n)
  frame : Frame (j0Frame St W SP K) m₀ s.mem

/-- After `j0`: `J₀`, the accumulator zeroed and the first counter block. -/
structure J0Out (Ctx St W SP : BitVec 32) (K : Nat) (D : BitVec 32) (n : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  j0 : blockAt s.mem (w64 St) = Spec.Gcm.j0 (Hk m₀ Ctx) (bytesAt m₀ (w64 D) n)
  y : blockAt s.mem (w64 St + BitVec.ofNat 64 16) = 0
  cb : blockAt s.mem (w64 St + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 (Hk m₀ Ctx) (bytesAt m₀ (w64 D) n))
  frame : Frame (j0Frame St W SP K) m₀ s.mem

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay Ctx St W SP K)
include L

theorem ctx_j0Frame : ∀ r ∈ j0Frame St W SP K, (⟨w64 Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.cs.sub_left (Lay.ctxSub (by decide))
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

theorem kept_j0Frame : ∀ r ∈ j0Frame St W SP K, (keptR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 80) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

omit L in
theorem st_j0Frame {m m' : Mem} {d k : Nat} (h : Frame [⟨w64 St + BitVec.ofNat 64 d, k⟩] m m') (hk : d + k ≤ 80) :
    Frame (j0Frame St W SP K) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., by simpa using Lay.stSub (St := w64 St) hk⟩

/-- `J₀` of a 12-byte nonce, after `edi := D`. -/
theorem j012b_ok {D : BitVec 32} {s : State} (he : Env Ctx St W SP s) (hd : DataOk St W SP K s D 12)
    (hdi : s.gpr .edi = D) :
    ∃ s', runBlock isa [.mov .eax (.mem (at_ .edi 0)), .mov .ecx (.mem (at_ .edi 4)), .mov .edx (.mem (at_ .edi 8)),
        .store (at_ .esi 0) .eax, .store (at_ .esi 4) .ecx, .store (at_ .esi 8) .edx,
        .mov .eax (imm 0x01000000), .store (at_ .esi 12) .eax] s = some s' ∧
      s'.mem = store4 s.mem (w64 St) (s.mem.readW (w64 D) 32) (s.mem.readW (w64 D + BitVec.ofNat 64 4) 32)
        (s.mem.readW (w64 D + BitVec.ofNat 64 8) 32) (BitVec.ofNat 32 0x01000000) ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have r₀ := in_off hd.rd (show 0 + 4 ≤ 12 by decide) (by decide)
  have r₁ := in_off hd.rd (show 4 + 4 ≤ 12 by decide) (by decide)
  have r₂ := in_off hd.rd (show 8 + 4 ≤ 12 by decide) (by decide)
  have e₀ : w64 (D + BitVec.ofNat 32 0) = w64 D + BitVec.ofNat 64 0 := hd.ptr (by decide)
  have e₁ : w64 (D + BitVec.ofNat 32 4) = w64 D + BitVec.ofNat 64 4 := hd.ptr (by decide)
  have e₂ : w64 (D + BitVec.ofNat 32 8) = w64 D + BitVec.ofNat 64 8 := hd.ptr (by decide)
  refine ⟨_, by xrun [hdi, he.esi, e₀, e₁, e₂, r₀, r₁, r₂, L.aS, he.stIn], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setMem, mem_setReg, store4, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  · regs []
  · regs []
  · regs []
  all_goals rfl

theorem j012_pc {D : BitVec 32} :
    Pc (fun (m₀ : Mem) s => J0In Ctx St W SP K D 12 s ∧ s.mem = m₀) j012 (J0Mid Ctx St W SP K D 12 ·) := by
  refine Pc.seq (Q := fun m₀ s => (J0In Ctx St W SP K D 12 s ∧ s.mem = m₀) ∧ s.gpr .edi = D)
    (Pc.taint [.ebp] (fun m₀ s ⟨h, hm⟩ => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.ebp, h₂.1.env.ebp]) (by taint_decide)) ?_
  · have he := h.env
    have hd := h.dO
    refine WP.of_runBlock ⟨_, by xrun [he.ebp, L.aW, he.wIn', hd], ⟨⟨?_, ?_, ?_, ?_, ?_, h.nlt, ?_⟩, ?_⟩, ?_⟩
    · exact he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by mems [])
    · mems []; exact h.dO
    · mems []; exact h.nO
    · mems []; exact h.nl
    · mems []; exact h.z
    · exact h.data.of_eq (by mems []) (by mems [])
    · mems []; exact hm
    · regs [hd]
  refine Pc.taint [.edi, .esi] (fun m₀ s ⟨⟨h, hm⟩, hdi⟩ => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2, h₂.2]
    · rw [h₁.1.1.env.esi, h₂.1.1.env.esi]) (by taint_decide)
  have he := h.env
  obtain ⟨s', run, m', bp, si, sp, rd, wr⟩ := j012b_ok L he h.data hdi
  refine WP.of_runBlock ⟨s', run, ?_⟩
  have f : Frame [⟨w64 St + BitVec.ofNat 64 0, 16⟩] s.mem s'.mem := by
    rw [m']; simpa using Cmac.frame_store4 (m := s.mem) (w64 St) _ _ _ _
  refine ⟨he.keep bp si sp rd wr (slot_frame f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm),
    ?_, by rw [← hm]; exact st_j0Frame f (by decide)⟩
  · have hH : Hk s.mem Ctx = Hk m₀ Ctx := by rw [hm]
    have hb : bytesAt s.mem (w64 D) 12 = bytesAt s.mem (w64 D) 4 ++ bytesAt s.mem (w64 D + BitVec.ofNat 64 4) 4 ++
        bytesAt s.mem (w64 D + BitVec.ofNat 64 8) 4 := by
      rw [show (12 : Nat) = 4 + 8 from rfl, bytesAt_add, show (8 : Nat) = 4 + 4 from rfl, bytesAt_add,
        add_ofNat_assoc, List.append_assoc]
    rw [← hm, Proof.Gcm.j0_12 _ (length_bytesAt _ _ _), blockAt, m', Cmac.bytesAt_store4, Cmac.le4_readW,
      Cmac.le4_readW, Cmac.le4_readW, le4_one, hb]

theorem initState_ok {D : BitVec 32} {n : Nat} {m₀ : Mem} {s : State} (h : J0Mid Ctx St W SP K D n m₀ s) :
    WP isa (.block initState) s (J0Out Ctx St W SP K D n m₀) := by
  have he := h.env
  have e0 : w64 St + BitVec.ofNat 64 0 = w64 St := BitVec.add_zero _
  have i0 : InRegions s.wr (w64 St) 4 := by have := he.stIn (d := 0) (n := 4) (by decide); rwa [e0] at this
  have i0' : InRegions (s.rd ++ s.wr) (w64 St) 4 := by
    have := he.stIn' (d := 0) (n := 4) (by decide); rwa [e0] at this
  generalize hw0 : s.mem.readW (w64 St) 32 = w0
  generalize hw1 : s.mem.readW (w64 St + BitVec.ofNat 64 4) 32 = w1
  generalize hw2 : s.mem.readW (w64 St + BitVec.ofNat 64 8) 32 = w2
  generalize hw3 : s.mem.readW (w64 St + BitVec.ofNat 64 12) 32 = w3
  obtain ⟨s', run, m', bp, si, sp, rd, wr⟩ : ∃ s', runBlock isa initState s = some s' ∧
      s'.mem = store4 (store4 s.mem (w64 St + BitVec.ofNat 64 48) w0 w1 w2 (byteRev32 (byteRev32 w3 + 1)))
        (w64 St + BitVec.ofNat 64 16) 0 0 0 0 ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
    refine ⟨_, by xrun [initState, he.esi, L.aS, e0, i0, i0', he.stIn, he.stIn', readW_writeW_off, hw0, hw1, hw2,
      hw3], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setMem, mem_setReg, mem_arithFlags, store4, add_ofNat_assoc, Nat.reduceAdd, bswap_eq]
      rfl
    · regs []
    · regs []
    · regs []
    all_goals rfl
  refine WP.of_runBlock ⟨s', run, ?_⟩
  have f₄ := Cmac.frame_store4 (m := s.mem) (w64 St + BitVec.ofNat 64 48) w0 w1 w2 (byteRev32 (byteRev32 w3 + 1))
  have fz := Cmac.frame_store4 (m := store4 s.mem (w64 St + BitVec.ofNat 64 48) w0 w1 w2
    (byteRev32 (byteRev32 w3 + 1))) (w64 St + BitVec.ofNat 64 16) 0 0 0 0
  rw [← m'] at fz
  have ff : Frame (j0Frame St W SP K) s.mem s'.mem :=
    (st_j0Frame f₄ (by decide)).trans (st_j0Frame fz (by decide))
  have d16 : ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 16, 16⟩ : Region)], (⟨w64 St + BitVec.ofNat 64 0, 16⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  have d48 : ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 48, 16⟩ : Region)], (⟨w64 St + BitVec.ofNat 64 0, 16⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  have hJ : blockAt s'.mem (w64 St) = blockAt s.mem (w64 St) := by
    have := (blockAt_frame fz d16).trans (blockAt_frame f₄ d48)
    rwa [e0] at this
  refine ⟨he.keep bp si sp rd wr (slot_frame ff fun r hr =>
      (kept_j0Frame L r hr).sub_left (Offset.sub _ (by decide) (by decide))), by rw [hJ, h.j0], ?_, ?_,
    h.frame.trans ff⟩
  · rw [blockAt, m', show store4 _ (w64 St + BitVec.ofNat 64 16) 0 0 0 0 =
      Cmac.zero4 (store4 s.mem (w64 St + BitVec.ofNat 64 48) w0 w1 w2 (byteRev32 (byteRev32 w3 + 1)))
        (w64 St + BitVec.ofNat 64 16) from rfl, zero4_bytes', ofBytes_zeros]
  · rw [blockAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inr (by decide)) (by decide) (by decide)),
      blockAt, Cmac.bytesAt_store4, ofBytes_le4, Cmac.byteRev32_byteRev32, ← h.j0, blockAt, Cmac.ofBytes_rev4,
      hw0, hw1, hw2, hw3, inc32_words]

omit L in
theorem abs_j0Frame {m m' : Mem} (h : Frame (absFrame St W SP K 0) m m') : Frame (j0Frame St W SP K) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by simpa using Lay.stSub (St := w64 St) (d := 0) (n := 16) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., by simpa using Lay.stSub (St := w64 St) (d := 32) (n := 16) (by decide)⟩
    · exact ⟨wsR W, by simp, fun _ h => h⟩
    · exact ⟨below SP K, by simp, fun _ h => h⟩

omit L in
theorem t_j0Frame {m m' : Mem} (h : Frame (tFrame St W SP K 0) m m') : Frame (j0Frame St W SP K) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by simpa using Lay.stSub (St := w64 St) (d := 0) (n := 16) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨wsR W, by simp, fun _ h => h⟩
    · exact ⟨below SP K, by simp, fun _ h => h⟩

omit L in
theorem pslot_j0Frame {m m' : Mem} (h : Frame [pslotR W] m m') : Frame (j0Frame St W SP K) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨wsR W, by simp, pslot_ws W⟩

/-- The kept slots `j0hash` reads. -/
abbrev J0Slots (W : BitVec 32) (n : Nat) (m : Mem) : Prop :=
  slotv m W nlO = BitVec.ofNat 32 n ∧ slotv m W zO = 0

/-- Part of the way through `j0hash`: `x` absorbed into the accumulator at the
state's first block. -/
structure J0H (Ctx St W SP : BitVec 32) (K : Nat) (n : Nat) (x : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  sl : J0Slots W n s.mem
  abs : Absorbed s.mem (w64 St + BitVec.ofNat 64 0) (w64 St + BitVec.ofNat 64 32) (Hk m₀ Ctx) x
  hk : Hk s.mem Ctx = Hk m₀ Ctx
  frame : Frame (j0Frame St W SP K) m₀ s.mem

theorem j0z_ok {D : BitVec 32} {n : Nat} {m₀ : Mem} {s : State} (h : J0In Ctx St W SP K D n s) (hm : s.mem = m₀) :
    WP isa (.block [.mov .eax (imm 0), .store (at_ .esi 0) .eax, .store (at_ .esi 4) .eax, .store (at_ .esi 8) .eax,
      .store (at_ .esi 12) .eax, .store (at_ .ebp bO) .eax]) s fun s' =>
      AbsIn Ctx St W SP K D n 0 s' ∧ J0H Ctx St W SP K n [] m₀ s' ∧ bytesAt s'.mem (w64 D) n = bytesAt m₀ (w64 D) n := by
  have he := h.env
  subst hm
  have hz : Cmac.zero4 s.mem (w64 St + BitVec.ofNat 64 0) = (((s.mem.writeW (w64 St + BitVec.ofNat 64 0)
      (BitVec.ofNat 32 0)).writeW (w64 St + BitVec.ofNat 64 4) (BitVec.ofNat 32 0)).writeW
      (w64 St + BitVec.ofNat 64 8) (BitVec.ofNat 32 0)).writeW (w64 St + BitVec.ofNat 64 12) (BitVec.ofNat 32 0) := by
    simp only [Cmac.zero4, store4, add_ofNat_assoc]; rfl
  refine WP.of_runBlock ⟨_, by xrun [he.esi, he.ebp, L.aS, L.aW, he.stIn, he.wIn], ?_⟩
  simp only [mem_setMem, mem_setReg, gpr_setMem, rd_setMem, wr_setMem, rd_setReg, wr_setReg, ← hz]
  generalize hZ : Cmac.zero4 s.mem (w64 St + BitVec.ofNat 64 0) = Z at *
  have fz : Frame [⟨w64 St + BitVec.ofNat 64 0, 16⟩] s.mem Z := by rw [← hZ]; exact Cmac.frame_store4 _ _ _ _ _
  have fb : Frame [⟨w64 W + BitVec.ofNat 64 bO, 4⟩] Z (Z.writeW (w64 W + BitVec.ofNat 64 bO) (BitVec.ofNat 32 0)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fb' : Frame [pslotR W] Z (Z.writeW (w64 W + BitVec.ofNat 64 bO) (BitVec.ofNat 32 0)) :=
    fb.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hf : Frame (j0Frame St W SP K) s.mem (Z.writeW (w64 W + BitVec.ofNat 64 bO) (BitVec.ofNat 32 0)) :=
    (st_j0Frame fz (by decide)).trans (pslot_j0Frame fb')
  have sl : ∀ {o}, 96 ≤ o → o + 4 ≤ 2560 → (o + 4 ≤ bO ∨ bO + 4 ≤ o) →
      slotv (Z.writeW (w64 W + BitVec.ofNat 64 bO) (BitVec.ofNat 32 0)) W o = slotv s.mem W o := fun h₁ h₂ h₃ => by
    rw [slotv_eq, slot_frame fb fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w h₃ (by omega) (by decide)]
    exact slot_frame fz fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.st_w (by decide) (.inr ⟨h₁, h₂⟩)).symm
  have dZ : ∀ r ∈ j0Frame St W SP K, (⟨w64 D, n⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.data.st
    · exact h.data.w.sub_right (Lay.wSub (by decide))
    · exact h.data.w.sub_right (Lay.wSub (by decide))
    · exact h.data.stk.symm
  have hD := bytesAt_frame hf dZ (by have := h.data.fit; omega)
  have he' : Env Ctx St W SP (setMem ((s.setReg .eax (BitVec.ofNat 32 0)))
      (Z.writeW (w64 W + BitVec.ofNat 64 bO) (BitVec.ofNat 32 0))) :=
    he.keep (by regs []) (by regs []) (by regs []) rfl rfl (by
      simp only [mem_setMem]; exact slot_frame hf fun r hr =>
        (kept_j0Frame L r hr).sub_left (Offset.sub _ (by decide) (by decide)))
  refine ⟨⟨he', ?_, ?_, ?_, by decide, h.nlt, h.data.of_eq rfl rfl⟩, ⟨he', ⟨?_, ?_⟩, ?_, ?_, hf⟩, hD⟩
  · rw [mem_setMem, sl (by decide) (by decide) (by decide)]; exact h.dO
  · rw [mem_setMem, sl (by decide) (by decide) (by decide)]; exact h.nO
  · simp only [mem_setMem, slotv_eq, Mem.readW_writeW_self32]
  · rw [mem_setMem, sl (by decide) (by decide) (by decide)]; exact h.nl
  · rw [mem_setMem, sl (by decide) (by decide) (by decide)]; exact h.z
  · refine Proof.Gcm.absorbed_nil _ ?_
    rw [mem_setMem, blockAt_frame fb fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩),
      blockAt, ← hZ, zero4_bytes', ofBytes_zeros]
  · exact blockAt_frame hf (ctx_j0Frame L)

theorem j0a_pc {D : BitVec 32} {n : Nat} (hnlt : n < 2 ^ 32) :
    Pc (fun (m₀ : Mem) s => AbsIn Ctx St W SP K D n 0 s ∧ J0H Ctx St W SP K n [] m₀ s ∧
        bytesAt s.mem (w64 D) n = bytesAt m₀ (w64 D) n) (absorb 0)
      (fun m₀ s => J0H Ctx St W SP K n (bytesAt m₀ (w64 D) n) m₀ s) := by
  refine Pc.mono (Pc.lift (absorb_pc L (yo := 0) (.inl rfl) (by decide) hnlt) (fun _ s => s.mem)
    fun m₀ s h => ⟨h.1, rfl⟩) (fun _ _ h => h) fun m₀ s' ⟨s, ⟨_, hh, hD⟩, ho, _, _⟩ => ?_
  have hk := hk_frame L (.inl rfl) ho.frame
  refine ⟨ho.env, ⟨?_, ?_⟩, ?_, by rw [hk, hh.hk], hh.frame.trans (abs_j0Frame ho.frame)⟩
  · rw [slotv_eq, slot_frame ho.frame (slot_absFrame L (.inl rfl) (by decide) (by decide))]; exact hh.sl.1
  · rw [slotv_eq, slot_frame ho.frame (slot_absFrame L (.inl rfl) (by decide) (by decide))]; exact hh.sl.2
  · have := ho.abs [] rfl (by rw [hh.hk]; exact hh.abs)
    rwa [List.nil_append, hD, hh.hk] at this

theorem J0H.wslot {n : Nat} {x : List Byte} {m₀ : Mem} {s s' : State} (h : J0H Ctx St W SP K n x m₀ s) {o : Nat}
    (ho₁ : 240 ≤ o) (ho₂ : o + 4 ≤ 2560) {v : BitVec 32}
    (hm : s'.mem = s.mem.writeW (w64 W + BitVec.ofNat 64 o) v)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : J0H Ctx St W SP K n x m₀ s' := by
  have fb : Frame [⟨w64 W + BitVec.ofNat 64 o, 4⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hf : Frame (j0Frame St W SP K) s.mem s'.mem := fb.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨wsR W, by simp, Offset.sub _ (by omega) (by omega)⟩
  have dS : ∀ {a k : Nat}, a + k ≤ 80 → ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region)],
      (⟨w64 St + BitVec.ofNat 64 a, k⟩ : Region).Disjoint r := fun hak r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.st_w hak (.inr ⟨by omega, ho₂⟩)
  have sK : ∀ {q}, 128 ≤ q → q + 4 ≤ 240 → slotv s'.mem W q = slotv s.mem W q := fun h₁ h₂ =>
    slot_frame fb fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) ho₂
  have hk : Hk s'.mem Ctx = Hk s.mem Ctx := blockAt_frame fb fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by omega)
  refine ⟨h.env.keep hbp hsi hsp hrd hwr (sK (by decide) (by decide)),
    ⟨by rw [sK (by decide) (by decide)]; exact h.sl.1, by rw [sK (by decide) (by decide)]; exact h.sl.2⟩,
    h.abs.congr (blockAt_frame fb (dS (by decide))) (bytesAt_frame fb (dS (by omega)) (by omega)),
    by rw [hk, h.hk], h.frame.trans hf⟩

theorem j0b_pc {n : Nat} (hnlt : n < 2 ^ 32) {x : Mem → List Byte} :
    Pc (fun (m₀ : Mem) s => J0H Ctx St W SP K n (x m₀) m₀ s)
      (.block [.mov .eax (slot nlO), .alu .and .eax (imm 15), .store (at_ .ebp bO) .eax])
      (fun m₀ s => J0H Ctx St W SP K n (x m₀) m₀ s ∧ slotv s.mem W bO = BitVec.ofNat 32 (n % 16)) := by
  refine Pc.taint [.ebp] (fun m₀ s h => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)
  have he := h.env
  have hn := h.sl.1
  have hand := and15 (BitVec.ofNat 32 n)
  rw [toNat_ofNat32 hnlt] at hand
  refine WP.of_runBlock ⟨_, by xrun [he.ebp, L.aW, he.wIn, he.wIn', hn], ?_, ?_⟩
  · exact h.wslot L (o := bO) (v := BitVec.ofNat 32 n &&& BitVec.ofNat 32 15) (by decide) (by decide) (by mems [])
      (by regs []) (by regs []) (by regs []) (by mems []) (by mems [])
  · mems [slotv_eq, hand]

theorem j0c_pc {D : BitVec 32} {n : Nat} :
    Pc (fun (m₀ : Mem) s => J0H Ctx St W SP K n (bytesAt m₀ (w64 D) n) m₀ s ∧
        slotv s.mem W bO = BitVec.ofNat 32 (n % 16)) (flush 0)
      (fun m₀ s => J0H Ctx St W SP K n (bytesAt m₀ (w64 D) n ++ zeros (padLen n)) m₀ s) := by
  refine Pc.mono (Pc.lift (flush_pc L (yo := 0) (.inl rfl) (b := n % 16) (Nat.mod_lt _ (by decide)))
    (fun _ s => s.mem) fun m₀ s h => ⟨⟨h.1.env, h.2⟩, rfl⟩) (fun _ _ h => h) fun m₀ s' ⟨s, ⟨hh, _⟩, ho, _, _⟩ => ?_
  have hk : Hk s'.mem Ctx = Hk s.mem Ctx := blockAt_frame ho.frame (ctx_tFrame L (.inl rfl))
  refine ⟨ho.env, ⟨?_, ?_⟩, ?_, by rw [hk, hh.hk], hh.frame.trans (t_j0Frame ho.frame)⟩
  · rw [slotv_eq, slot_frame ho.frame (slot_tFrame L (.inl rfl) (by decide) (by decide))]; exact hh.sl.1
  · rw [slotv_eq, slot_frame ho.frame (slot_tFrame L (.inl rfl) (by decide) (by decide))]; exact hh.sl.2
  · have := ho.abs (bytesAt m₀ (w64 D) n) (by rw [length_bytesAt]) (by rw [hh.hk]; exact hh.abs)
    rwa [length_bytesAt, hh.hk] at this

theorem j0d_pc {D : BitVec 32} {n : Nat} (hnlt : n < 2 ^ 32) (hn : n ≠ 12) :
    Pc (fun (m₀ : Mem) s => J0H Ctx St W SP K n (bytesAt m₀ (w64 D) n ++ zeros (padLen n)) m₀ s)
      (lens 0 zO zO nlO zO) (J0Mid Ctx St W SP K D n ·) := by
  refine Pc.mono (Pc.lift (lens_pc L (yo := 0) (al := zO) (ah := zO) (tl := nlO) (th := zO)
    (.inl ⟨rfl, rfl, rfl, rfl, rfl⟩) (alo := 0) (ahi := 0) (tlo := BitVec.ofNat 32 n) (thi := 0))
    (fun _ s => s.mem) fun m₀ s h => ⟨⟨h.env, h.sl.2, h.sl.2, h.sl.1, h.sl.2⟩, rfl⟩) (fun _ _ h => h)
    fun m₀ s' ⟨s, hh, ho, _, _⟩ => ?_
  refine ⟨ho.env, ?_, hh.frame.trans (t_j0Frame ho.frame)⟩
  have hl : (bytesAt m₀ (w64 D) n ++ zeros (padLen n)).length % 16 = 0 := by
    rw [List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod n
  have ha := hh.abs.1
  rw [Proof.Gcm.whole_of_mod hl, List.take_of_length_le (Nat.le_refl _)] at ha
  have hv : val64 (BitVec.ofNat 32 n) 0 = n := by simp [val64, toNat_ofNat32 hnlt]
  have hz : val64 0 0 = 0 := rfl
  have := ho.out
  rw [ha, hh.hk, hv, hz] at this
  have e0 : w64 St + BitVec.ofNat 64 0 = w64 St := BitVec.add_zero _
  rw [e0] at this
  rw [this, Proof.Gcm.j0_eq _ (by rw [length_bytesAt]; exact hn), length_bytesAt]

theorem j0hash_pc {D : BitVec 32} {n : Nat} (hnlt : n < 2 ^ 32) (hn : n ≠ 12) :
    Pc (fun (m₀ : Mem) s => J0In Ctx St W SP K D n s ∧ s.mem = m₀) j0hash (J0Mid Ctx St W SP K D n ·) := by
  refine Pc.seq (Pc.taint [.ebp, .esi] (fun m₀ s ⟨h, hm⟩ => j0z_ok L h hm) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.env.ebp, h₂.1.env.ebp]
    · rw [h₁.1.env.esi, h₂.1.env.esi]) (by taint_decide)) ?_
  exact Pc.seq (j0a_pc L hnlt) (Pc.seq (j0b_pc L hnlt (x := fun m₀ => bytesAt m₀ (w64 D) n))
    (Pc.seq (j0c_pc L) (j0d_pc L hnlt hn)))

theorem j0_pc {D : BitVec 32} {n : Nat} :
    Pc (fun (m₀ : Mem) s => J0In Ctx St W SP K D n s ∧ s.mem = m₀) j0 (J0Out Ctx St W SP K D n ·) := by
  refine Pc.seq (Q := fun m₀ s => (J0In Ctx St W SP K D n s ∧ s.mem = m₀) ∧ s.zf = some (decide (n = 12)))
    (Pc.taint [.ebp] (fun m₀ s ⟨h, hm⟩ => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.ebp, h₂.1.env.ebp]) (by taint_decide)) ?_
  · have he := h.env
    have hl := h.nl
    refine WP.of_runBlock ⟨_, by xrun [he.ebp, L.aW, he.wIn', hl], ⟨⟨?_, ?_, ?_, ?_, ?_, h.nlt, ?_⟩, ?_⟩, ?_⟩
    · exact he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by mems [])
    · mems []; exact h.dO
    · mems []; exact h.nO
    · mems []; exact h.nl
    · mems []; exact h.z
    · exact h.data.of_eq (by mems []) (by mems [])
    · mems []; exact hm
    · mems []; rw [sub_beq32 h.nlt (by decide)]
  refine Pc.seq (Q := fun m₀ s => J0Mid Ctx St W SP K D n m₀ s) ?_
    (Pc.taint [.esi] (fun m₀ s h => initState_ok L h) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.esi, h₂.env.esi]) (by taint_decide))
  refine Pc.ite (decide (n = 12)) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
  · have h12 : n = 12 := by simpa using ht
    subst h12
    exact Pc.mono (j012_pc L) (fun _ _ h => h.1) fun _ _ h => h
  · have h12 : n ≠ 12 := by simpa using hf
    by_cases hlt : n < 2 ^ 32
    · exact Pc.mono (j0hash_pc L hlt h12) (fun _ _ h => h.1) fun _ _ h => h
    · exact Pc.vacuous fun _ _ h => hlt h.1.1.nlt

end

end VG.Proof.AesGcm.X86
