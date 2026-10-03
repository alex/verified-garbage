import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerified

/-!
# AES-GCM on x86-64: calling `vg_aes_gcm_encrypt_blocks` and `_decrypt_blocks`

Untrusted: everything here is checked by Lean. What a call of either needs,
from a state whose `rsp` points to `scratch` (pushed in a frame), and what
it leaves (`blk_call`), from its contract (with `WP.call`); and that two
calls with the same public arguments leak the same (`blk_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctr32 aesWith)

/-- What a call needs, from a state `s` with `scratch` at `rsp`: the key
context at `K` for `R` rounds, the counter block at `C`, `Y` at `Y`, `q`
blocks at `D` and working space at `S`. -/
structure BlkCall (s : State) (K C Y D S : Addr) (R q : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = Y
  r8 : s.gpr .r8 = D
  r9 : s.gpr .r9 = BitVec.ofNat 64 q
  arg : s.mem.readW (s.gpr .rsp) 64 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  w_k : K.toNat + 256 ≤ 2 ^ 64
  w_c : C.toNat + 16 ≤ 2 ^ 64
  w_y : Y.toNat + 16 ≤ 2 ^ 64
  w_d : D.toNat + q * 16 ≤ 2 ^ 64
  w_s : S.toNat + 2112 ≤ 2 ^ 64
  w_sp : (s.gpr .rsp - 8).toNat + 16 ≤ 2 ^ 64
  k_c : (⟨K, 256⟩ : Region).Disjoint ⟨C, 16⟩
  k_y : (⟨K, 256⟩ : Region).Disjoint ⟨Y, 16⟩
  k_d : (⟨K, 256⟩ : Region).Disjoint ⟨D, q * 16⟩
  k_s : (⟨K, 256⟩ : Region).Disjoint ⟨S, 2112⟩
  c_y : (⟨C, 16⟩ : Region).Disjoint ⟨Y, 16⟩
  c_d : (⟨C, 16⟩ : Region).Disjoint ⟨D, q * 16⟩
  c_s : (⟨C, 16⟩ : Region).Disjoint ⟨S, 2112⟩
  y_d : (⟨Y, 16⟩ : Region).Disjoint ⟨D, q * 16⟩
  y_s : (⟨Y, 16⟩ : Region).Disjoint ⟨S, 2112⟩
  d_s : (⟨D, q * 16⟩ : Region).Disjoint ⟨S, 2112⟩
  /-- The stack: `scratch` on it, and the return addresses of the call and of
  its calls, in the 24 bytes from `rsp - 16`. -/
  t_k : (⟨s.gpr .rsp - 16, 24⟩ : Region).Disjoint ⟨K, 256⟩
  t_c : (⟨s.gpr .rsp - 16, 24⟩ : Region).Disjoint ⟨C, 16⟩
  t_y : (⟨s.gpr .rsp - 16, 24⟩ : Region).Disjoint ⟨Y, 16⟩
  t_d : (⟨s.gpr .rsp - 16, 24⟩ : Region).Disjoint ⟨D, q * 16⟩
  t_s : (⟨s.gpr .rsp - 16, 24⟩ : Region).Disjoint ⟨S, 2112⟩
  reads : Covers ([⟨K, 256⟩, ⟨s.gpr .rsp, 8⟩] ++ [⟨C, 16⟩, ⟨Y, 16⟩, ⟨D, q * 16⟩, ⟨S, 2112⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨Y, 16⟩, ⟨D, q * 16⟩, ⟨S, 2112⟩] s.wr

theorem sep_of_disj {a b : Addr} {n k : Nat} (h : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) : Mem.Sep a n b k :=
  fun x h₁ h₂ => h x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)

namespace BlkCall

variable {s : State} {K C Y D S : Addr} {R q : Nat} (h : BlkCall s K C Y D S R q)
include h

/-- The regions the callee may read and write. -/
abbrev rd (s : State) (K : Addr) : List Region := [⟨K, 256⟩, ⟨s.gpr .rsp, 8⟩]
abbrev wr (C Y D S : Addr) (q : Nat) : List Region := [⟨C, 16⟩, ⟨Y, 16⟩, ⟨D, q * 16⟩, ⟨S, 2112⟩]

omit h in
theorem stackArgAddr_eq (rd wr : List Region) : stackArgAddr (s.callEntry.withRegions rd wr) 0 = s.gpr .rsp := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp]
  exact BitVec.sub_add_cancel _ _

omit h in
/-- The stack the callee uses is in the 24 bytes below `rsp + 8`. -/
theorem below_sub : Region.Sub (below (s.gpr .rsp - 8) 8) ⟨s.gpr .rsp - 16, 24⟩ := by
  have e : s.gpr .rsp - 8 - BitVec.ofNat 64 8 = s.gpr .rsp - 16 := by
    rw [← Offset.sub_add_eq]; rfl
  show Region.Sub ⟨s.gpr .rsp - 8 - BitVec.ofNat 64 8, 8⟩ _
  rw [e]; exact Region.sub_prefix (by decide)

omit h in
theorem ret_sub : Region.Sub ⟨s.gpr .rsp - 8, 8⟩ ⟨s.gpr .rsp - 16, 24⟩ := by
  have e : s.gpr .rsp - 8 = s.gpr .rsp - 16 + BitVec.ofNat 64 8 := by
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]
    exact Offset.sub_ofNat_eq _ (by decide)
  rw [e]; exact Offset.sub_base _ (by decide)

omit h in
theorem arg_sub : Region.Sub ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsp - 16, 24⟩ := by
  have e : s.gpr .rsp = s.gpr .rsp - 16 + BitVec.ofNat 64 16 := (BitVec.sub_add_cancel _ _).symm
  conv => lhs; rw [e]
  exact Offset.sub_base _ (by decide)

theorem pre : Proof.AesGcm.blocksPre (s.callEntry.withRegions (rd s K) (wr C Y D S q)) := by
  have hq : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.w_d; omega)
  have hR : (BitVec.ofNat 64 R).toNat = R := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases h.rounds with h | h | h <;> omega)
  have hsa := stackArgAddr_eq (s := s) (rd s K) (wr C Y D S q)
  have sep : Mem.Sep (s.gpr .rsp) (64 / 8) (s.gpr .rsp - 8) (64 / 8) := by
    have := Offset.sep_below (s.gpr .rsp) 8 (a := 0) (n := 8) (b := 8) (k := 8) (by decide) (by decide)
      (.inr (by decide)) (by decide) (by decide)
    simpa using this
  have harg : stackArg (s.callEntry.withRegions (rd s K) (wr C Y D S q)) 0 = S := by
    unfold stackArg; rw [hsa, State.withRegions_mem, State.callEntry_mem, Mem.readW_writeW_sep sep (by decide), h.arg]
  simp only [Proof.AesGcm.blocksPre, Proof.AesGcm.args, Proof.AesGcm.arg, Proof.AesGcm.ret, Proof.AesGcm.stk,
    Proof.AesGcm.rounds, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.callEntry_rsp,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hq, hR, hsa, harg, Nat.mul_one]
  have bs := below_sub (s := s)
  have rs := ret_sub (s := s)
  have as := arg_sub (s := s)
  refine ⟨trivial, trivial, h.k_c, h.k_y, h.k_d, h.k_s, h.c_y, h.c_d, h.c_s, (h.t_c.sub_left as).symm, h.y_d, h.y_s,
    (h.t_y.sub_left as).symm, h.d_s, (h.t_d.sub_left as).symm, (h.t_s.sub_left as).symm,
    h.t_c.sub_left rs, h.t_y.sub_left rs, h.t_d.sub_left rs, h.t_s.sub_left rs,
    h.t_k.sub_left bs, h.t_c.sub_left bs, h.t_y.sub_left bs, h.t_d.sub_left bs, h.t_s.sub_left bs,
    h.w_k, h.w_c, h.w_y, h.w_d, h.w_s, h.w_sp, h.rounds⟩

end BlkCall

theorem ctr_nosp_all (c : Proof.Aes.X86_64.Ctr32Impl) :
    c.callee.code.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]; intro i hi; simp [c.nosp i hi]

theorem gh_nosp_all (g : GhashImpl) : g.fn.code.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]; intro i hi; simp [g.nosp i hi]

theorem nosp_of_all {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c :=
  nosp_of (by rw [← Code.allInstrs_eq]; exact h)

section
variable (v : GcmImpl) (stitch : Bool)

theorem encryptBlocks_nosp : NoSp (Blocks.encrypt v.callees.ctr v.callees.gh stitch) := by
  have hc := ctr_nosp_all v.ctr
  have hg := gh_nosp_all v.gh
  refine nosp_of_all ?_
  cases stitch <;>
  simp only [Blocks.encrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.allInstrs,
    GcmImpl.callees, hc, hg, Bool.true_and, Bool.and_true, Bool.false_eq_true, ite_false,
    ite_true] <;> decide +kernel

theorem decryptBlocks_nosp : NoSp (Blocks.decrypt v.callees.ctr v.callees.gh stitch) := by
  have hc := ctr_nosp_all v.ctr
  have hg := gh_nosp_all v.gh
  refine nosp_of_all ?_
  cases stitch <;>
  simp only [Blocks.decrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.allInstrs,
    GcmImpl.callees, hc, hg, Bool.true_and, Bool.and_true, Bool.false_eq_true, ite_false,
    ite_true] <;> decide +kernel

theorem encryptBlocks_depth : (Blocks.encrypt v.callees.ctr v.callees.gh stitch).depth = 1 := by
  cases stitch <;> simp only [Blocks.encrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall,
    Code.depth, GcmImpl.callees, v.ctr.depth, v.gh.depth, Bool.false_eq_true, ite_false, ite_true] <;> decide

theorem decryptBlocks_depth : (Blocks.decrypt v.callees.ctr v.callees.gh stitch).depth = 1 := by
  cases stitch <;> simp only [Blocks.decrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall,
    Code.depth, GcmImpl.callees, v.ctr.depth, v.gh.depth, Bool.false_eq_true, ite_false, ite_true] <;> decide

end

/-- What a call leaves, besides its result. -/
structure BlkPost (s : State) (C Y D S : Addr) (q : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame (BlkCall.wr C Y D S q ++ [below (s.gpr .rsp) 16]) s.mem s'.mem

namespace BlkCall

variable {s : State} {K C Y D S : Addr} {R q : Nat} (h : BlkCall s K C Y D S R q)
include h

/-- The values the call reads, at its entry, after the return address is stored. -/
theorem entry_eqs :
    Spec.Aes.bytesAt s.callEntry.mem K (16 * (R + 1)) = Spec.Aes.bytesAt s.mem K (16 * (R + 1)) ∧
      blockAt s.callEntry.mem C = blockAt s.mem C ∧ blockAt s.callEntry.mem Y = blockAt s.mem Y ∧
      blocksAt s.callEntry.mem D q = blocksAt s.mem D q ∧
      blockAt s.callEntry.mem (K + 240) = blockAt s.mem (K + 240) := by
  have fE := callEntry_frame s
  have rs : Region.Sub (below (s.gpr .rsp) 8) ⟨s.gpr .rsp - 16, 24⟩ := ret_sub (s := s)
  have hRb : 16 * (R + 1) ≤ 256 := by rcases h.rounds with h | h | h <;> subst h <;> decide
  refine ⟨bytesAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((h.t_k.sub_left rs).sub_right (Region.sub_prefix hRb)).symm) (by have := h.w_k; omega),
    blockAt_frame fE (disj_below (h.t_c.sub_left rs)), blockAt_frame fE (disj_below (h.t_y.sub_left rs)),
    blocksAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [Nat.mul_comm]; exact (h.t_d.sub_left rs).symm) (by have := h.w_d; omega),
    blockAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((h.t_k.sub_left rs).sub_right (Offset.sub_base (d := 240) _ (by decide))).symm)⟩

end BlkCall

/-- A call of `vg_aes_gcm_encrypt_blocks`. -/
theorem blkE_call (v : GcmImpl) {s : State} {K C Y D S : Addr} {R q : Nat} (h : BlkCall s K C Y D S R q) :
    WP isa (.call v.callees.enc.name v.callees.enc.code) s fun s' => BlkPost s C Y D S q s' ∧
      blocksAt s'.mem D q = ctr32 (aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))) (blockAt s.mem C)
        (blocksAt s.mem D q) ∧
      blockAt s'.mem C = Nat.repeat Spec.Gcm.inc32 q (blockAt s.mem C) ∧
      blockAt s'.mem Y = ghashFrom (blockAt s.mem (K + 240)) (blockAt s.mem Y) (blocksAt s'.mem D q) := by
  have hq : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.w_d; omega)
  have hR : (BitVec.ofNat 64 R).toNat = R := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases h.rounds with h | h | h <;> omega)
  refine WP.call (k := Proof.AesGcm.encryptBlocksX86_64) (encryptBlocks_correct v v.stitch)
    (encryptBlocks_nosp v v.stitch) (by rw [encryptBlocks_depth]; decide)
    (rd := BlkCall.rd s K) (wr := BlkCall.wr C Y D S q) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [encryptBlocks_depth] at hf
  obtain ⟨eK, eC, eY, eD, eH⟩ := h.entry_eqs
  simp only [Proof.AesGcm.encryptBlocksX86_64, Spec.Gcm.ctxCiph, Spec.Gcm.ctxH, State.withRegions_gpr,
    State.withRegions_mem, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hq, hR, hm₂,
    eK, eC, eY, eD, eH] at hpost
  exact ⟨⟨hrd, hwr, hcs, hf⟩, hpost.1, hpost.2.1, by rw [hpost.1]; exact hpost.2.2⟩

/-- A call of `vg_aes_gcm_decrypt_blocks`. -/
theorem blkD_call (v : GcmImpl) {s : State} {K C Y D S : Addr} {R q : Nat} (h : BlkCall s K C Y D S R q) :
    WP isa (.call v.callees.dec.name v.callees.dec.code) s fun s' => BlkPost s C Y D S q s' ∧
      blocksAt s'.mem D q = ctr32 (aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))) (blockAt s.mem C)
        (blocksAt s.mem D q) ∧
      blockAt s'.mem C = Nat.repeat Spec.Gcm.inc32 q (blockAt s.mem C) ∧
      blockAt s'.mem Y = ghashFrom (blockAt s.mem (K + 240)) (blockAt s.mem Y) (blocksAt s.mem D q) := by
  have hq : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.w_d; omega)
  have hR : (BitVec.ofNat 64 R).toNat = R := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases h.rounds with h | h | h <;> omega)
  refine WP.call (k := Proof.AesGcm.decryptBlocksX86_64) (decryptBlocks_correct v v.stitch)
    (decryptBlocks_nosp v v.stitch) (by rw [decryptBlocks_depth]; decide)
    (rd := BlkCall.rd s K) (wr := BlkCall.wr C Y D S q) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [decryptBlocks_depth] at hf
  obtain ⟨eK, eC, eY, eD, eH⟩ := h.entry_eqs
  simp only [Proof.AesGcm.decryptBlocksX86_64, Spec.Gcm.ctxCiph, Spec.Gcm.ctxH, State.withRegions_gpr,
    State.withRegions_mem, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hq, hR, hm₂,
    eK, eC, eY, eD, eH] at hpost
  exact ⟨⟨hrd, hwr, hcs, hf⟩, hpost.1, hpost.2.1, hpost.2.2⟩

end VG.Proof.AesGcm.X86_64
