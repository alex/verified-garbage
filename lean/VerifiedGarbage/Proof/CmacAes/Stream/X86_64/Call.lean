import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Contract
import VerifiedGarbage.Proof.Framework.OffsetBelow

/-!
# Streaming AES-CMAC on x86-64: the calls

A call of each function the streaming functions call (`vg_aes_expand_key`,
`vg_cmac_aes_subkeys`, `vg_cmac_aes_update` and `vg_cmac_aes_finalize`, for
any implementation of AES), from its contract (with `WP.call`): what it needs
(`…Args`), what it leaves (`…Post`, in terms of the memory before the call),
and that two calls with the same arguments leak the same (`…_rel`). Each
callee's stack is in the 16 bytes below the stack pointer (`below sp 16`): its
return address, and that of the call of `vg_aes_ctr32` it makes.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (updateX86_64 subkeysX86_64 finalizeX86_64 update_correct subkeys_correct
  finalize_correct update_ct subkeys_ct finalize_ct callEntry_frame bytesAt_frame toNat_rounds)

/-! ## The stack -/

theorem ret_sub (sp : Addr) : Region.Sub ⟨sp - 8, 8⟩ (below sp 16) :=
  Offset.sub_below sp (a := 8) (b := 16) (by decide) (by decide)

theorem stk_sub (sp : Addr) : Region.Sub (below (sp - 8) 8) (below sp 16) := by
  show Region.Sub ⟨sp - BitVec.ofNat 64 8 - BitVec.ofNat 64 8, 8⟩ _
  rw [Offset.sub_sub_ofNat]
  exact Offset.sub_below sp (a := 16) (b := 16) (by decide) (by decide)

theorem below8_sub (sp : Addr) : Region.Sub (below sp 8) (below sp 16) :=
  Offset.sub_below sp (a := 8) (b := 16) (by decide) (by decide)

/-- The bytes of a region the stack does not overlap, once a call has
stored its return address. -/
theorem callEntry_bytes (s : State) {p : Addr} {n : Nat} (h : (below (s.gpr .rsp) 16).Disjoint ⟨p, n⟩)
    (hn : n ≤ 2 ^ 64) : Spec.Aes.bytesAt s.callEntry.mem p n = Spec.Aes.bytesAt s.mem p n :=
  bytesAt_frame (callEntry_frame s) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.sub_left (below8_sub _)).symm) hn

theorem toNat_ofNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## No writes of `rsp` -/

theorem nosp_of_all {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c := by
  rw [Code.allInstrs_eq] at h
  exact fun i hi => by simpa using List.all_eq_true.mp h i hi

theorem all_of_nosp {c : Prog isa} (h : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  exact fun i hi => by simp [h i hi]

theorem update_nosp (v : Ctr32Impl) : NoSp (Impl.CmacAes.X86_64.update v.callee) :=
  nosp_of_all (by
    simp only [Impl.CmacAes.X86_64.update, Impl.CmacAes.X86_64.body, Code.allInstrs, all_of_nosp v.nosp]
    decide +kernel)

theorem update_depth (v : Ctr32Impl) : (Impl.CmacAes.X86_64.update v.callee).depth = 1 := by
  simp [Impl.CmacAes.X86_64.update, Impl.CmacAes.X86_64.body, Code.depth, v.depth]

/-! ## `vg_cmac_aes_update` -/

/-- What a call of `vg_cmac_aes_update` needs: the key schedule `W`, the
chaining value `C`, `n` blocks at `D`, the working space `S` and the rounds
`R`. -/
structure UArgs (s : State) (W C D S : Addr) (R n : Nat) : Prop where
  rdi : s.gpr .rdi = W
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = D
  r8 : s.gpr .r8 = BitVec.ofNat 64 n
  r9 : s.gpr .r9 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hn : 16 * n < 2 ^ 64
  wc : (⟨W, 240⟩ : Region).Disjoint ⟨C, 16⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  dc : (⟨D, 16 * n⟩ : Region).Disjoint ⟨C, 16⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 2176⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  stkW : (below (s.gpr .rsp) 16).Disjoint ⟨W, 240⟩
  stkD : (below (s.gpr .rsp) 16).Disjoint ⟨D, 16 * n⟩
  stkC : (below (s.gpr .rsp) 16).Disjoint ⟨C, 16⟩
  stkS : (below (s.gpr .rsp) 16).Disjoint ⟨S, 2176⟩
  wrapC : C.toNat + 16 ≤ 2 ^ 64
  wrapD : D.toNat + 16 * n ≤ 2 ^ 64
  wrapS : S.toNat + 2176 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩, ⟨D, 16 * n⟩] ++ [⟨C, 16⟩, ⟨S, 2176⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_update` leaves. -/
structure UPost (s : State) (W C D S : Addr) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨S, 2176⟩, below (s.gpr .rsp) 16] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem C 16 =
    Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1))))
      (Spec.Aes.bytesAt s.mem C 16) (Spec.Cmac.blocksAt s.mem D 16 n)

theorem UArgs.pre {s : State} {W C D S : Addr} {R n : Nat} (h : UArgs s W C D S R n) :
    updateX86_64.pre (s.callEntry.withRegions [⟨W, 240⟩, ⟨D, 16 * n⟩] [⟨C, 16⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega)
  simp only [updateX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hR, hN]
  exact ⟨trivial, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, h.stkC.sub_left (ret_sub _),
    h.stkS.sub_left (ret_sub _), h.stkW.sub_left (stk_sub _), h.stkD.sub_left (stk_sub _),
    h.stkC.sub_left (stk_sub _), h.stkS.sub_left (stk_sub _), h.wrapC, h.wrapD, h.wrapS, h.rounds⟩

theorem upd_call (v : Ctr32Impl) (nm : String) {s : State} {W C D S : Addr} {R n : Nat}
    (h : UArgs s W C D S R n) :
    WP isa (.call nm (Impl.CmacAes.X86_64.update v.callee)) s (UPost s W C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega)
  refine WP.call (k := updateX86_64) (update_correct v) (update_nosp v) (by rw [update_depth]; decide)
    h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [update_depth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  simp only [updateX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hN] at hpost
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  rw [← hm₂, hpost, X86_64.ciphAt, Proof.Cmac.Stream.blocksAt_eq, Proof.Cmac.Stream.blocksAt_eq,
    callEntry_bytes s (h.stkW.sub_right (Region.sub_prefix hRb)) (by omega),
    callEntry_bytes s h.stkC (by decide), callEntry_bytes s h.stkD (by have := h.hn; omega)]

theorem upd_rel (v : Ctr32Impl) (nm : String) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W C D S : Addr, ∃ R n : Nat,
      UArgs s₁ W C D S R n ∧ UArgs s₂ W C D S R n ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call nm (Impl.CmacAes.X86_64.update v.callee)) fun _ _ => True := by
  refine RelCT.callEx (update_correct v) (update_ct v) fun s₁ s₂ hp => ?_
  obtain ⟨W, C, D, S, R, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [updateX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_cmac_aes_subkeys` -/

theorem subkeys_nosp (v : Ctr32Impl) : NoSp (Impl.CmacAes.X86_64.subkeys v.callee) :=
  nosp_of_all (by
    simp only [Impl.CmacAes.X86_64.subkeys, Code.allInstrs, all_of_nosp v.nosp]
    decide +kernel)

theorem subkeys_depth (v : Ctr32Impl) : (Impl.CmacAes.X86_64.subkeys v.callee).depth = 1 := by
  simp [Impl.CmacAes.X86_64.subkeys, Code.depth, v.depth]

/-- What a call of `vg_cmac_aes_subkeys` needs: the key schedule `W`, the
subkeys `K`, the working space `S` and the rounds `R`. -/
structure SArgs (s : State) (W K S : Addr) (R : Nat) : Prop where
  rdi : s.gpr .rdi = W
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = K
  rcx : s.gpr .rcx = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wk : (⟨W, 240⟩ : Region).Disjoint ⟨K, 32⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  ks : (⟨K, 32⟩ : Region).Disjoint ⟨S, 2176⟩
  stkW : (below (s.gpr .rsp) 16).Disjoint ⟨W, 240⟩
  stkK : (below (s.gpr .rsp) 16).Disjoint ⟨K, 32⟩
  stkS : (below (s.gpr .rsp) 16).Disjoint ⟨S, 2176⟩
  wrapK : K.toNat + 32 ≤ 2 ^ 64
  wrapS : S.toNat + 2176 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨K, 32⟩, ⟨S, 2176⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨K, 32⟩, ⟨S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_subkeys` leaves. -/
structure SPost (s : State) (W K S : Addr) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨K, 32⟩, ⟨S, 2176⟩, below (s.gpr .rsp) 16] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem K 32 =
    (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1)))) 16).1 ++
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1)))) 16).2

theorem SArgs.pre {s : State} {W K S : Addr} {R : Nat} (h : SArgs s W K S R) :
    subkeysX86_64.pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨K, 32⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [subkeysX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, hR]
  exact ⟨trivial, trivial, h.wk, h.ws, h.ks, h.stkK.sub_left (ret_sub _),
    h.stkS.sub_left (ret_sub _), h.stkW.sub_left (stk_sub _), h.stkK.sub_left (stk_sub _),
    h.stkS.sub_left (stk_sub _), h.wrapK, h.wrapS, h.rounds⟩

theorem sub_call (v : Ctr32Impl) (nm : String) {s : State} {W K S : Addr} {R : Nat}
    (h : SArgs s W K S R) :
    WP isa (.call nm (Impl.CmacAes.X86_64.subkeys v.callee)) s (SPost s W K S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := subkeysX86_64) (subkeys_correct v) (subkeys_nosp v) (by rw [subkeys_depth]; decide)
    h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [subkeys_depth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  simp only [subkeysX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx, hR] at hpost
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  rw [← hm₂, hpost, X86_64.ciphAt, callEntry_bytes s (h.stkW.sub_right (Region.sub_prefix hRb)) (by omega)]

theorem sub_rel (v : Ctr32Impl) (nm : String) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W K S : Addr, ∃ R : Nat,
      SArgs s₁ W K S R ∧ SArgs s₂ W K S R ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call nm (Impl.CmacAes.X86_64.subkeys v.callee)) fun _ _ => True := by
  refine RelCT.callEx (subkeys_correct v) (subkeys_ct v) fun s₁ s₂ hp => ?_
  obtain ⟨W, K, S, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [subkeysX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_cmac_aes_finalize` -/

theorem finalize_nosp (v : Ctr32Impl) : NoSp (Impl.CmacAes.X86_64.finalize v.callee) :=
  nosp_of_all (by
    simp only [Impl.CmacAes.X86_64.finalize, Impl.CmacAes.X86_64.finPre, Impl.CmacAes.X86_64.partialBlock,
      Impl.CmacAes.X86_64.copy, Code.allInstrs, all_of_nosp v.nosp]
    decide +kernel)

theorem finalize_depth (v : Ctr32Impl) : (Impl.CmacAes.X86_64.finalize v.callee).depth = 1 := by
  simp [Impl.CmacAes.X86_64.finalize, Impl.CmacAes.X86_64.finPre, Impl.CmacAes.X86_64.partialBlock,
    Impl.CmacAes.X86_64.copy, Code.depth, v.depth]

/-- What a call of `vg_cmac_aes_finalize` needs: the key schedule and
subkeys `K`, the state `St`, the `L` last bytes at `P`, the working space
`S` and the rounds `R`. -/
structure FArgs (s : State) (K St P S : Addr) (L R : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = St
  rcx : s.gpr .rcx = P
  r8 : s.gpr .r8 = BitVec.ofNat 64 L
  r9 : s.gpr .r9 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16
  kst : (⟨K, 272⟩ : Region).Disjoint ⟨St, 16⟩
  ks : (⟨K, 272⟩ : Region).Disjoint ⟨S, 2176⟩
  pst : (⟨P, L⟩ : Region).Disjoint ⟨St, 16⟩
  ps : (⟨P, L⟩ : Region).Disjoint ⟨S, 2176⟩
  sts : (⟨St, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  stkK : (below (s.gpr .rsp) 16).Disjoint ⟨K, 272⟩
  stkP : (below (s.gpr .rsp) 16).Disjoint ⟨P, L⟩
  stkSt : (below (s.gpr .rsp) 16).Disjoint ⟨St, 16⟩
  stkS : (below (s.gpr .rsp) 16).Disjoint ⟨S, 2176⟩
  wrapK : K.toNat + 272 ≤ 2 ^ 64
  wrapSt : St.toNat + 16 ≤ 2 ^ 64
  wrapP : P.toNat + L ≤ 2 ^ 64
  wrapS : S.toNat + 2176 ≤ 2 ^ 64
  reads : Covers ([⟨K, 272⟩, ⟨P, L⟩] ++ [⟨St, 16⟩, ⟨S, 2176⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨St, 16⟩, ⟨S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_finalize` leaves. -/
structure FPost (s : State) (K St P S : Addr) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨St, 16⟩, ⟨S, 2176⟩, below (s.gpr .rsp) 16] s.mem s'.mem
  out : let ciph := Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (K + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < L) →
      Spec.Aes.bytesAt s.mem St 16 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem St 16 = Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem P L)

theorem FArgs.pre {s : State} {K St P S : Addr} {L R : Nat} (h : FArgs s K St P S L R) :
    finalizeX86_64.pre (s.callEntry.withRegions [⟨K, 272⟩, ⟨P, L⟩] [⟨St, 16⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega)
  simp only [finalizeX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hR, hL]
  exact ⟨trivial, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, h.stkSt.sub_left (ret_sub _),
    h.stkS.sub_left (ret_sub _), h.stkK.sub_left (stk_sub _), h.stkP.sub_left (stk_sub _),
    h.stkSt.sub_left (stk_sub _), h.stkS.sub_left (stk_sub _), h.wrapK, h.wrapSt, h.wrapP, h.wrapS,
    h.rounds, h.len⟩

theorem fin_call (v : Ctr32Impl) (nm : String) {s : State} {K St P S : Addr} {L R : Nat}
    (h : FArgs s K St P S L R) :
    WP isa (.call nm (Impl.CmacAes.X86_64.finalize v.callee)) s (FPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega)
  refine WP.call (k := finalizeX86_64) (finalize_correct v) (finalize_nosp v)
    (by rw [finalize_depth]; decide) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [finalize_depth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  simp only [finalizeX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hL] at hpost
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  have eK : Spec.Aes.bytesAt s.callEntry.mem K (16 * (R + 1)) = Spec.Aes.bytesAt s.mem K (16 * (R + 1)) :=
    callEntry_bytes s (h.stkK.sub_right (Region.sub_prefix (by omega))) (by omega)
  have eK2 : Spec.Aes.bytesAt s.callEntry.mem (K + 240) 32 = Spec.Aes.bytesAt s.mem (K + 240) 32 :=
    callEntry_bytes s (h.stkK.sub_right (Offset.sub_base K (d := 240) (n := 32) (by decide))) (by decide)
  have eSt := callEntry_bytes s h.stkSt (by decide)
  have eP := callEntry_bytes s h.stkP (by omega)
  intro _ _ hk msg hm hne hst
  simp only [X86_64.ciphAt, eK, eK2, eSt, eP] at hpost
  rw [← hm₂]
  exact hpost hk msg hm hne hst

theorem fin_rel (v : Ctr32Impl) (nm : String) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K St Q S : Addr, ∃ L R : Nat,
      FArgs s₁ K St Q S L R ∧ FArgs s₂ K St Q S L R ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call nm (Impl.CmacAes.X86_64.finalize v.callee)) fun _ _ => True := by
  refine RelCT.callEx (finalize_correct v) (finalize_ct v) fun s₁ s₂ hp => ?_
  obtain ⟨K, St, Q, S, L, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [finalizeX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_expand_key` -/

/-- What a call of `vg_aes_expand_key` needs: the key `Kp` of `KL` bytes,
the schedule `W` and the working space `S`. -/
structure EArgs (s : State) (Kp W S : Addr) (KL : Nat) : Prop where
  rdi : s.gpr .rdi = Kp
  rsi : s.gpr .rsi = BitVec.ofNat 64 KL
  rdx : s.gpr .rdx = W
  rcx : s.gpr .rcx = S
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32
  kw : (⟨Kp, KL⟩ : Region).Disjoint ⟨W, 240⟩
  ks : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 512⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 512⟩
  stkK : (below (s.gpr .rsp) 16).Disjoint ⟨Kp, KL⟩
  stkW : (below (s.gpr .rsp) 16).Disjoint ⟨W, 240⟩
  stkS : (below (s.gpr .rsp) 16).Disjoint ⟨S, 512⟩
  reads : Covers ([⟨Kp, KL⟩] ++ [⟨W, 240⟩, ⟨S, 512⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨W, 240⟩, ⟨S, 512⟩] s.wr

/-- What a call of `vg_aes_expand_key` leaves. -/
structure EPost (s : State) (Kp W S : Addr) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨W, 240⟩, ⟨S, 512⟩, below (s.gpr .rsp) 16] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem W (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
    Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem Kp KL)

theorem EArgs.pre {s : State} {Kp W S : Addr} {KL : Nat} (h : EArgs s Kp W S KL) :
    Proof.Aes.expandKeyX86_64.pre (s.callEntry.withRegions [⟨Kp, KL⟩] [⟨W, 240⟩, ⟨S, 512⟩]) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega)
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, hK]
  exact ⟨trivial, trivial, h.kw, h.ks, h.ws, h.stkW.sub_left (ret_sub _),
    h.stkS.sub_left (ret_sub _), h.klen⟩

theorem ek_call (v : Ctr32Impl) {s : State} {Kp W S : Addr} {KL : Nat} (h : EArgs s Kp W S KL) :
    WP isa (.call v.expand.name v.expand.code) s (EPost s Kp W S KL) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega)
  refine WP.call (k := Proof.Aes.expandKeyX86_64) v.expandOk v.expandNosp
    (by rw [v.expandDepth]; decide) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [v.expandDepth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using Frame.below_mono hf (b := 16) (by decide) (by decide), ?_⟩
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx, hK] at hpost
  rw [← hm₂, hpost, callEntry_bytes s h.stkK (by rcases h.klen with h | h | h <;> omega)]

theorem ek_rel (v : Ctr32Impl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ Kp W S : Addr, ∃ KL : Nat,
      EArgs s₁ Kp W S KL ∧ EArgs s₂ Kp W S KL ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call v.expand.name v.expand.code) fun _ _ => True := by
  refine RelCT.callEx v.expandOk v.expandCt fun s₁ s₂ hp => ?_
  obtain ⟨Kp, W, S, KL, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.CmacAes.Stream.X86_64
