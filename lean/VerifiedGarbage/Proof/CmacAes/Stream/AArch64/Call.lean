import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Contract
import VerifiedGarbage.Proof.CmacAes.AArch64.Variant

/-!
# Streaming AES-CMAC on AArch64: the calls

A call of each function the streaming functions call (`vg_aes_expand_key`,
`vg_cmac_aes_subkeys`, `vg_cmac_aes_update` and `vg_cmac_aes_finalize`, for
any implementation of AES), from its contract (with `WP.call`): what it needs
(`…Args`), what it leaves (`…Post`, in terms of the memory before the call),
and that two calls with the same arguments leak the same (`…_rel`). A call
stores nothing in memory: the callees change only the buffers they are given.
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.CmacAes.AArch64 (updateAArch64 subkeysAArch64 finalizeAArch64 update_correct subkeys_correct
  finalize_correct update_ct subkeys_ct finalize_ct toNat_rounds callEntry_x0 callEntry_x1 callEntry_x2
  callEntry_x3 callEntry_x4 callEntry_x5)

theorem toNat_ofNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## No frames -/

theorem subkeys_noFrames (v : Ctr32Impl) : (Impl.CmacAes.AArch64.subkeys v.callee).noFrames = true := by
  simp [Impl.CmacAes.AArch64.subkeys, Code.noFrames, v.noFrames]

theorem finalize_noFrames (v : Ctr32Impl) : (Impl.CmacAes.AArch64.finalize v.callee).noFrames = true := by
  simp [Impl.CmacAes.AArch64.finalize, Impl.CmacAes.AArch64.finPre, Impl.CmacAes.AArch64.partialBlock,
    Impl.CmacAes.AArch64.copy, Code.noFrames, v.noFrames]

/-! ## `vg_cmac_aes_update` -/

/-- What a call of `vg_cmac_aes_update` needs: the key schedule `W`, the
chaining value `C`, `n` blocks at `D`, the working space `S` and the rounds
`R`. -/
structure UArgs (s : State) (W C D S : Addr) (R n : Nat) : Prop where
  x0 : s.gpr .x0 = W
  x1 : s.gpr .x1 = BitVec.ofNat 64 R
  x2 : s.gpr .x2 = C
  x3 : s.gpr .x3 = D
  x4 : s.gpr .x4 = BitVec.ofNat 64 n
  x5 : s.gpr .x5 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hn : 16 * n < 2 ^ 64
  wc : (⟨W, 240⟩ : Region).Disjoint ⟨C, 16⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  dc : (⟨D, 16 * n⟩ : Region).Disjoint ⟨C, 16⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 2176⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  wrapC : C.toNat + 16 ≤ 2 ^ 64
  wrapD : D.toNat + 16 * n ≤ 2 ^ 64
  wrapS : S.toNat + 2176 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩, ⟨D, 16 * n⟩] ++ [⟨C, 16⟩, ⟨S, 2176⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_update` leaves. -/
structure UPost (s : State) (W C D S : Addr) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem C 16 =
    Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1))))
      (Spec.Aes.bytesAt s.mem C 16) (Spec.Cmac.blocksAt s.mem D 16 n)

theorem UArgs.pre {s : State} {W C D S : Addr} {R n : Nat} (h : UArgs s W C D S R n) :
    updateAArch64.pre (s.callEntry.withRegions [⟨W, 240⟩, ⟨D, 16 * n⟩] [⟨C, 16⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega)
  simp only [updateAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, callEntry_x5,
    h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, hR, hN]
  exact ⟨trivial, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, h.wrapC, h.wrapD, h.wrapS, h.rounds⟩

theorem upd_call (v : Proof.CmacAes.AArch64.UpdateImpl) (nm : String) {s : State} {W C D S : Addr} {R n : Nat}
    (h : UArgs s W C D S R n) :
    WP isa (.call nm v.callee.code) s (UPost s W C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega)
  refine WP.call (k := updateAArch64) v.ok h.pre h.reads h.writes ?_ v.noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [updateAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, h.x0, h.x1, h.x2, h.x3, h.x4,
    hR, hN] at hpost
  exact hpost

theorem upd_rel (v : Proof.CmacAes.AArch64.UpdateImpl) (nm : String) {W C D S : Addr} {R n : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → UArgs s₁ W C D S R n ∧ UArgs s₂ W C D S R n ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call nm v.callee.code) fun _ _ => True := by
  refine RelCT.call v.ok v.ct [⟨W, 240⟩, ⟨D, 16 * n⟩] [⟨C, 16⟩, ⟨S, 2176⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [updateAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, callEntry_x5,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₁.x5, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, h₂.x5, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_cmac_aes_subkeys` -/

/-- What a call of `vg_cmac_aes_subkeys` needs: the key schedule `W`, the
subkeys `K`, the working space `S` and the rounds `R`. -/
structure SArgs (s : State) (W K S : Addr) (R : Nat) : Prop where
  x0 : s.gpr .x0 = W
  x1 : s.gpr .x1 = BitVec.ofNat 64 R
  x2 : s.gpr .x2 = K
  x3 : s.gpr .x3 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wk : (⟨W, 240⟩ : Region).Disjoint ⟨K, 32⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  ks : (⟨K, 32⟩ : Region).Disjoint ⟨S, 2176⟩
  wrapK : K.toNat + 32 ≤ 2 ^ 64
  wrapS : S.toNat + 2176 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨K, 32⟩, ⟨S, 2176⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨K, 32⟩, ⟨S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_subkeys` leaves. -/
structure SPost (s : State) (W K S : Addr) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨K, 32⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem K 32 =
    (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1)))) 16).1 ++
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1)))) 16).2

theorem SArgs.pre {s : State} {W K S : Addr} {R : Nat} (h : SArgs s W K S R) :
    subkeysAArch64.pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨K, 32⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [subkeysAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, h.x0, h.x1, h.x2, h.x3, hR]
  exact ⟨trivial, trivial, h.wk, h.ws, h.ks, h.wrapK, h.wrapS, h.rounds⟩

theorem sub_call (v : Ctr32Impl) (nm : String) {s : State} {W K S : Addr} {R : Nat}
    (h : SArgs s W K S R) :
    WP isa (.call nm (Impl.CmacAes.AArch64.subkeys v.callee)) s (SPost s W K S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := subkeysAArch64) (subkeys_correct v) h.pre h.reads h.writes ?_ (subkeys_noFrames v)
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [subkeysAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, h.x0, h.x1, h.x2, hR] at hpost
  exact hpost

theorem sub_rel (v : Ctr32Impl) (nm : String) {W K S : Addr} {R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → SArgs s₁ W K S R ∧ SArgs s₂ W K S R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call nm (Impl.CmacAes.AArch64.subkeys v.callee)) fun _ _ => True := by
  refine RelCT.call (subkeys_correct v) (subkeys_ct v) [⟨W, 240⟩] [⟨K, 32⟩, ⟨S, 2176⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [subkeysAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₂.x0, h₂.x1, h₂.x2, h₂.x3, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_cmac_aes_finalize` -/

/-- What a call of `vg_cmac_aes_finalize` needs: the key schedule and
subkeys `K`, the state `St`, the `L` last bytes at `P`, the working space
`S` and the rounds `R`. -/
structure FArgs (s : State) (K St P S : Addr) (L R : Nat) : Prop where
  x0 : s.gpr .x0 = K
  x1 : s.gpr .x1 = BitVec.ofNat 64 R
  x2 : s.gpr .x2 = St
  x3 : s.gpr .x3 = P
  x4 : s.gpr .x4 = BitVec.ofNat 64 L
  x5 : s.gpr .x5 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16
  kst : (⟨K, 272⟩ : Region).Disjoint ⟨St, 16⟩
  ks : (⟨K, 272⟩ : Region).Disjoint ⟨S, 2176⟩
  pst : (⟨P, L⟩ : Region).Disjoint ⟨St, 16⟩
  ps : (⟨P, L⟩ : Region).Disjoint ⟨S, 2176⟩
  sts : (⟨St, 16⟩ : Region).Disjoint ⟨S, 2176⟩
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
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : let ciph := Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (K + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < L) →
      Spec.Aes.bytesAt s.mem St 16 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem St 16 = Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem P L)

theorem FArgs.pre {s : State} {K St P S : Addr} {L R : Nat} (h : FArgs s K St P S L R) :
    finalizeAArch64.pre (s.callEntry.withRegions [⟨K, 272⟩, ⟨P, L⟩] [⟨St, 16⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega)
  simp only [finalizeAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, callEntry_x5,
    h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, hR, hL]
  exact ⟨trivial, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, h.wrapK, h.wrapSt, h.wrapP, h.wrapS,
    h.rounds, h.len⟩

theorem fin_call (v : Ctr32Impl) (nm : String) {s : State} {K St P S : Addr} {L R : Nat}
    (h : FArgs s K St P S L R) :
    WP isa (.call nm (Impl.CmacAes.AArch64.finalize v.callee)) s (FPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega)
  refine WP.call (k := finalizeAArch64) (finalize_correct v) h.pre h.reads h.writes ?_
    (finalize_noFrames v)
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [finalizeAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, h.x0, h.x1, h.x2, h.x3, h.x4,
    hR, hL] at hpost
  exact hpost

theorem fin_rel (v : Ctr32Impl) (nm : String) {K St Q S : Addr} {L R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → FArgs s₁ K St Q S L R ∧ FArgs s₂ K St Q S L R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call nm (Impl.CmacAes.AArch64.finalize v.callee)) fun _ _ => True := by
  refine RelCT.call (finalize_correct v) (finalize_ct v) [⟨K, 272⟩, ⟨Q, L⟩] [⟨St, 16⟩, ⟨S, 2176⟩]
    fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [finalizeAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, callEntry_x5,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₁.x5, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, h₂.x5, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_expand_key` -/

/-- What a call of `vg_aes_expand_key` needs: the key `Kp` of `KL` bytes,
the schedule `W` and the working space `S`. -/
structure EArgs (s : State) (Kp W S : Addr) (KL : Nat) : Prop where
  x0 : s.gpr .x0 = Kp
  x1 : s.gpr .x1 = BitVec.ofNat 64 KL
  x2 : s.gpr .x2 = W
  x3 : s.gpr .x3 = S
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32
  kw : (⟨Kp, KL⟩ : Region).Disjoint ⟨W, 240⟩
  ks : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 512⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 512⟩
  reads : Covers ([⟨Kp, KL⟩] ++ [⟨W, 240⟩, ⟨S, 512⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨W, 240⟩, ⟨S, 512⟩] s.wr

/-- What a call of `vg_aes_expand_key` leaves. -/
structure EPost (s : State) (Kp W S : Addr) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨W, 240⟩, ⟨S, 512⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem W (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
    Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem Kp KL)

theorem EArgs.pre {s : State} {Kp W S : Addr} {KL : Nat} (h : EArgs s Kp W S KL) :
    Proof.Aes.expandKeyAArch64.pre (s.callEntry.withRegions [⟨Kp, KL⟩] [⟨W, 240⟩, ⟨S, 512⟩]) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega)
  simp only [Proof.Aes.expandKeyAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, h.x0, h.x1, h.x2, h.x3, hK]
  exact ⟨trivial, trivial, h.kw, h.ks, h.ws, h.klen⟩

theorem ek_call (v : Ctr32Impl) {s : State} {Kp W S : Addr} {KL : Nat} (h : EArgs s Kp W S KL) :
    WP isa (.call v.expand.name v.expand.code) s (EPost s Kp W S KL) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega)
  refine WP.call (k := Proof.Aes.expandKeyAArch64) v.expandOk h.pre h.reads h.writes ?_ v.expandNoFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [Proof.Aes.expandKeyAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, h.x0, h.x1, h.x2, hK] at hpost
  exact hpost

theorem ek_rel (v : Ctr32Impl) {Kp W S : Addr} {KL : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → EArgs s₁ Kp W S KL ∧ EArgs s₂ Kp W S KL ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call v.expand.name v.expand.code) fun _ _ => True := by
  refine RelCT.call v.expandOk v.expandCt [⟨Kp, KL⟩] [⟨W, 240⟩, ⟨S, 512⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.expandKeyAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₂.x0, h₂.x1, h₂.x2, h₂.x3, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.CmacAes.Stream.AArch64
