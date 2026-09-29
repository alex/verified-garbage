import VerifiedGarbage.Proof.Pbkdf2.X86_64.Derive.Common
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Init
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.UpdateCT
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.FinalizeCT
import VerifiedGarbage.Proof.Hmac.X86_64.Init
import VerifiedGarbage.Proof.Hmac.X86_64.Finalize

/-!
# PBKDF2-HMAC-SHA-256 on x86-64: the calls

Untrusted: everything here is checked by Lean. Each call of a verified
function, from its proof of `Verified` (with `WP.call`): what it needs of the
state it is called from (`…_pre`), and what holds when it returns
(`…_call`). The stack the calls use is within the 24 bytes below the return
address.
-/

namespace VG.Proof.Pbkdf2.X86_64.Derive

open VG VG.X86_64
open VG.Spec.Sha256 (bytesAt Repr)
open VG.Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey sha256)
open VG.Impl.Sha256.X86_64.Stream (Callee)

/-! ## The callees' registers and stack -/

theorem nosp_of {c : Prog isa} (h : ((instrs c).all fun i => !Taint.clobbers i .rsp) = true) : NoSp c :=
  fun i hi => by simpa using List.all_eq_true.mp h i hi

theorem sinit_nosp : NoSp Impl.Sha256.X86_64.Stream.init := nosp_of (by rw [← Code.allInstrs_eq]; decide +kernel)
theorem sinit_depth : Impl.Sha256.X86_64.Stream.init.depth = 0 := by decide +kernel

/-- What the calls need of the compression function: that it is correct and
constant time (`Callee.Ok`), and never loads MXCSR. -/
structure Vf (f : Callee) : Prop where
  ok : f.Ok
  hm : f.code.allInstrs (fun i => !loadsMxcsr i) = true

section
variable {f : Callee} (hv : Vf f)
include hv

theorem Vf.rsp : (f.code.allInstrs fun i => !Taint.clobbers i .rsp) = true := by
  rw [Code.allInstrs_eq]; exact List.all_eq_true.mpr fun i hi => by simp [hv.ok.nosp i hi]

theorem Vf.update_nosp : NoSp (Impl.Sha256.X86_64.Stream.update f) := by
  refine nosp_of ?_
  rw [← Code.allInstrs_eq]
  simp only [Impl.Sha256.X86_64.Stream.update, Impl.Sha256.X86_64.Stream.updateBody,
    Impl.Sha256.X86_64.Stream.updateTail, Impl.Sha256.X86_64.Stream.compressAt, Code.allInstrs, hv.rsp,
    Bool.true_and]
  decide +kernel
theorem Vf.sfin_nosp : NoSp (Impl.Sha256.X86_64.Stream.finalize f) := by
  refine nosp_of ?_
  rw [← Code.allInstrs_eq]
  simp only [Impl.Sha256.X86_64.Stream.finalize, Impl.Sha256.X86_64.Stream.finalizeBody,
    Impl.Sha256.X86_64.Stream.compressAt, Code.allInstrs, hv.rsp, Bool.true_and]
  decide +kernel
theorem Vf.hinit_nosp : NoSp (Impl.Hmac.X86_64.init f) := by
  refine nosp_of ?_
  rw [← Code.allInstrs_eq]
  simp only [Impl.Hmac.X86_64.init, Impl.Sha256.X86_64.Stream.compressAt, Code.allInstrs, hv.rsp,
    Bool.true_and, Bool.and_true]
  decide +kernel
theorem Vf.hfin_nosp (name : String) : NoSp (Impl.Hmac.X86_64.finalize f name) := by
  refine nosp_of ?_
  rw [← Code.allInstrs_eq]
  simp only [Impl.Hmac.X86_64.finalize, Impl.Hmac.X86_64.sha256Finalize, Impl.Sha256.X86_64.Stream.finalize,
    Impl.Sha256.X86_64.Stream.finalizeBody, Impl.Sha256.X86_64.Stream.compressAt, Code.allInstrs, hv.rsp,
    Bool.true_and, Bool.and_true]
  decide +kernel
theorem Vf.iter_nosp : NoSp (Impl.Pbkdf2.X86_64.iterate f) := by
  refine nosp_of ?_
  rw [← Code.allInstrs_eq]
  simp only [Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body, Impl.Pbkdf2.X86_64.compressBlock,
    Code.allInstrs, hv.rsp, Bool.and_true]
  decide +kernel

theorem Vf.update_depth : (Impl.Sha256.X86_64.Stream.update f).depth = 1 := by
  simp only [Impl.Sha256.X86_64.Stream.update, Impl.Sha256.X86_64.Stream.updateBody,
    Impl.Sha256.X86_64.Stream.updateTail, Impl.Sha256.X86_64.Stream.compressAt, Code.depth, hv.ok.depth]
  decide +kernel
theorem Vf.sfin_depth : (Impl.Sha256.X86_64.Stream.finalize f).depth = 1 := by
  simp only [Impl.Sha256.X86_64.Stream.finalize, Impl.Sha256.X86_64.Stream.finalizeBody,
    Impl.Sha256.X86_64.Stream.compressAt, Code.depth, hv.ok.depth]
  decide +kernel
theorem Vf.hinit_depth : (Impl.Hmac.X86_64.init f).depth = 1 := by
  simp only [Impl.Hmac.X86_64.init, Impl.Sha256.X86_64.Stream.compressAt, Code.depth, hv.ok.depth]
  decide +kernel
theorem Vf.hfin_depth (name : String) : (Impl.Hmac.X86_64.finalize f name).depth = 2 := by
  simp only [Impl.Hmac.X86_64.finalize, Impl.Hmac.X86_64.sha256Finalize, Impl.Sha256.X86_64.Stream.finalize,
    Impl.Sha256.X86_64.Stream.finalizeBody, Impl.Sha256.X86_64.Stream.compressAt, Code.depth, hv.ok.depth]
  decide +kernel
theorem Vf.iter_depth : (Impl.Pbkdf2.X86_64.iterate f).depth = 1 := by
  simp only [Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body, Impl.Pbkdf2.X86_64.compressBlock,
    Code.depth, hv.ok.depth]
  decide +kernel

theorem Vf.update_hm : (Impl.Sha256.X86_64.Stream.update f).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [Impl.Sha256.X86_64.Stream.update, Impl.Sha256.X86_64.Stream.updateBody,
    Impl.Sha256.X86_64.Stream.updateTail, Impl.Sha256.X86_64.Stream.compressAt, Code.allInstrs, hv.hm,
    Bool.true_and]
  decide +kernel
theorem Vf.update_v : Verified X86_64.target (Impl.Sha256.X86_64.Stream.update f) Proof.Sha256.updateX86_64 :=
  Proof.Sha256.X86_64.Stream.Update.verified_of hv.ok hv.update_hm
    (Proof.Sha256.X86_64.Stream.Update.constantTime hv.ok)
theorem Vf.sfin_hm : (Impl.Sha256.X86_64.Stream.finalize f).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [Impl.Sha256.X86_64.Stream.finalize, Impl.Sha256.X86_64.Stream.finalizeBody,
    Impl.Sha256.X86_64.Stream.compressAt, Code.allInstrs, hv.hm, Bool.true_and]
  decide +kernel
theorem Vf.sfin_v : Verified X86_64.target (Impl.Sha256.X86_64.Stream.finalize f) Proof.Sha256.finalizeX86_64 :=
  Proof.Sha256.X86_64.Stream.Finalize.verified_of hv.ok hv.sfin_hm
    (Proof.Sha256.X86_64.Stream.Finalize.constantTime hv.ok)
theorem Vf.hinit_hm : (Impl.Hmac.X86_64.init f).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [Impl.Hmac.X86_64.init, Impl.Sha256.X86_64.Stream.compressAt, Code.allInstrs, hv.hm,
    Bool.true_and, Bool.and_true]
  decide +kernel
theorem Vf.hinit_v : Verified X86_64.target (Impl.Hmac.X86_64.init f) Proof.Hmac.initSha256X86_64 :=
  Proof.Hmac.X86_64.Init.verified_of hv.ok hv.hinit_hm
theorem Vf.hfin_hm (name : String) :
    (Impl.Hmac.X86_64.finalize f name).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [Impl.Hmac.X86_64.finalize, Impl.Hmac.X86_64.sha256Finalize, Code.allInstrs, hv.sfin_hm,
    Bool.and_true]
  decide +kernel
theorem Vf.hfin_v (name : String) :
    Verified X86_64.target (Impl.Hmac.X86_64.finalize f name) Proof.Hmac.finalizeSha256X86_64 :=
  Proof.Hmac.X86_64.Finalize.verified_of hv.ok hv.sfin_hm name
theorem Vf.iter_hm : (Impl.Pbkdf2.X86_64.iterate f).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body, Impl.Pbkdf2.X86_64.compressBlock,
    Code.allInstrs, hv.hm, Bool.and_true]
  decide +kernel
theorem Vf.iter_v : Verified X86_64.target (Impl.Pbkdf2.X86_64.iterate f) Proof.Pbkdf2.iterateSha256X86_64 :=
  Proof.Pbkdf2.X86_64.Iterate.verified_of hv.ok hv.iter_hm (Proof.Pbkdf2.X86_64.Iterate.constantTime hv.ok)

end

theorem ce_gpr (s : State) {r : Reg} (h : r ≠ .rsp) : s.callEntry.gpr r = s.gpr r := State.callEntry_gpr _ h

/-- The return address and the stack of a callee called from `sp`. -/
theorem ret_sub (sp : Addr) : Region.Sub ⟨sp - 8, 8⟩ (below sp 24) := by
  intro x hx; simp only [Region.Contains] at *; bv_omega
theorem stk8_sub (sp : Addr) : Region.Sub ⟨sp - 8 - 8, 8⟩ (below sp 24) := by
  intro x hx; simp only [Region.Contains] at *; bv_omega
theorem stk16_sub (sp : Addr) : Region.Sub ⟨sp - 8 - 16, 16⟩ (below sp 24) := by
  intro x hx; simp only [Region.Contains] at *; bv_omega

/-- The frame of a call, with the stack it uses widened to 24 bytes. -/
theorem frame24 {wr : List Region} {sp : Addr} {d : Nat} {m m' : Mem} (h : Frame (wr ++ [below sp (8 * (d + 1))]) m m')
    (hd : d ≤ 2) : Frame (wr ++ [below sp 24]) m m' :=
  Frame.below_mono h (by omega) (by omega)

theorem ce_frame (s : State) : Frame [below (s.gpr .rsp) 24] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega))

theorem ce_bytes (s : State) {p : Addr} {n : Nat} (hd : (below (s.gpr .rsp) 24).Disjoint ⟨p, n⟩)
    (hn : n ≤ 2 ^ 64) : bytesAt s.callEntry.mem p n = bytesAt s.mem p n :=
  frame_bytesAt (ce_frame s) (by simpa using hd.symm) hn

theorem ce_repr (s : State) {p : Addr} (hd : (below (s.gpr .rsp) 24).Disjoint ⟨p, 96⟩) {m : List Byte}
    (h : Repr s.mem p m) : Repr s.callEntry.mem p m :=
  repr_frame (ce_frame s) (by simpa using hd.symm) h

/-! ## `vg_sha256_init` -/

theorem sinit_pre {s : State} {St : Addr} (hrdi : s.gpr .rdi = St)
    (hk : (below (s.gpr .rsp) 24).Disjoint ⟨St, 96⟩) :
    Proof.Sha256.initX86_64.pre (s.callEntry.withRegions [] [⟨St, 96⟩]) := by
  simp only [Proof.Sha256.initX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, ce_gpr s (by decide : Reg.rdi ≠ .rsp), hrdi]
  exact ⟨trivial, trivial, hk.sub_left (ret_sub _)⟩

theorem sinit_call {s : State} {St : Addr} (hrdi : s.gpr .rdi = St)
    (hk : (below (s.gpr .rsp) 24).Disjoint ⟨St, 96⟩)
    (hc : Covers ([] ++ [⟨St, 96⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨St, 96⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨St, 96⟩, below (s.gpr .rsp) 24] s.mem s'.mem → Repr s'.mem St [] → Q s') :
    WP isa (.call "vg_sha256_init" Impl.Sha256.X86_64.Stream.init) s Q := by
  refine WP.call (k := Proof.Sha256.initX86_64) Proof.Sha256.X86_64.Stream.init_verified.1 sinit_nosp
    (by rw [sinit_depth]; decide) (sinit_pre hrdi hk) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [sinit_depth] at hf
  refine hQ s' hrd hwr hcs (frame24 hf (by omega)) ?_
  simp only [Proof.Sha256.initX86_64, State.withRegions_gpr, ce_gpr s (by decide : Reg.rdi ≠ .rsp), hrdi,
    hm₂] at hpost
  exact hpost

/-! ## `vg_sha256_update` -/

theorem update_pre {s : State} {St D Sc : Addr} {n : Nat} (hrdi : s.gpr .rdi = St) (hrdx : s.gpr .rdx = D)
    (hrcx : (s.gpr .rcx).toNat = n) (hr8 : s.gpr .r8 = Sc)
    (d₁ : Region.Disjoint ⟨St, 96⟩ ⟨Sc, 160⟩) (d₂ : Region.Disjoint ⟨D, n⟩ ⟨St, 96⟩)
    (d₃ : Region.Disjoint ⟨D, n⟩ ⟨Sc, 160⟩) (kS : (below (s.gpr .rsp) 24).Disjoint ⟨St, 96⟩)
    (kD : (below (s.gpr .rsp) 24).Disjoint ⟨D, n⟩) (kC : (below (s.gpr .rsp) 24).Disjoint ⟨Sc, 160⟩) :
    Proof.Sha256.updateX86_64.pre (s.callEntry.withRegions [⟨D, n⟩] [⟨St, 96⟩, ⟨Sc, 160⟩]) := by
  simp only [Proof.Sha256.updateX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, ce_gpr s (by decide : Reg.rdi ≠ .rsp), ce_gpr s (by decide : Reg.rdx ≠ .rsp),
    ce_gpr s (by decide : Reg.rcx ≠ .rsp), ce_gpr s (by decide : Reg.r8 ≠ .rsp), hrdi, hrdx, hrcx, hr8]
  exact ⟨trivial, trivial, d₁, d₂, d₃, kS.sub_left (ret_sub _), kC.sub_left (ret_sub _),
    kS.sub_left (stk8_sub _), kD.sub_left (stk8_sub _), kC.sub_left (stk8_sub _)⟩

theorem update_call {f : Callee} (hv : Vf f) {nm : String} {s : State} {St D Sc : Addr} {n : Nat} (hrdi : s.gpr .rdi = St) (hrdx : s.gpr .rdx = D)
    (hrcx : (s.gpr .rcx).toNat = n) (hr8 : s.gpr .r8 = Sc)
    (d₁ : Region.Disjoint ⟨St, 96⟩ ⟨Sc, 160⟩) (d₂ : Region.Disjoint ⟨D, n⟩ ⟨St, 96⟩)
    (d₃ : Region.Disjoint ⟨D, n⟩ ⟨Sc, 160⟩) (kS : (below (s.gpr .rsp) 24).Disjoint ⟨St, 96⟩)
    (kD : (below (s.gpr .rsp) 24).Disjoint ⟨D, n⟩) (kC : (below (s.gpr .rsp) 24).Disjoint ⟨Sc, 160⟩)
    (hc : Covers ([⟨D, n⟩] ++ [⟨St, 96⟩, ⟨Sc, 160⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨St, 96⟩, ⟨Sc, 160⟩] s.wr)
    {m : List Byte} (hm : Repr s.mem St m) (hrsi : s.gpr .rsi = BitVec.ofNat 64 m.length) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨St, 96⟩, ⟨Sc, 160⟩, below (s.gpr .rsp) 24] s.mem s'.mem →
      Repr s'.mem St (m ++ bytesAt s.mem D n) → Q s') :
    WP isa (.call nm (Impl.Sha256.X86_64.Stream.update f)) s Q := by
  refine WP.call (k := Proof.Sha256.updateX86_64) hv.update_v.1
    hv.update_nosp (by rw [hv.update_depth]; decide) (update_pre hrdi hrdx hrcx hr8 d₁ d₂ d₃ kS kD kC) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [hv.update_depth] at hf
  refine hQ s' hrd hwr hcs (frame24 hf (by omega)) ?_
  simp only [Proof.Sha256.updateX86_64, State.withRegions_gpr, State.withRegions_mem,
    ce_gpr s (by decide : Reg.rdi ≠ .rsp), ce_gpr s (by decide : Reg.rsi ≠ .rsp),
    ce_gpr s (by decide : Reg.rdx ≠ .rsp), ce_gpr s (by decide : Reg.rcx ≠ .rsp), hrdi, hrdx, hrcx,
    hm₂] at hpost
  have h := hpost m (ce_repr s kS hm) hrsi
  rwa [ce_bytes s kD (by have := (s.gpr .rcx).isLt; omega)] at h

/-! ## `vg_sha256_finalize` -/

theorem sfin_pre {s : State} {St O Sc : Addr} (hrdi : s.gpr .rdi = St) (hrdx : s.gpr .rdx = O)
    (hrcx : s.gpr .rcx = Sc)
    (d₁ : Region.Disjoint ⟨St, 96⟩ ⟨O, 32⟩) (d₂ : Region.Disjoint ⟨St, 96⟩ ⟨Sc, 160⟩)
    (d₃ : Region.Disjoint ⟨O, 32⟩ ⟨Sc, 160⟩) (kS : (below (s.gpr .rsp) 24).Disjoint ⟨St, 96⟩)
    (kO : (below (s.gpr .rsp) 24).Disjoint ⟨O, 32⟩) (kC : (below (s.gpr .rsp) 24).Disjoint ⟨Sc, 160⟩) :
    Proof.Sha256.finalizeX86_64.pre (s.callEntry.withRegions [] [⟨St, 96⟩, ⟨O, 32⟩, ⟨Sc, 160⟩]) := by
  simp only [Proof.Sha256.finalizeX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, ce_gpr s (by decide : Reg.rdi ≠ .rsp), ce_gpr s (by decide : Reg.rdx ≠ .rsp),
    ce_gpr s (by decide : Reg.rcx ≠ .rsp), hrdi, hrdx, hrcx]
  exact ⟨trivial, trivial, d₁, d₂, d₃, kS.sub_left (ret_sub _), kO.sub_left (ret_sub _),
    kC.sub_left (ret_sub _), kS.sub_left (stk8_sub _), kO.sub_left (stk8_sub _), kC.sub_left (stk8_sub _)⟩

theorem sfin_call {f : Callee} (hv : Vf f) {nm : String} {s : State} {St O Sc : Addr} (hrdi : s.gpr .rdi = St) (hrdx : s.gpr .rdx = O)
    (hrcx : s.gpr .rcx = Sc)
    (d₁ : Region.Disjoint ⟨St, 96⟩ ⟨O, 32⟩) (d₂ : Region.Disjoint ⟨St, 96⟩ ⟨Sc, 160⟩)
    (d₃ : Region.Disjoint ⟨O, 32⟩ ⟨Sc, 160⟩) (kS : (below (s.gpr .rsp) 24).Disjoint ⟨St, 96⟩)
    (kO : (below (s.gpr .rsp) 24).Disjoint ⟨O, 32⟩) (kC : (below (s.gpr .rsp) 24).Disjoint ⟨Sc, 160⟩)
    (hc : Covers ([] ++ [⟨St, 96⟩, ⟨O, 32⟩, ⟨Sc, 160⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨St, 96⟩, ⟨O, 32⟩, ⟨Sc, 160⟩] s.wr)
    {m : List Byte} (hm : Repr s.mem St m) (hrsi : s.gpr .rsi = BitVec.ofNat 64 m.length) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨St, 96⟩, ⟨O, 32⟩, ⟨Sc, 160⟩, below (s.gpr .rsp) 24] s.mem s'.mem →
      bytesAt s'.mem O 32 = Spec.Sha256.hash m → Q s') :
    WP isa (.call nm (Impl.Sha256.X86_64.Stream.finalize f)) s Q := by
  refine WP.call (k := Proof.Sha256.finalizeX86_64) hv.sfin_v.1
    hv.sfin_nosp (by rw [hv.sfin_depth]; decide) (sfin_pre hrdi hrdx hrcx d₁ d₂ d₃ kS kO kC) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [hv.sfin_depth] at hf
  refine hQ s' hrd hwr hcs (frame24 hf (by omega)) ?_
  simp only [Proof.Sha256.finalizeX86_64, State.withRegions_gpr, State.withRegions_mem,
    ce_gpr s (by decide : Reg.rdi ≠ .rsp), ce_gpr s (by decide : Reg.rsi ≠ .rsp),
    ce_gpr s (by decide : Reg.rdx ≠ .rsp), hrdi, hrdx, hm₂] at hpost
  exact hpost m (ce_repr s kS hm) hrsi

/-! ## `vg_hmac_sha256_init` -/

theorem hinit_pre {s : State} {I O K Sc : Addr} {n : Nat} (hrdi : s.gpr .rdi = I) (hrsi : s.gpr .rsi = O)
    (hrdx : s.gpr .rdx = K) (hrcx : (s.gpr .rcx).toNat = n) (hr8 : s.gpr .r8 = Sc) (hn : n ≤ 64)
    (d₁ : Region.Disjoint ⟨I, 96⟩ ⟨O, 96⟩) (d₂ : Region.Disjoint ⟨I, 96⟩ ⟨Sc, 160⟩)
    (d₃ : Region.Disjoint ⟨O, 96⟩ ⟨Sc, 160⟩) (d₄ : Region.Disjoint ⟨K, n⟩ ⟨I, 96⟩)
    (d₅ : Region.Disjoint ⟨K, n⟩ ⟨O, 96⟩) (d₆ : Region.Disjoint ⟨K, n⟩ ⟨Sc, 160⟩)
    (kI : (below (s.gpr .rsp) 24).Disjoint ⟨I, 96⟩) (kO : (below (s.gpr .rsp) 24).Disjoint ⟨O, 96⟩)
    (kK : (below (s.gpr .rsp) 24).Disjoint ⟨K, n⟩) (kC : (below (s.gpr .rsp) 24).Disjoint ⟨Sc, 160⟩) :
    Proof.Hmac.initSha256X86_64.pre (s.callEntry.withRegions [⟨K, n⟩] [⟨I, 96⟩, ⟨O, 96⟩, ⟨Sc, 160⟩]) := by
  simp only [Proof.Hmac.initSha256X86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, ce_gpr s (by decide : Reg.rdi ≠ .rsp),
    ce_gpr s (by decide : Reg.rsi ≠ .rsp), ce_gpr s (by decide : Reg.rdx ≠ .rsp),
    ce_gpr s (by decide : Reg.rcx ≠ .rsp), ce_gpr s (by decide : Reg.r8 ≠ .rsp), hrdi, hrsi, hrdx, hrcx, hr8]
  exact ⟨hn, trivial, trivial, d₁, d₂, d₃, d₄, d₅, d₆, kI.sub_left (ret_sub _), kO.sub_left (ret_sub _),
    kC.sub_left (ret_sub _), kI.sub_left (stk8_sub _), kO.sub_left (stk8_sub _), kK.sub_left (stk8_sub _),
    kC.sub_left (stk8_sub _)⟩

theorem hinit_call {f : Callee} (hv : Vf f) {nm : String} {s : State} {I O K Sc : Addr} {n : Nat} (hrdi : s.gpr .rdi = I) (hrsi : s.gpr .rsi = O)
    (hrdx : s.gpr .rdx = K) (hrcx : (s.gpr .rcx).toNat = n) (hr8 : s.gpr .r8 = Sc) (hn : n ≤ 64)
    (d₁ : Region.Disjoint ⟨I, 96⟩ ⟨O, 96⟩) (d₂ : Region.Disjoint ⟨I, 96⟩ ⟨Sc, 160⟩)
    (d₃ : Region.Disjoint ⟨O, 96⟩ ⟨Sc, 160⟩) (d₄ : Region.Disjoint ⟨K, n⟩ ⟨I, 96⟩)
    (d₅ : Region.Disjoint ⟨K, n⟩ ⟨O, 96⟩) (d₆ : Region.Disjoint ⟨K, n⟩ ⟨Sc, 160⟩)
    (kI : (below (s.gpr .rsp) 24).Disjoint ⟨I, 96⟩) (kO : (below (s.gpr .rsp) 24).Disjoint ⟨O, 96⟩)
    (kK : (below (s.gpr .rsp) 24).Disjoint ⟨K, n⟩) (kC : (below (s.gpr .rsp) 24).Disjoint ⟨Sc, 160⟩)
    (hc : Covers ([⟨K, n⟩] ++ [⟨I, 96⟩, ⟨O, 96⟩, ⟨Sc, 160⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨I, 96⟩, ⟨O, 96⟩, ⟨Sc, 160⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨I, 96⟩, ⟨O, 96⟩, ⟨Sc, 160⟩, below (s.gpr .rsp) 24] s.mem s'.mem →
      Repr s'.mem I (xorPad (blockKey sha256 (bytesAt s.mem K n)) ipad) →
      Repr s'.mem O (xorPad (blockKey sha256 (bytesAt s.mem K n)) opad) → Q s') :
    WP isa (.call nm (Impl.Hmac.X86_64.init f)) s Q := by
  refine WP.call (k := Proof.Hmac.initSha256X86_64) hv.hinit_v.1
    hv.hinit_nosp (by rw [hv.hinit_depth]; decide)
    (hinit_pre hrdi hrsi hrdx hrcx hr8 hn d₁ d₂ d₃ d₄ d₅ d₆ kI kO kK kC) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [hv.hinit_depth] at hf
  simp only [Proof.Hmac.initSha256X86_64, State.withRegions_gpr, State.withRegions_mem,
    ce_gpr s (by decide : Reg.rdi ≠ .rsp), ce_gpr s (by decide : Reg.rsi ≠ .rsp),
    ce_gpr s (by decide : Reg.rdx ≠ .rsp), ce_gpr s (by decide : Reg.rcx ≠ .rsp), hrdi, hrsi, hrdx, hrcx,
    hm₂, ce_bytes s kK (by omega)] at hpost
  exact hQ s' hrd hwr hcs (frame24 hf (by omega)) hpost.1 hpost.2

/-! ## `vg_hmac_sha256_finalize` -/

theorem hfin_pre {s : State} {I O Sc : Addr} (hrdi : s.gpr .rdi = I) (hrsi : s.gpr .rsi = O)
    (hrcx : s.gpr .rcx = Sc)
    (d₁ : Region.Disjoint ⟨I, 96⟩ ⟨O, 96⟩) (d₂ : Region.Disjoint ⟨I, 96⟩ ⟨Sc, 240⟩)
    (d₃ : Region.Disjoint ⟨O, 96⟩ ⟨Sc, 240⟩)
    (kI : (below (s.gpr .rsp) 24).Disjoint ⟨I, 96⟩) (kO : (below (s.gpr .rsp) 24).Disjoint ⟨O, 96⟩)
    (kC : (below (s.gpr .rsp) 24).Disjoint ⟨Sc, 240⟩) :
    Proof.Hmac.finalizeSha256X86_64.pre (s.callEntry.withRegions [⟨O, 96⟩] [⟨I, 96⟩, ⟨Sc, 240⟩]) := by
  simp only [Proof.Hmac.finalizeSha256X86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, ce_gpr s (by decide : Reg.rdi ≠ .rsp),
    ce_gpr s (by decide : Reg.rsi ≠ .rsp), ce_gpr s (by decide : Reg.rcx ≠ .rsp), hrdi, hrsi, hrcx]
  exact ⟨trivial, trivial, d₁, d₂, d₃, kI.sub_left (ret_sub _), kO.sub_left (ret_sub _),
    kC.sub_left (ret_sub _), kI.sub_left (stk16_sub _), kO.sub_left (stk16_sub _), kC.sub_left (stk16_sub _)⟩

theorem hfin_call {f : Callee} (hv : Vf f) {nm : String} (name : String) {s : State} {I O Sc : Addr} (hrdi : s.gpr .rdi = I) (hrsi : s.gpr .rsi = O)
    (hrcx : s.gpr .rcx = Sc)
    (d₁ : Region.Disjoint ⟨I, 96⟩ ⟨O, 96⟩) (d₂ : Region.Disjoint ⟨I, 96⟩ ⟨Sc, 240⟩)
    (d₃ : Region.Disjoint ⟨O, 96⟩ ⟨Sc, 240⟩)
    (kI : (below (s.gpr .rsp) 24).Disjoint ⟨I, 96⟩) (kO : (below (s.gpr .rsp) 24).Disjoint ⟨O, 96⟩)
    (kC : (below (s.gpr .rsp) 24).Disjoint ⟨Sc, 240⟩)
    (hc : Covers ([⟨O, 96⟩] ++ [⟨I, 96⟩, ⟨Sc, 240⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨I, 96⟩, ⟨Sc, 240⟩] s.wr)
    {k : List Byte} (hk : k.length = 64) {text : List Byte} (hI : Repr s.mem I (xorPad k ipad ++ text))
    (hO : Repr s.mem O (xorPad k opad)) (hrdx : s.gpr .rdx = BitVec.ofNat 64 (64 + text.length))
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨I, 96⟩, ⟨Sc, 240⟩, below (s.gpr .rsp) 24] s.mem s'.mem →
      bytesAt s'.mem (Sc + 176) 32 = hmacBlockKey sha256 k text → Q s') :
    WP isa (.call nm (Impl.Hmac.X86_64.finalize f name)) s Q := by
  refine WP.call (k := Proof.Hmac.finalizeSha256X86_64) (hv.hfin_v name).1
    (hv.hfin_nosp name) (by rw [hv.hfin_depth name]; decide) (hfin_pre hrdi hrsi hrcx d₁ d₂ d₃ kI kO kC) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [hv.hfin_depth name] at hf
  refine hQ s' hrd hwr hcs (frame24 hf (by omega)) ?_
  simp only [Proof.Hmac.finalizeSha256X86_64, State.withRegions_gpr, State.withRegions_mem,
    ce_gpr s (by decide : Reg.rdi ≠ .rsp), ce_gpr s (by decide : Reg.rsi ≠ .rsp),
    ce_gpr s (by decide : Reg.rdx ≠ .rsp), ce_gpr s (by decide : Reg.rcx ≠ .rsp), hrdi, hrsi, hrcx,
    hm₂] at hpost
  exact hpost k text hk (ce_repr s kI hI) hrdx (ce_repr s kO hO)

/-! ## `vg_pbkdf2_hmac_sha256_iterate` -/

theorem iter_pre {s : State} {K U T Sc : Addr} (hrdi : s.gpr .rdi = K) (hrsi : s.gpr .rsi = U)
    (hrcx : s.gpr .rcx = T) (hr8 : s.gpr .r8 = Sc)
    (d₁ : Region.Disjoint ⟨K, 192⟩ ⟨T, 32⟩) (d₂ : Region.Disjoint ⟨K, 192⟩ ⟨Sc, 384⟩)
    (d₃ : Region.Disjoint ⟨U, 32⟩ ⟨T, 32⟩) (d₄ : Region.Disjoint ⟨U, 32⟩ ⟨Sc, 384⟩)
    (d₅ : Region.Disjoint ⟨T, 32⟩ ⟨Sc, 384⟩)
    (kK : (below (s.gpr .rsp) 24).Disjoint ⟨K, 192⟩) (kU : (below (s.gpr .rsp) 24).Disjoint ⟨U, 32⟩)
    (kT : (below (s.gpr .rsp) 24).Disjoint ⟨T, 32⟩) (kC : (below (s.gpr .rsp) 24).Disjoint ⟨Sc, 384⟩) :
    Proof.Pbkdf2.iterateSha256X86_64.pre (s.callEntry.withRegions [⟨K, 192⟩, ⟨U, 32⟩] [⟨T, 32⟩, ⟨Sc, 384⟩]) := by
  simp only [Proof.Pbkdf2.iterateSha256X86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, ce_gpr s (by decide : Reg.rdi ≠ .rsp),
    ce_gpr s (by decide : Reg.rsi ≠ .rsp), ce_gpr s (by decide : Reg.rcx ≠ .rsp),
    ce_gpr s (by decide : Reg.r8 ≠ .rsp), hrdi, hrsi, hrcx, hr8]
  exact ⟨trivial, trivial, d₁, d₂, d₃, d₄, d₅, kK.sub_left (ret_sub _), kU.sub_left (ret_sub _),
    kT.sub_left (ret_sub _), kC.sub_left (ret_sub _), kK.sub_left (stk8_sub _), kU.sub_left (stk8_sub _),
    kT.sub_left (stk8_sub _), kC.sub_left (stk8_sub _)⟩

theorem iter_call {f : Callee} (hv : Vf f) {nm : String} {s : State} {K U T Sc : Addr} (hrdi : s.gpr .rdi = K) (hrsi : s.gpr .rsi = U)
    (hrcx : s.gpr .rcx = T) (hr8 : s.gpr .r8 = Sc)
    (d₁ : Region.Disjoint ⟨K, 192⟩ ⟨T, 32⟩) (d₂ : Region.Disjoint ⟨K, 192⟩ ⟨Sc, 384⟩)
    (d₃ : Region.Disjoint ⟨U, 32⟩ ⟨T, 32⟩) (d₄ : Region.Disjoint ⟨U, 32⟩ ⟨Sc, 384⟩)
    (d₅ : Region.Disjoint ⟨T, 32⟩ ⟨Sc, 384⟩)
    (kK : (below (s.gpr .rsp) 24).Disjoint ⟨K, 192⟩) (kU : (below (s.gpr .rsp) 24).Disjoint ⟨U, 32⟩)
    (kT : (below (s.gpr .rsp) 24).Disjoint ⟨T, 32⟩) (kC : (below (s.gpr .rsp) 24).Disjoint ⟨Sc, 384⟩)
    (hc : Covers ([⟨K, 192⟩, ⟨U, 32⟩] ++ [⟨T, 32⟩, ⟨Sc, 384⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨T, 32⟩, ⟨Sc, 384⟩] s.wr)
    {k : List Byte} (hk : k.length = 64) (hI : Repr s.mem K (xorPad k ipad))
    (hO : Repr s.mem (K + 96) (xorPad k opad)) (kO : (below (s.gpr .rsp) 24).Disjoint ⟨K + 96, 96⟩)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨T, 32⟩, ⟨Sc, 384⟩, below (s.gpr .rsp) 24] s.mem s'.mem →
      bytesAt s'.mem T 32 = Spec.Pbkdf2.iterate (hmacBlockKey sha256 k) ((s.gpr .rdx).setWidth 32).toNat
        (bytesAt s.mem U 32) (bytesAt s.mem T 32) → Q s') :
    WP isa (.call nm (Impl.Pbkdf2.X86_64.iterate f)) s Q := by
  refine WP.call (k := Proof.Pbkdf2.iterateSha256X86_64) hv.iter_v.1
    hv.iter_nosp (by rw [hv.iter_depth]; decide) (iter_pre hrdi hrsi hrcx hr8 d₁ d₂ d₃ d₄ d₅ kK kU kT kC) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [hv.iter_depth] at hf
  refine hQ s' hrd hwr hcs (frame24 hf (by omega)) ?_
  simp only [Proof.Pbkdf2.iterateSha256X86_64, State.withRegions_gpr, State.withRegions_mem,
    ce_gpr s (by decide : Reg.rdi ≠ .rsp), ce_gpr s (by decide : Reg.rsi ≠ .rsp),
    ce_gpr s (by decide : Reg.rdx ≠ .rsp), ce_gpr s (by decide : Reg.rcx ≠ .rsp), hrdi, hrsi, hrcx,
    hm₂] at hpost
  rw [hpost k hk (ce_repr s (by simpa using kK.sub_right (Region.sub_prefix (by omega))) hI) (ce_repr s kO hO),
    ce_bytes s kU (by omega), ce_bytes s kT (by omega)]

end VG.Proof.Pbkdf2.X86_64.Derive
