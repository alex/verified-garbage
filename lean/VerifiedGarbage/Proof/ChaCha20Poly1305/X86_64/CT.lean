import VerifiedGarbage.Proof.Poly1305.X86_64.Init
import VerifiedGarbage.Proof.Poly1305.X86_64.Blocks
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Blocks
import VerifiedGarbage.Proof.Poly1305.X86_64.Finalize
import VerifiedGarbage.Proof.ChaCha20.X86_64.Variant
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.ChaCha20Poly1305
import VerifiedGarbage.TCB.X86_64.Target
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.ContractPost
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ChaCha20-Poly1305 on x86-64: the calls

Untrusted: everything here is checked by Lean. Each call of a verified
function, from its proof of `Verified` (with `WP.call`): what it needs of the
state it is called from, and what holds when it returns.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-! ## Memory -/

theorem bytesAt_eq : Spec.ChaCha20.bytesAt = Spec.Poly1305.bytesAt := rfl

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem sub_off (p : Addr) {a n len : Nat} (h : a + n ≤ len) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, n⟩ ⟨p, len⟩ := Offset.sub_base p h

/-- A Poly1305 state outside a frame is unchanged. -/
theorem Repr.frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr}
    (hd : ∀ r ∈ rs, (⟨P, 128⟩ : Region).Disjoint r) {key msg : List Byte} (h : Repr m P key msg) :
    Repr m' P key msg := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · rw [show (P + 24 : Addr) = P + BitVec.ofNat 64 24 from rfl,
      bytesAt_frame hf (n := 32) (fun r hr => (hd r hr).sub_left (sub_off P (a := 24) (by lit_omega)))
      (by lit_omega)]
    exact h2
  · rw [bytesAt_frame hf (n := 24) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by lit_omega)))
      (by lit_omega)]
    exact h3

/-- A ChaCha20 state outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p :=
  VG.Proof.ChaCha20.X86_64.Xor.stateAt_frame hf hd

/-- The return address a call stores. -/
theorem callEntry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by lit_omega) (by lit_omega))

/-! ## The callees' registers -/

theorem init_keeps : ((instrs Impl.Poly1305.X86_64.init).all fun i =>
    !Taint.clobbers i .rdi && !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem blocks_keeps : ((instrs Impl.Poly1305.X86_64.blocks).all fun i =>
    !Taint.clobbers i .rdi && !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem finalize_keeps : ((instrs Impl.Poly1305.X86_64.finalize).all fun i =>
    !Taint.clobbers i .rdi && !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem init_depth : Impl.Poly1305.X86_64.init.depth = 0 := by lit_decide
theorem blocks_depth : Impl.Poly1305.X86_64.blocks.depth = 0 := by lit_decide
theorem finalize_depth : Impl.Poly1305.X86_64.finalize.depth = 0 := by lit_decide

theorem keeps_of {c : Prog isa} {p : Instr → Bool} (h : (instrs c).all p = true) {r : Reg}
    (hr : ∀ i, p i = true → Taint.clobbers i r = false) : ∀ i ∈ instrs c, Taint.clobbers i r = false :=
  fun i hi => hr i (List.all_eq_true.mp h i hi)

theorem and_left {a b : Bool} (h : (!a && !b) = true) : a = false := by simp_all
theorem and_right {a b : Bool} (h : (!a && !b) = true) : b = false := by simp_all

theorem callEntry_gpr' (s : State) {r : Reg} (h : r ≠ .rsp) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr _ h

/-! ## `vg_poly1305_init` -/

theorem init_call {s : State} {P K : Addr} (hrdi : s.gpr .rdi = P) (hrsi : s.gpr .rsi = K)
    (hdj : (⟨P, 128⟩ : Region).Disjoint ⟨K, 32⟩)
    (hsP : (below (s.gpr .rsp) 8).Disjoint ⟨P, 128⟩) (hsK : (below (s.gpr .rsp) 8).Disjoint ⟨K, 32⟩)
    (hc : Covers ([⟨K, 32⟩] ++ [⟨P, 128⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨P, 128⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨P, 128⟩, below (s.gpr .rsp) 8] s.mem s'.mem → s'.gpr .rdi = P →
      Repr s'.mem P (bytesAt s.mem K 32) [] → Q s') :
    WP isa (.call "vg_poly1305_init" Impl.Poly1305.X86_64.init) s Q := by
  refine WP.call (k := Proof.Poly1305.initX86_64) Proof.Poly1305.X86_64.init_ok
    (keeps_of init_keeps fun _ h => and_right h) (by rw [init_depth]; decide)
    (rd := [⟨K, 32⟩]) (wr := [⟨P, 128⟩]) ?_ hc hw ?_
  · simp only [Proof.Poly1305.initX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), hrdi, hrsi]
    exact ⟨trivial, trivial, hdj, hsP⟩
  · intro s' hrd hwr hcs hf hkeep ⟨s₂, hm₂, _, hpost⟩
    rw [init_depth] at hf
    refine hQ s' hrd hwr hcs hf (by rw [hkeep .rdi (keeps_of init_keeps fun _ h => and_left h), hrdi]) ?_
    simp only [Proof.Poly1305.initX86_64, State.withRegions_gpr, State.withRegions_mem,
      callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), hrdi,
      hrsi, hm₂] at hpost
    rwa [bytesAt_frame (callEntry_frame s) (by simpa using hsK.symm) (by lit_omega)] at hpost

/-! ## `vg_poly1305_blocks` -/

theorem avx2_keeps : ((instrs Impl.Poly1305.X86_64.Avx2.blocksAvx2).all fun i =>
    !Taint.clobbers i .rdi && !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem avx2_depth : Impl.Poly1305.X86_64.Avx2.blocksAvx2.depth = 1 := by lit_decide

/-- The stack below `rsp` that a call of `vg_poly1305_blocks` uses (16 bytes
for `vg_poly1305_blocks_avx2`, which calls `vg_poly1305_blocks`). -/
theorem below8_16 (sp : Addr) : Region.Sub (below sp 8) (below sp 16) := below_sub (by lit_omega) (by lit_omega)

/-- What a call of an implementation of `vg_poly1305_blocks` leaves. -/
def BlocksPost (s : State) (P p : Addr) (n : Nat) (s' : State) : Prop :=
  s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
    Frame [⟨P, 128⟩, below (s.gpr .rsp) 16] s.mem s'.mem ∧ s'.gpr .rdi = P ∧
    (∀ key msg, Repr s.mem P key msg → Repr s'.mem P key (msg ++ bytesAt s.mem p (16 * n))) ∧
    s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

section
variable {s : State} {P p : Addr} {n : Nat} (hrdi : s.gpr .rdi = P) (hrsi : s.gpr .rsi = p)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) (hn : 16 * n < 2 ^ 64)
    (hdj : (⟨P, 128⟩ : Region).Disjoint ⟨p, 16 * n⟩) (hwrap : p.toNat + 16 * n ≤ 2 ^ 64)
    (hsP : (below (s.gpr .rsp) 16).Disjoint ⟨P, 128⟩) (hsp : (below (s.gpr .rsp) 16).Disjoint ⟨p, 16 * n⟩)
    (hc : Covers ([⟨p, 16 * n⟩] ++ [⟨P, 128⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨P, 128⟩] s.wr)
include hrdi hrsi hrdx hn hdj hwrap hsP hsp hc hw

theorem scalar_call : WP isa (.call "vg_poly1305_blocks" Impl.Poly1305.X86_64.blocks) s (BlocksPost s P p n) := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by lit_omega)
  have hsP8 := hsP.sub_left (below8_16 _)
  refine WP.call_mx (k := Proof.Poly1305.blocksX86_64) Proof.Poly1305.X86_64.blocks_ok
    (keeps_of blocks_keeps fun _ h => and_right h) (by rw [blocks_depth]; decide)
    (rd := [⟨p, 16 * n⟩]) (wr := [⟨P, 128⟩]) ?_ hc hw ?_
  · simp only [Proof.Poly1305.blocksX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi,
      hrsi, hrdx, hn']
    exact ⟨trivial, trivial, hdj, hsP8, hwrap⟩
  · intro s' hrd hwr hcs hf hkeep ⟨s₂, hm₂, _, hpost⟩ hmx
    rw [blocks_depth] at hf
    refine ⟨hrd, hwr, hcs, hf.sub fun r hr => ?_,
      by rw [hkeep .rdi (keeps_of blocks_keeps fun _ h => and_left h), hrdi], fun key msg hr => ?_, hmx⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, below8_16 _⟩
    simp only [Proof.Poly1305.blocksX86_64, State.withRegions_gpr, State.withRegions_mem,
      callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi, hrsi, hrdx, hn', hm₂] at hpost
    have h := hpost key msg (Repr.frame (callEntry_frame s) (h := hr) (by simpa using hsP8.symm))
    rwa [bytesAt_frame (callEntry_frame s) (by simpa using (hsp.sub_left (below8_16 _)).symm)
      (by lit_omega)] at h

theorem avx2_call :
    WP isa (.call "vg_poly1305_blocks_avx2" Impl.Poly1305.X86_64.Avx2.blocksAvx2) s (BlocksPost s P p n) := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by lit_omega)
  have hsP8 := hsP.sub_left (below8_16 _)
  refine WP.call_mx (k := Proof.Poly1305.X86_64.Avx2.blocksAvx2X86_64)
    Proof.Poly1305.X86_64.Avx2.blocksAvx2_ok
    (keeps_of avx2_keeps fun _ h => and_right h) (by rw [avx2_depth]; decide)
    (rd := [⟨p, 16 * n⟩]) (wr := [⟨P, 128⟩]) ?_ hc hw ?_
  · simp only [Proof.Poly1305.X86_64.Avx2.blocksAvx2X86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi,
      hrsi, hrdx, hn']
    exact ⟨trivial, trivial, hdj, hsP8, hsP.sub_left (below_callee _ 8),
      hsp.sub_left (below_callee _ 8), hwrap⟩
  · intro s' hrd hwr hcs hf hkeep ⟨s₂, hm₂, _, hpost⟩ hmx
    rw [avx2_depth] at hf
    refine ⟨hrd, hwr, hcs, hf,
      by rw [hkeep .rdi (keeps_of avx2_keeps fun _ h => and_left h), hrdi], fun key msg hr => ?_, hmx⟩
    simp only [Proof.Poly1305.X86_64.Avx2.blocksAvx2X86_64, Proof.Poly1305.blocksX86_64,
      State.withRegions_gpr, State.withRegions_mem,
      callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi, hrsi, hrdx, hn', hm₂] at hpost
    have h := hpost key msg (Repr.frame (callEntry_frame s) (h := hr) (by simpa using hsP8.symm))
    rwa [bytesAt_frame (callEntry_frame s) (by simpa using (hsp.sub_left (below8_16 _)).symm)
      (by lit_omega)] at h

/-- A call of the implementation `b` of `vg_poly1305_blocks`. -/
theorem blocks_call (b : Impl.Poly1305.X86_64.Blocks) : WP isa (.call b.name b.code) s (BlocksPost s P p n) := by
  cases b
  · exact scalar_call hrdi hrsi hrdx hn hdj hwrap hsP hsp hc hw
  · exact avx2_call hrdi hrsi hrdx hn hdj hwrap hsP hsp hc hw

end

/-! ## `vg_poly1305_finalize` -/

theorem finalize_call {s : State} {P O : Addr} (hrdi : s.gpr .rdi = P) (hrsi : s.gpr .rsi = 0)
    (hrdx : s.gpr .rdx = O) (hPO : (⟨P, 128⟩ : Region).Disjoint ⟨O, 16⟩)
    (hsP : (below (s.gpr .rsp) 8).Disjoint ⟨P, 128⟩) (hsO : (below (s.gpr .rsp) 8).Disjoint ⟨O, 16⟩)
    (hc : Covers ([] ++ [⟨P, 128⟩, ⟨O, 16⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨P, 128⟩, ⟨O, 16⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨P, 128⟩, ⟨O, 16⟩, below (s.gpr .rsp) 8] s.mem s'.mem → s'.gpr .rdi = P → s'.gpr .rcx = O →
      (∀ key msg, Repr s.mem P key msg → bytesAt s'.mem O 16 = mac key msg) → Q s') :
    WP isa (.call "vg_poly1305_finalize" Impl.Poly1305.X86_64.finalize) s Q := by
  have k1 : ∀ i ∈ instrs Impl.Poly1305.X86_64.finalize, Taint.clobbers i .rdi = false :=
    keeps_of finalize_keeps fun _ h => and_left h
  have k3 : ∀ i ∈ instrs Impl.Poly1305.X86_64.finalize, Taint.clobbers i .rsp = false :=
    keeps_of finalize_keeps fun _ h => and_right h
  refine WP.call (k := Proof.Poly1305.finalizeX86_64) Proof.Poly1305.X86_64.finalize_ok
    k3 (by rw [finalize_depth]; decide) (rd := []) (wr := [⟨P, 128⟩, ⟨O, 16⟩]) ?_ hc hw ?_
  · simp only [Proof.Poly1305.finalizeX86_64, State.withRegions_gpr, State.withRegions_wr,
      State.callEntry_rsp, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi, hrdx]
    exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self, hPO, hsP, hsO⟩
  · intro s' hrd hwr hcs hf hkeep ⟨s₂, hm₂, hg₂, hrcx₂, hpost⟩
    rw [finalize_depth] at hf
    refine hQ s' hrd hwr hcs hf (by rw [hkeep .rdi k1, hrdi]) ?_ fun key msg hr => ?_
    · rw [← hg₂ .rcx (by decide), hrcx₂, State.withRegions_gpr, callEntry_gpr' s (by decide), hrdx]
    simp only [State.withRegions_gpr, State.withRegions_mem, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi,
      hrsi, hrdx, hm₂] at hpost
    refine hpost key msg (Proof.Poly1305.Repr.buffered
      (Repr.frame (callEntry_frame s) (h := hr) (by simpa using hsP.symm))) ?_
    rw [show (0 : BitVec 64).toNat = 0 from rfl, hr.1]

/-! ## `vg_chacha20_block` -/

theorem block_call {s : State} {S B : Addr} (hrdi : s.gpr .rdi = S) (hrsi : s.gpr .rsi = B)
    (hdj : (⟨B, 256⟩ : Region).Disjoint ⟨S, 64⟩)
    (hsB : (below (s.gpr .rsp) 8).Disjoint ⟨B, 256⟩) (hsS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 64⟩)
    (hc : Covers ([⟨S, 64⟩] ++ [⟨B, 256⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨B, 256⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨B, 256⟩, below (s.gpr .rsp) 8] s.mem s'.mem → s'.gpr .rsi = B →
      stateAt s'.mem B = Spec.ChaCha20.block (stateAt s.mem S) → Q s') :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block) s Q := by
  refine WP.call (k := Proof.ChaCha20.blockX86_64) Proof.ChaCha20.X86_64.block_correct
    (Proof.ChaCha20.X86_64.Xor.block_keeps_reg (by simp [Proof.ChaCha20.X86_64.Xor.kept]))
    (by rw [Proof.ChaCha20.X86_64.Xor.block_depth]; decide) (rd := [⟨S, 64⟩]) (wr := [⟨B, 256⟩]) ?_ hc hw ?_
  · simp only [Proof.ChaCha20.blockX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), hrdi, hrsi]
    exact ⟨trivial, trivial, hdj, hsB⟩
  · intro s' hrd hwr hcs hf hkeep ⟨s₂, hm₂, _, hpost⟩
    rw [Proof.ChaCha20.X86_64.Xor.block_depth] at hf
    refine hQ s' hrd hwr hcs hf (by rw [hkeep .rsi (Proof.ChaCha20.X86_64.Xor.block_keeps_reg
      (by simp [Proof.ChaCha20.X86_64.Xor.kept])), hrsi]) ?_
    simp only [Proof.ChaCha20.blockX86_64, State.withRegions_gpr, State.withRegions_mem,
      callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), hrdi,
      hrsi, hm₂] at hpost
    rwa [stateAt_frame (callEntry_frame s) (by simpa using hsS.symm)] at hpost

/-! ## `vg_chacha20_xor` -/

theorem below8_24 (s : State) : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 24) :=
  below_sub (by lit_omega) (by lit_omega)

/-- The precondition of the implementation `v` of `vg_chacha20_xor`, called
with 24 bytes of stack below `rsp`: 8 for its return address, and at most 16
for its calls. -/
theorem xor_pre (v : Proof.ChaCha20.X86_64.XorImpl) {s : State} {S D B : Addr} {n : Nat}
    (hrdi : s.gpr .rdi = S) (hrsi : s.gpr .rsi = D)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) (hrcx : s.gpr .rcx = B) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩) (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hwrap : D.toNat + n ≤ 2 ^ 64)
    (hsS : (below (s.gpr .rsp) 24).Disjoint ⟨S, 64⟩) (hsD : (below (s.gpr .rsp) 24).Disjoint ⟨D, n⟩)
    (hsB : (below (s.gpr .rsp) 24).Disjoint ⟨B, 320⟩) :
    (Proof.ChaCha20.xorStack v.stack).pre (s.callEntry.withRegions [] [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have hk := v.stack_le
  have h8 := below8_24 s
  have hk' : Region.Sub ⟨s.gpr .rsp - 8 - BitVec.ofNat 64 v.stack, v.stack⟩ (below (s.gpr .rsp) 24) := by
    rw [show s.gpr .rsp - 8 - BitVec.ofNat 64 v.stack = s.gpr .rsp - BitVec.ofNat 64 (8 + v.stack) by
      rw [BitVec.sub_sub, BitVec.ofNat_add]; rfl]
    exact Offset.sub_below _ (by lit_omega) (by lit_omega)
  simp only [Proof.ChaCha20.xorStack, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
    callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp),
    callEntry_gpr' s (by decide : Reg.rcx ≠ .rsp), hrdi, hrsi, hrdx, hrcx, hn']
  exact ⟨trivial, trivial, hSD, hSB, hDB, hsS.sub_left h8, hsD.sub_left h8, hsB.sub_left h8,
    hsS.sub_left hk', hsD.sub_left hk', hsB.sub_left hk', hwrap⟩

/-- A call of the implementation `v` of `vg_chacha20_xor` (see `xor_pre`). -/
theorem xor_call (v : Proof.ChaCha20.X86_64.XorImpl) {s : State} {S D B : Addr} {n : Nat}
    (hrdi : s.gpr .rdi = S) (hrsi : s.gpr .rsi = D)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) (hrcx : s.gpr .rcx = B) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩) (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hwrap : D.toNat + n ≤ 2 ^ 64)
    (hsS : (below (s.gpr .rsp) 24).Disjoint ⟨S, 64⟩) (hsD : (below (s.gpr .rsp) 24).Disjoint ⟨D, n⟩)
    (hsB : (below (s.gpr .rsp) 24).Disjoint ⟨B, 320⟩)
    (hc : Covers ([] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩, below (s.gpr .rsp) 24] s.mem s'.mem → s'.gpr .rsi = B →
      Spec.ChaCha20.bytesAt s'.mem D n =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem D n) (keystream (stateAt s.mem S) n) → Q s') :
    WP isa (.call v.callee.name v.callee.code) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have hd := v.depth_le
  have h8 := below8_24 s
  refine WP.call (k := Proof.ChaCha20.xorStack v.stack) v.ok v.nosp (by lit_omega)
    (xor_pre v hrdi hrsi hrdx hrcx hn hSD hSB hDB hwrap hsS hsD hsB) hc hw ?_
  intro s' hrd hwr hcs hf hkeep ⟨s₂, hm₂, hg₂, hpost, hrsi₂⟩
  have hf' : Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩, below (s.gpr .rsp) 24] s.mem s'.mem := by
    refine hf.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨below (s.gpr .rsp) 24, by simp, below_sub (by lit_omega) (by lit_omega)⟩
  refine hQ s' hrd hwr hcs hf' ?_ ?_
  · rw [← hg₂ .rsi (by decide), hrsi₂, State.withRegions_gpr, callEntry_gpr' s (by decide), hrcx]
  · simp only [Proof.ChaCha20.xorX86_64, State.withRegions_gpr, State.withRegions_mem,
      callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi, hrsi, hrdx, hn', hm₂] at hpost
    rw [hpost, bytesAt_eq, bytesAt_frame (callEntry_frame s) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hsD.sub_left h8).symm) (by lit_omega),
      stateAt_frame (callEntry_frame s) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hsS.sub_left h8).symm)]

end VG.Proof.ChaCha20Poly1305.X86_64

/-!
# ChaCha20-Poly1305 on x86-64: the entry state, regions and invariant

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20Poly1305

open Spec.ChaCha20Poly1305
open Spec.Poly1305 (bytesAt)

open VG.X86_64 in
/-- The precondition of both functions: `ctx` (1024 bytes) and `data` may be
read and written, `aad` read; none of them overlaps another (`aad` may overlap
nothing writable), the return address or the 24 bytes of stack below it, where
the calls store their return addresses (16 for that of `vg_chacha20_xor` and
the calls of any of its implementations, see `XorImpl`); nothing wraps around
the end of the address space. -/
def preX86_64 (s : X86_64.State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 1024⟩
  let aad : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
  let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  let stack : Region := ⟨s.gpr .rsp - 24, 24⟩
  s.rd = [aad] ∧ s.wr = [ctx, data] ∧
  ctx.Disjoint aad ∧ ctx.Disjoint data ∧ aad.Disjoint data ∧
  ret.Disjoint ctx ∧ ret.Disjoint aad ∧ ret.Disjoint data ∧
  stack.Disjoint ctx ∧ stack.Disjoint aad ∧ stack.Disjoint data ∧
  (s.gpr .rdi).toNat + 1024 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
  (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64

open VG.X86_64 in
def pubX86_64 (s₁ s₂ : X86_64.State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
  s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_chacha20_poly1305_seal(ctx, aad, aad_len, data, len)`. -/
def sealX86_64 : Contract X86_64.isa where
  pre := preX86_64
  post s s' :=
    let ctx := s.gpr .rdi
    encrypt (bytesAt s.mem ctx 32) (bytesAt s.mem (ctx + 32) 12)
        (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) =
      (bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat, bytesAt s'.mem (ctx + 48) 16)
  pub := pubX86_64

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_chacha20_poly1305_open(ctx, aad, aad_len, data, len) -> u32`. -/
def openX86_64 : Contract X86_64.isa where
  pre := preX86_64
  post s s' :=
    let ctx := s.gpr .rdi
    match decrypt (bytesAt s.mem ctx 32) (bytesAt s.mem (ctx + 32) 12)
        (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
        (bytesAt s.mem (ctx + 48) 16) with
    | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat = pt
    | none => (s'.gpr .rax).setWidth 32 = 0
  pub := pubX86_64

end VG.Proof.ChaCha20Poly1305

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-- `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofInt 64 (d : Int)

theorem off_eq (p : Addr) (d : Nat) : off p d = p + BitVec.ofNat 64 d := by
  simp only [off]; congr 1

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = off (s.gpr b) d := rfl

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem signExtend_of_msb {v : BitVec 32} (h : v.msb = false) :
    v.signExtend 64 = BitVec.ofNat 64 v.toNat := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false h]
  apply BitVec.eq_of_toNat_eq
  simp

theorem se_ofNat {k : Nat} (h : k < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 k) = BitVec.ofNat 64 k := by
  rw [signExtend_of_msb (by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by lit_omega)]; simp; omega)]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by lit_omega)]

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev cx : Addr := s₀.gpr .rdi
abbrev ad : Addr := s₀.gpr .rsi
abbrev AL : Nat := (s₀.gpr .rdx).toNat
abbrev dp : Addr := s₀.gpr .rcx
abbrev L : Nat := (s₀.gpr .r8).toNat
/-- The key, the nonce, the additional data, the data and the tag on entry. -/
abbrev K : List Byte := bytesAt s₀.mem (cx s₀) 32
abbrev N : List Byte := bytesAt s₀.mem (cx s₀ + 32) 12
abbrev A : List Byte := bytesAt s₀.mem (ad s₀) (AL s₀)
abbrev D : List Byte := bytesAt s₀.mem (dp s₀) (L s₀)
abbrev T0 : List Byte := bytesAt s₀.mem (cx s₀ + 48) 16
/-- The one-time Poly1305 key. -/
abbrev otk : List Byte := Spec.ChaCha20Poly1305.polyKeyGen (K s₀) (N s₀)
abbrev ctxR : Region := ⟨cx s₀, 1024⟩
abbrev aR : Region := ⟨ad s₀, AL s₀⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 24
/-- `ctx[k, k + n)`. -/
abbrev sub (k n : Nat) : Region := ⟨off (cx s₀) k, n⟩
end

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = [aR s₀]
  wr : s₀.wr = [ctxR s₀, dR s₀]
  c_a : (ctxR s₀).Disjoint (aR s₀)
  c_d : (ctxR s₀).Disjoint (dR s₀)
  a_d : (aR s₀).Disjoint (dR s₀)
  ret_c : (retR s₀).Disjoint (ctxR s₀)
  ret_a : (retR s₀).Disjoint (aR s₀)
  ret_d : (retR s₀).Disjoint (dR s₀)
  stk_c : (⟨s₀.gpr .rsp - 24, 24⟩ : Region).Disjoint (ctxR s₀)
  stk_a : (⟨s₀.gpr .rsp - 24, 24⟩ : Region).Disjoint (aR s₀)
  stk_d : (⟨s₀.gpr .rsp - 24, 24⟩ : Region).Disjoint (dR s₀)
  wrap_c : (cx s₀).toNat + 1024 ≤ 2 ^ 64
  wrap_a : (ad s₀).toNat + AL s₀ ≤ 2 ^ 64
  wrap_d : (dp s₀).toNat + L s₀ ≤ 2 ^ 64

theorem APre.of (s₀ : State) (h : preX86_64 s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem stkR_eq (s₀ : State) : stkR s₀ = ⟨s₀.gpr .rsp - 24, 24⟩ := rfl

/-! ## Regions -/

theorem sub_ctx (s₀ : State) {k n : Nat} (h : k + n ≤ 1024) : Region.Sub (sub s₀ k n) (ctxR s₀) := by
  rw [sub, off_eq]; exact sub_off _ h

theorem sub_sub (s₀ : State) {a m k n : Nat} (h₁ : a ≤ k) (h₂ : k + n ≤ a + m) (_h₃ : a + m ≤ 1024) :
    Region.Sub (sub s₀ k n) (sub s₀ a m) := by
  simp only [sub, off_eq]; exact Offset.sub (cx s₀) h₁ h₂

theorem sub_disj (s₀ : State) {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ 1024)
    (hb : b + m ≤ 1024) : (sub s₀ a n).Disjoint (sub s₀ b m) := by
  simp only [sub, off_eq]; exact Offset.disjoint (cx s₀) h (by lit_omega) (by lit_omega)

theorem contains_sub (s₀ : State) {k n a w : Nat} (h₁ : k ≤ a) (h₂ : a + w ≤ k + n) (h₃ : k + n ≤ 1024) :
    (sub s₀ k n).Contains (off (cx s₀) a) w := by
  simp only [sub, off_eq]; exact Offset.contains (cx s₀) h₁ h₂ (by lit_omega)

theorem contains_ctx (s₀ : State) {a w : Nat} (h : a + w ≤ 1024) : (ctxR s₀).Contains (off (cx s₀) a) w := by
  rw [off_eq]; exact Offset.contains_base (cx s₀) h (by lit_omega)

theorem APre.in_ctx {s₀ : State} (hp : APre s₀) {a w : Nat} (h : a + w ≤ 1024) :
    InRegions s₀.wr (off (cx s₀) a) w := ⟨ctxR s₀, by simp [hp.wr], contains_ctx s₀ h⟩

theorem APre.in_ctx' {s₀ : State} (hp : APre s₀) {a w : Nat} (h : a + w ≤ 1024) :
    InRegions (s₀.rd ++ s₀.wr) (off (cx s₀) a) w := ⟨ctxR s₀, by simp [hp.wr], contains_ctx s₀ h⟩

theorem APre.off_toNat {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k < 1024) :
    (off (cx s₀) k).toNat = (cx s₀).toNat + k := by
  have := hp.wrap_c
  rw [off_eq, BitVec.toNat_add, toNat_ofNat_lt (by lit_omega), Nat.mod_eq_of_lt (by lit_omega)]

/-- The stack below `rsp` that the calls use. -/
theorem below8_stk (s₀ : State) : Region.Sub (below (s₀.gpr .rsp) 8) (stkR s₀) := below_sub (by lit_omega) (by lit_omega)

theorem below16_stk (s₀ : State) : Region.Sub (below (s₀.gpr .rsp) 16) (stkR s₀) :=
  below_sub (by lit_omega) (by lit_omega)

theorem APre.stk_sub {s₀ : State} (hp : APre s₀) {k n : Nat} (h : k + n ≤ 1024) :
    (stkR s₀).Disjoint (sub s₀ k n) := hp.stk_c.sub_right (sub_ctx s₀ h)

theorem APre.below8_sub {s₀ : State} (hp : APre s₀) {k n : Nat} (h : k + n ≤ 1024) :
    (below (s₀.gpr .rsp) 8).Disjoint (sub s₀ k n) := (hp.stk_sub h).sub_left (below8_stk s₀)

theorem APre.below16_sub {s₀ : State} (hp : APre s₀) {k n : Nat} (h : k + n ≤ 1024) :
    (below (s₀.gpr .rsp) 16).Disjoint (sub s₀ k n) := (hp.stk_sub h).sub_left (below16_stk s₀)

/-! ## The saved registers and the invariant -/

/-- Our caller's `rbx, rbp, r13, r14, r15`, saved in `ctx[592, 632)`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (off (cx s₀) 592) 64 = s₀.gpr .rbx ∧ m.readW (off (cx s₀) 600) 64 = s₀.gpr .rbp ∧
  m.readW (off (cx s₀) 608) 64 = s₀.gpr .r13 ∧ m.readW (off (cx s₀) 616) 64 = s₀.gpr .r14 ∧
  m.readW (off (cx s₀) 624) 64 = s₀.gpr .r15

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (sub s₀ 592 40).Disjoint r) : Saved s₀ m' := by
  have c : ∀ d, 592 ≤ d → d + 8 ≤ 632 → (sub s₀ 592 40).Contains (off (cx s₀) d) (64 / 8) :=
    fun d h₁ h₂ => contains_sub s₀ h₁ h₂ (by lit_omega)
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by rw [hf.readW (c 592 (Nat.le_refl _) (by lit_omega)) hd (by decide), h1],
    by rw [hf.readW (c 600 (by lit_omega) (by lit_omega)) hd (by decide), h2],
    by rw [hf.readW (c 608 (by lit_omega) (by lit_omega)) hd (by decide), h3],
    by rw [hf.readW (c 616 (by lit_omega) (by lit_omega)) hd (by decide), h4],
    by rw [hf.readW (c 624 (by lit_omega) (by lit_omega)) hd (by decide), h5]⟩

/-- The working space: `ctx[64, 1024)`. -/
abbrev workR (s₀ : State) : Region := sub s₀ 64 960

/-- What holds between the parts of the code. -/
structure Inv (s₀ : State) (s : State) : Prop where
  r15 : s.gpr .r15 = cx s₀
  r14 : s.gpr .r14 = dp s₀
  r13 : s.gpr .r13 = s₀.gpr .r8
  r12 : s.gpr .r12 = s₀.gpr .r12
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  frame : Frame [workR s₀, dR s₀, stkR s₀] s₀.mem s.mem

/-! ## Pointers -/

set_option simprocs false in
theorem ptr_ok (d r : Reg) {k : Nat} (hk : k < 2 ^ 31) (s : State) :
    WP isa (.block (ptr d r k)) s fun s' =>
      s'.gpr d = off (s.gpr r) k ∧ (∀ q, q ≠ d → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ptr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, se_ofNat hk]
  exact ⟨by rw [off_eq], fun q hq => by simp [hq], trivial⟩

set_option simprocs false in
theorem anchor_ok (r : Reg) {k : Nat} (hk : k < 2 ^ 31) (s : State) :
    WP isa (.block (anchor r k)) s fun s' =>
      s'.gpr .r15 = s.gpr r - BitVec.ofNat 64 k ∧ (∀ q, q ≠ .r15 → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [anchor, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, se_ofNat hk]
  exact ⟨trivial, fun q hq => by simp [hq], trivial⟩

theorem off_sub (p : Addr) (k : Nat) : off p k - BitVec.ofNat 64 k = p := by
  rw [off_eq]; exact BitVec.add_sub_cancel _ _

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  simp only [off_eq, BitVec.ofNat_add, BitVec.add_assoc]

/-! ## Covering the callees' regions -/

theorem covers_sub {s₀ s : State} (hp : APre s₀) (hwr : s.wr = s₀.wr) (rs : List Region)
    (h : ∀ r ∈ rs, ∃ k, r = sub s₀ k r.len ∧ k + r.len ≤ 1024) : Covers rs s.wr := by
  refine Covers.of_sub fun r hr => ?_
  obtain ⟨k, hrk, hk⟩ := h r hr
  exact ⟨ctxR s₀, by simp [hwr, hp.wr], k, by rw [hrk]; simp [off_eq], hk⟩

theorem covers_left {rs wr : List Region} (rd : List Region) (h : Covers rs wr) : Covers rs (rd ++ wr) :=
  fun a n hi => by
    obtain ⟨r, hr, hc⟩ := h a n hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem covers_nil_append {rs rs' : List Region} (h : Covers rs rs') : Covers ([] ++ rs) rs' := by
  simpa using h

end VG.Proof.ChaCha20Poly1305.X86_64

/-!
# ChaCha20-Poly1305 on x86-64: the prologue

Untrusted: everything here is checked by Lean. Saving the registers, the
ChaCha20 state for counter 0, the one-time key and the Poly1305 state for it.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-! ## Saving the registers -/

theorem saveMoves_eq : save ++ ([.mov .r15 (.reg .rdi), .mov .rbx (.reg .rsi), .mov .rbp (.reg .rdx),
    .mov .r14 (.reg .rcx), .mov .r13 (.reg .r8)] : List Instr) =
    [.store (at_ .rdi 592) .rbx, .store (at_ .rdi 600) .rbp, .store (at_ .rdi 608) .r13,
     .store (at_ .rdi 616) .r14, .store (at_ .rdi 624) .r15,
     .mov .r15 (.reg .rdi), .mov .rbx (.reg .rsi), .mov .rbp (.reg .rdx),
     .mov .r14 (.reg .rcx), .mov .r13 (.reg .r8)] := rfl

theorem readW64_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 :=
  Mem.readW_writeW_sep (VG.Proof.ChaCha20.X86_64.off_sep p hd he (by lit_omega) (by lit_omega) h) (by decide)

set_option simprocs false in
theorem saveMoves_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.block (save ++ ([.mov .r15 (.reg .rdi), .mov .rbx (.reg .rsi), .mov .rbp (.reg .rdx),
      .mov .r14 (.reg .rcx), .mov .r13 (.reg .r8)] : List Instr))) s₀ fun s =>
      s.gpr .r15 = cx s₀ ∧ s.gpr .rbx = ad s₀ ∧ s.gpr .rbp = s₀.gpr .rdx ∧ s.gpr .r14 = dp s₀ ∧
      s.gpr .r13 = s₀.gpr .r8 ∧ (∀ r, r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r14 → r ≠ .r13 →
        s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
      Frame [sub s₀ 592 40] s₀.mem s.mem ∧ Saved s₀ s.mem := by
  have o0 := hp.in_ctx (a := 592) (w := 8) (by lit_omega)
  have o1 := hp.in_ctx (a := 600) (w := 8) (by lit_omega)
  have o2 := hp.in_ctx (a := 608) (w := 8) (by lit_omega)
  have o3 := hp.in_ctx (a := 616) (w := 8) (by lit_omega)
  have o4 := hp.in_ctx (a := 624) (w := 8) (by lit_omega)
  simp only [off] at o0 o1 o2 o3 o4
  apply WP.of_runBlock
  rw [saveMoves_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc, State.store64, State.setReg, o0, o1, o2, o3, o4, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, fun r h₁ h₂ h₃ h₄ h₅ => by simp [h₁, h₂, h₃, h₄, h₅],
    trivial, trivial, ?_, ?_⟩
  · have c : ∀ d, 592 ≤ d → d + 8 ≤ 632 → (sub s₀ 592 40).Contains (off (cx s₀) d) (64 / 8) :=
      fun d h₁ h₂ => contains_sub s₀ h₁ h₂ (by lit_omega)
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 592 (Nat.le_refl _) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 600 (by lit_omega) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 608 (by lit_omega) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 616 (by lit_omega) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 624 (by lit_omega) (by lit_omega))
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (config := {decide := true}) only [off, Mem.readW_writeW_self64, readW64_off]

/-! ## The ChaCha20 state -/

/-- The word `stW k` stores, from memory `m` and the context `c`. -/
def wordOf (m : Mem) (c : Addr) (k : Nat) : BitVec 32 :=
  if k < 4 then [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574].getD k 0
  else if k < 12 then m.readW (off c (4 * (k - 4))) 32
  else if k = 12 then 0
  else m.readW (off c (32 + 4 * (k - 13))) 32

/-- The context may be read and written. -/
def CtxOk (c : Addr) (s : State) : Prop :=
  ∀ a w, a + w ≤ 1024 → InRegions (s.rd ++ s.wr) (off c a) w ∧ InRegions s.wr (off c a) w

set_option simprocs false in
theorem stW_ok {c : Addr} {k : Nat} (hk : k < 16) {s : State} (hr15 : s.gpr .r15 = c) (hc : CtxOk c s) :
    WP isa (.block (stW k)) s fun s' =>
      s'.mem = s.mem.writeW (off c (64 + 4 * k)) (wordOf s.mem c k) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o := (hc (64 + 4 * k) 4 (by lit_omega)).2
  simp only [off] at o
  unfold stW stSrc wordOf
  split_ifs with h₁ h₂ h₃
  · apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
      readSrc32, State.store32, State.setReg32, State.setReg, hr15, o, ite_true, ite_false,
      Option.map_some, Option.some.injEq, exists_eq_left', BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq]
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  · have i := (hc (4 * (k - 4)) 4 (by lit_omega)).1
    simp only [off] at i
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
      readSrc32, State.load32, State.store32, State.setReg32, State.setReg, hr15, o, i, ite_true,
      ite_false, Option.map_some, Option.some.injEq, exists_eq_left', BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq]
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  · apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
      readSrc32, State.store32, State.setReg32, State.setReg, hr15, o, ite_true, ite_false,
      Option.map_some, Option.some.injEq, exists_eq_left', BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq]
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  · have i := (hc (32 + 4 * (k - 13)) 4 (by lit_omega)).1
    simp only [off] at i
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
      readSrc32, State.load32, State.store32, State.setReg32, State.setReg, hr15, o, i, ite_true,
      ite_false, Option.map_some, Option.some.injEq, exists_eq_left', BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq]
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩

theorem readW32_off (m : Mem) (p : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 32 = m.readW (off p d) 32 :=
  VG.Proof.ChaCha20.X86_64.readW_writeW_off m p v (Or.inl rfl) hd he h

/-- The context's words `[a, a + 4)` outside `[64, 64 + n)`. -/
theorem readW_frame_ctx {c : Addr} {m m' : Mem} {n : Nat} (hf : Frame [⟨off c 64, n⟩] m m') {a : Nat}
    (ha : a + 4 ≤ 64) (hn : n ≤ 960) : m'.readW (off c a) 32 = m.readW (off c a) 32 := by
  refine hf.readW (r := ⟨off c a, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq, off_eq]
  exact Offset.disjoint c (.inl ha) (by lit_omega) (by lit_omega)

theorem wordOf_frame {c : Addr} {m m' : Mem} {n : Nat} (hf : Frame [⟨off c 64, n⟩] m m') (hn : n ≤ 960)
    {k : Nat} (hk : k < 16) : wordOf m' c k = wordOf m c k := by
  unfold wordOf
  split_ifs <;> [rfl; exact readW_frame_ctx hf (by lit_omega) hn; rfl; exact readW_frame_ctx hf (by lit_omega) hn]

theorem initState_step (j : Nat) : (List.range (j + 1)).flatMap stW = (List.range j).flatMap stW ++ stW j := by
  simp [List.range_succ, List.flatMap_append]

/-- The first `j` words of the ChaCha20 state. -/
theorem initState_ok {c : Addr} {j : Nat} (hj : j ≤ 16) {s : State} (hr15 : s.gpr .r15 = c)
    (hc : CtxOk c s) :
    WP isa (.block ((List.range j).flatMap stW)) s fun s' =>
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨off c 64, 4 * j⟩] s.mem s'.mem ∧
      ∀ i < j, s'.mem.readW (off c (64 + 4 * i)) 32 = wordOf s.mem c i := by
  induction j with
  | zero =>
    exact WP.block_nil (M := isa) ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by lit_omega)⟩
  | succ j ih =>
    rw [initState_step]
    refine WP.block_append (WP.mono (ih (by lit_omega)) fun s₁ ⟨g₁, rd₁, wr₁, f₁, w₁⟩ => ?_)
    have hc₁ : CtxOk c s₁ := by rw [CtxOk, rd₁, wr₁]; exact hc
    refine WP.mono (stW_ok (by lit_omega) (by rw [g₁ _ (by decide), hr15]) hc₁) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_
    refine ⟨fun r hr => by rw [g₂ r hr, g₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_, fun i hi => ?_⟩
    · rw [m₂]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by lit_omega)
      · simp only [off_eq]
        exact Offset.contains c (by lit_omega) (by lit_omega) (by lit_omega)
    · rw [m₂, wordOf_frame f₁ (by lit_omega) (by lit_omega)]
      by_cases h : i = j
      · subst h; exact Mem.readW_writeW_self32 _ _ _
      · rw [readW32_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega)]
        exact w₁ i (by lit_omega)

theorem consts_eq : ∀ i < 4, ([0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] : List (BitVec 32)).getD i 0 =
    Spec.ChaCha20.constants.getD i 0 := by decide

/-- The words stored are the initial ChaCha20 state for the key, counter 0
and the nonce. -/
theorem stateAt_initState {s₀ : State} {m₁ m' : Mem} (hf₁ : Frame [sub s₀ 592 40] s₀.mem m₁)
    (hw : ∀ i < 16, m'.readW (off (cx s₀) (64 + 4 * i)) 32 = wordOf m₁ (cx s₀) i) :
    stateAt m' (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
  have r₁ : ∀ a, a + 4 ≤ 44 → m₁.readW (off (cx s₀) a) 32 = s₀.mem.readW (off (cx s₀) a) 32 := by
    intro a ha
    refine hf₁.readW (r := sub s₀ a 4) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  apply Vector.ext
  intro i hi
  simp only [stateAt, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  rw [show off (cx s₀) 64 + BitVec.ofNat 64 (4 * i) = off (cx s₀) (64 + 4 * i) by
    simp only [off_eq, BitVec.ofNat_add, BitVec.add_assoc], hw i hi]
  unfold wordOf
  split_ifs with h₁ h₂ h₃
  · exact consts_eq i h₁
  · rw [r₁ _ (by lit_omega), show (K s₀) = Spec.ChaCha20.bytesAt s₀.mem (cx s₀) 32 from rfl,
      wordLE_bytesAt s₀.mem (cx s₀) (n := 32) (j := i - 4) (by lit_omega), off_eq]
  · rfl
  · rw [r₁ _ (by lit_omega)]
    rw [show (N s₀) = Spec.ChaCha20.bytesAt s₀.mem (cx s₀ + 32) 12 from rfl,
      wordLE_bytesAt s₀.mem (cx s₀ + 32) (n := 12) (j := i - 13) (by lit_omega), off_eq]
    congr 1
    rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl

/-- The first `n ≤ 64` bytes of a ChaCha20 state in memory. -/
theorem bytesAt_serialize (m : Mem) (p : Addr) {n : Nat} (hn : n ≤ 64) :
    bytesAt m p n = (Spec.ChaCha20.serialize (stateAt m p)).take n := by
  apply List.ext_getElem
  · simp [bytesAt, VG.Proof.ChaCha20.length_serialize]; omega
  · intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    have e := VG.Proof.ChaCha20.serialize_stateAt m p (i := i) (by lit_omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [VG.Proof.ChaCha20.length_serialize]; omega), Option.getD_some] at e
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, e]

/-! ## The whole prologue -/

/-- After the prologue. -/
structure PostP (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  rbx : s.gpr .rbx = ad s₀
  rbp : s.gpr .rbp = s₀.gpr .rdx
  fine : Frame [workR s₀, stkR s₀] s₀.mem s.mem
  poly : Repr s.mem (off (cx s₀) 448) (otk s₀) []
  st : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)

theorem B1_eq : save ++ ([.mov .r15 (.reg .rdi), .mov .rbx (.reg .rsi), .mov .rbp (.reg .rdx),
    .mov .r14 (.reg .rcx), .mov .r13 (.reg .r8)] : List Instr) ++ initState ++ ptr .rdi .r15 64 ++ ptr .rsi .r15 128 =
    (save ++ ([.mov .r15 (.reg .rdi), .mov .rbx (.reg .rsi), .mov .rbp (.reg .rdx),
    .mov .r14 (.reg .rcx), .mov .r13 (.reg .r8)] : List Instr)) ++ (initState ++ (ptr .rdi .r15 64 ++ ptr .rsi .r15 128)) := by
  simp only [List.append_assoc]

theorem B3_eq : anchor .rsi 128 ++ ptr .rdi .r15 448 ++ ptr .rsi .r15 128 =
    anchor .rsi 128 ++ (ptr .rdi .r15 448 ++ ptr .rsi .r15 128) := by
  simp only [List.append_assoc]

theorem prologue_eq : prologue =
    .seq (.block (save ++ ([.mov .r15 (.reg .rdi), .mov .rbx (.reg .rsi), .mov .rbp (.reg .rdx),
      .mov .r14 (.reg .rcx), .mov .r13 (.reg .r8)] : List Instr) ++ initState ++ ptr .rdi .r15 64 ++ ptr .rsi .r15 128))
    (.seq (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block)
    (.seq (.block (anchor .rsi 128 ++ ptr .rdi .r15 448 ++ ptr .rsi .r15 128))
    (.seq (.call "vg_poly1305_init" Impl.Poly1305.X86_64.init) (.block (anchor .rdi 448))))) := rfl

theorem prologue_ok {s₀ : State} (hp : APre s₀) : WP isa prologue s₀ (PostP s₀) := by
  rw [prologue_eq, B1_eq]
  -- The registers, the saved ones, the ChaCha20 state and the pointers.
  refine WP.seq (WP.block_append (WP.mono (saveMoves_ok hp)
    fun s₁ ⟨e15, ebx, ebp, e14, e13, g₁, rd₁, wr₁, f₁, sv₁⟩ => ?_))
  have hc₁ : CtxOk (cx s₀) s₁ := fun a w h => by
    rw [rd₁, wr₁]; exact ⟨hp.in_ctx' h, hp.in_ctx h⟩
  refine WP.block_append (WP.mono (initState_ok (j := 16) (Nat.le_refl _) e15 hc₁)
    fun s₂ ⟨g₂, rd₂, wr₂, f₂, w₂⟩ => ?_)
  refine WP.block_append (WP.mono (ptr_ok .rdi .r15 (k := 64) (by lit_omega) s₂)
    fun s₃ ⟨e3, g₃, rd₃, wr₃, m₃⟩ => ?_)
  refine WP.mono (ptr_ok .rsi .r15 (k := 128) (by lit_omega) s₃) fun s₄ ⟨e4, g₄, rd₄, wr₄, m₄⟩ => ?_
  have r15₂ : s₂.gpr .r15 = cx s₀ := by rw [g₂ _ (by decide), e15]
  have r15₃ : s₃.gpr .r15 = cx s₀ := by rw [g₃ _ (by decide), r15₂]
  have rdi₄ : s₄.gpr .rdi = off (cx s₀) 64 := by rw [g₄ _ (by decide), e3, r15₂]
  have rsi₄ : s₄.gpr .rsi = off (cx s₀) 128 := by rw [e4, r15₃]
  have gg : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → s₄.gpr r = s₁.gpr r := fun r h₁ h₂ h₃ => by
    rw [g₄ r h₃, g₃ r h₂, g₂ r h₁]
  have rsp₄ : s₄.gpr .rsp = s₀.gpr .rsp := by
    rw [gg _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)]
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃, rd₂, rd₁]
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  have mm₄ : s₄.mem = s₂.mem := by rw [m₄, m₃]
  have st₄ : stateAt s₄.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [mm₄]; exact stateAt_initState f₁ w₂
  -- The block for counter 0: the one-time key.
  refine WP.seq (block_call rdi₄ rsi₄ (sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
    (by rw [rsp₄]; exact hp.below8_sub (by lit_omega)) (by rw [rsp₄]; exact hp.below8_sub (by lit_omega))
    (covers_left _ (covers_sub hp wr₄' _ (by
      intro r hr; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨64, rfl, show 64 + 64 ≤ 1024 by omega⟩
      · exact ⟨128, rfl, show 128 + 256 ≤ 1024 by omega⟩)))
    (covers_sub hp wr₄' _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ⟨128, rfl, show 128 + 256 ≤ 1024 by omega⟩))
    fun s₅ rd₅ wr₅ cs₅ f₅ rsi₅ blk₅ => ?_)
  rw [rsp₄] at f₅
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by rw [cs₅ _ (by simp [calleeSaved]), rsp₄]
  -- The pointers for the Poly1305 state.
  rw [B3_eq]
  refine WP.seq (WP.block_append (WP.mono (anchor_ok .rsi (k := 128) (by lit_omega) s₅)
    fun s₆ ⟨e6, g₆, rd₆, wr₆, m₆⟩ => ?_))
  have r15₆ : s₆.gpr .r15 = cx s₀ := by rw [e6, rsi₅, off_sub]
  refine WP.block_append (WP.mono (ptr_ok .rdi .r15 (k := 448) (by lit_omega) s₆)
    fun s₇ ⟨e7, g₇, rd₇, wr₇, m₇⟩ => ?_)
  refine WP.mono (ptr_ok .rsi .r15 (k := 128) (by lit_omega) s₇) fun s₈ ⟨e8, g₈, rd₈, wr₈, m₈⟩ => ?_
  have rdi₈ : s₈.gpr .rdi = off (cx s₀) 448 := by rw [g₈ _ (by decide), e7, r15₆]
  have rsi₈ : s₈.gpr .rsi = off (cx s₀) 128 := by rw [e8, g₇ _ (by decide), r15₆]
  have g₈' : ∀ r, r ≠ .r15 → r ≠ .rdi → r ≠ .rsi → s₈.gpr r = s₅.gpr r := fun r h₁ h₂ h₃ => by
    rw [g₈ r h₃, g₇ r h₂, g₆ r h₁]
  have rsp₈ : s₈.gpr .rsp = s₀.gpr .rsp := by rw [g₈' _ (by decide) (by decide) (by decide), rsp₅]
  have wr₈' : s₈.wr = s₀.wr := by rw [wr₈, wr₇, wr₆, wr₅, wr₄']
  have mm₈ : s₈.mem = s₅.mem := by rw [m₈, m₇, m₆]
  -- The Poly1305 state for the one-time key.
  refine WP.seq (init_call rdi₈ rsi₈ (sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
    (by rw [rsp₈]; exact hp.below8_sub (by lit_omega)) (by rw [rsp₈]; exact hp.below8_sub (by lit_omega))
    (covers_left _ (covers_sub hp wr₈' _ (by
      intro r hr; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨128, rfl, show 128 + 32 ≤ 1024 by omega⟩
      · exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩)))
    (covers_sub hp wr₈' _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩))
    fun s₉ rd₉ wr₉ cs₉ f₉ rdi₉ repr₉ => ?_)
  rw [rsp₈] at f₉
  refine WP.mono (anchor_ok .rdi (k := 448) (by lit_omega) s₉) fun s₁₀ ⟨e10, g₁₀, rd₁₀, wr₁₀, m₁₀⟩ => ?_
  -- The registers.
  have cs : ∀ r ∈ calleeSaved, r ≠ .r15 → s₁₀.gpr r = s₁.gpr r := fun r hr h15 => by
    have h' : r ≠ .rax ∧ r ≠ .rdi ∧ r ≠ .rsi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₁₀ r h15, cs₉ r hr, g₈' r h15 h'.2.1 h'.2.2, cs₅ r hr, gg r h'.1 h'.2.1 h'.2.2]
  -- The memory.
  have sub1 : ∀ {k n : Nat}, 64 ≤ k → k + n ≤ 1024 → Region.Sub (sub s₀ k n) (workR s₀) :=
    fun h₁ h₂ => sub_sub s₀ h₁ (by lit_omega) (by lit_omega)
  have fr : ∀ {k n : Nat} {m m' : Mem}, 64 ≤ k → k + n ≤ 1024 →
      Frame [sub s₀ k n, below (s₀.gpr .rsp) 8] m m' → Frame [workR s₀, stkR s₀] m m' :=
    fun h₁ h₂ hf => hf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨workR s₀, by simp, sub1 h₁ h₂⟩
      · exact ⟨stkR s₀, by simp, below8_stk s₀⟩
  have ff : Frame [workR s₀, stkR s₀] s₀.mem s₁₀.mem := by
    rw [m₁₀]
    refine (f₁.sub fun r hr => ?_).trans ((f₂.sub fun r hr => ?_).trans (?_ : Frame _ s₂.mem s₉.mem))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨workR s₀, by simp, sub1 (by lit_omega) (by lit_omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s₀, by simp, sub1 (k := 64) (n := 64) (by lit_omega) (by lit_omega)⟩
    · rw [← mm₄]; refine (fr (k := 128) (n := 256) (by lit_omega) (by lit_omega) f₅).trans ?_
      rw [← mm₈]; exact fr (k := 448) (n := 128) (by lit_omega) (by lit_omega) f₉
  have d_st : ∀ {k n : Nat}, 64 + 64 ≤ k → k + n ≤ 1024 → ∀ r ∈ [sub s₀ k n, below (s₀.gpr .rsp) 8],
      (⟨off (cx s₀) 64, 64⟩ : Region).Disjoint r := by
    intro k n h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact (hp.below8_sub (by lit_omega)).symm
  have d_sv : ∀ {k n : Nat}, k + n ≤ 592 → ∀ r ∈ [sub s₀ k n, below (s₀.gpr .rsp) 8],
      (sub s₀ 592 40).Disjoint r := by
    intro k n h₁ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact (hp.below8_sub (by lit_omega)).symm
  have st₉ : stateAt s₉.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame f₉ (d_st (k := 448) (by lit_omega) (by lit_omega)), mm₈,
      stateAt_frame f₅ (d_st (k := 128) (by lit_omega) (by lit_omega)), st₄]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, by rw [rd₁₀, rd₉, rd₈, rd₇, rd₆, rd₅, rd₄'],
    by rw [wr₁₀, wr₉, wr₈'], ?_, ff.sub fun r hr => ?_⟩, ?_, ?_, ff, ?_, ?_⟩
  · rw [e10, rdi₉, off_sub]
  · rw [cs .r14 (by simp [calleeSaved]) (by decide), e14]
  · rw [cs .r13 (by simp [calleeSaved]) (by decide), e13]
  · rw [cs .r12 (by simp [calleeSaved]) (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)]
  · rw [g₁₀ _ (by decide), cs₉ _ (by simp [calleeSaved]), rsp₈]
  · rw [m₁₀]
    rw [mm₄] at f₅
    refine (((sv₁.frame f₂ ?_).frame f₅ (d_sv (k := 128) (n := 256) (by lit_omega))).frame ?_
      (d_sv (k := 448) (n := 128) (by lit_omega)))
    · simp only [List.mem_singleton, forall_eq]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · rw [← mm₈]; exact f₉
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · rw [cs .rbx (by simp [calleeSaved]) (by decide), ebx]
  · rw [cs .rbp (by simp [calleeSaved]) (by decide), ebp]
  · rw [m₁₀]
    have hk : bytesAt s₈.mem (off (cx s₀) 128) 32 = otk s₀ := by
      rw [mm₈, bytesAt_serialize _ _ (by lit_omega), blk₅, st₄]; rfl
    rw [← hk]; exact repr₉
  · rw [m₁₀]; exact st₉

end VG.Proof.ChaCha20Poly1305.X86_64

/-!
# ChaCha20-Poly1305 on x86-64: absorbing padded data

Untrusted: everything here is checked by Lean. `macPad p n` absorbs the `n`
bytes at `p` into the Poly1305 state, and zeros to a multiple of 16:
`msg ++ x ++ pad16 x`.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20Poly1305 (pad16)

/-- The registers `macPad` may take its arguments in. -/
def MacRegs (p n : Reg) : Prop := (p = .rbx ∨ p = .r14) ∧ (n = .rbp ∨ n = .r13)

/-- What `macPad` needs of the bytes it absorbs. -/
structure Src (s₀ : State) (P : Addr) (len : Nat) : Prop where
  lt : len < 2 ^ 64
  wrap : P.toNat + len ≤ 2 ^ 64
  ctx : (ctxR s₀).Disjoint ⟨P, len⟩
  stk : (stkR s₀).Disjoint ⟨P, len⟩
  cov : Covers [⟨P, len⟩] (s₀.rd ++ s₀.wr)

theorem contains_off_sub {P : Addr} {a n len w : Nat} {x : Addr} (h : a + n ≤ len)
    (hc : (⟨P + BitVec.ofNat 64 a, n⟩ : Region).Contains x w) : (⟨P, len⟩ : Region).Contains x w := by
  simp only [Region.Contains] at *
  have : (x - P).toNat ≤ (x - (P + BitVec.ofNat 64 a)).toNat + a := by
    rw [show x - P = (x - (P + BitVec.ofNat 64 a)) + BitVec.ofNat 64 a by
      rw [Offset.sub_add_eq, BitVec.sub_add_cancel],
      BitVec.toNat_add, BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega

theorem Src.cov_sub {s₀ : State} {P : Addr} {len : Nat} (hs : Src s₀ P len) {a n : Nat} (h : a + n ≤ len)
    {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    Covers [⟨P + BitVec.ofNat 64 a, n⟩] (s.rd ++ s.wr) := by
  intro x w ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  rw [hrd, hwr]
  exact hs.cov x w ⟨_, List.mem_singleton_self _, contains_off_sub h hc⟩

theorem Src.disj_sub {P : Addr} {len : Nat} {R : Region} (hd : R.Disjoint ⟨P, len⟩) {a n : Nat}
    (h : a + n ≤ len) : R.Disjoint ⟨P + BitVec.ofNat 64 a, n⟩ :=
  fun x h₁ h₂ => hd x h₁ (contains_off_sub h h₂)

set_option simprocs false in
theorem macA_ok {p n : Reg} (hr : MacRegs p n) (s : State) :
    WP isa (.block (ptr .rdi .r15 448 ++ ([.mov .rsi (.reg p), .mov .rdx (.reg n), .shift .shr .rdx 4] : List Instr))) s
      fun s' => s'.gpr .rdi = off (s.gpr .r15) 448 ∧ s'.gpr .rsi = s.gpr p ∧
        s'.gpr .rdx = s.gpr n >>> 4 ∧ (∀ q, q ≠ .rdi → q ≠ .rsi → q ≠ .rdx → s'.gpr q = s.gpr q) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  obtain ⟨hp, hn⟩ := hr
  refine WP.block_append (WP.mono (ptr_ok .rdi .r15 (k := 448) (by lit_omega) s)
    fun s₁ ⟨e1, g₁, rd₁, wr₁, m₁⟩ => ?_)
  have hp₁ : s₁.gpr p = s.gpr p := g₁ p (by rcases hp with rfl | rfl <;> decide)
  have hn₁ : s₁.gpr n = s.gpr n := g₁ n (by rcases hn with rfl | rfl <;> decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execShift, State.setReg, State.setFlags, Option.map_some, Option.some.injEq, exists_eq_left',
    ite_true, ite_false]
  have hpd : p ≠ .rdx := by rcases hp with rfl | rfl <;> decide
  have hnd : n ≠ .rsi := by rcases hn with rfl | rfl <;> decide
  refine ⟨by simp [e1], by simp [hp₁], by simp [hnd, hn₁], fun q h₁ h₂ h₃ => by simp [h₂, h₃, g₁ q h₁],
    rd₁, wr₁, m₁⟩

set_option simprocs false in
theorem macC_ok {p n : Reg} (hr : MacRegs p n) (s : State) :
    WP isa (.block (anchor .rdi 448 ++ ([.mov .rdx (.reg n), .alu .and .rdx (.imm 15)] : List Instr))) s
      fun s' => s'.gpr .r15 = s.gpr .rdi - BitVec.ofNat 64 448 ∧ s'.gpr .rdx = s.gpr n &&& 15 ∧
        s'.zf = some (s.gpr n &&& 15 == 0) ∧
        (∀ q, q ≠ .r15 → q ≠ .rdx → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  obtain ⟨hp, hn⟩ := hr
  refine WP.block_append (WP.mono (anchor_ok .rdi (k := 448) (by lit_omega) s)
    fun s₁ ⟨e1, g₁, rd₁, wr₁, m₁⟩ => ?_)
  have hn₁ : s₁.gpr n = s.gpr n := g₁ n (by rcases hn with rfl | rfl <;> decide)
  have se15 : BitVec.signExtend 64 (15 : BitVec 32) = 15 := by decide
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, ite_false, se15]
  have hnd : n ≠ .rdx := by rcases hn with rfl | rfl <;> decide
  refine ⟨by simp [e1], by simp [hn₁], by simp [hn₁], fun q h₁ h₂ => by simp [h₂, g₁ q h₁],
    rd₁, wr₁, m₁⟩

set_option simprocs false in
theorem macD_ok {p n : Reg} (hr : MacRegs p n) (s : State) :
    WP isa (.block [.mov .rsi (.reg n), .alu .sub .rsi (.reg .rdx), .alu .add .rsi (.reg p)]) s
      fun s' => s'.gpr .rsi = s.gpr n - s.gpr .rdx + s.gpr p ∧
        (∀ q, q ≠ .rsi → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  obtain ⟨hp, hn⟩ := hr
  have hps : p ≠ .rsi := by rcases hp with rfl | rfl <;> decide
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, ite_false, hps]
  exact ⟨trivial, fun q hq => by simp [hq], trivial⟩

theorem se0' : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide

set_option simprocs false in
/-- Zeroing the padded block. -/
theorem padZ_ok {s₀ : State} (hp : APre s₀) {s : State} (hr15 : s.gpr .r15 = cx s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (at_ .r15 576) .rax, .store (at_ .r15 584) .rax,
      .mov32 .rcx (.imm 0)]) s fun s' =>
      s'.gpr .rcx = 0 ∧ (∀ q, q ≠ .rax → q ≠ .rcx → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [sub s₀ 576 16] s.mem s'.mem ∧ ∀ j < 16, s'.mem (off (cx s₀) (576 + j)) = 0 := by
  have o0 := hp.in_ctx (a := 576) (w := 8) (by lit_omega)
  have o1 := hp.in_ctx (a := 584) (w := 8) (by lit_omega)
  rw [← hwr] at o0 o1
  simp only [off] at o0 o1
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc32, State.store64, State.setReg, State.setReg32, hr15, o0, o1, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun q h₁ h₂ => by simp [h₁, h₂], trivial, trivial, ?_, fun j hj => ?_⟩
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  · have z : (BitVec.setWidth 64 (0 : BitVec 32)) = 0 := rfl
    simp only [z]
    rw [VG.Proof.Poly1305.writeW64_zero_apply, VG.Proof.Poly1305.writeW64_zero_apply]
    have e : ∀ d, d ≤ 576 + j → (off (cx s₀) (576 + j) - (cx s₀ + BitVec.ofInt 64 (d : Int))).toNat = 576 + j - d := by
      intro d hd
      rw [show cx s₀ + BitVec.ofInt 64 (d : Int) = off (cx s₀) d from rfl, off_eq, off_eq]
      exact Offset.sub_toNat _ hd (by lit_omega)
    by_cases h : 8 ≤ j
    · rw [e 584 (by lit_omega)]
      simp only [show 576 + j - 584 < 8 by omega, ite_true]
    · have w : ¬ (off (cx s₀) (576 + j) - (cx s₀ + BitVec.ofInt 64 ((584 : Nat) : Int))).toNat < 8 := by
        rw [show cx s₀ + BitVec.ofInt 64 ((584 : Nat) : Int) = off (cx s₀) 584 from rfl, off_eq, off_eq,
          Offset.sub_toNat' _ (by lit_omega) (by lit_omega)]
        split <;> omega
      simp only [w, ite_false, e 576 (by lit_omega), show 576 + j - 576 < 8 by omega, ite_true]

/-! ## Copying the last bytes -/

/-- Before byte `i` of the last `t` bytes at `Q` is copied into the padded
block, from the state `s₂` after the block was zeroed. -/
structure CpInv (s₀ s₂ : State) (Q : Addr) (i : Nat) (s : State) : Prop where
  rcx : s.gpr .rcx = BitVec.ofNat 64 i
  keep : ∀ r, r ≠ .rax → r ≠ .rcx → s.gpr r = s₂.gpr r
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame [sub s₀ 576 16] s₂.mem s.mem
  buf : ∀ j < 16, s.mem (off (cx s₀) (576 + j)) = if j < i then s₂.mem (Q + BitVec.ofNat 64 j) else 0

def copyBody : List Instr :=
  [.movzx8 .rax tailByte, .store8 padByte .rax, .alu .add .rcx (.imm 1), .alu .cmp .rcx (.reg .rdx)]

theorem se1' : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

set_option simprocs false in
theorem copy_step {s₀ : State} (hp : APre s₀) {s₂ : State} {Q : Addr} {t : Nat} (ht : t < 16)
    (hrsi : s₂.gpr .rsi = Q) (hrdx : s₂.gpr .rdx = BitVec.ofNat 64 t) (hr15 : s₂.gpr .r15 = cx s₀)
    (hwr : s₂.wr = s₀.wr) (hsrc : ∀ j < t, InRegions (s₂.rd ++ s₂.wr) (Q + BitVec.ofNat 64 j) 1)
    (hdisj : ∀ j < t, ∀ r ∈ [sub s₀ 576 16], (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint r)
    {i : Nat} (hi : i < t) {s : State} (h : CpInv s₀ s₂ Q i s) :
    WP isa (.block copyBody) s fun s' =>
      CpInv s₀ s₂ Q (i + 1) s' ∧ s'.zf = some (decide (i + 1 = t)) := by
  have hrsi' : s.gpr .rsi = Q := by rw [h.keep _ (by decide) (by decide), hrsi]
  have hrdx' : s.gpr .rdx = BitVec.ofNat 64 t := by rw [h.keep _ (by decide) (by decide), hrdx]
  have hr15' : s.gpr .r15 = cx s₀ := by rw [h.keep _ (by decide) (by decide), hr15]
  have ea1 : Q + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = Q + BitVec.ofNat 64 i := by simp
  have ea2 : cx s₀ + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 576 = off (cx s₀) (576 + i) := by
    rw [BitVec.mul_one, off_eq, show BitVec.ofInt 64 576 = BitVec.ofNat 64 576 by decide, BitVec.ofNat_add,
      BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 i)]
  have hin : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 i) 1 := by rw [h.rd, h.wr]; exact hsrc i hi
  have hout : InRegions s.wr (off (cx s₀) (576 + i)) 1 := by rw [h.wr, hwr]; exact hp.in_ctx (by lit_omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [copyBody, tailByte, padByte, runBlock_cons, runStep_some,
    runBlock_nil, exec, State.ea, readSrc, execAlu, arithFlags, State.load8, State.store8, State.setReg,
    State.setFlags, hrsi', hr15', h.rcx, ea1, ea2, hin, hout, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', se1']
  -- The byte copied is byte `i` of the tail, unchanged since `s₂`.
  have hbyte : s.mem (Q + BitVec.ofNat 64 i) = s₂.mem (Q + BitVec.ofNat 64 i) :=
    h.frame _ fun r hr hc => hdisj i hi r hr _ (by
      simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
  refine ⟨⟨?_, fun r h₁ h₂ => by simp [h₁, h₂, h.keep r h₁ h₂], h.rd, h.wr, ?_, fun k hk => ?_⟩, ?_⟩
  · simp only [ite_true]; rw [BitVec.ofNat_add]; rfl
  · exact h.frame.writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  · dsimp only
    rw [VG.Proof.ChaCha20.X86_64.Xor.writeW8_apply]
    by_cases hki : k = i
    · subst hki
      simp only [ite_true, show k < k + 1 by omega, BitVec.setWidth_setWidth_of_le _ (by omega :
        8 ≤ 64), BitVec.setWidth_eq, hbyte]
    · have hne : off (cx s₀) (576 + k) ≠ off (cx s₀) (576 + i) := by
        intro he
        rw [off_eq, off_eq] at he
        have := congrArg BitVec.toNat (show BitVec.ofNat 64 (576 + k) = BitVec.ofNat 64 (576 + i) by
          simpa using he)
        rw [toNat_ofNat_lt (by lit_omega), toNat_ofNat_lt (by lit_omega)] at this
        omega
      simp only [hne, ite_false]
      rw [h.buf k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega]
      · simp [hk', show ¬ k < i + 1 by omega]
  · rw [hrdx', show BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) by rw [BitVec.ofNat_add]; rfl]
    by_cases he : i + 1 = t
    · simp [he]
    · have : BitVec.ofNat 64 (i + 1) - BitVec.ofNat 64 t ≠ 0 := by
        intro h0
        have : BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 t := by
          rw [← BitVec.sub_add_cancel (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 t), h0]
          exact BitVec.zero_add _
        have := congrArg BitVec.toNat this
        rw [toNat_ofNat_lt (by lit_omega), toNat_ofNat_lt (by lit_omega)] at this
        exact he this
      simp only [he, decide_false, beq_eq_false_iff_ne, ne_eq]
      exact this

theorem copyLoop_eq : (Code.loop (.block [.movzx8 .rax tailByte, .store8 padByte .rax, .alu .add .rcx (.imm 1),
    .alu .cmp .rcx (.reg .rdx)]) .ne : Prog isa) = .loop (.block copyBody) .ne := rfl

/-- The padded block's bytes. -/
theorem padded_bytes {s₀ : State} {m mz : Mem} {Q : Addr} {t : Nat} (ht : t < 16)
    (h : ∀ j < 16, m (off (cx s₀) (576 + j)) = if j < t then mz (Q + BitVec.ofNat 64 j) else 0) :
    bytesAt m (off (cx s₀) 576) 16 = bytesAt mz Q t ++ List.replicate (16 - t) 0 := by
  apply List.ext_getElem
  · simp [bytesAt]; omega
  · intro k h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [show off (cx s₀) 576 + BitVec.ofNat 64 k = off (cx s₀) (576 + k) by
      rw [off_eq, off_eq, BitVec.ofNat_add, BitVec.add_assoc], h k h₁]
    by_cases hk : k < t
    · rw [List.getElem_append_left (by simp [hk])]
      simp [hk]
    · rw [List.getElem_append_right (by simp; omega)]
      simp [hk]

theorem padE_eq : ptr .rdi .r15 448 ++ ptr .rsi .r15 576 ++ ([.mov32 .rdx (.imm 1)] : List Instr) =
    ptr .rdi .r15 448 ++ (ptr .rsi .r15 576 ++ ([.mov32 .rdx (.imm 1)] : List Instr)) := by simp only [List.append_assoc]

set_option simprocs false in
theorem mov32_rdx_ok (v : BitVec 32) (s : State) :
    WP isa (.block [.mov32 .rdx (.imm v)]) s fun s' =>
      s'.gpr .rdx = v.setWidth 64 ∧ (∀ q, q ≠ .rdx → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32,
    State.setReg32, State.setReg, Option.map_some, Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨trivial, fun q hq => by simp [hq], trivial⟩

theorem padTail_eq (b : Impl.Poly1305.X86_64.Blocks) : padTail b =
    .seq (.block [.mov32 .rax (.imm 0), .store (at_ .r15 576) .rax, .store (at_ .r15 584) .rax,
      .mov32 .rcx (.imm 0)])
    (.seq (.loop (.block copyBody) .ne)
    (.seq (.block (ptr .rdi .r15 448 ++ (ptr .rsi .r15 576 ++ ([.mov32 .rdx (.imm 1)] : List Instr))))
    (.seq (.call b.name b.code) (.block (anchor .rdi 448))))) := by
  rw [padTail, padE_eq]; rfl

/-- The frame of the Poly1305 state and the padded block, and the calls. -/
abbrev macR (s₀ : State) : List Region := [sub s₀ 448 144, stkR s₀]

theorem sub_mac (s₀ : State) {k n : Nat} (h₁ : 448 ≤ k) (h₂ : k + n ≤ 592) : Region.Sub (sub s₀ k n) (sub s₀ 448 144) :=
  sub_sub s₀ h₁ (by lit_omega) (by lit_omega)

theorem frame_mac {s₀ : State} {k n : Nat} (h₁ : 448 ≤ k) (h₂ : k + n ≤ 592) {m m' : Mem}
    (hf : Frame [sub s₀ k n] m m') : Frame (macR s₀) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, sub_mac s₀ h₁ h₂⟩

theorem frame_mac' {s₀ : State} {k n : Nat} (h₁ : 448 ≤ k) (h₂ : k + n ≤ 592) {m m' : Mem}
    (hf : Frame [sub s₀ k n, below (s₀.gpr .rsp) 16] m m') : Frame (macR s₀) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, sub_mac s₀ h₁ h₂⟩
    · exact ⟨stkR s₀, by simp, below16_stk s₀⟩

theorem calleeSaved_ne {r : Reg} (hr : r ∈ calleeSaved) :
    r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .rdi := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem padTail_ok (b : Impl.Poly1305.X86_64.Blocks) {s₀ : State} (hp : APre s₀) {s : State} {Q : Addr} {t : Nat} (ht0 : 0 < t) (ht : t < 16)
    (hrsi : s.gpr .rsi = Q) (hrdx : s.gpr .rdx = BitVec.ofNat 64 t) (hr15 : s.gpr .r15 = cx s₀)
    (hrsp : s.gpr .rsp = s₀.gpr .rsp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hsrc : ∀ j < t, InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 j) 1)
    (hdisj : ∀ j < t, (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint (sub s₀ 576 16)) :
    WP isa (padTail b) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (macR s₀) s.mem s'.mem ∧ s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ (bytesAt s.mem Q t ++ List.replicate (16 - t) 0)) := by
  rw [padTail_eq]
  refine WP.seq (WP.mono_mx (by decide +kernel) (padZ_ok hp hr15 hwr) fun s₂ ⟨rcx₂, g₂, rd₂, wr₂, f₂, z₂⟩ mx₂ => ?_)
  have hd' : ∀ j < t, ∀ r ∈ [sub s₀ 576 16], (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint r := by
    intro j hj r hr; simp only [List.mem_singleton] at hr; subst hr; exact hdisj j hj
  have src₂ : ∀ j < t, s₂.mem (Q + BitVec.ofNat 64 j) = s.mem (Q + BitVec.ofNat 64 j) := fun j hj =>
    f₂ _ fun r hr hc => hd' j hj r hr _ (by simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
  refine WP.seq (WP.mono_mx (by decide +kernel) (Q := CpInv s₀ s₂ Q t) ?_ fun s₃ h₃ mx₃ => ?_)
  · let Inv : Nat → State → Prop := fun n s => ∃ i, n = t - i ∧ i < t ∧ CpInv s₀ s₂ Q i s
    have hstep : ∀ n s, Inv n s → WP isa (.block copyBody) s (fun s' =>
        (eval .ne s' = some false ∧ CpInv s₀ s₂ Q t s') ∨ (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨i, rfl, hi, hI⟩
      refine WP.mono (copy_step hp ht (by rw [g₂ _ (by decide) (by decide), hrsi])
        (by rw [g₂ _ (by decide) (by decide), hrdx]) (by rw [g₂ _ (by decide) (by decide), hr15])
        (by rw [wr₂, hwr]) (by rw [rd₂, wr₂]; exact hsrc) hd' hi hI) fun s' ⟨h', hz⟩ => ?_
      by_cases hl : i + 1 = t
      · exact .inl ⟨by simp [eval, hz, hl], hl ▸ h'⟩
      · exact .inr ⟨by simp [eval, hz, hl], t - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep t s₂ ⟨0, by simp, ht0, ⟨by rw [rcx₂]; rfl, fun _ _ _ => rfl, rfl, rfl,
      Frame.refl _ _, fun j hj => by simp [z₂ j hj]⟩⟩
  have g₃ : ∀ r, r ≠ .rax → r ≠ .rcx → s₃.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [h₃.keep r h₁ h₂, g₂ r h₁ h₂]
  refine WP.seq (WP.block_append (WP.mono_mx (by decide +kernel) (ptr_ok .rdi .r15 (k := 448) (by lit_omega) s₃)
    fun s₄ ⟨e4, g₄, rd₄, wr₄, m₄⟩ mx₄ => ?_))
  refine WP.block_append (WP.mono_mx (by decide +kernel) (ptr_ok .rsi .r15 (k := 576) (by lit_omega) s₄)
    fun s₅ ⟨e5, g₅, rd₅, wr₅, m₅⟩ mx₅ => ?_)
  refine WP.mono_mx (by decide +kernel) (mov32_rdx_ok 1 s₅) fun s₆ ⟨e6, g₆, rd₆, wr₆, m₆⟩ mx₆ => ?_
  have r15₃ : s₃.gpr .r15 = cx s₀ := by rw [g₃ _ (by decide) (by decide), hr15]
  have rdi₆ : s₆.gpr .rdi = off (cx s₀) 448 := by rw [g₆ _ (by decide), g₅ _ (by decide), e4, r15₃]
  have rsi₆ : s₆.gpr .rsi = off (cx s₀) 576 := by rw [g₆ _ (by decide), e5, g₄ _ (by decide), r15₃]
  have rdx₆ : s₆.gpr .rdx = BitVec.ofNat 64 1 := by rw [e6]; rfl
  have g₆' : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → s₆.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by rw [g₆ r h₅, g₅ r h₄, g₄ r h₃, g₃ r h₁ h₂]
  have rsp₆ : s₆.gpr .rsp = s₀.gpr .rsp := by
    rw [g₆' _ (by decide) (by decide) (by decide) (by decide) (by decide), hrsp]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, rd₄, h₃.rd, rd₂, hrd]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄, h₃.wr, wr₂, hwr]
  have mm₆ : s₆.mem = s₃.mem := by rw [m₆, m₅, m₄]
  refine WP.seq (WP.mono (blocks_call (n := 1) rdi₆ rsi₆ rdx₆ (by lit_omega)
    (sub_disj s₀ (b := 576) (m := 16 * 1) (by lit_omega) (by lit_omega) (by lit_omega))
    (by rw [hp.off_toNat (by lit_omega)]; have := hp.wrap_c; omega)
    (by rw [rsp₆]; exact hp.below16_sub (by lit_omega)) (by rw [rsp₆]; exact hp.below16_sub (by lit_omega))
    (covers_left _ (covers_sub hp wr₆' _ (by
      intro r hr; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨576, rfl, show 576 + 16 * 1 ≤ 1024 by omega⟩
      · exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩)))
    (covers_sub hp wr₆' _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩))
    b) fun s₇ ⟨rd₇, wr₇, cs₇, f₇, rdi₇, repr₇, mx₇⟩ => ?_)
  rw [rsp₆] at f₇
  refine WP.mono_mx (by decide +kernel) (anchor_ok .rdi (k := 448) (by lit_omega) s₇)
    fun s₈ ⟨e8, g₈, rd₈, wr₈, m₈⟩ mx₈ => ?_
  have hframe : Frame (macR s₀) s.mem s₆.mem := by
    rw [mm₆]
    exact (frame_mac (by lit_omega) (by lit_omega) f₂).trans (frame_mac (by lit_omega) (by lit_omega) h₃.frame)
  refine ⟨fun r hr => ?_, by rw [rd₈, rd₇, rd₆', hrd], by rw [wr₈, wr₇, wr₆', hwr], ?_,
    by rw [mx₈, mx₇, mx₆, mx₅, mx₄, mx₃, mx₂], fun key msg hr => ?_⟩
  · by_cases h15 : r = .r15
    · subst h15; rw [e8, rdi₇, off_sub, hr15]
    · have h' := calleeSaved_ne hr
      rw [g₈ r h15, cs₇ r hr, g₆' r h'.1 h'.2.1 h'.2.2.2.2 h'.2.2.2.1 h'.2.2.1]
  · rw [m₈]; exact hframe.trans (frame_mac' (by lit_omega) (by lit_omega) f₇)
  · rw [m₈]
    have f26 : Frame [sub s₀ 576 16] s.mem s₆.mem := by rw [mm₆]; exact f₂.trans h₃.frame
    have hr₆ : Repr s₆.mem (off (cx s₀) 448) key msg := Repr.frame f26 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) hr
    have hb : bytesAt s₆.mem (off (cx s₀) (576 : Nat)) (16 * 1) = bytesAt s.mem Q t ++ List.replicate (16 - t) 0 := by
        rw [mm₆, show 16 * 1 = 16 from rfl, padded_bytes ht h₃.buf]
        congr 1
        simp only [bytesAt]
        apply List.map_congr_left
        intro j hj
        exact src₂ j (List.mem_range.mp hj)
    have := repr₇ key msg hr₆
    rwa [hb] at this

theorem shr4_ofNat {len : Nat} (h : len < 2 ^ 64) : BitVec.ofNat 64 len >>> 4 = BitVec.ofNat 64 (len / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_lt h, toNat_ofNat_lt (by lit_omega), Nat.shiftRight_eq_div_pow]

theorem and15_ofNat {len : Nat} (h : len < 2 ^ 64) : BitVec.ofNat 64 len &&& 15 = BitVec.ofNat 64 (len % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat_lt h, toNat_ofNat_lt (by lit_omega),
    show (15 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem self_contains (a : Addr) : (⟨a, 1⟩ : Region).Contains a 1 := by
  simp only [Region.Contains]; rw [BitVec.sub_self]; simp

/-- The `len` bytes at `P` (in `p` and `n`), padded with zeros, absorbed. -/
theorem macPad_ok (b : Impl.Poly1305.X86_64.Blocks) {s₀ : State} (hp : APre s₀) {p n : Reg} (hr : MacRegs p n) {P : Addr} {len : Nat}
    (hs : Src s₀ P len) {s : State} (hr15 : s.gpr .r15 = cx s₀) (hrsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hP : s.gpr p = P) (hn : s.gpr n = BitVec.ofNat 64 len) :
    WP isa (macPad b p n) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (macR s₀) s.mem s'.mem ∧ s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ (bytesAt s.mem P len ++ pad16 (bytesAt s.mem P len))) := by
  have hpc : p ∈ calleeSaved := by rcases hr.1 with rfl | rfl <;> simp [calleeSaved]
  have hnc : n ∈ calleeSaved := by rcases hr.2 with rfl | rfl <;> simp [calleeSaved]
  have hp15 : p ≠ .r15 := by rcases hr.1 with rfl | rfl <;> decide
  have hn15 : n ≠ .r15 := by rcases hr.2 with rfl | rfl <;> decide
  have hcP : (ctxR s₀).Disjoint ⟨P, len⟩ := hs.ctx
  have hlt := hs.lt
  refine WP.seq (WP.mono_mx (by rcases hr with ⟨rfl | rfl, rfl | rfl⟩ <;> decide +kernel) (macA_ok hr s)
    fun s₁ ⟨rdi₁, rsi₁, rdx₁, g₁, rd₁, wr₁, m₁⟩ mx₁ => ?_)
  have g₁' : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r := fun r h =>
    g₁ r (calleeSaved_ne h).2.2.2.2 (calleeSaved_ne h).2.2.2.1 (calleeSaved_ne h).2.2.1
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [g₁' _ (by simp [calleeSaved]), hrsp]
  have hk : 16 * (len / 16) ≤ len := Nat.mul_div_le _ _
  refine WP.seq (WP.mono (blocks_call (P := off (cx s₀) 448) (p := P) (n := len / 16)
    (by rw [rdi₁, hr15]) (by rw [rsi₁, hP]) (by rw [rdx₁, hn, shr4_ofNat hlt]) (by lit_omega)
    ((hcP.sub_left (sub_ctx s₀ (by lit_omega))).sub_right (Region.sub_prefix hk))
    (by have := hs.wrap; omega)
    (by rw [rsp₁]; exact hp.below16_sub (by lit_omega))
    (by rw [rsp₁]; exact (hs.stk.sub_left (below16_stk s₀)).sub_right (Region.sub_prefix hk))
    (fun a w ⟨r, hr', hc⟩ => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · rw [rd₁, wr₁, hrd, hwr]
        exact hs.cov a w ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
      · refine covers_left _ (covers_sub hp (by rw [wr₁, hwr]) [sub s₀ 448 128] (fun r hr => ?_)) a w
          ⟨_, List.mem_singleton_self _, hc⟩
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩)
    (covers_sub hp (by rw [wr₁, hwr]) _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩))
    b) fun s₂ ⟨rd₂, wr₂, cs₂, f₂, rdi₂, repr₂, mx₂⟩ => ?_)
  rw [rsp₁, m₁] at f₂
  rw [m₁] at repr₂
  refine WP.seq (WP.mono_mx (by rcases hr with ⟨rfl | rfl, rfl | rfl⟩ <;> decide +kernel) (macC_ok hr s₂)
    fun s₃ ⟨r15₃, rdx₃, zf₃, g₃, rd₃, wr₃, m₃⟩ mx₃ => ?_)
  have n₂ : s₂.gpr n = BitVec.ofNat 64 len := by rw [cs₂ n hnc, g₁' n hnc, hn]
  have cs₃ : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := fun r h => by
    by_cases h15 : r = .r15
    · subst h15; rw [r15₃, rdi₂, off_sub, hr15]
    · rw [g₃ r h15 (calleeSaved_ne h).2.2.1, cs₂ r h, g₁' r h]
  have rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂, rd₁]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂, wr₁]
  have hdisjP : ∀ r ∈ [sub s₀ 448 128, below (s₀.gpr .rsp) 16], (⟨P, len⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hcP.sub_left (sub_ctx s₀ (by lit_omega))).symm
    · exact (hs.stk.sub_left (below16_stk s₀)).symm
  have fr₃ : Frame (macR s₀) s.mem s₃.mem := by rw [m₃]; exact frame_mac' (by lit_omega) (by lit_omega) f₂
  have x_eq : bytesAt s.mem P len = bytesAt s.mem P (16 * (len / 16)) ++
      bytesAt s.mem (P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) := by
    rw [← VG.Proof.Poly1305.bytesAt_add, Nat.div_add_mod]
  have hlen : (bytesAt s.mem P len).length = len := VG.Proof.Poly1305.length_bytesAt _ _ _
  have mx₃' : s₃.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by rw [mx₃, mx₂, mx₁]
  refine WP.ite (decide (len % 16 = 0)) (by
      simp only [eval, zf₃, n₂, and15_ofNat hlt]
      by_cases h0 : len % 16 = 0
      · simp [h0]
      · have : BitVec.ofNat 64 (len % 16) ≠ 0 := by
          intro he; have := congrArg BitVec.toNat he; rw [toNat_ofNat_lt (by lit_omega)] at this; exact h0 this
        simp [h0]; exact this) (fun h => ?_) (fun h => ?_)
  · -- A multiple of 16: nothing to pad.
    have h0 : len % 16 = 0 := by simpa using h
    refine WP.block_nil ⟨cs₃, rd₃', wr₃', fr₃, mx₃', fun key msg hr => ?_⟩
    rw [m₃]
    have := repr₂ key msg hr
    rwa [show pad16 (bytesAt s.mem P len) = [] by simp [pad16, hlen, h0], List.append_nil,
      ← show 16 * (len / 16) = len by omega]
  · have h0 : len % 16 ≠ 0 := by simpa using h
    refine WP.seq (WP.mono_mx (by rcases hr with ⟨rfl | rfl, rfl | rfl⟩ <;> decide +kernel) (macD_ok hr s₃)
      fun s₄ ⟨rsi₄, g₄, rd₄, wr₄, m₄⟩ mx₄ => ?_)
    have g₄' : ∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r := fun r h => by
      rw [g₄ r (calleeSaved_ne h).2.2.2.1, cs₃ r h]
    have hQ : s₄.gpr .rsi = P + BitVec.ofNat 64 (16 * (len / 16)) := by
      rw [rsi₄, g₃ n hn15 (by rcases hr.2 with rfl | rfl <;> decide), n₂, rdx₃, n₂, and15_ofNat hlt,
        g₃ p hp15 (by rcases hr.1 with rfl | rfl <;> decide), cs₂ p hpc, g₁' p hpc, hP]
      have e : len = 16 * (len / 16) + len % 16 := (Nat.div_add_mod _ _).symm
      have e' : BitVec.ofNat 64 len = BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 (len % 16) := by
        conv => lhs; rw [e]
        rw [BitVec.ofNat_add]
      rw [e', BitVec.add_sub_cancel, BitVec.add_comm]
    have hsrc : ∀ j < len % 16, InRegions (s₄.rd ++ s₄.wr)
        (P + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 j) 1 := fun j hj => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hs.cov_sub (a := 16 * (len / 16) + j) (n := 1) (by lit_omega) (by rw [rd₄, rd₃', hrd])
        (by rw [wr₄, wr₃', hwr]) _ _ ⟨_, List.mem_singleton_self _, self_contains _⟩
    have hdj : ∀ j < len % 16, (⟨P + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 j, 1⟩ :
        Region).Disjoint (sub s₀ 576 16) := fun j hj => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact (Src.disj_sub (hcP.sub_left (sub_ctx s₀ (by lit_omega))) (a := 16 * (len / 16) + j) (n := 1)
        (by lit_omega)).symm
    refine WP.mono (padTail_ok b hp (Q := P + BitVec.ofNat 64 (16 * (len / 16))) (t := len % 16)
      (by lit_omega) (by lit_omega) hQ
      (by rw [g₄ _ (by decide), rdx₃, n₂, and15_ofNat hlt])
      (by rw [g₄ _ (by decide), r15₃, rdi₂, off_sub])
      (by rw [g₄' _ (by simp [calleeSaved]), hrsp]) (by rw [rd₄, rd₃', hrd]) (by rw [wr₄, wr₃', hwr])
      hsrc hdj) fun s₅ ⟨cs₅, rd₅, wr₅, f₅, mx₅, repr₅⟩ => ?_
    refine ⟨fun r h => by rw [cs₅ r h, g₄' r h], by rw [rd₅, rd₄, rd₃'], by rw [wr₅, wr₄, wr₃'],
      fr₃.trans (by rw [← m₄]; exact f₅), by rw [mx₅, mx₄, mx₃'], fun key msg hr => ?_⟩
    have := repr₅ key _ (by rw [m₄, m₃]; exact repr₂ key msg hr)
    rw [m₄, m₃, bytesAt_frame f₂ (fun r hr => (hdisjP r hr).sub_left
      (sub_off P (a := 16 * (len / 16)) (by lit_omega))) (by lit_omega)] at this
    rw [show pad16 (bytesAt s.mem P len) = List.replicate (16 - len % 16) 0 by simp [pad16, hlen, h0],
      x_eq]
    simpa only [List.append_assoc] using this

end VG.Proof.ChaCha20Poly1305.X86_64

/-!
# ChaCha20-Poly1305 on x86-64: the other parts

Untrusted: everything here is checked by Lean. The lengths block, the
encryption, absorbing the lengths, the tag, comparing tags, and restoring the
registers.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt keystream)

theorem calleeSaved_rsp : Reg.rsp ∈ calleeSaved := by simp [calleeSaved]

/-- The invariant survives a part that keeps the callee-saved registers and
writes only the working space, the data and the stack. -/
theorem Inv.step {s₀ s s' : State} (h : Inv s₀ s) (cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [workR s₀, dR s₀, stkR s₀], Region.Sub r r')
    (hsv : ∀ r ∈ rs, (sub s₀ 592 40).Disjoint r) : Inv s₀ s' where
  r15 := by rw [cs _ (by simp [calleeSaved]), h.r15]
  r14 := by rw [cs _ (by simp [calleeSaved]), h.r14]
  r13 := by rw [cs _ (by simp [calleeSaved]), h.r13]
  r12 := by rw [cs _ (by simp [calleeSaved]), h.r12]
  rsp := by rw [cs _ calleeSaved_rsp, h.rsp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  saved := h.saved.frame hf hsv
  frame := h.frame.trans (hf.sub hsub)

/-- `ctx[k, k + n)` in the working space. -/
theorem sub_work (s₀ : State) {k n : Nat} (h₁ : 64 ≤ k) (h₂ : k + n ≤ 1024) :
    ∃ r' ∈ [workR s₀, dR s₀, stkR s₀], Region.Sub (sub s₀ k n) r' :=
  ⟨workR s₀, by simp, sub_sub s₀ h₁ (by lit_omega) (by lit_omega)⟩

theorem stk_work (s₀ : State) : ∃ r' ∈ [workR s₀, dR s₀, stkR s₀], Region.Sub (stkR s₀) r' :=
  ⟨stkR s₀, by simp, fun _ h => h⟩

theorem mac_inv {s₀ s s' : State} (hp : APre s₀) (h : Inv s₀ s) (cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame (macR s₀) s.mem s'.mem) : Inv s₀ s' :=
  h.step cs hrd hwr hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_work s₀ (by lit_omega) (by lit_omega)
      · exact stk_work s₀)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact (hp.stk_sub (by lit_omega)).symm)

/-! ## The lengths block -/

theorem bytesAt_16 (m : Mem) (p : Addr) :
    bytesAt m p 16 = leBytes 8 (m.readW p 64).toNat ++ leBytes 8 (m.readW (off p 8) 64).toNat := by
  rw [show 16 = 8 + 8 from rfl, VG.Proof.Poly1305.bytesAt_add, VG.Proof.Poly1305.bytesAt_leBytes_64,
    VG.Proof.Poly1305.bytesAt_leBytes_64, off_eq]

set_option simprocs false in
theorem lengths_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) (hrbp : s.gpr .rbp = s₀.gpr .rdx) :
    WP isa (.block lengths) s fun s' => Inv s₀ s' ∧ (∀ r, s'.gpr r = s.gpr r) ∧
      Frame [sub s₀ 656 16] s.mem s'.mem ∧
      bytesAt s'.mem (off (cx s₀) 656) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
  have o0 := hp.in_ctx (a := 656) (w := 8) (by lit_omega)
  have o1 := hp.in_ctx (a := 664) (w := 8) (by lit_omega)
  rw [← h.wr] at o0 o1
  simp only [off] at o0 o1
  apply WP.of_runBlock
  simp (config := {decide := true}) only [lengths, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    State.store64, h.r15, o0, o1, ite_true, Option.some.injEq, exists_eq_left']
  have hf : Frame [sub s₀ 656 16] s.mem ((s.mem.writeW (off (cx s₀) 656) (s.gpr .rbp)).writeW
      (off (cx s₀) 664) (s.gpr .r13)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  refine ⟨h.step (fun _ _ => rfl) rfl rfl hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_work s₀ (by lit_omega) (by lit_omega))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)),
    fun _ => trivial, hf, ?_⟩
  rw [bytesAt_16, off_off, show 656 + 8 = 664 from rfl, readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
    Mem.readW_writeW_self64, Mem.readW_writeW_self64, hrbp, h.r13]

/-! ## Restoring the registers -/

set_option simprocs false in
theorem restore_ok {s₀ : State} (hp : APre s₀) {s : State} (hrdi : s.gpr .rdi = off (cx s₀) 448)
    (hsv : Saved s₀ s.mem) (hr12 : s.gpr .r12 = s₀.gpr .r12) (hrsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block restore) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧
      s'.gpr .rax = s.gpr .rax ∧ s'.mem = s.mem := by
  have i : ∀ d, 448 ≤ d → d + 8 ≤ 1024 → InRegions (s.rd ++ s.wr) (off (off (cx s₀) 448) (d - 448)) 8 := by
    intro d h₁ h₂
    rw [off_off, show 448 + (d - 448) = d by omega, hrd, hwr]; exact hp.in_ctx' h₂
  have i0 := i 592 (by lit_omega) (by lit_omega)
  have i1 := i 600 (by lit_omega) (by lit_omega)
  have i2 := i 608 (by lit_omega) (by lit_omega)
  have i3 := i 616 (by lit_omega) (by lit_omega)
  have i4 := i 624 (by lit_omega) (by lit_omega)
  obtain ⟨v0, v1, v2, v3, v4⟩ := hsv
  have e : ∀ d, 448 ≤ d → off (off (cx s₀) 448) (d - 448) = off (cx s₀) d := fun d h => by
    rw [off_off, show 448 + (d - 448) = d by omega]
  rw [← e 592 (by lit_omega)] at v0
  rw [← e 600 (by lit_omega)] at v1
  rw [← e 608 (by lit_omega)] at v2
  rw [← e 616 (by lit_omega)] at v3
  rw [← e 624 (by lit_omega)] at v4
  apply WP.of_runBlock
  simp (config := {decide := true}) only [restore, saved, List.map_cons, List.map_nil, runBlock_cons,
    runStep_some, runBlock_nil, exec, ea_at, readSrc, State.load64, State.setReg, hrdi, i0, i1, i2, i3, i4,
    v0, v1, v2, v3, v4, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [ite_true, ite_false, hr12, hrsp]

/-! ## Comparing the tags -/

theorem bytesAt_8_eq {m : Mem} {p q : Addr} :
    bytesAt m p 8 = bytesAt m q 8 ↔ m.readW p 64 = m.readW q 64 := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [← VG.Proof.Poly1305.leNum_bytesAt_64, ← VG.Proof.Poly1305.leNum_bytesAt_64, h]
  · intro h
    rw [VG.Proof.Poly1305.bytesAt_leBytes_64, VG.Proof.Poly1305.bytesAt_leBytes_64, h]

/-- The tags differ in no bit if and only if they are equal. -/
theorem tag_eq (m : Mem) (p q : Addr) :
    ((m.readW p 64 ^^^ m.readW q 64) ||| (m.readW (off p 8) 64 ^^^ m.readW (off q 8) 64)) = 0#64 ↔
      bytesAt m p 16 = bytesAt m q 16 := by
  rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, BitVec.xor_eq_zero_iff, show 16 = 8 + 8 from rfl,
    VG.Proof.Poly1305.bytesAt_add, VG.Proof.Poly1305.bytesAt_add, ← off_eq, ← off_eq, ← bytesAt_8_eq,
    ← bytesAt_8_eq]
  constructor
  · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
  · intro h
    exact List.append_inj h (by rw [VG.Proof.Poly1305.length_bytesAt, VG.Proof.Poly1305.length_bytesAt])

theorem ea_disp (s : State) (b : Reg) (d : Int) :
    s.ea { base := b, disp := d } = s.gpr b + BitVec.ofInt 64 d := rfl

theorem off_neg {p : Addr} {a d : Nat} (h : d ≤ a) :
    off p a + BitVec.ofInt 64 (-(d : Int)) = off p (a - d) := by
  rw [off_eq, off_eq]
  have : BitVec.ofInt 64 (-(d : Int)) = -BitVec.ofNat 64 d := by
    rw [BitVec.ofInt_neg, BitVec.ofInt_natCast]
  rw [this, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, Offset.ofNat_sub_ofNat h]

set_option simprocs false in
theorem compare_ok {s₀ : State} (hp : APre s₀) {s : State} (hrcx : s.gpr .rcx = off (cx s₀) 640)
    (hrdi : s.gpr .rdi = off (cx s₀) 448) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block compare) s fun s' =>
      (s'.gpr .rax).setWidth 32 =
        (if bytesAt s.mem (off (cx s₀) 640) 16 = bytesAt s.mem (off (cx s₀) 48) 16 then 1 else 0) ∧
      (∀ q, q ≠ .rax → q ≠ .rdx → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e0 : off (off (cx s₀) 640) 0 = off (cx s₀) 640 := by rw [off_off]
  have e1 : off (cx s₀) 448 + BitVec.ofInt 64 (-400) = off (cx s₀) 48 := off_neg (d := 400) (by lit_omega)
  have e3 : off (cx s₀) 448 + BitVec.ofInt 64 (-392) = off (off (cx s₀) 48) 8 := by
    rw [off_off]; exact off_neg (d := 392) (by lit_omega)
  have i : ∀ a, a + 8 ≤ 1024 → InRegions (s.rd ++ s.wr) (off (cx s₀) a) 8 := fun a h => by
    rw [hrd, hwr]; exact hp.in_ctx' h
  have i0 := i 640 (by lit_omega)
  have i1 := i 48 (by lit_omega)
  have i2 : InRegions (s.rd ++ s.wr) (off (off (cx s₀) 640) 8) 8 := by rw [off_off]; exact i 648 (by lit_omega)
  have i3 : InRegions (s.rd ++ s.wr) (off (off (cx s₀) 48) 8) 8 := by rw [off_off]; exact i 56 (by lit_omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [VG.Impl.ChaCha20Poly1305.X86_64.compare, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    ea_disp, readSrc, readSrc32, execAlu, execAlu32, arithFlags, State.load64, State.setReg, State.setReg32,
    State.setFlags, hrcx, hrdi, e0, e1, e3, i0, i1, i2, i3, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', se1']
  refine ⟨?_, fun q h₁ h₂ => by simp [h₁, h₂], trivial⟩
  have ht := tag_eq s.mem (off (cx s₀) 640) (off (cx s₀) 48)
  generalize ((s.mem.readW (off (cx s₀) 640) 64 ^^^ s.mem.readW (off (cx s₀) 48) 64) |||
    (s.mem.readW (off (off (cx s₀) 640) 8) 64 ^^^ s.mem.readW (off (off (cx s₀) 48) 8) 64)) = x at ht ⊢
  by_cases hb : bytesAt s.mem (off (cx s₀) 640) 16 = bytesAt s.mem (off (cx s₀) 48) 16
  · rw [ite_eq_left hb, ht.mpr hb]; decide
  · have hx : ¬ x.toNat < 1 := fun h => hb (ht.mp (BitVec.eq_of_toNat_eq (by simp; omega)))
    rw [ite_eq_right hb]; simp [hx]

/-! ## Encrypting -/

theorem set12_initState (key nonce : List Byte) :
    (Spec.ChaCha20.initState key 0 nonce).set 12 1 = Spec.ChaCha20.initState key 1 nonce := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_set, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  by_cases h : 12 = i
  · subst h; simp
  · simp only [h, ite_false, show ¬ i = 12 from fun h' => h h'.symm]

/-- Setting the block counter in memory. -/
theorem stateAt_ctr (m : Mem) (c : Addr) :
    stateAt (m.writeW (off c 112) (1 : BitVec 32)) (off c 64) = (stateAt m (off c 64)).set 12 1 := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_set, Vector.getElem_ofFn]
  rw [show off c 64 + BitVec.ofNat 64 (4 * i) = off c (64 + 4 * i) by
    simp only [off_eq, BitVec.ofNat_add, BitVec.add_assoc]]
  by_cases h : 12 = i
  · subst h; simp only [ite_true]; exact Mem.readW_writeW_self32 _ _ _
  · simp only [h, ite_false]
    exact readW32_off m c 1 (by lit_omega) (by lit_omega) (by lit_omega)

set_option simprocs false in
theorem cryptA_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block cryptArgs) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s'.gpr .rdi = off (cx s₀) 64 ∧
      s'.gpr .rsi = dp s₀ ∧ s'.gpr .rdx = s₀.gpr .r8 ∧ s'.gpr .rcx = off (cx s₀) 128 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o := hp.in_ctx (a := 112) (w := 4) (by lit_omega)
  rw [← h.wr] at o
  simp only [off] at o
  apply WP.of_runBlock
  simp (config := {decide := true}) only [cryptArgs, ptr, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, ea_at, readSrc, readSrc32, execAlu, arithFlags, State.store32, State.setReg,
    State.setReg32, State.setFlags, h.r15, h.r14, h.r13, o, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', se_ofNat (show 64 < 2 ^ 31 by omega),
    se_ofNat (show 128 < 2 ^ 31 by omega), BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  refine ⟨trivial, by rw [off_eq], trivial, trivial, by rw [off_eq], fun r hr => ?_, trivial⟩
  have := calleeSaved_ne hr
  simp [this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2]

theorem hL (s₀ : State) : s₀.gpr .r8 = BitVec.ofNat 64 (L s₀) := by simp [L]

/-- The arguments of `vg_chacha20_xor`, as `cryptArgs` sets them up. -/
structure XArgs (s₀ s : State) : Prop where
  rdi : s.gpr .rdi = off (cx s₀) 64
  rsi : s.gpr .rsi = dp s₀
  rdx : s.gpr .rdx = s₀.gpr .r8
  rcx : s.gpr .rcx = off (cx s₀) 128
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r13 : s.gpr .r13 = s₀.gpr .r8
  r14 : s.gpr .r14 = dp s₀
  wr : s.wr = s₀.wr

theorem XArgs.of {s₀ s s' : State} (h : Inv s₀ s) (rdi : s'.gpr .rdi = off (cx s₀) 64) (rsi : s'.gpr .rsi = dp s₀)
    (rdx : s'.gpr .rdx = s₀.gpr .r8) (rcx : s'.gpr .rcx = off (cx s₀) 128)
    (cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (wr : s'.wr = s.wr) : XArgs s₀ s' :=
  ⟨rdi, rsi, rdx, rcx, by rw [cs _ calleeSaved_rsp, h.rsp], by rw [cs _ (by simp [calleeSaved]), h.r13],
    by rw [cs _ (by simp [calleeSaved]), h.r14], by rw [wr, h.wr]⟩

theorem cryptArgs_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block cryptArgs) s (XArgs s₀) :=
  WP.mono (cryptA_ok hp h) fun _ ⟨_, rdi, rsi, rdx, rcx, cs, _, wr⟩ => XArgs.of h rdi rsi rdx rcx cs wr

section
variable {s₀ : State} (hp : APre s₀) {s : State} (h : XArgs s₀ s)
include hp h

theorem XArgs.hw : Covers [⟨off (cx s₀) 64, 64⟩, ⟨dp s₀, L s₀⟩, ⟨off (cx s₀) 128, 320⟩] s.wr := by
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨ctxR s₀, by simp [h.wr, hp.wr], 64, by simp [off_eq], by show 64 + 64 ≤ 1024; omega⟩
  · exact ⟨dR s₀, by simp [h.wr, hp.wr], 0, by simp, by simp⟩
  · exact ⟨ctxR s₀, by simp [h.wr, hp.wr], 128, by simp [off_eq], by show 128 + 320 ≤ 1024; omega⟩

/-- The precondition of the implementation `v` of `vg_chacha20_xor`. -/
theorem XArgs.pre (v : Proof.ChaCha20.X86_64.XorImpl) :
    (Proof.ChaCha20.xorStack v.stack).pre
      (s.callEntry.withRegions [] [⟨off (cx s₀) 64, 64⟩, ⟨dp s₀, L s₀⟩, ⟨off (cx s₀) 128, 320⟩]) :=
  xor_pre v h.rdi h.rsi (by rw [h.rdx]; exact hL s₀) h.rcx (s₀.gpr .r8).isLt
    (hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega)))
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    (hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))) hp.wrap_d
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega)) (by rw [h.rsp]; exact hp.stk_d)
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega))

/-- The call of the implementation `v` of `vg_chacha20_xor`. -/
theorem XArgs.call (v : Proof.ChaCha20.X86_64.XorImpl) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨off (cx s₀) 64, 64⟩, ⟨dp s₀, L s₀⟩, ⟨off (cx s₀) 128, 320⟩, stkR s₀] s.mem s'.mem →
      s'.gpr .rsi = off (cx s₀) 128 →
      Spec.ChaCha20.bytesAt s'.mem (dp s₀) (L s₀) = List.zipWith (· ^^^ ·)
        (Spec.ChaCha20.bytesAt s.mem (dp s₀) (L s₀)) (keystream (stateAt s.mem (off (cx s₀) 64)) (L s₀)) →
      Q s') :
    WP isa (.call v.callee.name v.callee.code) s Q :=
  xor_call v h.rdi h.rsi (by rw [h.rdx]; exact hL s₀) h.rcx (s₀.gpr .r8).isLt
    (hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega)))
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    (hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))) hp.wrap_d
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega)) (by rw [h.rsp]; exact hp.stk_d)
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega)) (covers_nil_append (covers_left _ (h.hw hp))) (h.hw hp)
    fun s' rd wr cs f rsi data => hQ s' rd wr cs (by rw [h.rsp] at f; exact f) rsi data

end

/-- The data encrypted (or decrypted) from block counter 1, by any
implementation of `vg_chacha20_xor`. -/
theorem crypt_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)) :
    WP isa (crypt v.callee) s fun s' => Inv s₀ s' ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s'.mem ∧
      bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  refine WP.seq (WP.mono (cryptA_ok hp h) fun s₁ ⟨m₁, rdi₁, rsi₁, rdx₁, rcx₁, cs₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq ((XArgs.of h rdi₁ rsi₁ rdx₁ rcx₁ cs₁ wr₁).call hp v fun s₂ rd₂ wr₂ cs₂ f₂ rsi₂ data₂ => ?_)
  refine WP.mono (anchor_ok .rsi (k := 128) (by lit_omega) s₂) fun s₃ ⟨e3, g₃, rd₃, wr₃, m₃⟩ => ?_
  have cs : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := fun r hr => by
    by_cases h15 : r = .r15
    · subst h15; rw [e3, rsi₂, off_sub, h.r15]
    · rw [g₃ r h15, cs₂ r hr, cs₁ r hr]
  have f1 : Frame [sub s₀ 64 64] s.mem s₁.mem := by
    rw [m₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  have hsub : ∀ r ∈ [sub s₀ 64 384, dR s₀, stkR s₀], ∃ r' ∈ [workR s₀, dR s₀, stkR s₀], Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_work s₀ (by lit_omega) (by lit_omega)
    · exact ⟨dR s₀, by simp, fun _ h => h⟩
    · exact stk_work s₀
  have hf : Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s₃.mem := by
    rw [m₃]
    refine (f1.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  refine ⟨h.step cs (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁]) hf hsub (fun r hr => ?_), cs, hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))
    · exact (hp.stk_sub (by lit_omega)).symm
  · have d₁ : bytesAt s₁.mem (dp s₀) (L s₀) = bytesAt s.mem (dp s₀) (L s₀) :=
      bytesAt_frame f1 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).symm) (Nat.le_of_lt (s₀.gpr .r8).isLt)
    have st₁ : stateAt s₁.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 1 (N s₀) := by
      rw [m₁, stateAt_ctr, hst, set12_initState]
    rw [m₃, ← bytesAt_eq, data₂, st₁, bytesAt_eq, d₁, encrypt_eq, VG.Proof.Poly1305.length_bytesAt]

/-! ## Absorbing the lengths and the tag -/

set_option simprocs false in
theorem ptrs_ok (k : Nat) (hk : k < 2 ^ 31) (v : BitVec 32) (s : State) :
    WP isa (.block (ptr .rdi .r15 448 ++ ptr .rsi .r15 k ++ ([.mov32 .rdx (.imm v)] : List Instr))) s fun s' =>
      s'.gpr .rdi = off (s.gpr .r15) 448 ∧ s'.gpr .rsi = off (s.gpr .r15) k ∧ s'.gpr .rdx = v.setWidth 64 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ptr, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, readSrc32, execAlu, arithFlags, State.setReg, State.setReg32, State.setFlags,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    se_ofNat (show 448 < 2 ^ 31 by omega), se_ofNat hk]
  refine ⟨by rw [off_eq], by rw [off_eq], trivial, fun r hr => ?_, trivial⟩
  have := calleeSaved_ne hr
  simp [this.2.2.1, this.2.2.2.1, this.2.2.2.2]

theorem absorbLengths_eq (b : Impl.Poly1305.X86_64.Blocks) : absorbLengths b =
    .seq (.block (ptr .rdi .r15 448 ++ ptr .rsi .r15 656 ++ ([.mov32 .rdx (.imm 1)] : List Instr)))
    (.seq (.call b.name b.code) (.block (anchor .rdi 448))) := rfl

/-- The lengths block absorbed. -/
theorem absorbLengths_ok (b : Impl.Poly1305.X86_64.Blocks) {s₀ : State} (hp : APre s₀) {s : State}
    (h : Inv s₀ s) :
    WP isa (absorbLengths b) s fun s' => Inv s₀ s' ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      Frame (macR s₀) s.mem s'.mem ∧ s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ bytesAt s.mem (off (cx s₀) 656) 16) := by
  rw [absorbLengths_eq]
  refine WP.seq (WP.mono_mx (by decide +kernel) (ptrs_ok 656 (by lit_omega) 1 s)
    fun s₁ ⟨rdi₁, rsi₁, rdx₁, cs₁, rd₁, wr₁, m₁⟩ mx₁ => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [cs₁ _ calleeSaved_rsp, h.rsp]
  have wr₁' : s₁.wr = s₀.wr := by rw [wr₁, h.wr]
  rw [h.r15] at rdi₁ rsi₁
  refine WP.seq (WP.mono (blocks_call (n := 1) rdi₁ rsi₁ (by rw [rdx₁]; rfl) (by lit_omega)
    (sub_disj s₀ (b := 656) (m := 16 * 1) (by lit_omega) (by lit_omega) (by lit_omega))
    (by rw [hp.off_toNat (by lit_omega)]; have := hp.wrap_c; omega)
    (by rw [rsp₁]; exact hp.below16_sub (by lit_omega)) (by rw [rsp₁]; exact hp.below16_sub (by lit_omega))
    (covers_left _ (covers_sub hp wr₁' _ (by
      intro r hr; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨656, rfl, show 656 + 16 * 1 ≤ 1024 by omega⟩
      · exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩)))
    (covers_sub hp wr₁' _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩))
    b) fun s₂ ⟨rd₂, wr₂, cs₂, f₂, rdi₂, repr₂, mx₂⟩ => ?_)
  rw [rsp₁, m₁] at f₂
  rw [m₁] at repr₂
  refine WP.mono_mx (by decide +kernel) (anchor_ok .rdi (k := 448) (by lit_omega) s₂)
    fun s₃ ⟨e3, g₃, rd₃, wr₃, m₃⟩ mx₃ => ?_
  have cs : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := fun r hr => by
    by_cases h15 : r = .r15
    · subst h15; rw [e3, rdi₂, off_sub, h.r15]
    · rw [g₃ r h15, cs₂ r hr, cs₁ r hr]
  have hf : Frame (macR s₀) s.mem s₃.mem := by rw [m₃]; exact frame_mac' (by lit_omega) (by lit_omega) f₂
  exact ⟨mac_inv hp h cs (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁]) hf, cs, hf,
    by rw [mx₃, mx₂, mx₁], fun key msg hr => by rw [m₃]; exact repr₂ key msg hr⟩

set_option simprocs false in
theorem fptrs_ok (k : Nat) (hk : k < 2 ^ 31) (s : State) :
    WP isa (.block (ptr .rdi .r15 448 ++ ([.mov32 .rsi (.imm 0)] : List Instr) ++ ptr .rdx .r15 k)) s fun s' =>
      s'.gpr .rdi = off (s.gpr .r15) 448 ∧ s'.gpr .rsi = 0 ∧ s'.gpr .rdx = off (s.gpr .r15) k ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ptr, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, readSrc32, execAlu, arithFlags, State.setReg, State.setReg32, State.setFlags,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    se_ofNat (show 448 < 2 ^ 31 by omega), se_ofNat hk]
  refine ⟨by rw [off_eq], trivial, by rw [off_eq], fun r hr => ?_, trivial⟩
  have := calleeSaved_ne hr
  simp [this.2.2.1, this.2.2.2.1, this.2.2.2.2]

theorem finalizeTo_eq (out : Nat) : finalizeTo out =
    .seq (.block (ptr .rdi .r15 448 ++ ([.mov32 .rsi (.imm 0)] : List Instr) ++ ptr .rdx .r15 out))
      (.call "vg_poly1305_finalize" Impl.Poly1305.X86_64.finalize) := rfl

/-- The tag written to `ctx[out, out + 16)`. -/
theorem finalizeTo_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) {out : Nat}
    (hout : out + 16 ≤ 448 ∨ (576 ≤ out ∧ out + 16 ≤ 656)) :
    WP isa (finalizeTo out) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.gpr .rdi = off (cx s₀) 448 ∧ s'.gpr .rcx = off (cx s₀) out ∧
      Frame [sub s₀ 448 128, sub s₀ out 16, stkR s₀] s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg → bytesAt s'.mem (off (cx s₀) out) 16 = mac key msg := by
  rw [finalizeTo_eq]
  have ho : out + 16 ≤ 1024 := by omega
  refine WP.seq (WP.mono (fptrs_ok out (by lit_omega) s) fun s₁ ⟨rdi₁, rsi₁, rdx₁, cs₁, rd₁, wr₁, m₁⟩ => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [cs₁ _ calleeSaved_rsp, h.rsp]
  have wr₁' : s₁.wr = s₀.wr := by rw [wr₁, h.wr]
  rw [h.r15] at rdi₁ rdx₁
  refine finalize_call rdi₁ rsi₁ rdx₁ (sub_disj s₀ (by lit_omega) (by lit_omega) ho)
    (by rw [rsp₁]; exact hp.below8_sub (by lit_omega)) (by rw [rsp₁]; exact hp.below8_sub ho)
    (covers_left _ (covers_sub hp wr₁' _ (by
      intro r hr; simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩
      · exact ⟨out, rfl, ho⟩)))
    (covers_sub hp wr₁' _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩
      · exact ⟨out, rfl, ho⟩))
    fun s₃ rd₃ wr₃ cs₃ f₃ rdi₃ rcx₃ tag₃ => ?_
  rw [rsp₁, m₁] at f₃
  refine ⟨fun r hr => by rw [cs₃ r hr, cs₁ r hr], by rw [rd₃, rd₁], by rw [wr₃, wr₁], rdi₃, rcx₃,
    f₃.sub fun r hr => ?_, fun key msg hr => tag₃ key msg (by rw [m₁]; exact hr)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨sub s₀ 448 128, by simp, fun _ h => h⟩
  · exact ⟨sub s₀ out 16, by simp, fun _ h => h⟩
  · exact ⟨stkR s₀, by simp, below8_stk s₀⟩

end VG.Proof.ChaCha20Poly1305.X86_64

/-!
# ChaCha20-Poly1305 on x86-64: correctness

Untrusted: everything here is checked by Lean. `seal` and `open`, from their
parts.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 24) (d := 24) (n := 8) (k := 24) (by decide) (by decide)
  rwa [BitVec.sub_add_cancel] at this

theorem APre.stk_d' {s₀ : State} (hp : APre s₀) : (stkR s₀).Disjoint (dR s₀) := hp.stk_d
theorem APre.stk_a' {s₀ : State} (hp : APre s₀) : (stkR s₀).Disjoint (aR s₀) := hp.stk_a

/-- That two of the regions the parts use are disjoint: parts of the context
at different offsets, the stack below the return address, and the data.
(Matching only reducibly, so that a lemma that does not apply fails fast.) -/
macro "rdisj" : tactic => `(tactic| first
  | with_reducible exact sub_disj _ (by lit_omega) (by lit_omega) (by lit_omega)
  | with_reducible exact (APre.stk_sub ‹APre _› (by lit_omega)).symm
  | with_reducible exact APre.stk_sub ‹APre _› (by lit_omega)
  | with_reducible exact (‹APre _›).c_d.sub_left (sub_ctx _ (by lit_omega))
  | with_reducible exact (‹APre _›).c_d.symm.sub_right (sub_ctx _ (by lit_omega))
  | with_reducible exact (APre.stk_d' ‹APre _›).symm
  | with_reducible exact (‹APre _›).c_a.symm.sub_right (sub_ctx _ (by lit_omega))
  | with_reducible exact (APre.stk_a' ‹APre _›).symm
  | with_reducible exact (‹APre _›).a_d
  | with_reducible exact (‹APre _›).ret_c.sub_right (sub_ctx _ (by lit_omega))
  | with_reducible exact (‹APre _›).ret_d
  | with_reducible exact ret_stk _)

/-- A region is disjoint from each of a list of regions. -/
macro "rdisj_all" : tactic => `(tactic| (
  simp only [macR, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  repeat' apply And.intro
  all_goals rdisj))

theorem hRDX (s₀ : State) : s₀.gpr .rdx = BitVec.ofNat 64 (AL s₀) := by simp [AL]

theorem srcA {s₀ : State} (hp : APre s₀) : Src s₀ (ad s₀) (AL s₀) :=
  ⟨(s₀.gpr .rdx).isLt, hp.wrap_a, hp.c_a, hp.stk_a, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; simp [hp.rd], hc⟩⟩

theorem srcD {s₀ : State} (hp : APre s₀) : Src s₀ (dp s₀) (L s₀) :=
  ⟨(s₀.gpr .r8).isLt, hp.wrap_d, hp.c_d, hp.stk_d, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; simp [hp.wr], hc⟩⟩

theorem length_encrypt (key nonce m : List Byte) : (Spec.ChaCha20.encrypt key 1 nonce m).length = m.length := by
  rw [encrypt_eq, List.length_zipWith, VG.Proof.ChaCha20.length_keystream, Nat.min_self]

theorem off48 (s₀ : State) : cx s₀ + 48 = off (cx s₀) 48 := by rw [off_eq]; rfl

/-- The return address is unchanged. -/
theorem ret_kept {s₀ : State} (hp : APre s₀) {m₆ m' : Mem} (hi : Frame [workR s₀, dR s₀, stkR s₀] s₀.mem m₆)
    {out : Nat} (ho : out + 16 ≤ 1024) (hf : Frame [sub s₀ 448 128, sub s₀ out 16, stkR s₀] m₆ m') :
    m'.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 := by
  have c : (retR s₀).Contains (s₀.gpr .rsp) (64 / 8) := Region.contains_self _ _
  rw [hf.readW c (by rdisj_all) (by lit_omega), hi.readW c (by rdisj_all) (by lit_omega)]

theorem prologue_mx : prologue.allInstrs (fun i => !loadsMxcsr i) = true := by decide +kernel

theorem crypt_mx (v : Proof.ChaCha20.X86_64.XorImpl) :
    (crypt v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [crypt, Code.allInstrs, v.mxcsr]
  decide +kernel

theorem seal_correct (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre s₀) :
    WP isa («seal» v.callee v.poly) s₀ fun s' => abiPreserved s₀ s' ∧ sealX86_64.post s₀ s' := by
  have hL' := (Nat.le_of_lt (s₀.gpr .r8).isLt)
  refine WP.seq (WP.mono_mx prologue_mx (prologue_ok hp) fun s₁ h₁ mx₁ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.fine (by rdisj_all) (Nat.le_of_lt (s₀.gpr .rdx).isLt)
  refine WP.seq (WP.mono (macPad_ok v.poly hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp)
    h₁.inv.r15 h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, mx₂, r₂⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  refine WP.seq (WP.mono_mx (by decide +kernel) (lengths_ok hp i₂ (by rw [cs₂ _ (by simp [calleeSaved]), h₁.rbp]))
    fun s₃ ⟨i₃, _, f₃, len₃⟩ mx₃ => ?_)
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame f₃ (by rdisj_all), stateAt_frame f₂ (by rdisj_all), h₁.st]
  have D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame f₃ (by rdisj_all) hL', bytesAt_frame f₂ (by rdisj_all) hL',
      bytesAt_frame h₁.fine (by rdisj_all) hL']
  refine WP.seq (WP.mono_mx (crypt_mx v) (crypt_ok v hp i₃ st₃) fun s₄ ⟨i₄, _, f₄, ct₄⟩ mx₄ => ?_)
  rw [D₃] at ct₄
  refine WP.seq (WP.mono (macPad_ok v.poly hp (p := .r14) (n := .r13) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₄.r15
    i₄.rsp i₄.rd i₄.wr i₄.r14 (by rw [i₄.r13]; exact hL s₀))
    fun s₅ ⟨cs₅, rd₅, wr₅, f₅, mx₅, r₅⟩ => ?_)
  have i₅ := mac_inv hp i₄ cs₅ rd₅ wr₅ f₅
  refine WP.seq (WP.mono (absorbLengths_ok v.poly hp i₅) fun s₆ ⟨i₆, _, f₆, mx₆, r₆⟩ => ?_)
  refine WP.seq (WP.mono_mx (by decide +kernel) (finalizeTo_ok hp i₆ (out := 48) (.inl (by lit_omega)))
    fun s₇ ⟨cs₇, rd₇, wr₇, rdi₇, _, f₇, tag₇⟩ mx₇ => ?_)
  refine WP.mono_mx (by decide +kernel) (restore_ok hp rdi₇ (i₆.saved.frame f₇ (by rdisj_all))
    (by rw [cs₇ _ (by simp [calleeSaved]), i₆.r12]) (by rw [cs₇ _ calleeSaved_rsp, i₆.rsp])
    (by rw [rd₇, i₆.rd]) (by rw [wr₇, i₆.wr])) fun s₈ ⟨cs₈, _, m₈⟩ mx₈ => ?_
  have R₄ := Repr.frame f₄ (by rdisj_all) (Repr.frame f₃ (by rdisj_all) (r₂ (otk s₀) [] h₁.poly))
  have T₇ := tag₇ _ _ (r₆ _ _ (r₅ _ _ R₄))
  have L₅ : bytesAt s₅.mem (off (cx s₀) 656) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame f₅ (by rdisj_all) (by lit_omega), bytesAt_frame f₄ (by rdisj_all) (by lit_omega), len₃]
  have C₈ : bytesAt s₈.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [m₈, bytesAt_frame f₇ (by rdisj_all) hL', bytesAt_frame f₆ (by rdisj_all) hL',
      bytesAt_frame f₅ (by rdisj_all) hL', ct₄]
  have C₄ : bytesAt s₄.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := ct₄
  refine ⟨⟨cs₈, by rw [m₈]; exact ret_kept hp i₆.frame (by lit_omega) f₇,
    by rw [mx₈, mx₇, mx₆, mx₅, mx₄, mx₃, mx₂, mx₁]⟩, ?_⟩
  show Spec.ChaCha20Poly1305.encrypt (K s₀) (N s₀) (A s₀) (D s₀) =
    (bytesAt s₈.mem (dp s₀) (L s₀), bytesAt s₈.mem (cx s₀ + 48) 16)
  rw [C₈, off48, m₈, T₇, L₅, C₄, hA]
  simp only [Spec.ChaCha20Poly1305.encrypt, macData, List.nil_append,
    List.append_assoc, VG.Proof.Poly1305.length_bytesAt, length_encrypt]

theorem open_eq (x : Impl.ChaCha20.X86_64.Callee) (b : Impl.Poly1305.X86_64.Blocks) : «open» x b =
    .seq prologue (.seq (macPad b .rbx .rbp) (.seq (macPad b .r14 .r13) (.seq (.block lengths)
    (.seq (absorbLengths b) (.seq (crypt x) (.seq (finalizeTo 640) (.block (compare ++ restore)))))))) := rfl

theorem open_correct (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre s₀) :
    WP isa («open» v.callee v.poly) s₀ fun s' => abiPreserved s₀ s' ∧ openX86_64.post s₀ s' := by
  have hL' := (Nat.le_of_lt (s₀.gpr .r8).isLt)
  refine WP.seq (WP.mono_mx prologue_mx (prologue_ok hp) fun s₁ h₁ mx₁ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.fine (by rdisj_all) (Nat.le_of_lt (s₀.gpr .rdx).isLt)
  refine WP.seq (WP.mono (macPad_ok v.poly hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp)
    h₁.inv.r15 h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, mx₂, r₂⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  have D₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame f₂ (by rdisj_all) hL', bytesAt_frame h₁.fine (by rdisj_all) hL']
  refine WP.seq (WP.mono (macPad_ok v.poly hp (p := .r14) (n := .r13) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₂.r15
    i₂.rsp i₂.rd i₂.wr i₂.r14 (by rw [i₂.r13]; exact hL s₀))
    fun s₃ ⟨cs₃, rd₃, wr₃, f₃, mx₃, r₃⟩ => ?_)
  have i₃ := mac_inv hp i₂ cs₃ rd₃ wr₃ f₃
  refine WP.seq (WP.mono_mx (by decide +kernel) (lengths_ok hp i₃ (by rw [cs₃ _ (by simp [calleeSaved]),
    cs₂ _ (by simp [calleeSaved]), h₁.rbp])) fun s₄ ⟨i₄, _, f₄, len₄⟩ mx₄ => ?_)
  refine WP.seq (WP.mono (absorbLengths_ok v.poly hp i₄) fun s₅ ⟨i₅, _, f₅, mx₅, r₅⟩ => ?_)
  have st₅ : stateAt s₅.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame f₅ (by rdisj_all), stateAt_frame f₄ (by rdisj_all), stateAt_frame f₃ (by rdisj_all),
      stateAt_frame f₂ (by rdisj_all), h₁.st]
  refine WP.seq (WP.mono_mx (crypt_mx v) (crypt_ok v hp i₅ st₅) fun s₆ ⟨i₆, _, f₆, pt₆⟩ mx₆ => ?_)
  refine WP.seq (WP.mono_mx (by decide +kernel) (finalizeTo_ok hp i₆ (out := 640) (.inr ⟨by omega, by omega⟩))
    fun s₇ ⟨cs₇, rd₇, wr₇, rdi₇, rcx₇, f₇, tag₇⟩ mx₇ => ?_)
  refine WP.block_append (WP.mono_mx (by decide +kernel) (compare_ok hp rcx₇ rdi₇ (by rw [rd₇, i₆.rd])
    (by rw [wr₇, i₆.wr])) fun s₈ ⟨rax₈, g₈, m₈, rd₈, wr₈⟩ mx₈ => ?_)
  have g₈' : ∀ r ∈ calleeSaved, s₈.gpr r = s₇.gpr r := fun r hr =>
    g₈ r (calleeSaved_ne hr).1 (calleeSaved_ne hr).2.2.1
  refine WP.mono_mx (by decide +kernel) (restore_ok hp (by rw [g₈ _ (by decide) (by decide), rdi₇])
    (by rw [m₈]; exact i₆.saved.frame f₇ (by rdisj_all))
    (by rw [g₈' _ (by simp [calleeSaved]), cs₇ _ (by simp [calleeSaved]), i₆.r12])
    (by rw [g₈' _ calleeSaved_rsp, cs₇ _ calleeSaved_rsp, i₆.rsp])
    (by rw [rd₈, rd₇, i₆.rd]) (by rw [wr₈, wr₇, i₆.wr])) fun s₉ ⟨cs₉, rax₉, m₉⟩ mx₉ => ?_
  -- The tag computed, and the one received.
  have R₃ := r₃ _ _ (r₂ (otk s₀) [] h₁.poly)
  have T₇ := tag₇ _ _ (Repr.frame f₆ (by rdisj_all) (r₅ _ _ (Repr.frame f₄ (by rdisj_all) R₃)))
  have L₄ : bytesAt s₄.mem (off (cx s₀) 656) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := len₄
  have T0₇ : bytesAt s₇.mem (off (cx s₀) 48) 16 = T0 s₀ := by
    rw [bytesAt_frame f₇ (by rdisj_all) (by lit_omega), bytesAt_frame i₆.frame (by rdisj_all) (by lit_omega), ← off48]
  have P₉ : bytesAt s₉.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [m₉, m₈, bytesAt_frame f₇ (by rdisj_all) hL', pt₆, bytesAt_frame f₅ (by rdisj_all) hL',
      bytesAt_frame f₄ (by rdisj_all) hL', bytesAt_frame f₃ (by rdisj_all) hL', D₂]
  rw [L₄, D₂, hA] at T₇
  refine ⟨⟨cs₉, by rw [m₉, m₈]; exact ret_kept hp i₆.frame (by lit_omega) f₇,
    by rw [mx₉, mx₈, mx₇, mx₆, mx₅, mx₄, mx₃, mx₂, mx₁]⟩, ?_⟩
  have hm : mac (otk s₀) (macData (A s₀) (D s₀)) = bytesAt s₇.mem (off (cx s₀) 640) 16 := by
    rw [T₇]
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
  rw [openX86_64, Contract.post_mk]
  dsimp only
  rw [rax₉, rax₈]
  split
  next pt hpt =>
    obtain ⟨hmac, rfl⟩ := decrypt_eq_some hpt
    exact ⟨ite_eq_left (hm.symm.trans (hmac.trans T0₇.symm)), P₉⟩
  next hn => exact ite_eq_right fun he => decrypt_eq_none hn ((hm.trans he).trans T0₇)

end VG.Proof.ChaCha20Poly1305.X86_64

/-!
# ChaCha20-Poly1305 on x86-64: constant time

Untrusted: everything here is checked by Lean. `seal` and `open` call an
implementation of `vg_chacha20_xor` that the proof does not know, so the
taint analysis cannot follow them into it. The code before the call and the
code after it are checked by the taint analysis; the call is constant time
by the implementation's own proof (`RelCT.callEx`), since its arguments,
which correctness determines (`XArgs`), agree in two runs; and after it,
correctness says again where `rsi` points (`After`), from which the rest is
checked.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64

/-- The public registers and what is known about memory on entry: the lengths
of the context and the data (the data's varies) and the registers holding
their bases. -/
def τ₀ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false, lens := [1024, 0],
    bases := [(.rdi, 0, 0), (.rcx, 1, 0)] }

theorem agree₀ {s₁ s₂ : State} (h₁ : preX86_64 s₁) (h₂ : preX86_64 s₂) (hpub : pubX86_64 s₁ s₂) :
    X86_64.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
  have wf : ∀ s, preX86_64 s → X86_64.Taint.Wf τ₀ s := by
    intro s hs
    obtain ⟨-, hw, -, d, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τ₀], by simp [hw, d], by simp [hw, (Nat.le_of_lt (s.gpr .r8).isLt)]⟩, fun p hp => ?_⟩
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p4, p5]
  · intro sl h; simp [τ₀] at h
  · intro sl h; simp [τ₀] at h

/-! ## The code around the call -/

/-- `seal` up to the call of `vg_chacha20_xor`. -/
def sealPre (b : Impl.Poly1305.X86_64.Blocks) : Prog isa :=
  .seq prologue (.seq (macPad b .rbx .rbp) (.seq (.block lengths) (.block cryptArgs)))

/-- `seal` after the call of `vg_chacha20_xor`. -/
def sealPost (b : Impl.Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (.block (anchor .rsi 128))
    (.seq (macPad b .r14 .r13) (.seq (absorbLengths b) (.seq (finalizeTo 48) (.block restore))))

/-- `open` up to the call of `vg_chacha20_xor`. -/
def openPre (b : Impl.Poly1305.X86_64.Blocks) : Prog isa :=
  .seq prologue (.seq (macPad b .rbx .rbp) (.seq (macPad b .r14 .r13) (.seq (.block lengths)
    (.seq (absorbLengths b) (.block cryptArgs)))))

/-- `open` after the call of `vg_chacha20_xor`. -/
def openPost : Prog isa :=
  .seq (.block (anchor .rsi 128)) (.seq (finalizeTo 640) (.block (compare ++ restore)))

theorem seal_exec {x : Impl.ChaCha20.X86_64.Callee} {b : Impl.Poly1305.X86_64.Blocks} {s s' : State}
    {t : List Leak} (h : Exec isa («seal» x b) s t s') :
    Exec isa (.seq (sealPre b) (.seq (.call x.name x.code) (sealPost b))) s t s' := by
  cases h with | seq e₁ h => cases h with | seq e₂ h => cases h with | seq e₃ h => cases h with | seq h e₆ =>
  cases h with | seq e₄ h => cases h with | seq c e₅ =>
  have := Exec.seq (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ e₄))) (Exec.seq c (Exec.seq e₅ e₆))
  simp only [List.append_assoc] at this ⊢
  exact this

theorem open_exec {x : Impl.ChaCha20.X86_64.Callee} {b : Impl.Poly1305.X86_64.Blocks} {s s' : State}
    {t : List Leak} (h : Exec isa («open» x b) s t s') :
    Exec isa (.seq (openPre b) (.seq (.call x.name x.code) openPost)) s t s' := by
  cases h with | seq e₁ h => cases h with | seq e₂ h => cases h with | seq e₃ h => cases h with | seq e₄ h =>
  cases h with | seq e₅ h => cases h with | seq h e₈ => cases h with | seq e₆ h => cases h with | seq c e₇ =>
  have := Exec.seq (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ e₆)))))
    (Exec.seq c (Exec.seq e₇ e₈))
  simp only [List.append_assoc] at this ⊢
  exact this

theorem RelCT.of_exec {P Q : State → State → Prop} {c c' : Prog isa}
    (he : ∀ {s t s'}, Exec isa c s t s' → Exec isa c' s t s') (h : RelCT isa P c' Q) : RelCT isa P c Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (he e₁) (he e₂)

theorem sealPre_ok (b : Impl.Poly1305.X86_64.Blocks) {s₀ : State} (hp : APre s₀) :
    WP isa (sealPre b) s₀ (XArgs s₀) := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (macPad_ok b hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp) h₁.inv.r15
    h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, _⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  exact WP.seq (WP.mono (lengths_ok hp i₂ (by rw [cs₂ _ (by simp [calleeSaved]), h₁.rbp]))
    fun _ ⟨i₃, _⟩ => cryptArgs_ok hp i₃)

theorem openPre_ok (b : Impl.Poly1305.X86_64.Blocks) {s₀ : State} (hp : APre s₀) :
    WP isa (openPre b) s₀ (XArgs s₀) := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (macPad_ok b hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp) h₁.inv.r15
    h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, _⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  refine WP.seq (WP.mono (macPad_ok b hp (p := .r14) (n := .r13) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₂.r15
    i₂.rsp i₂.rd i₂.wr i₂.r14 (by rw [i₂.r13]; exact hL s₀))
    fun s₃ ⟨cs₃, rd₃, wr₃, f₃, _⟩ => ?_)
  have i₃ := mac_inv hp i₂ cs₃ rd₃ wr₃ f₃
  refine WP.seq (WP.mono (lengths_ok hp i₃ (by rw [cs₃ _ (by simp [calleeSaved]),
    cs₂ _ (by simp [calleeSaved]), h₁.rbp])) fun s₄ ⟨i₄, _⟩ => ?_)
  exact WP.seq (WP.mono (absorbLengths_ok b hp i₄) fun _ ⟨i₅, _⟩ => cryptArgs_ok hp i₅)

/-! ## After the call -/

/-- What is known after the call of `vg_chacha20_xor`, in one run. -/
structure After (s₀ s : State) : Prop where
  rsi : s.gpr .rsi = off (cx s₀) 128
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r13 : s.gpr .r13 = s₀.gpr .r8
  r14 : s.gpr .r14 = dp s₀
  wr : s.wr = s₀.wr

/-- The taint after the call: `rsi` points at `ctx + 128`, and the lengths of
the regions are those on entry. -/
def τ₁ : X86_64.Taint.T :=
  { regs := .ofList [.rsi, .rsp, .r13, .r14], flags := false, lens := [1024, 0], bases := [(.rsi, 0, 128)] }

section
variable {s₀ s₀' : State} (hp : APre s₀) (hp' : APre s₀') (hq : pubX86_64 s₀ s₀')

omit hp' in
include hp in
theorem After.wf {s : State} (h : After s₀ s) : X86_64.Taint.Wf τ₁ s := by
  have hw : s.wr = [ctxR s₀, dR s₀] := by rw [h.wr, hp.wr]
  refine ⟨fun _ => ⟨by simp [hw, τ₁], by simp [hw, hp.c_d], by simp [hw, (Nat.le_of_lt (s₀.gpr .r8).isLt)]⟩, fun p hm => ?_⟩
  simp only [τ₁, List.mem_singleton] at hm
  subst hm
  simp [X86_64.Taint.region, hw, h.rsi, off_eq]

include hp hp' hq in
theorem agree₁ {s₁ s₂ : State} (h₁ : After s₀ s₁) (h₂ : After s₀' s₂) : X86_64.Taint.Agree τ₁ s₁ s₂ := by
  obtain ⟨p1, -, -, p4, p5, p6⟩ := hq
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, h₁.wf hp, h₂.wf hp', ?_, ?_, X86_64.Taint.noLo⟩
  · simp only [τ₁, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.rsi, h₂.rsi, cx, cx, p1]
    · rw [h₁.rsp, h₂.rsp, p6]
    · rw [h₁.r13, h₂.r13, p5]
    · rw [h₁.r14, h₂.r14, dp, dp, p4]
  · rw [h₁.wr, h₂.wr, hp.wr, hp'.wr, ctxR, ctxR, dR, dR, cx, cx, dp, dp, L, L, p1, p4, p5]
  · intro sl h; simp [τ₁] at h
  · intro sl h; simp [τ₁] at h

include hp hp' hq in
/-- The call of any implementation `v` of `vg_chacha20_xor`. -/
theorem call_rel (v : Proof.ChaCha20.X86_64.XorImpl) :
    RelCT isa (fun s₁ s₂ => XArgs s₀ s₁ ∧ XArgs s₀' s₂) (.call v.callee.name v.callee.code)
      fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂ := by
  obtain ⟨p1, -, -, p4, p5, p6⟩ := hq
  have ct := RelCT.callEx (n := v.callee.name) (P := fun s₁ s₂ => XArgs s₀ s₁ ∧ XArgs s₀' s₂) v.ok v.ct fun s₁ s₂ ⟨a₁, a₂⟩ =>
    ⟨[], _, [], _, a₁.pre hp v, a₂.pre hp' v, by
      simp only [Proof.ChaCha20.xorStack, Proof.ChaCha20.xorX86_64, State.withRegions_gpr,
        State.callEntry_rsp, callEntry_gpr' s₁ (by decide : Reg.rdi ≠ .rsp),
        callEntry_gpr' s₁ (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s₁ (by decide : Reg.rdx ≠ .rsp),
        callEntry_gpr' s₁ (by decide : Reg.rcx ≠ .rsp), callEntry_gpr' s₂ (by decide : Reg.rdi ≠ .rsp),
        callEntry_gpr' s₂ (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s₂ (by decide : Reg.rdx ≠ .rsp),
        callEntry_gpr' s₂ (by decide : Reg.rcx ≠ .rsp), a₁.rdi, a₁.rsi, a₁.rdx, a₁.rcx, a₁.rsp, a₂.rdi,
        a₂.rsi, a₂.rdx, a₂.rcx, a₂.rsp, cx, dp, p1, p4, p5, p6]
      exact ⟨trivial, trivial, trivial, trivial, trivial⟩,
      covers_nil_append (covers_left _ (a₁.hw hp)), a₁.hw hp, covers_nil_append (covers_left _ (a₂.hw hp')),
      a₂.hw hp', by rw [a₁.rsp, a₂.rsp, p6]⟩
  have after : ∀ {σ₀ s : State}, APre σ₀ → XArgs σ₀ s →
      WP isa (.call v.callee.name v.callee.code) s (After σ₀) := fun hp a =>
    a.call hp v fun _ _ wr cs _ rsi _ =>
      ⟨rsi, by rw [cs _ calleeSaved_rsp, a.rsp], by rw [cs _ (by simp [calleeSaved]), a.r13],
        by rw [cs _ (by simp [calleeSaved]), a.r14], by rw [wr, a.wr]⟩
  exact (ct.wp fun _ _ h => ⟨after hp h.1, after hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end

/-! ## `seal` and `open` -/

/-- The code around the call of `vg_chacha20_xor`, for each implementation of
`vg_poly1305_blocks`: the analysis descends into its calls, so it runs on
each implementation's code. -/
theorem sealPre_taint (b : Impl.Poly1305.X86_64.Blocks) :
    ∃ h, (taint.check τ₀ (sealPre b) h).isSome = true := by
  cases b <;> exact ⟨_, by taint_decide⟩

theorem sealPost_taint (b : Impl.Poly1305.X86_64.Blocks) :
    ∃ h, (taint.check τ₁ (sealPost b) h).isSome = true := by
  cases b <;> exact ⟨_, by taint_decide⟩

theorem openPre_taint (b : Impl.Poly1305.X86_64.Blocks) :
    ∃ h, (taint.check τ₀ (openPre b) h).isSome = true := by
  cases b <;> exact ⟨_, by taint_decide⟩

theorem openPost_taint : ∃ h, (taint.check τ₁ openPost h).isSome = true := ⟨_, by taint_decide⟩

section
variable (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ s₀' : State} (h₀ : preX86_64 s₀) (h₀' : preX86_64 s₀')
  (hq : pubX86_64 s₀ s₀')
include h₀ h₀' hq

theorem seal_rel : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («seal» v.callee v.poly) fun _ _ => True := by
  have hp := APre.of _ h₀
  have hp' := APre.of _ h₀'
  obtain ⟨_, hpre⟩ := sealPre_taint v.poly
  obtain ⟨_, hpost⟩ := sealPost_taint v.poly
  have pre := ((RelCT.taint (A := taint) (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') τ₀
    (fun _ _ h => h.1 ▸ h.2 ▸ agree₀ h₀ h₀' hq) hpre).wp (F₁ := XArgs s₀) (F₂ := XArgs s₀') fun _ _ h =>
    ⟨by rw [h.1]; exact sealPre_ok v.poly hp, by rw [h.2]; exact sealPre_ok v.poly hp'⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have post := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂) τ₁
    (fun _ _ h => agree₁ hp hp' hq h.1 h.2) hpost
  exact RelCT.of_exec seal_exec (pre.seq ((call_rel hp hp' hq v).seq post))

theorem open_rel : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («open» v.callee v.poly) fun _ _ => True := by
  have hp := APre.of _ h₀
  have hp' := APre.of _ h₀'
  obtain ⟨_, hpre⟩ := openPre_taint v.poly
  obtain ⟨_, hpost⟩ := openPost_taint
  have pre := ((RelCT.taint (A := taint) (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') τ₀
    (fun _ _ h => h.1 ▸ h.2 ▸ agree₀ h₀ h₀' hq) hpre).wp (F₁ := XArgs s₀) (F₂ := XArgs s₀') fun _ _ h =>
    ⟨by rw [h.1]; exact openPre_ok v.poly hp, by rw [h.2]; exact openPre_ok v.poly hp'⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have post := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂) τ₁
    (fun _ _ h => agree₁ hp hp' hq h.1 h.2) hpost
  exact RelCT.of_exec open_exec (pre.seq ((call_rel hp hp' hq v).seq post))

end

end VG.Proof.ChaCha20Poly1305.X86_64
