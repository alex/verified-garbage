import VerifiedGarbage.Proof.Poly1305.X86_64.Init
import VerifiedGarbage.Proof.Poly1305.X86_64.Blocks
import VerifiedGarbage.Proof.Poly1305.X86_64.Finalize
import VerifiedGarbage.Proof.ChaCha20.X86_64.Xor
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64

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
    Region.Sub ⟨p + BitVec.ofNat 64 a, n⟩ ⟨p, len⟩ := by
  intro x hx
  simp only [Region.Contains] at *
  have : (x - p).toNat ≤ (x - (p + BitVec.ofNat 64 a)).toNat + a := by
    rw [show x - p = (x - (p + BitVec.ofNat 64 a)) + BitVec.ofNat 64 a by bv_omega,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega

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
  VG.Proof.ChaCha20.X86_64.Xor.stateAt_frame hf hd

/-- The return address a call stores. -/
theorem callEntry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega))

/-! ## The callees' registers -/

theorem init_keeps : ((instrs Impl.Poly1305.X86_64.init).all fun i =>
    !Taint.clobbers i .rdi && !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem blocks_keeps : ((instrs Impl.Poly1305.X86_64.blocks).all fun i =>
    !Taint.clobbers i .rdi && !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem finalize_keeps : ((instrs Impl.Poly1305.X86_64.finalize).all fun i =>
    !Taint.clobbers i .rdi && !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem init_depth : Impl.Poly1305.X86_64.init.depth = 0 := by decide +kernel
theorem blocks_depth : Impl.Poly1305.X86_64.blocks.depth = 0 := by decide +kernel
theorem finalize_depth : Impl.Poly1305.X86_64.finalize.depth = 0 := by decide +kernel
theorem xor_depth : Impl.ChaCha20.X86_64.Xor.xor.depth = 1 := by decide +kernel

theorem keeps_of {c : Prog isa} {p : Instr → Bool} (h : (instrs c).all p = true) {r : Reg}
    (hr : ∀ i, p i = true → Taint.clobbers i r = false) : ∀ i ∈ instrs c, Taint.clobbers i r = false :=
  fun i hi => hr i (List.all_eq_true.mp h i hi)

theorem xor_keeps_rsp : ∀ i ∈ instrs Impl.ChaCha20.X86_64.Xor.xor, Taint.clobbers i .rsp = false := by
  have : ((instrs Impl.ChaCha20.X86_64.Xor.xor).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  exact keeps_of this fun i h => by simpa using h

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
    rwa [bytesAt_frame (callEntry_frame s) (by simpa using hsK.symm) (by omega)] at hpost

/-! ## `vg_poly1305_blocks` -/

theorem blocks_call {s : State} {P p : Addr} {n : Nat} (hrdi : s.gpr .rdi = P) (hrsi : s.gpr .rsi = p)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) (hn : 16 * n < 2 ^ 64)
    (hdj : (⟨P, 128⟩ : Region).Disjoint ⟨p, 16 * n⟩) (hwrap : p.toNat + 16 * n ≤ 2 ^ 64)
    (hsP : (below (s.gpr .rsp) 8).Disjoint ⟨P, 128⟩) (hsp : (below (s.gpr .rsp) 8).Disjoint ⟨p, 16 * n⟩)
    (hc : Covers ([⟨p, 16 * n⟩] ++ [⟨P, 128⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨P, 128⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨P, 128⟩, below (s.gpr .rsp) 8] s.mem s'.mem → s'.gpr .rdi = P →
      (∀ key msg, Repr s.mem P key msg → Repr s'.mem P key (msg ++ bytesAt s.mem p (16 * n))) → Q s') :
    WP isa (.call "vg_poly1305_blocks" Impl.Poly1305.X86_64.blocks) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine WP.call (k := Proof.Poly1305.blocksX86_64) Proof.Poly1305.X86_64.blocks_ok
    (keeps_of blocks_keeps fun _ h => and_right h) (by rw [blocks_depth]; decide)
    (rd := [⟨p, 16 * n⟩]) (wr := [⟨P, 128⟩]) ?_ hc hw ?_
  · simp only [Proof.Poly1305.blocksX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi,
      hrsi, hrdx, hn']
    exact ⟨trivial, trivial, hdj, hsP, hwrap⟩
  · intro s' hrd hwr hcs hf hkeep ⟨s₂, hm₂, _, hpost⟩
    rw [blocks_depth] at hf
    refine hQ s' hrd hwr hcs hf (by rw [hkeep .rdi (keeps_of blocks_keeps fun _ h => and_left h), hrdi])
      fun key msg hr => ?_
    simp only [Proof.Poly1305.blocksX86_64, State.withRegions_gpr, State.withRegions_mem,
      callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi, hrsi, hrdx, hn', hm₂] at hpost
    have h := hpost key msg (Repr.frame (callEntry_frame s) (h := hr) (by simpa using hsP.symm))
    rwa [bytesAt_frame (callEntry_frame s) (by simpa using hsp.symm) (by omega)] at h

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

/-- The contract of `vg_chacha20_xor`, and that it returns with `rsi = buf`. -/
def xorK : Contract isa where
  pre := Proof.ChaCha20.xorX86_64.pre
  post s s' := Proof.ChaCha20.xorX86_64.post s s' ∧ s'.gpr .rsi = s.gpr .rcx
  pub := Proof.ChaCha20.xorX86_64.pub

theorem xor_call {s : State} {S D B : Addr} {n : Nat} (hrdi : s.gpr .rdi = S) (hrsi : s.gpr .rsi = D)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) (hrcx : s.gpr .rcx = B) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩) (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hwrap : D.toNat + n ≤ 2 ^ 64)
    (hsS : (below (s.gpr .rsp) 16).Disjoint ⟨S, 64⟩) (hsD : (below (s.gpr .rsp) 16).Disjoint ⟨D, n⟩)
    (hsB : (below (s.gpr .rsp) 16).Disjoint ⟨B, 320⟩)
    (hc : Covers ([] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩, below (s.gpr .rsp) 16] s.mem s'.mem → s'.gpr .rsi = B →
      Spec.ChaCha20.bytesAt s'.mem D n =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem D n) (keystream (stateAt s.mem S) n) → Q s') :
    WP isa (.call "vg_chacha20_xor" Impl.ChaCha20.X86_64.Xor.xor) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have h8 : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 16) := below_sub (by omega) (by omega)
  have h8' : Region.Sub ⟨s.gpr .rsp - 8 - 8, 8⟩ (below (s.gpr .rsp) 16) := by
    intro x hx
    simp only [Region.Contains] at *
    bv_omega
  refine WP.call (k := xorK) Proof.ChaCha20.X86_64.Xor.xor_rsi xor_keeps_rsp
    (by rw [xor_depth]; decide) (rd := []) (wr := [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) ?_ hc hw ?_
  · simp only [xorK, Proof.ChaCha20.xorX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rcx ≠ .rsp), hrdi, hrsi, hrdx, hrcx, hn']
    exact ⟨trivial, trivial, hSD, hSB, hDB, hsS.sub_left h8, hsD.sub_left h8, hsB.sub_left h8,
      hsS.sub_left h8', hsD.sub_left h8', hsB.sub_left h8', hwrap⟩
  · intro s' hrd hwr hcs hf hkeep ⟨s₂, hm₂, hg₂, hpost, hrsi₂⟩
    rw [xor_depth] at hf
    refine hQ s' hrd hwr hcs hf ?_ ?_
    · rw [← hg₂ .rsi (by decide), hrsi₂, State.withRegions_gpr, callEntry_gpr' s (by decide), hrcx]
    · simp only [Proof.ChaCha20.xorX86_64, State.withRegions_gpr, State.withRegions_mem,
        callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp),
        callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi, hrsi, hrdx, hn', hm₂] at hpost
      rw [hpost, bytesAt_eq, bytesAt_frame (callEntry_frame s) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact (hsD.sub_left h8).symm) (by omega),
        stateAt_frame (callEntry_frame s) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact (hsS.sub_left h8).symm)]

end VG.Proof.ChaCha20Poly1305.X86_64
