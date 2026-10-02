import VerifiedGarbage.Proof.Aes.X86_64.Variant
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-!
# AES-CMAC on x86-64: calling `vg_aes_ctr32` on one block

`ctr_call`: a call of any implementation of `vg_aes_ctr32` with the counter
block `C`, one data block `D` holding zeros, and working space `S`, from its
contract (with `WP.call`): `D` then holds `CIPH_K(C)`, as bytes
(`Cmac.aesWith`), and only `C`, `D`, `S` and the return address change.
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.Aes.bytesAt m' p n = Spec.Aes.bytesAt m p n := by
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- The return address a call stores. -/
theorem callEntry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

theorem ofBytes_zeros : Spec.Gcm.ofBytes (Spec.Cmac.zeros 16) = 0 := by decide

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 64 R).toNat = R := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem one_toNat : (1 : BitVec 64).toNat = 1 := rfl

/-- What a call of `vg_aes_ctr32` on one block needs. -/
structure CallPre (s : State) (W C D S : Addr) (R : Nat) : Prop where
  rdi : s.gpr .rdi = W
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = D
  r8 : s.gpr .r8 = 1
  r9 : s.gpr .r9 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wc : (⟨W, 240⟩ : Region).Disjoint ⟨C, 16⟩
  wd : (⟨W, 240⟩ : Region).Disjoint ⟨D, 16⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16⟩ : Region).Disjoint ⟨S, 2048⟩
  stkW : (below (s.gpr .rsp) 8).Disjoint ⟨W, 240⟩
  stkC : (below (s.gpr .rsp) 8).Disjoint ⟨C, 16⟩
  stkD : (below (s.gpr .rsp) 8).Disjoint ⟨D, 16⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 2048⟩
  wrap : D.toNat + 16 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩] s.wr
  zero : Spec.Aes.bytesAt s.mem D 16 = Spec.Cmac.zeros 16

/-- What a call of `vg_aes_ctr32` on one block leaves. -/
structure CallPost (s : State) (W C D S : Addr) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩, below (s.gpr .rsp) 8] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem D 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1))) (Spec.Aes.bytesAt s.mem C 16)

/-- `vg_aes_ctr32`'s precondition, on entry to a call with the regions it is given. -/
theorem CallPre.ctr_pre {s : State} {W C D S : Addr} {R : Nat} (h : CallPre s W C D S R) :
    Proof.Aes.ctr32X86_64.pre
      (s.callEntry.withRegions [⟨W, 240⟩] [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [Proof.Aes.ctr32X86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hR,
    one_toNat, Nat.mul_one]
  exact ⟨trivial, trivial, h.wc, by simpa using h.wd, h.ws, by simpa using h.cd, h.cs,
    by simpa using h.ds, h.stkC, by simpa using h.stkD, h.stkS, by simpa using h.wrap, h.rounds⟩

theorem ctr_call (v : Ctr32Impl) {s : State} {W C D S : Addr} {R : Nat} (h : CallPre s W C D S R) :
    WP isa (.call v.callee.name v.callee.code) s (CallPost s W C D S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := Proof.Aes.ctr32X86_64) v.ok v.nosp (by rw [v.depth]; decide)
    (rd := [⟨W, 240⟩]) (wr := [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩]) h.ctr_pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [v.depth] at hf
  refine ⟨hrd, hwr, hcs, ?_, ?_⟩
  · simpa using hf
  · obtain ⟨hdata, -⟩ := hpost
    simp only [State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR,
      one_toNat] at hdata
    have fE := callEntry_frame s
    have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with rfl | rfl | rfl <;> decide
    have eW := bytesAt_frame fE (p := W) (n := 16 * (R + 1))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.stkW.sub_right (Region.sub_prefix hRb)).symm)
      (by omega)
    have eC := bytesAt_frame fE (p := C) (n := 16)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.stkC.symm) (by decide)
    have eD := bytesAt_frame fE (p := D) (n := 16)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.stkD.symm) (by decide)
    have one : ∀ m : Mem, Spec.Gcm.blocksAt m D 1 = [Spec.Gcm.blockAt m D] := fun m => by
      simp [Spec.Gcm.blocksAt]
    have bD : Spec.Gcm.blockAt s.callEntry.mem D = 0 := by
      rw [Spec.Gcm.blockAt, eD, h.zero, ofBytes_zeros]
    have bC : Spec.Gcm.blockAt s.callEntry.mem C = Spec.Gcm.ofBytes (Spec.Aes.bytesAt s.mem C 16) := by
      rw [Spec.Gcm.blockAt, eC]
    rw [one, one, bD, bC, eW, Proof.Cmac.ctr32_one, List.cons.injEq] at hdata
    rw [← hm₂, Proof.Cmac.bytesAt_blockAt, hdata.1,
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _)]

/-- Calls of `vg_aes_ctr32` on one block, with the same arguments in both
runs, are constant time. -/
theorem ctr_rel (v : Ctr32Impl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W C D S : Addr, ∃ R : Nat,
      CallPre s₁ W C D S R ∧ CallPre s₂ W C D S R ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call v.callee.name v.callee.code) fun _ _ => True := by
  refine RelCT.callEx v.ok v.ct fun s₁ s₂ hp => ?_
  obtain ⟨W, C, D, S, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.ctr_pre, h₂.ctr_pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.ctr32X86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.CmacAes.X86_64
