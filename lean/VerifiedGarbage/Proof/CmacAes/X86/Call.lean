import VerifiedGarbage.Proof.Aes.X86.Ctr32
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Impl.CmacAes.X86

/-!
# AES-CMAC on x86: calling `vg_aes_ctr32` on one block

Untrusted: everything here is checked by Lean.

`ctr_call`: the frame that pushes `vg_aes_ctr32`'s six arguments (`eax` the
schedule, `ecx` the rounds, `edx` the counter block `C`, `ebx` the data
block `D` holding zeros, `edi = 1` and `ebp` the working space `S`) around
its call: `D` then holds `CIPH_K(C)`, as bytes (`Cmac.aesWith`), and only
`C`, `D`, `S` and the 28 bytes below `esp` change in memory. `ctr_rel`: such
calls are constant time, by `vg_aes_ctr32`'s own proof.
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86

theorem ofBytes_zeros : Spec.Gcm.ofBytes (Spec.Cmac.zeros 16) = 0 := by decide

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 32 R).toNat = R := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem ctr_nosp : NoSp Impl.Aes.X86.ctr32 := NoSp.of_all (by decide +kernel)

theorem ctr_stack : stackUse Impl.Aes.X86.ctr32 = 0 := by decide +kernel

/-- The registers the call pushes, as `vg_aes_ctr32`'s arguments. -/
abbrev ctrRegs : List Reg := [.ebp, .edi, .ebx, .edx, .ecx, .eax]

/-- What a call of `vg_aes_ctr32` on one block needs. -/
structure CtrPre (s : State) (W C D S : BitVec 32) (R : Nat) : Prop where
  eax : s.gpr .eax = W
  ecx : s.gpr .ecx = BitVec.ofNat 32 R
  edx : s.gpr .edx = C
  ebx : s.gpr .ebx = D
  edi : s.gpr .edi = 1
  ebp : s.gpr .ebp = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  esp : 28 ≤ (s.gpr .esp).toNat
  wc : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨C.setWidth 64, 16⟩
  wd : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨D.setWidth 64, 16⟩
  ws : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨S.setWidth 64, 2048⟩
  cd : (⟨C.setWidth 64, 16⟩ : Region).Disjoint ⟨D.setWidth 64, 16⟩
  cs : (⟨C.setWidth 64, 16⟩ : Region).Disjoint ⟨S.setWidth 64, 2048⟩
  ds : (⟨D.setWidth 64, 16⟩ : Region).Disjoint ⟨S.setWidth 64, 2048⟩
  bw : (below (s.gpr .esp) 28).Disjoint ⟨W.setWidth 64, 240⟩
  bc : (below (s.gpr .esp) 28).Disjoint ⟨C.setWidth 64, 16⟩
  bd : (below (s.gpr .esp) 28).Disjoint ⟨D.setWidth 64, 16⟩
  bs : (below (s.gpr .esp) 28).Disjoint ⟨S.setWidth 64, 2048⟩
  hW : W.toNat + 240 ≤ 2 ^ 32
  hC : C.toNat + 16 ≤ 2 ^ 32
  hD : D.toNat + 16 ≤ 2 ^ 32
  hS : S.toNat + 2048 ≤ 2 ^ 32
  reads : Covers [⟨W.setWidth 64, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨C.setWidth 64, 16⟩, ⟨D.setWidth 64, 16⟩, ⟨S.setWidth 64, 2048⟩] s.wr
  zero : Spec.Aes.bytesAt s.mem (D.setWidth 64) 16 = Spec.Cmac.zeros 16

/-- What a call of `vg_aes_ctr32` on one block leaves. -/
structure CtrPost (s : State) (W C D S : BitVec 32) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C.setWidth 64, 16⟩, ⟨D.setWidth 64, 16⟩, ⟨S.setWidth 64, 2048⟩, below (s.gpr .esp) 28]
    s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (D.setWidth 64) 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (W.setWidth 64) (16 * (R + 1)))
      (Spec.Aes.bytesAt s.mem (C.setWidth 64) 16)

/-- The regions `vg_aes_ctr32` is called with. -/
abbrev ctrRd (E W : BitVec 32) : List Region := [⟨W.setWidth 64, 240⟩, ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩]
abbrev ctrWr (C D S : BitVec 32) : List Region :=
  [⟨C.setWidth 64, 16⟩, ⟨D.setWidth 64, 16⟩, ⟨S.setWidth 64, 2048⟩]

theorem hrs : Reg.esp ∉ ctrRegs := by decide

namespace CtrPre
variable {s : State} {W C D S : BitVec 32} {R : Nat} (h : CtrPre s W C D S R)
include h

theorem fit : 4 * ctrRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem args : arg (pushed ctrRegs s).callEntry 0 = W ∧ arg (pushed ctrRegs s).callEntry 1 = BitVec.ofNat 32 R ∧
    arg (pushed ctrRegs s).callEntry 2 = C ∧ arg (pushed ctrRegs s).callEntry 3 = D ∧
    arg (pushed ctrRegs s).callEntry 4 = 1 ∧ arg (pushed ctrRegs s).callEntry 5 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit hrs (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx, h.edi, h.ebp]

theorem sub24 : Region.Sub (below (s.gpr .esp) 24) (below (s.gpr .esp) 28) := below_sub (by omega) h.esp

theorem sub4 : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 28).setWidth 64, 4⟩ (below (s.gpr .esp) 28) := by
  have := below_inner (sp := s.gpr .esp) (a := 4) (b := 28) (k := 24) (by omega) h.esp
  rw [show s.gpr .esp - BitVec.ofNat 32 28 = s.gpr .esp - BitVec.ofNat 32 24 - BitVec.ofNat 32 4 by
    rw [← VG.Offset.sub_add_eq]; rfl]
  exact this

theorem callPre : CallPre Proof.Aes.ctr32X86 ctrRegs (ctrRd (s.gpr .esp) W) (ctrWr C D S) s := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args
  have hR := toNat_rounds h.rounds
  have eA : argAddr (pushed ctrRegs s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 24).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed ctrRegs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 28 := by
    rw [callEntry_esp']; rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Aes.ctr32X86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, eA, eSp, hR,
      show (1 : BitVec 32).toNat = 1 from rfl, Nat.mul_one]
    refine ⟨trivial, trivial, h.wc, h.wd, h.ws, h.cd, h.cs, h.ds, (h.bc.sub_left h.sub24).symm.symm,
      (h.bd.sub_left h.sub24), (h.bs.sub_left h.sub24), h.bc.sub_left h.sub4, h.bd.sub_left h.sub4,
      h.bs.sub_left h.sub4, h.hW, h.hC, h.hD, h.hS, ?_, h.rounds⟩
    rw [sub_toNat (by have := h.esp; omega)]; have := (s.gpr .esp).isLt; omega
  · intro a n ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a n ⟨_, List.mem_singleton_self _, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a n ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a n hi
    obtain ⟨r', hr', hc'⟩ := h.writes a n hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end CtrPre

theorem ctr_call {s : State} {W C D S : BitVec 32} {R : Nat} (h : CtrPre s W C D S R) :
    WP isa ctrCall s (CtrPost s W C D S R) := by
  have hR := toNat_rounds h.rounds
  have hR' : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  unfold ctrCall
  refine WP.callWith (rs := ctrRegs) (k := Proof.Aes.ctr32X86) Proof.Aes.X86.ctr32_correct ctr_nosp (by simp) hrs
    (by rw [ctr_stack]; have := h.esp; simp only [List.length_cons, List.length_nil]; omega) h.callPre
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args
  rw [ctr_stack] at f'
  have fE := callEntry_frame h.fit hrs
  rw [show 4 * ctrRegs.length + 4 = 28 from rfl] at fE
  have keep : ∀ {p : BitVec 32} {n k : Nat}, (below (s.gpr .esp) 28).Disjoint ⟨p.setWidth 64, n⟩ → k ≤ n →
      n ≤ 240 →
      Spec.Aes.bytesAt (pushed ctrRegs s).callEntry.mem (p.setWidth 64) k = Spec.Aes.bytesAt s.mem (p.setWidth 64) k :=
    fun hd hk hn => Proof.Cmac.bytesAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hd.sub_right (Region.sub_prefix hk)).symm) (by omega)
  obtain ⟨hdata, -⟩ := post
  simp only [arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, hR,
    show (1 : BitVec 32).toNat = 1 from rfl, m₂] at hdata
  have one : ∀ m : Mem, Spec.Gcm.blocksAt m (D.setWidth 64) 1 = [Spec.Gcm.blockAt m (D.setWidth 64)] :=
    fun m => by simp [Spec.Gcm.blocksAt]
  have bD : Spec.Gcm.blockAt (pushed ctrRegs s).callEntry.mem (D.setWidth 64) = 0 := by
    rw [Spec.Gcm.blockAt, keep h.bd (le_refl _) (by decide), h.zero, ofBytes_zeros]
  rw [one, one, bD, Proof.Cmac.ctr32_one, List.cons.injEq] at hdata
  refine ⟨rd', wr', cs', ?_, ?_⟩
  · exact f'.mono fun r hr => by simp only [List.cons_append, List.nil_append] at hr; simpa using hr
  · rw [Proof.Cmac.bytesAt_blockAt, hdata.1, Spec.Gcm.blockAt, keep h.bw hR' (le_refl _), keep h.bc (le_refl _) (by decide),
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _)]

/-- Calls of `vg_aes_ctr32` on one block, with the same arguments and stack
pointer in both runs, are constant time. -/
theorem ctr_rel {W C D S E : BitVec 32} {R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → CtrPre s₁ W C D S R ∧ CtrPre s₂ W C D S R ∧ s₁.gpr .esp = E ∧ s₂.gpr .esp = E) :
    RelCT isa P ctrCall fun _ _ => True := by
  refine RelCT.callWith Proof.Aes.X86.ctr32_correct Proof.Aes.X86.ctr32_ct (ctrRd E W) (ctrWr C D S)
    fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]
  · rw [a5, b5]

end VG.Proof.CmacAes.X86
