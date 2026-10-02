import VerifiedGarbage.Proof.Aes.X86.Ctr32
import VerifiedGarbage.Proof.Aes.X86.Ctr32CT
import VerifiedGarbage.Proof.Aes.X86.ExpandKey
import VerifiedGarbage.Proof.Aes.X86.ExpandKeyCT
import VerifiedGarbage.Proof.Gcm.X86.Ghash
import VerifiedGarbage.Proof.Gcm.X86.GhashCT
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.AesGcm.X86.CT
import VerifiedGarbage.Impl.AesGcm.X86
import VerifiedGarbage.Proof.Gcm.Compose

/-!
# AES-GCM on x86: the calls

Untrusted: everything here is checked by Lean. Each call of `vg_ghash`,
`vg_aes_ctr32` and `vg_aes_expand_key`, in a frame of its arguments, from
the callee's contract (`WP.callWith`): what it needs of the registers it
pushes and of the regions it is given (`GhCall`, `CtrCall`, `KeyCall`), and
what it leaves (`GhPost`, `CtrPost`, `KeyPost`), in terms of the memory
before the call; and that it is constant time (`gh_ct`, `ctr_ct`, `key_ct`)
by the callee's own proof, when the arguments are the same in both runs.
-/

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.Impl.AesGcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctr32 aesWith)

/-- The 64-bit address of a 32-bit pointer. -/
abbrev w64 (x : BitVec 32) : Addr := x.setWidth 64

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem toNat_add32 {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, toNat_ofNat32 (by omega), Nat.mod_eq_of_lt h]

theorem w64_add {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    w64 (x + BitVec.ofNat 32 k) = w64 x + BitVec.ofNat 64 k := addr_eq h

theorem toNat_w64 (x : BitVec 32) : (w64 x).toNat = x.toNat := by
  simp only [w64, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  rw [blockAt, blockAt, bytesAt_frame hf hd (by decide)]

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    blocksAt m' p n = blocksAt m p n := by
  rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, bytesAt_frame hf hd hn]

theorem one_disj {k : Region} {p : Addr} {n : Nat} (h : k.Disjoint ⟨p, n⟩) :
    ∀ r ∈ [k], (⟨p, n⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact h.symm

/-! ## The callees -/

theorem gh_nosp : NoSp Impl.Gcm.X86.ghash := NoSp.of_all (by decide +kernel)
theorem gh_stack : stackUse Impl.Gcm.X86.ghash = 0 := by decide +kernel
theorem ctr_nosp : NoSp Impl.Aes.X86.ctr32 := NoSp.of_all (by decide +kernel)
theorem ctr_stack : stackUse Impl.Aes.X86.ctr32 = 0 := by decide +kernel
theorem key_nosp : NoSp Impl.Aes.X86.expandKey := NoSp.of_all (by decide +kernel)
theorem key_stack : stackUse Impl.Aes.X86.expandKey = 0 := by decide +kernel

/-! ## `vg_ghash` -/

abbrev ghRegs : List Reg := [.ebp, .edi, .ebx, .edx, .eax]

theorem ghRegs_esp : Reg.esp ∉ ghRegs := by decide

/-- What a call of `vg_ghash` needs: the hash subkey at `H`, the accumulator
at `Y`, `n` blocks at `D` and working space at `S`. -/
structure GhCall (s : State) (H Y D S : BitVec 32) (n : Nat) : Prop where
  eax : s.gpr .eax = H
  edx : s.gpr .edx = Y
  ebx : s.gpr .ebx = D
  edi : s.gpr .edi = BitVec.ofNat 32 n
  ebp : s.gpr .ebp = S
  esp : 24 ≤ (s.gpr .esp).toNat
  hy : (⟨w64 H, 16⟩ : Region).Disjoint ⟨w64 Y, 16⟩
  hs : (⟨w64 H, 16⟩ : Region).Disjoint ⟨w64 S, 256⟩
  yd : (⟨w64 Y, 16⟩ : Region).Disjoint ⟨w64 D, 16 * n⟩
  ys : (⟨w64 Y, 16⟩ : Region).Disjoint ⟨w64 S, 256⟩
  ds : (⟨w64 D, 16 * n⟩ : Region).Disjoint ⟨w64 S, 256⟩
  kh : (below (s.gpr .esp) 24).Disjoint ⟨w64 H, 16⟩
  ky : (below (s.gpr .esp) 24).Disjoint ⟨w64 Y, 16⟩
  kd : (below (s.gpr .esp) 24).Disjoint ⟨w64 D, 16 * n⟩
  ks : (below (s.gpr .esp) 24).Disjoint ⟨w64 S, 256⟩
  fH : H.toNat + 16 ≤ 2 ^ 32
  fY : Y.toNat + 16 ≤ 2 ^ 32
  fD : D.toNat + 16 * n ≤ 2 ^ 32
  fS : S.toNat + 256 ≤ 2 ^ 32
  reads : Covers [⟨w64 H, 16⟩, ⟨w64 D, 16 * n⟩] (s.rd ++ s.wr)
  writes : Covers [⟨w64 Y, 16⟩, ⟨w64 S, 256⟩] s.wr

/-- What a call of `vg_ghash` leaves. -/
structure GhPost (s : State) (H Y D S : BitVec 32) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨w64 Y, 16⟩, ⟨w64 S, 256⟩, below (s.gpr .esp) 24] s.mem s'.mem
  out : blockAt s'.mem (w64 Y) = ghashFrom (blockAt s.mem (w64 H)) (blockAt s.mem (w64 Y))
    (blocksAt s.mem (w64 D) n)

/-- The regions `vg_ghash` is called with. -/
abbrev ghRd (E H D : BitVec 32) (n : Nat) : List Region :=
  [⟨w64 H, 16⟩, ⟨w64 D, 16 * n⟩, below E 20]
abbrev ghWr (Y S : BitVec 32) : List Region := [⟨w64 Y, 16⟩, ⟨w64 S, 256⟩]

namespace GhCall
variable {s : State} {H Y D S : BitVec 32} {n : Nat} (h : GhCall s H Y D S n)
include h

theorem fit : 4 * ghRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem n_lt : n < 2 ^ 32 := by have := h.fD; omega

theorem args : arg (pushed ghRegs s).callEntry 0 = H ∧ arg (pushed ghRegs s).callEntry 1 = Y ∧
    arg (pushed ghRegs s).callEntry 2 = D ∧ arg (pushed ghRegs s).callEntry 3 = BitVec.ofNat 32 n ∧
    arg (pushed ghRegs s).callEntry 4 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit ghRegs_esp (by decide)] <;> simp [h.eax, h.edx, h.ebx, h.edi, h.ebp]

theorem sub20 : Region.Sub (below (s.gpr .esp) 20) (below (s.gpr .esp) 24) := below_sub (by omega) h.esp

theorem sub4 : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 24).setWidth 64, 4⟩ (below (s.gpr .esp) 24) := by
  have := below_inner (sp := s.gpr .esp) (a := 4) (b := 24) (k := 20) (by omega) h.esp
  rw [show s.gpr .esp - BitVec.ofNat 32 24 = s.gpr .esp - BitVec.ofNat 32 20 - BitVec.ofNat 32 4 by
    rw [← VG.Offset.sub_add_eq]; rfl]
  exact this

theorem callPre : CallPre Proof.Gcm.ghashX86 ghRegs (ghRd (s.gpr .esp) H D n) (ghWr Y S) s := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := h.args
  have hn := toNat_ofNat32 h.n_lt
  have eA : argAddr (pushed ghRegs s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed ghRegs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 24 := by
    rw [callEntry_esp']; rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Gcm.ghashX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, hn]
    refine ⟨trivial, trivial, h.hy, h.hs, h.yd, h.ys, h.ds, h.ky.sub_left h.sub20,
      h.ks.sub_left h.sub20, h.ky.sub_left h.sub4, h.ks.sub_left h.sub4, h.fH, h.fY, h.fD, h.fS, ?_⟩
    rw [sub_toNat (by have := h.esp; omega)]; have := (s.gpr .esp).isLt; omega
  · intro a m ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a m ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · obtain ⟨r', hr', hc'⟩ := h.reads a m ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a m ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a m hi
    obtain ⟨r', hr', hc'⟩ := h.writes a m hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end GhCall

theorem gh_call {s : State} {H Y D S : BitVec 32} {n : Nat} (h : GhCall s H Y D S n) :
    WP isa ghCall s (GhPost s H Y D S n) := by
  have hn := toNat_ofNat32 h.n_lt
  unfold ghCall
  refine WP.callWith (rs := ghRegs) (k := Proof.Gcm.ghashX86) Proof.Gcm.X86.ghash_correct gh_nosp (by simp)
    ghRegs_esp (by rw [gh_stack]; have := h.esp; simp only [List.length_cons, List.length_nil]; omega)
    h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, -⟩ := h.args
  rw [gh_stack] at f'
  have fE := callEntry_frame h.fit ghRegs_esp
  rw [show 4 * ghRegs.length + 4 = 24 from rfl] at fE
  simp only [Proof.Gcm.ghashX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, hn, m₂] at post
  refine ⟨rd', wr', cs', ?_, ?_⟩
  · exact f'.mono fun r hr => by simp only [List.cons_append, List.nil_append] at hr; simpa using hr
  · rw [post, blockAt_frame fE (one_disj h.kh), blockAt_frame fE (one_disj h.ky),
      blocksAt_frame fE (one_disj h.kd) (by have := h.fD; omega)]

/-- Calls of `vg_ghash` with the same arguments and stack pointer in both
runs are constant time. -/
theorem gh_ct {I : State → Prop} {H Y D S E : BitVec 32} {n : Nat}
    (h : ∀ s, I s → GhCall s H Y D S n ∧ s.gpr .esp = E) : CT I ghCall := by
  refine CT.callWith Proof.Gcm.X86.ghash_correct Proof.Gcm.X86.ghash_ct (ghRd E H D n) (ghWr Y S)
    fun s₁ s₂ i₁ i₂ => ?_
  obtain ⟨h₁, e₁⟩ := h s₁ i₁
  obtain ⟨h₂, e₂⟩ := h s₂ i₂
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]

/-! ## `vg_aes_ctr32` -/

abbrev ctrRegs : List Reg := [.ebp, .edi, .ebx, .edx, .ecx, .eax]

theorem ctrRegs_esp : Reg.esp ∉ ctrRegs := by decide

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 32 R).toNat = R :=
  toNat_ofNat32 (by omega)

/-- What a call of `vg_aes_ctr32` needs: the key schedule at `K` for `R`
rounds, the counter block at `C`, `n` blocks at `D` and working space at `S`. -/
structure CtrCall (s : State) (K C D S : BitVec 32) (R n : Nat) : Prop where
  eax : s.gpr .eax = K
  ecx : s.gpr .ecx = BitVec.ofNat 32 R
  edx : s.gpr .edx = C
  ebx : s.gpr .ebx = D
  edi : s.gpr .edi = BitVec.ofNat 32 n
  ebp : s.gpr .ebp = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  esp : 28 ≤ (s.gpr .esp).toNat
  kc : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 C, 16⟩
  kd : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, 16 * n⟩
  ks : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 S, 2048⟩
  cd : (⟨w64 C, 16⟩ : Region).Disjoint ⟨w64 D, 16 * n⟩
  cs : (⟨w64 C, 16⟩ : Region).Disjoint ⟨w64 S, 2048⟩
  ds : (⟨w64 D, 16 * n⟩ : Region).Disjoint ⟨w64 S, 2048⟩
  bk : (below (s.gpr .esp) 28).Disjoint ⟨w64 K, 240⟩
  bc : (below (s.gpr .esp) 28).Disjoint ⟨w64 C, 16⟩
  bd : (below (s.gpr .esp) 28).Disjoint ⟨w64 D, 16 * n⟩
  bs : (below (s.gpr .esp) 28).Disjoint ⟨w64 S, 2048⟩
  fK : K.toNat + 240 ≤ 2 ^ 32
  fC : C.toNat + 16 ≤ 2 ^ 32
  fD : D.toNat + 16 * n ≤ 2 ^ 32
  fS : S.toNat + 2048 ≤ 2 ^ 32
  reads : Covers [⟨w64 K, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨w64 C, 16⟩, ⟨w64 D, 16 * n⟩, ⟨w64 S, 2048⟩] s.wr

/-- What a call of `vg_aes_ctr32` leaves. -/
structure CtrPost (s : State) (K C D S : BitVec 32) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨w64 C, 16⟩, ⟨w64 D, 16 * n⟩, ⟨w64 S, 2048⟩, below (s.gpr .esp) 28] s.mem s'.mem
  out : blocksAt s'.mem (w64 D) n = ctr32 (aesWith R (bytesAt s.mem (w64 K) (16 * (R + 1))))
    (blockAt s.mem (w64 C)) (blocksAt s.mem (w64 D) n)
  ctr : blockAt s'.mem (w64 C) = Nat.repeat Spec.Gcm.inc32 n (blockAt s.mem (w64 C))

abbrev ctrRd (E K : BitVec 32) : List Region := [⟨w64 K, 240⟩, below E 24]
abbrev ctrWr (C D S : BitVec 32) (n : Nat) : List Region :=
  [⟨w64 C, 16⟩, ⟨w64 D, 16 * n⟩, ⟨w64 S, 2048⟩]

namespace CtrCall
variable {s : State} {K C D S : BitVec 32} {R n : Nat} (h : CtrCall s K C D S R n)
include h

theorem fit : 4 * ctrRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem n_lt : n < 2 ^ 32 := by have := h.fD; omega

theorem args : arg (pushed ctrRegs s).callEntry 0 = K ∧ arg (pushed ctrRegs s).callEntry 1 = BitVec.ofNat 32 R ∧
    arg (pushed ctrRegs s).callEntry 2 = C ∧ arg (pushed ctrRegs s).callEntry 3 = D ∧
    arg (pushed ctrRegs s).callEntry 4 = BitVec.ofNat 32 n ∧ arg (pushed ctrRegs s).callEntry 5 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit ctrRegs_esp (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx, h.edi, h.ebp]

theorem sub24 : Region.Sub (below (s.gpr .esp) 24) (below (s.gpr .esp) 28) := below_sub (by omega) h.esp

theorem sub4 : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 28).setWidth 64, 4⟩ (below (s.gpr .esp) 28) := by
  have := below_inner (sp := s.gpr .esp) (a := 4) (b := 28) (k := 24) (by omega) h.esp
  rw [show s.gpr .esp - BitVec.ofNat 32 28 = s.gpr .esp - BitVec.ofNat 32 24 - BitVec.ofNat 32 4 by
    rw [← VG.Offset.sub_add_eq]; rfl]
  exact this

theorem callPre : CallPre Proof.Aes.ctr32X86 ctrRegs (ctrRd (s.gpr .esp) K) (ctrWr C D S n) s := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat32 h.n_lt
  have eA : argAddr (pushed ctrRegs s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 24).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed ctrRegs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 28 := by
    rw [callEntry_esp']; rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Aes.ctr32X86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, eA, eSp, hR, hn]
    refine ⟨trivial, trivial, h.kc, h.kd, h.ks, h.cd, h.cs, h.ds, h.bc.sub_left h.sub24,
      h.bd.sub_left h.sub24, h.bs.sub_left h.sub24, h.bc.sub_left h.sub4, h.bd.sub_left h.sub4,
      h.bs.sub_left h.sub4, h.fK, h.fC, h.fD, h.fS, ?_, h.rounds⟩
    rw [sub_toNat (by have := h.esp; omega)]; have := (s.gpr .esp).isLt; omega
  · intro a m ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a m ⟨_, List.mem_singleton_self _, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a m ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a m hi
    obtain ⟨r', hr', hc'⟩ := h.writes a m hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end CtrCall

theorem ctr_call {s : State} {K C D S : BitVec 32} {R n : Nat} (h : CtrCall s K C D S R n) :
    WP isa ctrCall s (CtrPost s K C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat32 h.n_lt
  have hR' : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  unfold ctrCall
  refine WP.callWith (rs := ctrRegs) (k := Proof.Aes.ctr32X86) Proof.Aes.X86.ctr32_correct ctr_nosp (by simp)
    ctrRegs_esp (by rw [ctr_stack]; have := h.esp; simp only [List.length_cons, List.length_nil]; omega)
    h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, a4, -⟩ := h.args
  rw [ctr_stack] at f'
  have fE := callEntry_frame h.fit ctrRegs_esp
  rw [show 4 * ctrRegs.length + 4 = 28 from rfl] at fE
  obtain ⟨hdata, hctr⟩ := post
  simp only [arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, hR, hn, m₂] at hdata hctr
  have eK := bytesAt_frame fE (p := w64 K) (n := 16 * (R + 1))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.bk.sub_right (Region.sub_prefix hR')).symm) (by omega)
  rw [blockAt_frame fE (one_disj h.bc), blocksAt_frame fE (one_disj h.bd) (by have := h.fD; omega),
    eK] at hdata
  rw [blockAt_frame fE (one_disj h.bc)] at hctr
  refine ⟨rd', wr', cs', ?_, hdata, hctr⟩
  exact f'.mono fun r hr => by simp only [List.cons_append, List.nil_append] at hr; simpa using hr

/-- Calls of `vg_aes_ctr32` with the same arguments and stack pointer in
both runs are constant time. -/
theorem ctr_ct {I : State → Prop} {K C D S E : BitVec 32} {R n : Nat}
    (h : ∀ s, I s → CtrCall s K C D S R n ∧ s.gpr .esp = E) : CT I ctrCall := by
  refine CT.callWith Proof.Aes.X86.ctr32_correct Proof.Aes.X86.ctr32_ct (ctrRd E K) (ctrWr C D S n)
    fun s₁ s₂ i₁ i₂ => ?_
  obtain ⟨h₁, e₁⟩ := h s₁ i₁
  obtain ⟨h₂, e₂⟩ := h s₂ i₂
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

/-! ## `vg_aes_expand_key` -/

abbrev keyRegs : List Reg := [.ebp, .edx, .ecx, .eax]

theorem keyRegs_esp : Reg.esp ∉ keyRegs := by decide

/-- What a call of `vg_aes_expand_key` needs: the `L`-byte key at `K`, the key
schedule at `C` and working space at `S`. -/
structure KeyCall (s : State) (K C S : BitVec 32) (L : Nat) : Prop where
  eax : s.gpr .eax = K
  ecx : s.gpr .ecx = BitVec.ofNat 32 L
  edx : s.gpr .edx = C
  ebp : s.gpr .ebp = S
  len : L = 16 ∨ L = 24 ∨ L = 32
  esp : 20 ≤ (s.gpr .esp).toNat
  kc : (⟨w64 K, L⟩ : Region).Disjoint ⟨w64 C, 240⟩
  ks : (⟨w64 K, L⟩ : Region).Disjoint ⟨w64 S, 512⟩
  cs : (⟨w64 C, 240⟩ : Region).Disjoint ⟨w64 S, 512⟩
  bk : (below (s.gpr .esp) 20).Disjoint ⟨w64 K, L⟩
  bc : (below (s.gpr .esp) 20).Disjoint ⟨w64 C, 240⟩
  bs : (below (s.gpr .esp) 20).Disjoint ⟨w64 S, 512⟩
  fK : K.toNat + L ≤ 2 ^ 32
  fC : C.toNat + 240 ≤ 2 ^ 32
  fS : S.toNat + 512 ≤ 2 ^ 32
  reads : Covers [⟨w64 K, L⟩] (s.rd ++ s.wr)
  writes : Covers [⟨w64 C, 240⟩, ⟨w64 S, 512⟩] s.wr

/-- What a call of `vg_aes_expand_key` leaves. -/
structure KeyPost (s : State) (K C S : BitVec 32) (L : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨w64 C, 240⟩, ⟨w64 S, 512⟩, below (s.gpr .esp) 20] s.mem s'.mem
  out : bytesAt s'.mem (w64 C) (16 * (Spec.Aes.rounds (L / 4) + 1)) = Spec.Aes.expandKey (bytesAt s.mem (w64 K) L)

abbrev keyRd (E K : BitVec 32) (L : Nat) : List Region := [⟨w64 K, L⟩, below E 16]
abbrev keyWr (C S : BitVec 32) : List Region := [⟨w64 C, 240⟩, ⟨w64 S, 512⟩]

namespace KeyCall
variable {s : State} {K C S : BitVec 32} {L : Nat} (h : KeyCall s K C S L)
include h

theorem fit : 4 * keyRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem L_lt : L < 2 ^ 32 := by rcases h.len with h' | h' | h' <;> omega

theorem args : arg (pushed keyRegs s).callEntry 0 = K ∧ arg (pushed keyRegs s).callEntry 1 = BitVec.ofNat 32 L ∧
    arg (pushed keyRegs s).callEntry 2 = C ∧ arg (pushed keyRegs s).callEntry 3 = S := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit keyRegs_esp (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebp]

theorem sub16 : Region.Sub (below (s.gpr .esp) 16) (below (s.gpr .esp) 20) := below_sub (by omega) h.esp

theorem sub4 : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 4⟩ (below (s.gpr .esp) 20) := by
  have := below_inner (sp := s.gpr .esp) (a := 4) (b := 20) (k := 16) (by omega) h.esp
  rw [show s.gpr .esp - BitVec.ofNat 32 20 = s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 4 by
    rw [← VG.Offset.sub_add_eq]; rfl]
  exact this

theorem callPre : CallPre Proof.Aes.expandKeyX86 keyRegs (keyRd (s.gpr .esp) K L) (keyWr C S) s := by
  obtain ⟨a0, a1, a2, a3⟩ := h.args
  have hL := toNat_ofNat32 h.L_lt
  have eA : argAddr (pushed keyRegs s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed keyRegs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 20 := by
    rw [callEntry_esp']; rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Aes.expandKeyX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, hL]
    refine ⟨trivial, trivial, h.kc, h.ks, h.cs, h.bc.sub_left h.sub16, h.bs.sub_left h.sub16,
      h.bc.sub_left h.sub4, h.bs.sub_left h.sub4, h.fK, h.fC, h.fS, ?_, h.len⟩
    rw [sub_toNat (by have := h.esp; omega)]; have := (s.gpr .esp).isLt; omega
  · intro a m ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a m ⟨_, List.mem_singleton_self _, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a m ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a m hi
    obtain ⟨r', hr', hc'⟩ := h.writes a m hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end KeyCall

theorem key_call {s : State} {K C S : BitVec 32} {L : Nat} (h : KeyCall s K C S L) :
    WP isa keyCall s (KeyPost s K C S L) := by
  have hL := toNat_ofNat32 h.L_lt
  unfold keyCall
  refine WP.callWith (rs := keyRegs) (k := Proof.Aes.expandKeyX86) Proof.Aes.X86.expandKey_correct key_nosp
    (by simp) keyRegs_esp (by rw [key_stack]; have := h.esp; simp only [List.length_cons, List.length_nil]; omega)
    h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, -⟩ := h.args
  rw [key_stack] at f'
  have fE := callEntry_frame h.fit keyRegs_esp
  rw [show 4 * keyRegs.length + 4 = 20 from rfl] at fE
  simp only [Proof.Aes.expandKeyX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, hL, m₂] at post
  refine ⟨rd', wr', cs', ?_, ?_⟩
  · exact f'.mono fun r hr => by simp only [List.cons_append, List.nil_append] at hr; simpa using hr
  · rw [post, bytesAt_frame fE (one_disj h.bk) (by rcases h.len with rfl | rfl | rfl <;> decide)]

/-- Calls of `vg_aes_expand_key` with the same arguments and stack pointer
in both runs are constant time. -/
theorem key_ct {I : State → Prop} {K C S E : BitVec 32} {L : Nat}
    (h : ∀ s, I s → KeyCall s K C S L ∧ s.gpr .esp = E) : CT I keyCall := by
  refine CT.callWith Proof.Aes.X86.expandKey_correct Proof.Aes.X86.expandKey_ct (keyRd E K L) (keyWr C S)
    fun s₁ s₂ i₁ i₂ => ?_
  obtain ⟨h₁, e₁⟩ := h s₁ i₁
  obtain ⟨h₂, e₂⟩ := h s₂ i₂
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]

end VG.Proof.AesGcm.X86
