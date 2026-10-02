import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Update
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Keys

/-!
# TDEA-CMAC on x86-64: `vg_cmac_triple_des_init`, the key schedule

`initPre` saves the registers and stores the three DES keys, as big-endian
integers, in slots 12–14; each iteration of the loop then writes one DES key's
sixteen round keys (`KInv`).
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.X86_64.Straight VG.Impl.CmacTripleDes.X86_64 VG.Proof.CmacTripleDes
  VG.Proof.Cmac

section
variable (s₀ : State)

abbrev K : Addr := s₀.gpr .rdi
abbrev Kl : Nat := (s₀.gpr .rsi).toNat
abbrev O : Addr := s₀.gpr .rdx
abbrev Sc : Addr := s₀.gpr .rcx

/-- The key's bytes. -/
abbrev keyB : List Byte := Spec.Aes.bytesAt s₀.mem (K s₀) (Kl s₀)

/-- DES key `j`, as a big-endian integer. -/
abbrev kw (j : Nat) : BitVec 64 := byteRev64 (s₀.mem.readW (K s₀ + BitVec.ofNat 64 (keyOff (Kl s₀) j)) 64)

end

/-- The precondition, by name. -/
structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨K s₀, Kl s₀⟩]
  wr : s₀.wr = [⟨O s₀, 400⟩, ⟨Sc s₀, 640⟩]
  key_out : (⟨K s₀, Kl s₀⟩ : Region).Disjoint ⟨O s₀, 400⟩
  key_scr : (⟨K s₀, Kl s₀⟩ : Region).Disjoint ⟨Sc s₀, 640⟩
  out_scr : (⟨O s₀, 400⟩ : Region).Disjoint ⟨Sc s₀, 640⟩
  ret_out : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨O s₀, 400⟩
  ret_scr : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨Sc s₀, 640⟩
  key_wrap : (K s₀).toNat + Kl s₀ ≤ 2 ^ 64
  out_wrap : (O s₀).toNat + 400 ≤ 2 ^ 64
  scr_wrap : (Sc s₀).toNat + 640 ≤ 2 ^ 64
  valid : Kl s₀ = 16 ∨ Kl s₀ = 24

theorem IPre.of {s₀ : State} (h : initX86_64.pre s₀) : IPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k⟩

/-- After the round keys of `i` DES keys. -/
structure KInv (s₀ : State) (i : Nat) (s : State) : Prop where
  r15 : s.gpr .r15 = Sc s₀
  rbx : s.gpr .rbx = Sc s₀ + BitVec.ofNat 64 (96 + 8 * i)
  rbp : s.gpr .rbp = O s₀ + BitVec.ofNat 64 (128 * i)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (3 - i)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keys : ∀ j < 3, s.mem.readW (Sc s₀ + BitVec.ofNat 64 (96 + 8 * j)) 64 = kw s₀ j
  sched : ∀ n < 16 * i, s.mem.readW (O s₀ + BitVec.ofNat 64 (8 * n)) 64 =
    (Spec.TripleDes.expandKey (keyB s₀)).getD n 0
  frame : Frame [⟨Sc s₀ + BitVec.ofNat 64 96, 24⟩, ⟨O s₀, 384⟩] (savedMem s₀ (Sc s₀)) s.mem

/-! ## The prologue -/

theorem keyOff_le {s₀ : State} (hp : IPre s₀) {j : Nat} (hj : j < 3) : keyOff (Kl s₀) j + 8 ≤ Kl s₀ := by
  simp only [keyOff]; rcases hp.valid with h | h <;> rw [h] <;> split <;> omega

theorem initA_ok (s : State)
    (hw : ∀ d, 48 ≤ d → d + 8 ≤ 112 → InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 d) 8)
    (r0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 8) (r8 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa (save .rcx ++ ([.mov .r15 (.reg .rcx), .mov .rbp (.reg .rdx)] : List Instr) ++
        keyWord 0 12 ++ keyWord 8 13 ++ ([.alu .cmp .rsi (.imm 16)] : List Instr)) s = some s' ∧
      s'.gpr .r15 = s.gpr .rcx ∧ s'.gpr .rbp = s.gpr .rdx ∧ s'.gpr .rdi = s.gpr .rdi ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.zf = some (s.gpr .rsi - BitVec.signExtend 64 (16 : BitVec 32) == 0) ∧
      s'.mem = (((savedMem s (s.gpr .rcx)).writeW (s.gpr .rcx + BitVec.ofNat 64 96)
          (bswap64 ((savedMem s (s.gpr .rcx)).readW (s.gpr .rdi) 64))).writeW (s.gpr .rcx + BitVec.ofNat 64 104)
          (bswap64 (((savedMem s (s.gpr .rcx)).writeW (s.gpr .rcx + BitVec.ofNat 64 96)
            (bswap64 ((savedMem s (s.gpr .rcx)).readW (s.gpr .rdi) 64))).readW
            (s.gpr .rdi + BitVec.ofNat 64 8) 64))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, h₁, g₁, m₁, rd₁, wr₁⟩ := save_ok s .rcx fun d h₁ h₂ => hw d h₁ (by omega)
  have hw' : ∀ d, 48 ≤ d → d + 8 ≤ 112 → InRegions s₁.wr (s₁.gpr .rcx + BitVec.ofNat 64 d) 8 := by
    rw [g₁, wr₁]; exact hw
  have r0' : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi + BitVec.ofNat 64 0) 8 := by
    rw [g₁, rd₁, wr₁, BitVec.add_zero]; exact r0
  have r8' : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi + BitVec.ofNat 64 8) 8 := by
    rw [g₁, rd₁, wr₁]; exact r8
  refine ⟨_, by
    rw [List.append_assoc, List.append_assoc, List.append_assoc, runBlock_append, h₁, Option.bind_some]
    simp (config := {decide := true}) only [keyWord, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, at_, exec, readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat,
      Option.bind_some, Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false,
      hw' 96 (by decide) (by decide), hw' 104 (by decide) (by decide), r0', r8']
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, zf_arithFlags, 
    mem_arithFlags, rd_arithFlags, wr_arithFlags, ite_true, ite_false, g₁, m₁, rd₁, wr₁,
    BitVec.add_zero, and_self]

theorem loadKey_ok (s : State) (d : Nat) (r : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ .rdi d))] s = some s' ∧
      s'.gpr .rax = s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 d) 64 ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea,
      offset_nat, Option.map_some, r, ite_true]
    rfl, ?_⟩
  refine ⟨by simp [gpr_setReg], fun r hr => by simp [gpr_setReg, hr], rfl, rfl, rfl⟩

theorem initC_ok (s : State) (w : InRegions s.wr (s.gpr .r15 + BitVec.ofNat 64 112) 8) :
    ∃ s', runBlock isa [.bswap .rax, .store (at_ .r15 112) .rax, .mov .rbx (.reg .r15), .alu .add .rbx (.imm 96),
        .mov32 .r10 (.imm 3)] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r15 + BitVec.ofNat 64 112) (byteRev64 (s.gpr .rax)) ∧
      s'.gpr .rbx = s.gpr .r15 + BitVec.ofNat 64 96 ∧ s'.gpr .r10 = BitVec.ofNat 64 3 ∧
      (∀ r, r ∉ [Reg.rax, .rbx, .r10] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      readSrc32, execAlu, State.store64, State.ea, State.setReg32, offset_nat, Option.bind_some, Option.map_some,
      gpr_setReg, rd_setReg, wr_setReg, ite_true, ite_false, w]
    rfl, ?_⟩
  refine ⟨by simp [mem_setReg, mem_arithFlags, bswap64_eq], by simp [gpr_setReg],
    by simp [gpr_setReg], fun r hr => ?_, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [gpr_setReg, hr.1, hr.2.1, hr.2.2]

section
variable {s₀ : State} (hp : IPre s₀)
include hp

theorem IPre.inScr {d n : Nat} (h : d + n ≤ 640) : InRegions s₀.wr (Sc s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := ⟨Sc s₀, 640⟩) (by simp) (Offset.contains_base _ h (by have := hp.scr_wrap; omega))

theorem IPre.inOut {d n : Nat} (h : d + n ≤ 400) : InRegions s₀.wr (O s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := ⟨O s₀, 400⟩) (by simp) (Offset.contains_base _ h (by have := hp.out_wrap; omega))

theorem IPre.inKey {d n : Nat} (h : d + n ≤ Kl s₀) (hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) (K s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := ⟨K s₀, Kl s₀⟩) (by simp) (Offset.contains_base _ h (by have := hp.key_wrap; omega))

/-- The key is unchanged while only the scratch buffer changes. -/
theorem IPre.keyRead {m : Mem} (hf : Frame [⟨Sc s₀, 640⟩] s₀.mem m) {d : Nat} (hd : d + 8 ≤ Kl s₀) :
    m.readW (K s₀ + BitVec.ofNat 64 d) 64 = s₀.mem.readW (K s₀ + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨K s₀ + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.key_scr.sub_left (Offset.sub_base _ hd)) (by decide)

end

theorem scrSub {S : Addr} {d n : Nat} (h : d + n ≤ 640) : Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 640⟩ :=
  Offset.sub_base _ h

theorem initPre_wp {s₀ : State} (hp : IPre s₀) : WP isa initPre s₀ (KInv s₀ 0) := by
  have sw := hp.scr_wrap
  have kl : 16 ≤ Kl s₀ := by rcases hp.valid with h | h <;> omega
  obtain ⟨s₁, run₁, r15₁, rbp₁, rdi₁, rsp₁, zf₁, m₁, rd₁, wr₁⟩ := initA_ok s₀
    (fun d _ h => hp.inScr (by omega)) (by simpa using hp.inKey (d := 0) (n := 8) (by omega) (by decide))
    (hp.inKey (d := 8) (n := 8) (by omega) (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  -- The memory so far.
  have fS : Frame [⟨Sc s₀, 640⟩] s₀.mem (savedMem s₀ (Sc s₀)) := (savedMem_frame s₀ (Sc s₀)).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, scrSub (by decide)⟩
  have c96 : (⟨Sc s₀ + BitVec.ofNat 64 96, 24⟩ : Region).Contains (Sc s₀ + BitVec.ofNat 64 96) (64 / 8) := by
    simpa using Offset.contains_base (Sc s₀ + BitVec.ofNat 64 96) (d := 0) (n := 8) (k := 24) (by decide) (by decide)
  have cAt (d : Nat) (h₁ : 96 ≤ d) (h₂ : d + 8 ≤ 120) :
      (⟨Sc s₀ + BitVec.ofNat 64 96, 24⟩ : Region).Contains (Sc s₀ + BitVec.ofNat 64 d) (64 / 8) := by
    rw [show Sc s₀ + BitVec.ofNat 64 d = Sc s₀ + BitVec.ofNat 64 96 + BitVec.ofNat 64 (d - 96) from
      (Offset.add_add_eq _ (by omega)).symm]
    exact Offset.contains_base _ (by omega) (by omega)
  have f₁ : Frame [⟨Sc s₀ + BitVec.ofNat 64 96, 24⟩] (savedMem s₀ (Sc s₀)) s₁.mem := by
    rw [m₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c96).writeW (List.mem_singleton_self _) _
      (cAt 104 (by decide) (by decide))
  have fA : Frame [⟨Sc s₀, 640⟩] s₀.mem s₁.mem := fS.trans (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, scrSub (by decide)⟩)
  have cS (d : Nat) (h : d + 8 ≤ 640) : (⟨Sc s₀, 640⟩ : Region).Contains (Sc s₀ + BitVec.ofNat 64 d) (64 / 8) :=
    Offset.contains_base _ (by omega) (by omega)
  have kr0 := hp.keyRead fS (d := 0) (by omega)
  have kr8 := hp.keyRead (fS.trans ((Frame.refl _ _).writeW (List.mem_singleton_self _)
    (bswap64 ((savedMem s₀ (Sc s₀)).readW (K s₀) 64)) (cS 96 (by decide)))) (d := 8) (by omega)
  simp only [BitVec.add_zero] at kr0
  have k0 : s₁.mem.readW (Sc s₀ + BitVec.ofNat 64 96) 64 = kw s₀ 0 := by
    rw [m₁, readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64, bswap64_eq]
    erw [kr0]
    simp [kw, keyOff]
  have k1 : s₁.mem.readW (Sc s₀ + BitVec.ofNat 64 104) 64 = kw s₀ 1 := by
    rw [m₁, Mem.readW_writeW_self64, bswap64_eq]
    erw [kr8]
    simp [kw, keyOff]
  -- The third DES key.
  have hz : isa.eval .e s₁ = some (decide (Kl s₀ = 16)) := by
    show s₁.zf = _
    rw [zf₁, show BitVec.signExtend 64 (16 : BitVec 32) = BitVec.ofNat 64 16 from rfl,
      show s₀.gpr .rsi = BitVec.ofNat 64 (Kl s₀) by apply BitVec.eq_of_toNat_eq; simp,
      Offset.ofNat_sub_ofNat_beq (by have := (s₀.gpr .rsi).isLt; omega) (by decide)]
  have third : ∀ d, d + 8 ≤ Kl s₀ → keyOff (Kl s₀) 2 = d →
      WP isa (.block [.mov .rax (.mem (at_ .rdi d))]) s₁ fun s₂ =>
        s₂.gpr .rax = s₀.mem.readW (K s₀ + BitVec.ofNat 64 d) 64 ∧ (∀ r, r ≠ .rax → s₂.gpr r = s₁.gpr r) ∧
        s₂.mem = s₁.mem ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr := by
    intro d hd _
    obtain ⟨s₂, run₂, ax₂, g₂, m₂, rd₂, wr₂⟩ := loadKey_ok s₁ d
      (by rw [rdi₁, rd₁, wr₁]; exact hp.inKey (by omega) (by decide))
    exact WP.of_runBlock ⟨s₂, run₂, by rw [ax₂, rdi₁, hp.keyRead fA hd], g₂, m₂, by rw [rd₂, rd₁],
      by rw [wr₂, wr₁]⟩
  refine WP.seq (WP.mono (Q := fun (s₂ : State) =>
      s₂.gpr .rax = s₀.mem.readW (K s₀ + BitVec.ofNat 64 (keyOff (Kl s₀) 2)) 64 ∧
        (∀ r, r ≠ .rax → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr) ?_
      fun s₂ h₂ => ?_)
  · by_cases h16 : Kl s₀ = 16
    · refine WP.ite true (by rw [hz]; simp [h16]) (fun _ => ?_) (fun h => by cases h)
      have := third 0 (by omega) (by simp [keyOff, h16])
      rwa [show keyOff (Kl s₀) 2 = 0 by simp [keyOff, h16]]
    · refine WP.ite false (by rw [hz]; simp [h16]) (fun h => by cases h) (fun _ => ?_)
      have h24 : Kl s₀ = 24 := by rcases hp.valid with h | h <;> omega
      have := third 16 (by omega) (by simp [keyOff, h24])
      rwa [show keyOff (Kl s₀) 2 = 16 by simp [keyOff, h24]]
  · obtain ⟨ax₂, g₂, m₂, rd₂, wr₂⟩ := h₂
    have r15₂ : s₂.gpr .r15 = Sc s₀ := by rw [g₂ _ (by decide), r15₁]
    obtain ⟨s₃, run₃, m₃, rbx₃, r10₃, g₃, rd₃, wr₃⟩ := initC_ok s₂
      (by rw [wr₂, r15₂]; exact hp.inScr (by decide))
    refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
    have gg (r : Reg) (hr : r ∉ [Reg.rax, .rbx, .r10]) : s₃.gpr r = s₁.gpr r := by
      rw [g₃ r hr, g₂ r (by rintro rfl; simp at hr)]
    rw [r15₂, m₂, ax₂] at m₃
    rw [r15₂] at rbx₃
    refine ⟨by rw [gg _ (by decide), r15₁], by rw [rbx₃], by rw [gg _ (by decide), rbp₁]; simp, by rw [r10₃],
      by rw [gg _ (by decide), rsp₁], by rw [rd₃, rd₂], by rw [wr₃, wr₂], fun j hj => ?_,
      fun n hn => absurd hn (by omega), ?_⟩
    · rw [m₃]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)]; exact k0
      · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)]; exact k1
      · rw [Mem.readW_writeW_self64]
    · rw [m₃]
      exact (f₁.mono fun r hr => by simp at hr; simp [hr]).writeW (r := ⟨Sc s₀ + BitVec.ofNat 64 96, 24⟩)
        (by simp) _ (cAt 112 (by decide) (by decide))

/-! ## The round keys -/

theorem loadRbx_ok (s : State) (r : InRegions (s.rd ++ s.wr) (s.gpr .rbx) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ .rbx 0))] s = some s' ∧
      s'.gpr .rax = s.mem.readW (s.gpr .rbx) 64 ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea,
      offset_nat, BitVec.add_zero, Option.map_some, r, ite_true]
    rfl, ?_⟩
  refine ⟨by simp [gpr_setReg], fun r hr => by simp [gpr_setReg, hr], rfl, rfl, rfl⟩

theorem keysTail_ok (s : State) :
    ∃ s', runBlock isa [.alu .add .rbp (.imm 128), .alu .add .rbx (.imm 8), .alu .sub .r10 (.imm 1)] s = some s' ∧
      s'.gpr .rbp = s.gpr .rbp + BitVec.ofNat 64 128 ∧ s'.gpr .rbx = s.gpr .rbx + BitVec.ofNat 64 8 ∧
      s'.gpr .r10 = s.gpr .r10 - 1 ∧ s'.zf = some ((s.gpr .r10 - 1) == 0) ∧
      (∀ r, r ∉ [Reg.rbp, .rbx, .r10] → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      Option.bind_some, gpr_setReg, gpr_arithFlags, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · rw [zf_setReg, zf_arithFlags]; simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_setReg, hr.1, hr.2.1, hr.2.2]

theorem keyStep_ok {s₀ : State} (hp : IPre s₀) {i : Nat} (hi : i < 3) {s : State} (h : KInv s₀ i s) :
    WP isa (.block keysBody) s fun s' => s'.zf = some (decide (i + 1 = 3)) ∧ KInv s₀ (i + 1) s' := by
  have sw := hp.scr_wrap
  have ow := hp.out_wrap
  have rdwr : s.rd ++ s.wr = [⟨K s₀, Kl s₀⟩, ⟨O s₀, 400⟩, ⟨Sc s₀, 640⟩] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  rw [keysBody, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, ax₁, g₁, m₁, rd₁, wr₁⟩ := loadRbx_ok s (by
    rw [rdwr, h.rbx]; exact in_rw (r := ⟨Sc s₀, 640⟩) (by simp) (Offset.contains_base _ (by omega) (by omega)))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have rbp₁ : s₁.gpr .rbp = O s₀ + BitVec.ofNat 64 (128 * i) := by rw [g₁ _ (by decide), h.rbp]
  have hok : Ok kCfg s₁ := by
    refine ⟨fun k hk => ?_, fun k hk => absurd hk (by simp [kCfg]), by decide, fun k _ j hj => absurd hj (by simp [kCfg])⟩
    rw [wr₁, h.wr, hp.wr, show kCfg.base = .rbp from rfl, rbp₁]
    exact ⟨⟨O s₀, 400⟩, by simp, contains_word (off := 128 * i) (n := 400) rfl
      (by simp only [kCfg] at hk; omega) (by show 400 ≤ 400; decide) (by show 400 < 2 ^ 64; decide)⟩
  obtain ⟨s₂, run₂, rk₂, rd₂, wr₂, g₂, f₂⟩ := roundKeys_ok hok
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain ⟨s₃, run₃, rbp₃, rbx₃, r10₃, zf₃, g₃, m₃, rd₃, wr₃⟩ := keysTail_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have gk (r : Reg) (h₁ : r ∉ kWrites) (h₂ : r ≠ .rax) : s₂.gpr r = s.gpr r := by rw [g₂ r h₁, g₁ r h₂]
  have slotR : slotRegion kCfg s₁ = ⟨O s₀ + BitVec.ofNat 64 (128 * i), 128⟩ := by
    simp only [slotRegion]; rw [show kCfg.base = .rbp from rfl, rbp₁]; rfl
  rw [slotR] at f₂
  have r10v : s.gpr .r10 = BitVec.ofNat 64 (3 - i) := h.r10
  have dec : BitVec.ofNat 64 (3 - i) - 1 = BitVec.ofNat 64 (3 - (i + 1)) := ofNat_sub_one (by omega) (by omega)
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun n hn => ?_, ?_⟩⟩
  · rw [zf₃, gk _ (by decide) (by decide), r10v, dec, ofNat_beq_zero (by omega)]
    simp only [Option.some.injEq, decide_eq_decide]; omega
  · rw [g₃ _ (by decide), gk _ (by decide) (by decide), h.r15]
  · rw [rbx₃, gk _ (by decide) (by decide), h.rbx, Offset.add_add, show 96 + 8 * i + 8 = 96 + 8 * (i + 1) by omega]
  · rw [rbp₃, gk _ (by decide) (by decide), h.rbp, Offset.add_add, show 128 * i + 128 = 128 * (i + 1) by omega]
  · rw [r10₃, gk _ (by decide) (by decide), r10v, dec]
  · rw [g₃ _ (by decide), gk _ (by decide) (by decide), h.rsp]
  · rw [rd₃, rd₂, rd₁, h.rd]
  · rw [wr₃, wr₂, wr₁, h.wr]
  · rw [m₃, ← h.keys j hj, ← m₁]
    refine f₂.readW (r := ⟨Sc s₀ + BitVec.ofNat 64 (96 + 8 * j), 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.out_scr.sub_left (Offset.sub_base _ (by omega))).symm.sub_left (scrSub (by omega))
  · rw [m₃]
    by_cases hn' : n < 16 * i
    · rw [← h.sched n hn', ← m₁]
      refine f₂.readW (r := ⟨O s₀ + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
        (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, n = 16 * i + j := ⟨n - 16 * i, by omega⟩
      have hj : j < 16 := by omega
      have hk := keyOff_le hp hi
      rw [show O s₀ + BitVec.ofNat 64 (8 * (16 * i + j)) = wordAddr (s₁.gpr .rbp) j by
          rw [rbp₁, wordAddr, Offset.add_add, show 128 * i + 8 * j = 8 * (16 * i + j) by omega],
        rk₂ j hj, ax₁, h.rbx, h.keys i hi, expandKey_getD _ hi hj, Proof.Cmac.bytesAt_length,
        decode_bytesAt _ _ hk]
  · rw [m₃]
    rw [m₁] at f₂
    exact h.frame.trans (f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨O s₀, 384⟩, by simp, Offset.sub_base _ (by omega)⟩)

theorem keys_ok {s₀ : State} (hp : IPre s₀) {s : State} (h : KInv s₀ 0 s) :
    WP isa (.loop (.block keysBody) .ne) s (KInv s₀ 3) := by
  refine WP.loop (M := isa) (body := .block keysBody) (c := .ne) (Q := KInv s₀ 3)
    (fun (n : Nat) (t : State) => ∃ i, n = 3 - i ∧ i < 3 ∧ KInv s₀ i t) ?_ 3 s ⟨0, rfl, by decide, h⟩
  rintro n t ⟨i, rfl, hi, ht⟩
  refine WP.mono (keyStep_ok hp hi ht) fun t' ⟨zf', h'⟩ => ?_
  by_cases hz : i + 1 = 3
  · left
    refine ⟨by simp [X86_64.eval, zf', hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by simp [X86_64.eval, zf', hz], 3 - (i + 1), by omega, i + 1, rfl, by omega, h'⟩

/-! ## The subkeys -/

theorem initD_ok (s : State) :
    ∃ s', runBlock isa [.mov .r14 (.reg .rbp), .alu .sub .r14 (.imm 384), .mov32 .rax (.imm 0)] s = some s' ∧
      s'.gpr .r14 = s.gpr .rbp - BitVec.ofNat 64 384 ∧ s'.gpr .rax = 0 ∧
      (∀ r, r ∉ [Reg.r14, .rax] → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, Option.bind_some,
      Option.map_some, State.setReg32]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_setReg], fun r hr => ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_setReg, hr.1, hr.2]

theorem dbl_ok (s : State) (d : Nat) (w : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa (dbl d) s = some s' ∧
      s'.gpr .rax = dbl64 (s.gpr .rax) ∧
      s'.mem = s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 d) (byteRev64 (dbl64 (s.gpr .rax))) ∧
      (∀ r, r ∉ [Reg.rax, .rcx, .rdx] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [dbl, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      readSrc32, execAlu, execShift, State.store64, State.ea, State.setReg32, offset_nat, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags, gpr_setFlags, rd_setReg, wr_setReg, rd_arithFlags,
      wr_arithFlags, rd_setFlags, wr_setFlags, ite_true, ite_false, w]
    rfl, ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · rw [← dbl64_eq]; simp [gpr_setReg]
  · rw [← dbl64_eq]; simp [mem_setReg, mem_arithFlags, mem_setFlags, bswap64_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_setReg, gpr_setFlags, hr.1, hr.2.1, hr.2.2]

theorem init_wp {s₀ : State} (h0 : initX86_64.pre s₀) :
    WP isa init s₀ fun s' => gprPreserved s₀ s' ∧ initX86_64.post s₀ s' := by
  have hp := IPre.of h0
  have sw := hp.scr_wrap
  have ow := hp.out_wrap
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (keys_ok hp h₁) fun s₂ h₂ => ?_)
  obtain ⟨s₃, run₃, r14₃, ax₃, g₃, m₃, rd₃, wr₃⟩ := initD_ok s₂
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have r14₃' : s₃.gpr .r14 = O s₀ := by
    rw [r14₃, h₂.rbp, show 128 * 3 = 384 from rfl, BitVec.add_sub_cancel]
  have r15₃ : s₃.gpr .r15 = Sc s₀ := by rw [g₃ _ (by decide), h₂.r15]
  have bp : BlockPre s₃ :=
    { sched := ⟨⟨O s₀, 400⟩, by rw [rd₃, wr₃, h₂.rd, h₂.wr, hp.rd, hp.wr]; simp, by rw [r14₃'],
        by show 384 ≤ 400; decide, by show 400 < 2 ^ 64; decide⟩
      scr := ⟨⟨Sc s₀, 640⟩, by rw [wr₃, h₂.wr, hp.wr]; simp, by rw [r15₃], by show 48 ≤ 640; decide,
        by show 640 < 2 ^ 64; decide⟩
      disj := by
        rw [r14₃', r15₃]
        exact (hp.out_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (block_ok bp) fun s₄ ⟨same₄, r14₄, ax₄⟩ => ?_)
  -- The key schedule.
  have hsch₂ : Spec.TripleDes.scheduleAt s₂.mem (O s₀) = Spec.TripleDes.expandKey (keyB s₀) := by
    apply Vector.ext
    intro n hn
    rw [← vgetD _ hn 0, ← vgetD _ hn 0, scheduleAt_getD _ _ hn, h₂.sched n (by omega)]
  have xR₃ : xR s₃ = ⟨Sc s₀, 48⟩ := by rw [xR, r15₃]
  have f₄ : Frame [⟨Sc s₀, 48⟩] s₂.mem s₄.mem := by rw [← m₃, ← xR₃]; exact same₄.frame
  have outX : ∀ r ∈ [(⟨Sc s₀, 48⟩ : Region)], (⟨O s₀, 384⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.out_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
  have hsch₄ : Spec.TripleDes.scheduleAt s₄.mem (O s₀) = Spec.TripleDes.expandKey (keyB s₀) := by
    rw [scheduleAt_frame f₄ outX, hsch₂]
  rw [WP.block_append_iff, WP.block_append_iff]
  have rbp₄ : s₄.gpr .rbp = O s₀ + BitVec.ofNat 64 384 := by
    rw [same₄.rbp, g₃ _ (by decide), h₂.rbp]
  obtain ⟨s₅, run₅, ax₅, m₅, g₅, rd₅, wr₅⟩ := dbl_ok s₄ 0 (by
    rw [same₄.wr, wr₃, h₂.wr, rbp₄, Offset.add_add]; exact hp.inOut (by decide))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have rbp₅ : s₅.gpr .rbp = O s₀ + BitVec.ofNat 64 384 := by rw [g₅ _ (by decide), rbp₄]
  obtain ⟨s₆, run₆, ax₆, m₆, g₆, rd₆, wr₆⟩ := dbl_ok s₅ 8 (by
    rw [wr₅, same₄.wr, wr₃, h₂.wr, rbp₅, Offset.add_add]; exact hp.inOut (by decide))
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  have r15₆ : s₆.gpr .r15 = Sc s₀ := by rw [g₆ _ (by decide), g₅ _ (by decide), same₄.r15, r15₃]
  have rdwr₆ : s₆.rd ++ s₆.wr = [⟨K s₀, Kl s₀⟩, ⟨O s₀, 400⟩, ⟨Sc s₀, 640⟩] := by
    rw [rd₆, wr₆, rd₅, wr₅, same₄.rd, same₄.wr, rd₃, wr₃, h₂.rd, h₂.wr, hp.rd, hp.wr]; rfl
  obtain ⟨s₇, run₇, b, c, d, e, f, g, rsp₇, m₇⟩ := restore_ok s₆ r15₆ fun d _ h₂' => by
    rw [rdwr₆]; exact in_rw (r := ⟨Sc s₀, 640⟩) (by simp) (Offset.contains_base _ (by omega) (by omega))
  refine WP.of_runBlock ⟨s₇, run₇, ?_⟩
  -- Memory.
  have sub384 : Region.Sub ⟨O s₀ + BitVec.ofNat 64 384, 16⟩ ⟨O s₀, 400⟩ := Offset.sub_base _ (by decide)
  have c8 : (⟨O s₀ + BitVec.ofNat 64 384, 16⟩ : Region).Contains (O s₀ + BitVec.ofNat 64 384 + BitVec.ofNat 64 8)
      (64 / 8) := Offset.contains_base _ (by decide) (by decide)
  have c0 : (⟨O s₀ + BitVec.ofNat 64 384, 16⟩ : Region).Contains (O s₀ + BitVec.ofNat 64 384 + BitVec.ofNat 64 0)
      (64 / 8) := Offset.contains_base _ (by decide) (by decide)
  have f₆ : Frame [⟨O s₀ + BitVec.ofNat 64 384, 16⟩] s₄.mem s₆.mem := by
    rw [m₆, m₅, rbp₅, rbp₄]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c8
  have fAll : Frame [⟨Sc s₀ + BitVec.ofNat 64 96, 24⟩, ⟨O s₀, 400⟩, ⟨Sc s₀, 48⟩] (savedMem s₀ (Sc s₀)) s₇.mem := by
    rw [m₇]
    refine ((h₂.frame.sub fun r hr => ?_).trans (f₄.mono fun r hr => by simp at hr; simp [hr])).trans
      (f₆.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨O s₀, 400⟩, by simp, Region.sub_prefix (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨O s₀, 400⟩, by simp, sub384⟩
  have hm : ∀ d, 48 ≤ d → d + 8 ≤ 96 →
      s₆.mem.readW (Sc s₀ + BitVec.ofNat 64 d) 64 = (savedMem s₀ (Sc s₀)).readW (Sc s₀ + BitVec.ofNat 64 d) 64 := by
    intro d h₁' h₂'
    rw [← m₇]
    refine fAll.readW (r := ⟨Sc s₀ + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (d := d) (e := 96) (by omega) (by omega) (by omega)
    · exact (hp.out_scr.sub_right (scrSub (by omega))).symm
    · exact Offset.disjoint_base _ (by omega) (by omega)
  refine ⟨⟨restored hm ⟨b, c, d, e, f, g⟩ (by rw [rsp₇, g₆ _ (by decide), g₅ _ (by decide), same₄.rsp,
    g₃ _ (by decide), h₂.rsp]), ?_⟩, ?_, ?_⟩
  · have big : Frame [⟨Sc s₀, 640⟩, ⟨O s₀, 400⟩] s₀.mem s₇.mem :=
      ((savedMem_frame s₀ (Sc s₀)).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨Sc s₀, 640⟩, by simp, scrSub (by decide)⟩).trans (fAll.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨Sc s₀, 640⟩, by simp, scrSub (by decide)⟩
        · exact ⟨⟨O s₀, 400⟩, by simp, fun _ h => h⟩
        · exact ⟨⟨Sc s₀, 640⟩, by simp, Region.sub_prefix (by decide)⟩)
    refine big.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.ret_scr
    · exact hp.ret_out
  · show Spec.TripleDes.scheduleAt s₇.mem (O s₀) = Spec.TripleDes.expandKey (keyB s₀)
    rw [m₇, scheduleAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (by decide) (by omega)), hsch₄]
  · show Spec.Aes.bytesAt s₇.mem (O s₀ + BitVec.ofNat 64 384) 16 =
      (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (keyB s₀))) 8).1 ++
        (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (keyB s₀))) 8).2
    have hk : sch s₃ = Spec.TripleDes.expandKey (keyB s₀) := by rw [sch, r14₃', m₃, hsch₂]
    rw [subkeys_tdes, m₇, m₆, rbp₅, ax₅, m₅, rbp₄, ax₄, ax₃, hk,
      show O s₀ + BitVec.ofNat 64 384 + BitVec.ofNat 64 0 = O s₀ + BitVec.ofNat 64 384 from BitVec.add_zero _]
    exact bytesAt_store2 _ _ _ _

end VG.Proof.CmacTripleDes.X86_64
