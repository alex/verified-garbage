import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksContract
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Impl.AesGcm.X86_64.Blocks

/-!
# AES-GCM on whole blocks, x86-64: the setting

Untrusted: everything here is checked by Lean. The arguments of the entry
state `s` (`K`, `C`, `Y`, `D`, `n`, `S`), their regions, and the facts of
`blocksPre` by name (`BP`); the load of `scratch` (`load_ok`) and the frame
that keeps the arguments (`pushed_kept`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Spec.Gcm (Block blockAt blocksAt)

section
variable (s : State)

abbrev K : Addr := s.gpr .rdi
abbrev C : Addr := s.gpr .rdx
abbrev Y : Addr := s.gpr .rcx
abbrev D : Addr := s.gpr .r8
abbrev n : Nat := (s.gpr .r9).toNat
abbrev S : Addr := stackArg s 0
abbrev SP : Addr := s.gpr .rsp
/-- The frame of the arguments: `rsp` in it. -/
abbrev F : Addr := SP s - BitVec.ofNat 64 56
abbrev kR : Region := ⟨K s, 256⟩
abbrev cR : Region := ⟨C s, 16⟩
abbrev yR : Region := ⟨Y s, 16⟩
abbrev dR : Region := ⟨D s, n s * 16⟩
abbrev sR : Region := ⟨S s, 2048⟩
/-- The stack argument `scratch`. -/
abbrev aR : Region := ⟨SP s + BitVec.ofNat 64 8, 8⟩
/-- The frame. -/
abbrev fR : Region := ⟨F s, 56⟩
/-- The stack the code uses: the frame and the return address of a call. -/
abbrev tR : Region := below (SP s) 64
/-- What the code writes: the counter, `Y`, the data and `scratch`. -/
abbrev wR : List Region := [cR s, yR s, dR s, sR s]

end

/-- `blocksPre`, by name. -/
structure BP (s : State) : Prop where
  rd : s.rd = [kR s, aR s]
  wr : s.wr = wR s
  k_c : (kR s).Disjoint (cR s)
  k_y : (kR s).Disjoint (yR s)
  k_d : (kR s).Disjoint (dR s)
  k_s : (kR s).Disjoint (sR s)
  c_y : (cR s).Disjoint (yR s)
  c_d : (cR s).Disjoint (dR s)
  c_s : (cR s).Disjoint (sR s)
  c_a : (cR s).Disjoint (aR s)
  y_d : (yR s).Disjoint (dR s)
  y_s : (yR s).Disjoint (sR s)
  y_a : (yR s).Disjoint (aR s)
  d_s : (dR s).Disjoint (sR s)
  d_a : (dR s).Disjoint (aR s)
  s_a : (sR s).Disjoint (aR s)
  r_c : (⟨SP s, 8⟩ : Region).Disjoint (cR s)
  r_y : (⟨SP s, 8⟩ : Region).Disjoint (yR s)
  r_d : (⟨SP s, 8⟩ : Region).Disjoint (dR s)
  r_s : (⟨SP s, 8⟩ : Region).Disjoint (sR s)
  t_k : (tR s).Disjoint (kR s)
  t_c : (tR s).Disjoint (cR s)
  t_y : (tR s).Disjoint (yR s)
  t_d : (tR s).Disjoint (dR s)
  t_s : (tR s).Disjoint (sR s)
  w_k : (K s).toNat + 256 ≤ 2 ^ 64
  w_c : (C s).toNat + 16 ≤ 2 ^ 64
  w_y : (Y s).toNat + 16 ≤ 2 ^ 64
  w_d : (D s).toNat + n s * 16 ≤ 2 ^ 64
  w_s : (S s).toNat + 2048 ≤ 2 ^ 64
  w_sp₀ : 64 ≤ (SP s).toNat
  w_sp : (SP s).toNat + 16 ≤ 2 ^ 64
  rounds : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14

theorem BP.of {s : State} (h : Proof.AesGcm.blocksPre s) : BP s := by
  simp only [Proof.AesGcm.blocksPre, Proof.AesGcm.args, Proof.AesGcm.arg, Proof.AesGcm.ret, Proof.AesGcm.stk64,
    Proof.AesGcm.rounds] at h
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := by simp [stackArgAddr]
  rw [hA] at h
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂, a₂₃,
    a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂, a₃₃⟩ := h
  exact ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂, a₂₃,
    a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂, a₃₃⟩

/-! ## The arguments kept -/

/-- The arguments kept in the frame at `F`: the data and the number of blocks
of what is left after `q` blocks, and `scratch`. -/
structure Kept (s : State) (q : Nat) (m : Mem) : Prop where
  ctx : m.readW (F s + BitVec.ofNat 64 48) 64 = K s
  rounds : m.readW (F s + BitVec.ofNat 64 40) 64 = s.gpr .rsi
  ctr : m.readW (F s + BitVec.ofNat 64 32) 64 = C s
  y : m.readW (F s + BitVec.ofNat 64 24) 64 = Y s
  data : m.readW (F s + BitVec.ofNat 64 16) 64 = D s + BitVec.ofNat 64 (16 * q)
  n : m.readW (F s + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 (n s - q)
  scr : m.readW (F s + BitVec.ofNat 64 0) 64 = S s

section
variable {s : State} (hp : BP s)
include hp

theorem a_in : InRegions (s.rd ++ s.wr) (SP s + BitVec.ofNat 64 8) 8 :=
  ⟨aR s, by rw [hp.rd]; simp, Region.contains_self _ _⟩

omit hp in
/-- The frame is in the stack the code uses. -/
theorem fR_sub : (fR s).Sub (tR s) := Offset.sub_below _ (by decide) (by decide)

omit hp in
/-- So is the return address of a call from the frame. -/
theorem fB_sub : (below (F s) 8).Sub (tR s) := by
  have e : F s - BitVec.ofNat 64 8 = SP s - BitVec.ofNat 64 64 := by
    simp only [F]; rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
  show Region.Sub ⟨F s - BitVec.ofNat 64 8, 8⟩ _
  rw [e]; exact Region.sub_prefix (by decide)

omit hp in
/-- The return address is apart from the stack the code uses. -/
theorem ret_tR : (⟨SP s, 8⟩ : Region).Disjoint (tR s) :=
  Offset.base_disjoint_below (SP s) (n := 64) (k := 8) (by decide)

/-- What a frame of the stack used and the regions written keeps: the return address. -/
theorem keep_r {m m' : Mem} (hf : Frame (tR s :: wR s) m m') : m'.readW (SP s) 64 = m.readW (SP s) 64 :=
  hf.readW (r := ⟨SP s, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ret_tR
    · exact hp.r_c
    · exact hp.r_y
    · exact hp.r_d
    · exact hp.r_s) (by decide)

theorem tw_k : ∀ r ∈ tR s :: wR s, (kR s).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [hp.t_k.symm, hp.k_c, hp.k_y, hp.k_d, hp.k_s]

/-- The key context, through a frame of the stack used and the regions written. -/
theorem keep_k {m m' : Mem} (hf : Frame (tR s :: wR s) m m') {d k : Nat} (h : d + k ≤ 256) :
    Spec.Aes.bytesAt m' (K s + BitVec.ofNat 64 d) k = Spec.Aes.bytesAt m (K s + BitVec.ofNat 64 d) k :=
  bytesAt_frame hf (fun r hr => (tw_k hp r hr).sub_left (Offset.sub_base _ h)) (by omega)

omit hp in
theorem arg_eq : s.mem.readW (SP s + BitVec.ofNat 64 8) 64 = S s := rfl

/-- `scratch`, loaded into `r11`. -/
theorem load_ok : WP isa (.block [.mov .r11 (.mem (at_ .rsp 8))]) s fun s₁ => s₁.gpr .r11 = S s ∧
    (∀ r, r ≠ .r11 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have a₀ := a_in hp
  refine WP.of_runBlock ⟨_, by xrun [a₀, arg_eq], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · intro r hr; simp [gpr_setReg, hr]
  all_goals rfl

end

/-- The frame's push, from the state after the load. -/
theorem pushed_kept {s s₁ : State} (hp : BP s) (h11 : s₁.gpr .r11 = S s) (hg : ∀ r, r ≠ .r11 → s₁.gpr r = s.gpr r)
    (hm : s₁.mem = s.mem) : (pushed frameRegs s₁).gpr .rsp = F s ∧ Kept s 0 (pushed frameRegs s₁).mem ∧
      Frame [fR s] s.mem (pushed frameRegs s₁).mem := by
  have hsp : s₁.gpr .rsp = SP s := hg _ (by decide)
  have h56 : 8 * frameRegs.length ≤ (s₁.gpr .rsp).toNat := by rw [hsp]; have := hp.w_sp₀; simp [frameRegs]; omega
  obtain ⟨hf, hpj⟩ := pushRegs_mem s₁ frameRegs (by decide) h56
  have e : ∀ j, j < 7 → s₁.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1)) = F s + BitVec.ofNat 64 (56 - 8 * (j + 1)) :=
    fun j hj => by rw [hsp]; exact Offset.sub_ofNat_eq _ (by omega)
  have r : ∀ j (hj : j < 7), (pushed frameRegs s₁).mem.readW (F s + BitVec.ofNat 64 (56 - 8 * (j + 1))) 64 =
      s₁.gpr (frameRegs[j]'(by simp [frameRegs]; omega)) := fun j hj => by
    rw [← e j hj]; exact hpj j (by simp [frameRegs]; omega)
  refine ⟨by rw [pushed_rsp, hsp]; rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [r 0 (by decide)]; exact hg _ (by decide)
  · rw [r 1 (by decide)]; exact hg _ (by decide)
  · rw [r 2 (by decide)]; exact hg _ (by decide)
  · rw [r 3 (by decide)]; exact hg _ (by decide)
  · rw [r 4 (by decide)]; simp only [frameRegs, Nat.mul_zero, BitVec.add_zero]; exact hg _ (by decide)
  · rw [r 5 (by decide)]; simp only [frameRegs, Nat.sub_zero]; rw [hg _ (by decide)]; simp
  · rw [r 6 (by decide)]; exact h11
  · have hf' : Frame [⟨s₁.gpr .rsp - BitVec.ofNat 64 (8 * frameRegs.length), 8 * frameRegs.length⟩] s₁.mem
        (pushed frameRegs s₁).mem := hf
    rw [hsp, hm] at hf'
    exact hf'

end VG.Proof.AesGcm.X86_64.Blocks
