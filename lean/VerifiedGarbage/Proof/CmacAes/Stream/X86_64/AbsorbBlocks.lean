import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Save

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb`'s straight-line code

Untrusted: everything here is checked by Lean. What each piece of code
between the copies and calls computes, in terms of `count` (`c`) and `len`
(`L`): the bytes held back `h = held c`, the bytes copied after them
`f = min L (16 - h)`, the data left `L - f`, whether to chain the block held
back (`b1`), the blocks chained after it (`nb`), and the rest (`rest`).
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64
open VG.Proof.Cmac.Stream (held held_le)

/-! ## The numbers -/

/-- The bytes copied after the `held c` held back. -/
def fOf (c L : Nat) : Nat := min L (16 - held c)

/-- The data left after them. -/
def leftOf (c L : Nat) : Nat := L - fOf c L

/-- The number of blocks the first call chains: the block held back, if data is left. -/
def b1Of (c L : Nat) : Nat := if leftOf c L = 0 then 0 else 1

/-- The number of blocks the second call chains: those of the data left but its
last 1 to 16 bytes. -/
def nbOf (c L : Nat) : Nat := if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16

/-- The bytes copied to the start of the bytes held back at the end. -/
def restOf (c L : Nat) : Nat := leftOf c L - 16 * nbOf c L

theorem f_le (c L : Nat) : fOf c L ≤ L ∧ fOf c L + held c ≤ 16 := by
  have := held_le c; unfold fOf; omega

theorem nb_le (c L : Nat) : fOf c L + 16 * nbOf c L + restOf c L = L := by
  have := f_le c L; unfold restOf nbOf leftOf; split <;> omega

/-! ## Arithmetic on registers -/

theorem sub16 {h : Nat} (hh : h ≤ 16) :
    BitVec.setWidth 64 (16 : BitVec 32) - BitVec.ofNat 64 h = BitVec.ofNat 64 (16 - h) :=
  Offset.ofNat_sub_ofNat hh

/-- `16 nb` for the data left `x > 0`, as `sub 1; mov; and 15; sub` computes it. -/
theorem nb16_bv {x : Nat} (hx : 0 < x) (hx' : x < 2 ^ 64) :
    BitVec.ofNat 64 x - 1 - ((BitVec.ofNat 64 x - 1) &&& 15) = BitVec.ofNat 64 (16 * ((x - 1) / 16)) := by
  apply BitVec.eq_of_toNat_eq
  have e : (BitVec.ofNat 64 x - 1).toNat = x - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]; omega
  rw [BitVec.toNat_sub, and15, e, BitVec.toNat_ofNat]
  omega

theorem shr4 {n : Nat} (hn : 16 * n < 2 ^ 64) :
    BitVec.ofNat 64 (16 * n) >>> 4 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-! ## `held`: the bytes held back -/

theorem held_wp {s : State} {c : Nat} (hc : c < 2 ^ 64) (hd : s.gpr .rdx = BitVec.ofNat 64 c)
    (hz : s.zf = some (s.gpr .rdx == 0)) :
    WP isa held s fun s' => s'.gpr .rax = BitVec.ofNat 64 (held c) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  by_cases h0 : c = 0
  · subst h0
    refine WP.ite true (by show s.zf = _; rw [hz, hd]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some]
      rfl, ?_⟩
    simp only [gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true]
    exact ⟨rfl, fun r h => by simp [h], trivial, trivial, trivial⟩
  · have hne : BitVec.ofNat 64 c ≠ 0 := fun e => h0 (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat hc] at this)
    refine WP.ite false (by show s.zf = _; rw [hz, hd, beq_eq_false_iff_ne.mpr hne]) (fun h => by cases h)
      fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
        Option.map_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, ite_true, hd, sx1, sx15]
    refine ⟨by rw [held_bv _ hne, toNat_ofNat hc], fun r h => by simp [h], trivial, trivial, trivial⟩

/-! ## `fill`: how many bytes to copy, and where -/

theorem fill_wp {s : State} {St : Addr} {c L : Nat} (hL : L < 2 ^ 64) (hax : s.gpr .rax = BitVec.ofNat 64 (held c))
    (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (hbx : s.gpr .rbx = St) :
    WP isa fill s fun s' => s'.gpr .rcx = BitVec.ofNat 64 (fOf c L) ∧
      s'.gpr .rdx = St + BitVec.ofNat 64 (288 + held c) ∧
      (∀ r, r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hh := held_le c
  obtain ⟨s₁, run₁, rcx₁, cf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov32 .rcx (.imm 16),
      .alu .sub .rcx (.reg .rax), .alu .cmp .r14 (.reg .rcx)] s = some s₁ ∧
      s₁.gpr .rcx = BitVec.ofNat 64 (16 - held c) ∧ s₁.cf = some (decide (L < 16 - held c)) ∧
      (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        State.setReg32, Option.map_some, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, cf_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, reduceCtorEq, ite_false, hax, h14, sub16 hh,
      toNat_ofNat hL, toNat_ofNat (show 16 - held c < 2 ^ 64 by omega)]
    exact ⟨trivial, trivial, fun r h => by simp [h], trivial, trivial, trivial⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .rcx = BitVec.ofNat 64 (fOf c L) ∧
    (∀ r, r ≠ .rcx → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr) ?_ fun s₂ h₂ => ?_)
  · by_cases hl : L < 16 - held c
    · refine WP.ite true (by show s₁.cf = _; rw [cf₁]; simp [hl]) (fun _ => ?_) (fun h => by cases h)
      refine WP.of_runBlock ⟨_, by
        simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
        rfl, ?_⟩
      simp only [gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true]
      refine ⟨by rw [g₁ _ (by decide), h14, fOf, Nat.min_eq_left (by omega)],
        fun r h => by simp [h, g₁ r h], m₁, rd₁, wr₁⟩
    · refine WP.ite false (by show s₁.cf = _; rw [cf₁]; simp [hl]) (fun h => by cases h) fun _ => ?_
      refine WP.block_nil ⟨by rw [rcx₁, fOf, Nat.min_eq_right (by omega)], g₁, m₁, rd₁, wr₁⟩
  · obtain ⟨rcx₂, g₂, m₂, rd₂, wr₂⟩ := h₂
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
        Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, ite_true, reduceCtorEq, ite_false, g₂ _ (by decide : Reg.rbx ≠ .rcx),
      g₂ _ (by decide : Reg.rax ≠ .rcx), hbx, hax, sx288, rcx₂]
    refine ⟨trivial, by rw [BitVec.add_assoc, ← BitVec.ofNat_add], fun r h₁ h₂ => by simp [h₂, g₂ r h₁],
      m₂, rd₂, wr₂⟩

/-! ## `chain1`: the arguments of the first call -/

theorem chain1_wp {s : State} {St D S : Addr} {f L : Nat} (hf : f ≤ L) (hL : L < 2 ^ 64)
    (h13 : s.gpr .r13 = D) (hcx : s.gpr .rcx = BitVec.ofNat 64 f) (h14 : s.gpr .r14 = BitVec.ofNat 64 L)
    (hbx : s.gpr .rbx = St) (h15 : s.gpr .r15 = S) :
    WP isa chain1 s fun s' => s'.gpr .r13 = D + BitVec.ofNat 64 f ∧ s'.gpr .r14 = BitVec.ofNat 64 (L - f) ∧
      s'.gpr .r8 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧ s'.gpr .rdi = St ∧
      s'.gpr .rsi = s.gpr .rbp ∧ s'.gpr .rdx = St + BitVec.ofNat 64 272 ∧
      s'.gpr .rcx = St + BitVec.ofNat 64 288 ∧ s'.gpr .r9 = S ∧
      (∀ r ∈ calleeSaved, r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r13₁, r14₁, r8₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.alu .add .r13 (.reg .rcx),
      .mov32 .r8 (.imm 0), .alu .sub .r14 (.reg .rcx)] s = some s₁ ∧
      s₁.gpr .r13 = D + BitVec.ofNat 64 f ∧ s₁.gpr .r14 = BitVec.ofNat 64 (L - f) ∧
      s₁.gpr .r8 = BitVec.ofNat 64 0 ∧ s₁.zf = some (decide (L - f = 0)) ∧
      (∀ r, r ≠ .r13 → r ≠ .r14 → r ≠ .r8 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        State.setReg32, Option.map_some, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, zf_setReg, zf_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, reduceCtorEq, ite_false, h13, h14, hcx,
      Offset.ofNat_sub_ofNat hf, beq_zero_iff, toNat_ofNat (show L - f < 2 ^ 64 by omega)]
    exact ⟨trivial, trivial, rfl, trivial, fun r a b c => by simp [a, b, c], trivial, trivial, trivial⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .r8 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧
    (∀ r, r ≠ .r8 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr) ?_ fun s₂ h₂ => ?_)
  · by_cases h0 : L - f = 0
    · refine WP.ite true (by show s₁.zf = _; rw [zf₁]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [r8₁]; simp [h0], fun _ _ => rfl, rfl, rfl, rfl⟩
    · refine WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine WP.of_runBlock ⟨_, by
        simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some]
        rfl, ?_⟩
      simp only [gpr_setReg, mem_setReg, rd_setReg, wr_setReg, h0, ↓reduceIte]
      exact ⟨rfl, fun r h => by simp [h], trivial, trivial, trivial⟩
  · obtain ⟨r8₂, g₂, m₂, rd₂, wr₂⟩ := h₂
    have g (r : Reg) (a : r ≠ .r13) (b : r ≠ .r14) (c : r ≠ .r8) : s₂.gpr r = s.gpr r := by
      rw [g₂ r c, g₁ r a b c]
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
        Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, ite_true, reduceCtorEq, ite_false, g _ (by decide : Reg.rbx ≠ .r13) (by decide) (by decide),
      g _ (by decide : Reg.rbp ≠ .r13) (by decide) (by decide),
      g _ (by decide : Reg.r15 ≠ .r13) (by decide) (by decide), hbx, h15, sx272, sx288,
      g₂ _ (by decide : Reg.r13 ≠ .r8), g₂ _ (by decide : Reg.r14 ≠ .r8), r13₁, r14₁, r8₂]
    refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, fun r hr a b => ?_,
      by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-! ## `chain2`: the arguments of the second call -/

theorem chain2_wp {s : State} {x : Nat} (hx : x < 2 ^ 64) (h14 : s.gpr .r14 = BitVec.ofNat 64 x) :
    WP isa chain2 s fun s' =>
      s'.gpr .r12 = BitVec.ofNat 64 (16 * (if x = 0 then 0 else (x - 1) / 16)) ∧
      s'.gpr .r8 = BitVec.ofNat 64 (if x = 0 then 0 else (x - 1) / 16) ∧ s'.gpr .rdi = s.gpr .rbx ∧
      s'.gpr .rsi = s.gpr .rbp ∧ s'.gpr .rdx = s.gpr .rbx + BitVec.ofNat 64 272 ∧
      s'.gpr .rcx = s.gpr .r13 ∧ s'.gpr .r9 = s.gpr .r15 ∧
      (∀ r ∈ calleeSaved, r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r12₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov32 .r12 (.imm 0),
      .alu .test .r14 (.reg .r14)] s = some s₁ ∧ s₁.gpr .r12 = BitVec.ofNat 64 0 ∧
      s₁.zf = some (decide (x = 0)) ∧ (∀ r, r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        State.setReg32, Option.map_some, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, reduceCtorEq, ite_false, h14, BitVec.and_self,
      beq_zero_iff, toNat_ofNat hx]
    exact ⟨rfl, trivial, fun r h => by simp [h], trivial, trivial, trivial⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := fun (s₂ : State) =>
    s₂.gpr .r12 = BitVec.ofNat 64 (16 * (if x = 0 then 0 else (x - 1) / 16)) ∧
    (∀ r, r ≠ .r12 → r ≠ .rax → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr) ?_
    fun s₂ h₂ => ?_)
  · by_cases h0 : x = 0
    · refine WP.ite true (by show s₁.zf = _; rw [zf₁]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [r12₁]; simp [h0], fun r h _ => g₁ r h, m₁, rd₁, wr₁⟩
    · refine WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine WP.of_runBlock ⟨_, by
        simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
          Option.bind_some]
        rfl, ?_⟩
      simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
        wr_arithFlags, reduceCtorEq, h0, ↓reduceIte, g₁ _ (by decide : Reg.r14 ≠ .r12), h14,
        sx1, sx15]
      exact ⟨nb16_bv (by omega) hx, fun r a b => by simp [a, b, g₁ r a], m₁, rd₁, wr₁⟩
  · obtain ⟨r12₂, g₂, m₂, rd₂, wr₂⟩ := h₂
    refine WP.of_runBlock ⟨_, by
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
        execAlu, execShift, Option.map_some, Option.bind_some, ite_true]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg,
      rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags, wr_setFlags, ite_true, reduceCtorEq, ite_false,
      g₂ _ (by decide : Reg.rbx ≠ .r12) (by decide), g₂ _ (by decide : Reg.rbp ≠ .r12) (by decide),
      g₂ _ (by decide : Reg.r13 ≠ .r12) (by decide), g₂ _ (by decide : Reg.r15 ≠ .r12) (by decide), sx272, r12₂]
    refine ⟨trivial, shr4 (by split <;> omega), trivial, trivial, trivial, trivial, trivial,
      fun r hr a => ?_, m₂, rd₂, wr₂⟩
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-! ## `rest`: the arguments of the last copy -/

theorem rest_ok {s : State} {D : Addr} {a x n : Nat} (hn : 16 * n ≤ x)
    (h13 : s.gpr .r13 = D + BitVec.ofNat 64 a) (h12 : s.gpr .r12 = BitVec.ofNat 64 (16 * n))
    (h14 : s.gpr .r14 = BitVec.ofNat 64 x) :
    ∃ s', runBlock isa rest s = some s' ∧ s'.gpr .r13 = D + BitVec.ofNat 64 (a + 16 * n) ∧
      s'.gpr .r14 = BitVec.ofNat 64 (x - 16 * n) ∧ s'.gpr .rdx = s.gpr .rbx + BitVec.ofNat 64 288 ∧
      s'.gpr .rcx = BitVec.ofNat 64 (x - 16 * n) ∧
      (∀ r ∈ calleeSaved, r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [rest, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
      Option.bind_some]
    rfl, ?_⟩
  simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
    wr_arithFlags, ite_true, reduceCtorEq, ite_false, h13, h12, h14, sx288, Offset.ofNat_sub_ofNat hn]
  refine ⟨by rw [BitVec.add_assoc, ← BitVec.ofNat_add], trivial, trivial, trivial, fun r hr a b => ?_,
    trivial, trivial, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

end VG.Proof.CmacAes.Stream.X86_64
