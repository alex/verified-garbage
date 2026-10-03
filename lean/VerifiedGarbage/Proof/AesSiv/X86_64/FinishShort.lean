import VerifiedGarbage.Proof.AesSiv.X86_64.CmacOf
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Copy

/-!
# AES-SIV on x86-64: finishing S2V with a string shorter than a block

For a last string `P` of `L < 16` bytes, `shortTail` builds `pad(P) ⊕ dbl(D)`
at `W + 32`: it zeroes the block, copies `P` into it, appends `0x80`, copies
`D` to `W + 144`, doubles it there (with the context pointer saved at
`W + 224` while `rbx` points to the working space) and XORs it into the
block. `shortMac` finalizes that one complete block from a zero state at
`W + out`, which is then the CMAC of `dbl(D) xor pad(P)`
(`Siv.s2vFinish_short`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64 VG.WriteBytes
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 zero2 zero2_bytes frame_store2 mn dblMem dbl_ok
  dblMem_bytes dblMem_frame xor2Mem xor2_ok xor2Mem_bytes xor2Mem_frame padded_bytes)
open VG.Proof.CmacAes.Stream.X86_64 (FArgs Copied copy_ok copyMem copyMem_frame copyMem_bytes toNat_ofNat)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-! ## The tail -/

theorem shortB1_ok (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) :
    ∃ s₁, runBlock isa (zero16 .r15 tailOff ++ [.mov .rdx (.reg .r15), .alu .add .rdx (imm tailOff),
        .mov .rcx (.reg .r14)]) s = some s₁ ∧ Regs s₀ C D P W R L s₁ ∧
      s₁.gpr .rdx = W + BitVec.ofNat 64 32 ∧ s₁.gpr .rcx = BitVec.ofNat 64 L ∧
      s₁.mem = zero2 s.mem (W + BitVec.ofNat 64 32) := by
  have w₀ := h.inW hr.wr (d := 32) (n := 8) (by decide)
  have w₁ := h.inW hr.wr (d := 40) (n := 8) (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [zero16, tailOff, imm, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, readSrc32, execAlu, State.store64,
      State.ea, State.setReg32, offset_nat, Option.bind_some, Option.map_some, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, ite_true, ite_false, hr.r15, w₀, w₁]
    rfl, ?_⟩
  refine ⟨hr.keep (fun r hr' => ?_) rfl rfl, ?_, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  · simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, ite_true, ite_false,
      sx_ofNat (show 32 < 2 ^ 31 by decide)]
  · simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, hr.r14]
  · simp only [mem_setReg, mem_arithFlags, zero2, Offset.add_add]

/-- The memory after appending `0x80`, copying `D` to `W + 144` and saving
the context pointer at `W + 224`. -/
def b3aMem (m : Mem) (C D W : Addr) (L : Nat) : Mem :=
  (copyMem (m.writeW (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 L) (0x80 : Byte)) (W + BitVec.ofNat 64 144) D).writeW
    (W + BitVec.ofNat 64 224) C

theorem pad80_ok (s : State) {A : Addr}
    (hc : s.gpr .r15 + s.gpr .r14 * BitVec.ofNat 64 1 + BitVec.ofInt 64 (tailOff : Int) = A)
    (wc : InRegions s.wr A 1) :
    ∃ s', runBlock isa [.mov32 .rax (imm 0x80), .store8 { base := .r15, index := some .r14, disp := tailOff } .rax]
        s = some s' ∧ s'.mem = s.mem.writeW A (0x80 : Byte) ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32,
      State.store8, State.ea, State.setReg32, Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      ite_true, ite_false, hc, wc]
    rfl, ?_⟩
  refine ⟨rfl, ?_, rfl, rfl⟩
  intro r hr; simp [gpr_setReg, hr]

theorem shortB3a_ok (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) (hL : L < 16) :
    ∃ s', runBlock isa [.mov32 .rax (imm 0x80), .store8 { base := .r15, index := some .r14, disp := tailOff } .rax,
        .mov .rax (.mem (at_ .r12 0)), .store (at_ .r15 dbOff) .rax, .mov .rax (.mem (at_ .r12 8)),
        .store (at_ .r15 (dbOff + 8)) .rax, .store (at_ .r15 ctxOff) .rbx, .mov .rbx (.reg .r15)] s = some s' ∧
      s'.mem = b3aMem s.mem C D W L ∧ s'.gpr .rbx = W ∧ (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hea : s.gpr .r15 + s.gpr .r14 * BitVec.ofNat 64 1 + BitVec.ofInt 64 (tailOff : Int) =
      W + BitVec.ofNat 64 32 + BitVec.ofNat 64 L := by
    rw [hr.r15, hr.r14, BitVec.mul_one, offset_nat, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 L),
      ← BitVec.add_assoc]; rfl
  have wp : InRegions s.wr (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 L) 1 := by
    rw [Offset.add_add]; exact h.inW hr.wr (by omega)
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := pad80_ok s hea wp
  have hr₁ (r : Reg) (hr' : r ≠ .rax) := g₁ r hr'
  have rD₀ := h.inRD hr.rd hr.wr (d := 0) (n := 8) (by decide)
  have rD₈ := h.inRD hr.rd hr.wr (d := 8) (n := 8) (by decide)
  rw [k0] at rD₀
  rw [← rd₁, ← wr₁] at rD₀ rD₈
  have w₁ := h.inW hr.wr (d := dbOff) (n := 8) (by decide)
  have w₂ := h.inW hr.wr (d := dbOff + 8) (n := 8) (by decide)
  have w₃ := h.inW hr.wr (d := ctxOff) (n := 8) (by decide)
  rw [← wr₁] at w₁ w₂ w₃
  have e152 : W + BitVec.ofNat 64 (dbOff + 8) = W + BitVec.ofNat 64 144 + BitVec.ofNat 64 8 := by
    rw [Offset.add_add]; rfl
  have r12₁ : s₁.gpr .r12 = D := by rw [g₁ _ (by decide), hr.r12]
  have r15₁ : s₁.gpr .r15 = W := by rw [g₁ _ (by decide), hr.r15]
  have rbx₁ : s₁.gpr .rbx = C := by rw [g₁ _ (by decide), hr.rbx]
  obtain ⟨s₂, run₂, m₂, rbx₂, g₂⟩ : ∃ s₂, runBlock isa [.mov .rax (.mem (at_ .r12 0)), .store (at_ .r15 dbOff) .rax,
      .mov .rax (.mem (at_ .r12 8)), .store (at_ .r15 (dbOff + 8)) .rax, .store (at_ .r15 ctxOff) .rbx,
      .mov .rbx (.reg .r15)] s₁ = some s₂ ∧
      s₂.mem = (copyMem s₁.mem (W + BitVec.ofNat 64 144) D).writeW (W + BitVec.ofNat 64 224) C ∧
      s₂.gpr .rbx = W ∧ (∀ r, r ≠ .rax → r ≠ .rbx → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, at_,
        exec, readSrc, State.load64, State.store64, State.ea, offset_nat, k0, Option.map_some,
        gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false, r12₁, r15₁, rD₀, rD₈, w₁, w₂, w₃]
      rfl, ?_⟩
    refine ⟨?_, ?_, fun r h₁ h₂ => ?_, rfl, rfl⟩
    · simp (config := {decide := true}) only [mem_setReg, rbx₁, copyMem, e152]
      rfl
    · simp [gpr_setReg]
    · simp [gpr_setReg, h₁, h₂]
  refine ⟨s₂, by
    rw [show ([.mov32 .rax (imm 0x80), .store8 { base := .r15, index := some .r14, disp := tailOff } .rax,
        .mov .rax (.mem (at_ .r12 0)), .store (at_ .r15 dbOff) .rax, .mov .rax (.mem (at_ .r12 8)),
        .store (at_ .r15 (dbOff + 8)) .rax, .store (at_ .r15 ctxOff) .rbx, .mov .rbx (.reg .r15)] : List Instr) =
        [.mov32 .rax (imm 0x80), .store8 { base := .r15, index := some .r14, disp := tailOff } .rax] ++
        [.mov .rax (.mem (at_ .r12 0)), .store (at_ .r15 dbOff) .rax, .mov .rax (.mem (at_ .r12 8)),
        .store (at_ .r15 (dbOff + 8)) .rax, .store (at_ .r15 ctxOff) .rbx, .mov .rbx (.reg .r15)] from rfl,
      runBlock_append, run₁, Option.bind_some, run₂], by rw [m₂, m₁, b3aMem], rbx₂,
    fun r h₁ h₂ => by rw [g₂.1 r h₁ h₂, g₁ r h₁], by rw [g₂.2.1, rd₁], by rw [g₂.2.2, wr₁]⟩

theorem shortB3b_ok {s : State} (h15 : s.gpr .r15 = W) (r₂₂₄ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 224) 8)
    (rp : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 32) 8) (rp8 : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 40) 8)
    (rq : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 144) 8)
    (rq8 : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 152) 8)
    (wc : InRegions s.wr (W + BitVec.ofNat 64 32) 8) (wc8 : InRegions s.wr (W + BitVec.ofNat 64 40) 8) :
    ∃ s', runBlock isa [.mov .rbx (.mem (at_ .r15 ctxOff)),
        .mov .rax (.mem (at_ .r15 tailOff)), .alu .xor .rax (.mem (at_ .r15 dbOff)),
        .store (at_ .r15 tailOff) .rax, .mov .rax (.mem (at_ .r15 (tailOff + 8))),
        .alu .xor .rax (.mem (at_ .r15 (dbOff + 8))), .store (at_ .r15 (tailOff + 8)) .rax] s = some s' ∧
      s'.mem = xor2Mem s.mem (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 144) ∧
      s'.gpr .rbx = s.mem.readW (W + BitVec.ofNat 64 224) 64 ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.setReg .rbx (s.mem.readW (W + BitVec.ofNat 64 224) 64)
  have run₁ : runBlock isa [.mov .rbx (.mem (at_ .r15 ctxOff))] s = some s₁ := by
    simp only [ctxOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea,
      offset_nat, Option.map_some, h15, r₂₂₄, ite_true]
    rfl
  have g₁ (r : Reg) (hr : r ≠ .rbx) : s₁.gpr r = s.gpr r := gpr_setReg_of_ne _ _ hr
  have e8 (d : Nat) : W + BitVec.ofNat 64 (d + 8) = W + BitVec.ofNat 64 d + BitVec.ofNat 64 8 :=
    (Offset.add_add _ _ _).symm
  obtain ⟨s₂, run₂, m₂, g₂, rd₂, wr₂⟩ := xor2_ok s₁ .r15 .r15 .r15 tailOff dbOff tailOff
    (P := W + BitVec.ofNat 64 32) (Q := W + BitVec.ofNat 64 144) (C := W + BitVec.ofNat 64 32)
    (by rw [g₁ _ (by decide), h15]; rfl) (by rw [g₁ _ (by decide), h15, e8]; rfl)
    (by rw [g₁ _ (by decide), h15]; rfl) (by rw [g₁ _ (by decide), h15, e8]; rfl)
    (by rw [g₁ _ (by decide), h15]; rfl) (by rw [g₁ _ (by decide), h15, e8]; rfl) ⟨by decide, by decide, by decide⟩
    rp (by rw [← e8]; exact rp8) rq (by rw [← e8]; exact rq8) wc (by rw [← e8]; exact wc8)
  refine ⟨s₂, ?_, m₂, ?_, fun r h₁ h₂ => by rw [g₂ r h₁, g₁ r h₂], rd₂, wr₂⟩
  · rw [show ([.mov .rbx (.mem (at_ .r15 ctxOff)), .mov .rax (.mem (at_ .r15 tailOff)),
        .alu .xor .rax (.mem (at_ .r15 dbOff)), .store (at_ .r15 tailOff) .rax,
        .mov .rax (.mem (at_ .r15 (tailOff + 8))), .alu .xor .rax (.mem (at_ .r15 (dbOff + 8))),
        .store (at_ .r15 (tailOff + 8)) .rax] : List Instr) = [.mov .rbx (.mem (at_ .r15 ctxOff))] ++
        [.mov .rax (.mem (at_ .r15 tailOff)), .alu .xor .rax (.mem (at_ .r15 dbOff)),
        .store (at_ .r15 tailOff) .rax, .mov .rax (.mem (at_ .r15 (tailOff + 8))),
        .alu .xor .rax (.mem (at_ .r15 (dbOff + 8))), .store (at_ .r15 (tailOff + 8)) .rax] from rfl,
      runBlock_append, run₁, Option.bind_some, run₂]
  · rw [g₂ _ (by decide)]; exact gpr_setReg_self ..

/-- The regions `shortTail` writes. -/
abbrev tailRegions (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 144, 16⟩, ⟨W + BitVec.ofNat 64 224, 8⟩]

theorem shortTail_wp (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) (hL : L < 16) :
    WP isa shortTail s fun s' => Regs s₀ C D P W R L s' ∧ Frame (tailRegions W) s.mem s'.mem ∧
      Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 32) 16 =
        Spec.Siv.xor (Spec.Siv.pad (Spec.Aes.bytesAt s.mem P L)) (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16)) := by
  have hwW := h.wW
  have hwD := h.wD
  obtain ⟨s₁, run₁, hr₁, rdx₁, rcx₁, m₁⟩ := shortB1_ok h hr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have dPT : (⟨P, L⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 32, L⟩ := h.p_w.sub_right (h.sW (by omega))
  refine WP.seq (WP.mono (copy_ok s₁ (by omega) hr₁.r13 rdx₁ rcx₁
    (fun i hi => h.inRP hr₁.rd hr₁.wr (by omega))
    (fun i hi => by rw [hr₁.wr, Offset.add_add]; exact h.inW rfl (by omega)) dPT) fun s₂ h₂ => ?_)
  have hr₂ : Regs s₀ C D P W R L s₂ := hr₁.keep (fun r hr' => h₂.other r (by rintro rfl; simp [calleeSaved] at hr')
    (by rintro rfl; simp [calleeSaved] at hr')) h₂.rd h₂.wr
  obtain ⟨s₃, run₃, m₃, rbx₃, g₃, rd₃, wr₃⟩ := shortB3a_ok h hr₂ hL
  obtain ⟨s₄, run₄, m₄, g₄, rd₄, wr₄⟩ := dbl_ok s₃ rbx₃ (src := dbOff) (dst := dbOff)
    (by rw [rd₃, wr₃]; exact h.inRW hr₂.rd hr₂.wr (by decide))
    (by rw [rd₃, wr₃]; exact h.inRW hr₂.rd hr₂.wr (by decide))
    (by rw [wr₃]; exact h.inW hr₂.wr (by decide)) (by rw [wr₃]; exact h.inW hr₂.wr (by decide))
  have r15₄ : s₄.gpr .r15 = W := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide), g₃ _ (by decide) (by decide), hr₂.r15]
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃, hr₂.rd]
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃, hr₂.wr]
  obtain ⟨s₅, run₅, m₅, rbx₅, g₅, rd₅, wr₅⟩ := shortB3b_ok r15₄
    (h.inRW rd₄' wr₄' (by decide)) (h.inRW rd₄' wr₄' (by decide)) (h.inRW rd₄' wr₄' (by decide))
    (h.inRW rd₄' wr₄' (by decide)) (h.inRW rd₄' wr₄' (by decide)) (h.inW wr₄' (by decide)) (h.inW wr₄' (by decide))
  refine WP.of_runBlock ⟨s₅, by
    rw [show (([.mov32 .rax (imm 0x80), .store8 { base := .r15, index := some .r14, disp := tailOff } .rax,
        .mov .rax (.mem (at_ .r12 0)), .store (at_ .r15 dbOff) .rax, .mov .rax (.mem (at_ .r12 8)),
        .store (at_ .r15 (dbOff + 8)) .rax, .store (at_ .r15 ctxOff) .rbx, .mov .rbx (.reg .r15)] : List Instr) ++
        Impl.CmacAes.X86_64.dbl dbOff dbOff ++
        ([.mov .rbx (.mem (at_ .r15 ctxOff)), .mov .rax (.mem (at_ .r15 tailOff)),
        .alu .xor .rax (.mem (at_ .r15 dbOff)), .store (at_ .r15 tailOff) .rax,
        .mov .rax (.mem (at_ .r15 (tailOff + 8))), .alu .xor .rax (.mem (at_ .r15 (dbOff + 8))),
        .store (at_ .r15 (tailOff + 8)) .rax] : List Instr)) = _ from rfl]
    rw [runBlock_append, runBlock_append, run₃, Option.bind_some, run₄, Option.bind_some, run₅], ?_⟩
  -- The memory, step by step.
  have hlen : (Spec.Aes.bytesAt s₁.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
  have c32 (d n : Nat) (hd : d + n ≤ 16) :
      (⟨W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 d) n :=
    Offset.contains_base _ hd (by omega)
  have f₁ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s₁.mem := by rw [m₁]; exact frame_store2 _ _ _
  have f₂ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₁.mem s₂.mem := by
    rw [h₂.mem]; exact writeBytes_frame _ _ _ (by rw [hlen]; simpa using c32 0 L (by omega))
  have fB : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₂.mem (s₂.mem.writeW (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 L)
      (0x80 : Byte)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c32 L 1 (by omega))
  have fC : Frame [⟨W + BitVec.ofNat 64 144, 16⟩, ⟨W + BitVec.ofNat 64 224, 8⟩]
      (s₂.mem.writeW (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 L) (0x80 : Byte)) s₃.mem := by
    rw [m₃, b3aMem]
    exact ((copyMem_frame _ _ _).sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).writeW (by simp) _
      (Region.contains_self _ _)
  have f₄ : Frame [⟨W + BitVec.ofNat 64 144, 16⟩] s₃.mem s₄.mem := by rw [m₄]; exact dblMem_frame _ _ _ _
  have f₅ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₄.mem s₅.mem := by rw [m₅]; exact xor2Mem_frame _ _ _ _
  have sub (rs : List Region) (hs : ∀ r ∈ rs, r ∈ tailRegions W) : ∀ r ∈ rs, ∃ r' ∈ tailRegions W, Region.Sub r r' :=
    fun r hr => ⟨r, hs r hr, fun _ h => h⟩
  have frame : Frame (tailRegions W) s.mem s₅.mem :=
    ((((f₁.sub (sub _ (by simp))).trans (f₂.sub (sub _ (by simp)))).trans (fB.sub (sub _ (by simp)))).trans
      (fC.sub (sub _ (by simp)))).trans ((f₄.sub (sub _ (by simp))).trans (f₅.sub (sub _ (by simp))))
  have dWW (d n e k : Nat) (hs : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 2560) (he : e + k ≤ 2560) :
      (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ :=
    Offset.disjoint W hs (by omega) (by omega)
  -- The context pointer, back in `rbx`.
  have hC₄ : s₄.mem.readW (W + BitVec.ofNat 64 224) 64 = C := by
    rw [f₄.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dWW 224 8 144 16 (by omega) (by omega) (by omega))
        (by decide), m₃, b3aMem, Mem.readW_writeW_self64]
  have keep (r : Reg) (h₁ : r ≠ .rax) (h₂' : r ≠ .rbx) (h₃ : r ≠ .rdx) (h₄ : r ≠ .rcx) (h₅ : r ≠ .r8) :
      s₅.gpr r = s₂.gpr r := by
    rw [g₅ r h₁ h₂', g₄ r h₁ h₃ h₄ h₅, g₃ r h₁ h₂']
  have hr₅ : Regs s₀ C D P W R L s₅ :=
    ⟨by rw [rbx₅, hC₄], by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rbp],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r12],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r13],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r14],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r15],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rsp],
      by rw [rd₅, rd₄'], by rw [wr₅, wr₄']⟩
  refine ⟨hr₅, frame, ?_⟩
  -- The tail: `pad(P)` XOR `dbl(D)`.
  have e8 (d : Nat) : W + BitVec.ofNat 64 d + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 (d + 8) := Offset.add_add _ _ _
  rw [m₅, xor2Mem_bytes _ (by rw [e8]; exact dWW 32 8 40 8 (by omega) (by omega) (by omega))
    (by rw [e8]; exact dWW 32 8 152 8 (by omega) (by omega) (by omega))]
  have t₄ : Spec.Aes.bytesAt s₄.mem (W + BitVec.ofNat 64 32) 16 = Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 32) 16 :=
    bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dWW 32 16 144 16 (by omega) (by omega) (by omega))
      (by decide)
  have t₃ : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 32) 16 = Spec.Aes.bytesAt (s₂.mem.writeW
      (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 L) (0x80 : Byte)) (W + BitVec.ofNat 64 32) 16 :=
    bytesAt_frame fC (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dWW 32 16 144 16 (by omega) (by omega) (by omega)
      · exact dWW 32 16 224 8 (by omega) (by omega) (by omega)) (by decide)
  have hz : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 32) 16 = Spec.Cmac.zeros 16 := by rw [m₁]; exact zero2_bytes _ _
  have pad := padded_bytes s₁.mem (W + BitVec.ofNat 64 32) (Spec.Aes.bytesAt s₁.mem P L) (by rw [hlen]; exact hL) hz
  rw [hlen] at pad
  have hP : Spec.Aes.bytesAt s₁.mem P L = Spec.Aes.bytesAt s.mem P L :=
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.p_w.sub_right (h.sW (by decide)))
      (by have := h.lt; omega)
  have d₄ : Spec.Aes.bytesAt s₄.mem (W + BitVec.ofNat 64 144) 16 =
      Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 144) 16) := by
    rw [m₄]; exact dblMem_bytes s₃.mem W dbOff dbOff
  have dD (r : Region) (hr : r ∈ [(⟨W + BitVec.ofNat 64 32, 16⟩ : Region)]) : (⟨D, 16⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr; subst hr; exact h.d_w.sub_right (h.sW (by decide))
  have q₃ : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 144) 16 = Spec.Aes.bytesAt s.mem D 16 := by
    rw [m₃, b3aMem, bytesAt_frame (rs := [⟨W + BitVec.ofNat 64 224, 8⟩]) ((Frame.refl _ _).writeW
        (List.mem_singleton_self _) _ (Region.contains_self _ _)) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact dWW 144 16 224 8 (by omega) (by omega) (by omega))
        (by decide),
      copyMem_bytes _ (h.d_w.sub_right (h.sW (by decide))).symm, bytesAt_frame fB dD (by decide),
      bytesAt_frame f₂ dD (by decide), bytesAt_frame f₁ dD (by decide)]
  rw [t₄, t₃, h₂.mem, pad, hP, d₄, q₃, Spec.Siv.pad, Proof.Cmac.bytesAt_length, show 16 - L - 1 = 15 - L by omega]
  rfl

end VG.Proof.AesSiv.X86_64
