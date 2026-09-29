import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Rounds
import VerifiedGarbage.Proof.ChaCha20.Keystream

/-!
# ChaCha20 on x86-64 with AVX2: the eight input states

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx2

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt)
open VG.Proof.ChaCha20

/-- What `buf[128, 224)` holds once the constants are stored: the rotation
masks, and the counter increments `0, …, 7` as doublewords. -/
structure Consts (m : Mem) (buf : Addr) : Prop where
  lo16 : (m.readW (buf + BitVec.ofNat 64 128) 256).extractLsb' 0 128 = rot16Mask
  hi16 : (m.readW (buf + BitVec.ofNat 64 128) 256).extractLsb' 128 128 = rot16Mask
  m8 : M8 m buf
  inc : ∀ l q, l < 2 → q < 4 →
    m.readW (buf + BitVec.ofNat 64 (192 + (16 * l + 4 * q))) 32 = BitVec.ofNat 32 (4 * l + q)

theorem shuf_00 (a : BitVec 128) {q : Nat} (hq : q < 4) : dword (shufDwords a 0x00) q = dword a 0 :=
  dword_shufDwords_bcast a (k := 0) (by decide) hq
theorem shuf_55 (a : BitVec 128) {q : Nat} (hq : q < 4) : dword (shufDwords a 0x55) q = dword a 1 :=
  dword_shufDwords_bcast a (k := 1) (by decide) hq
theorem shuf_aa (a : BitVec 128) {q : Nat} (hq : q < 4) : dword (shufDwords a 0xaa) q = dword a 2 :=
  dword_shufDwords_bcast a (k := 2) (by decide) hq
theorem shuf_ff (a : BitVec 128) {q : Nat} (hq : q < 4) : dword (shufDwords a 0xff) q = dword a 3 :=
  dword_shufDwords_bcast a (k := 3) (by decide) hq

theorem ctr_get (S : CState) (j k : Nat) (hk : k < 16) :
    (ctr S j)[k] = if k = 12 then S[12] + BitVec.ofNat 32 j else S[k] := by
  simp only [ctr, Vector.getElem_set]
  by_cases h : k = 12
  · subst h; simp
  · simp [h, Ne.symm h]

/-- Word `4 row + i` of the state at `st`, from a 128-bit read of row `row`. -/
theorem dword_row (m : Mem) (st : Addr) {row i : Nat} (hrow : row < 4) (hi : i < 4) :
    dword (m.readW (st + BitVec.ofNat 64 (16 * row)) 128) i =
      (stateAt m st)[4 * row + i]'(by omega) := by
  rw [dword_readW _ _ hi, add_ofNat]
  simp only [stateAt, Vector.getElem_ofFn]
  congr 3; omega

/-- The state region. -/
abbrev stR (st : Addr) : Region := ⟨st, 64⟩

theorem in_st {rs ws : List Region} {st : Addr} (hw : stR st ∈ ws) {d n : Nat} (h : d + n ≤ 64) :
    InRegions (rs ++ ws) (st + BitVec.ofNat 64 d) n := by
  refine ⟨stR st, List.mem_append_right _ hw, ?_⟩
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat st (by omega)]; exact h

theorem Consts.w2 {m : Mem} {buf : Addr} (h : Consts m buf) {i : Nat} (hi : slotOff i + 64 ≤ 128)
    (y₁ y₂ : BitVec 256) : Consts (W2 m buf i y₁ y₂) buf := by
  have k : ∀ d, 128 ≤ d → d ≤ 192 →
      (W2 m buf i y₁ y₂).readW (buf + BitVec.ofNat 64 d) 256 = m.readW (buf + BitVec.ofNat 64 d) 256 :=
    fun d h₁ h₂ => (readW_writeW_off _ buf y₂ (d := d) (e := slotOff i + 32) (n := 32) (by omega)
      (by omega) (by omega)).trans (readW_writeW_off _ buf y₁ (d := d) (e := slotOff i) (n := 32)
      (by omega) (by omega) (by omega))
  refine ⟨?_, ?_, ⟨?_, ?_⟩, fun l q hl hq => ?_⟩
  · rw [k 128 (by omega) (by omega)]; exact h.lo16
  · rw [k 128 (by omega) (by omega)]; exact h.hi16
  · rw [k 160 (by omega) (by omega)]; exact h.m8.1
  · rw [k 160 (by omega) (by omega)]; exact h.m8.2
  · exact (W2_other m buf hi y₁ y₂ (by omega) (by omega)).trans (h.inc l q hl hq)

/-! ## Broadcasting rows -/

/-- `vbroadcasti128 src, [rdi + off]` and the four `vpshufd` that spread its words. -/
def bcast (src d0 d1 d2 d3 : XReg) (off : Nat) : List Instr :=
  [.vbroadcasti128 src (at_ .rdi off), .vop (.vpshufd .l256 d0 src 0x00),
   .vop (.vpshufd .l256 d1 src 0x55), .vop (.vpshufd .l256 d2 src 0xaa),
   .vop (.vpshufd .l256 d3 src 0xff)]

theorem bcast_ok {src d0 d1 d2 d3 : XReg} (h0 : d0 ≠ src) (h1 : d1 ≠ src) (h2 : d2 ≠ src)
    (h3 : d3 ≠ src) (e01 : d0 ≠ d1) (e02 : d0 ≠ d2) (e03 : d0 ≠ d3) (e12 : d1 ≠ d2) (e13 : d1 ≠ d3)
    (e23 : d2 ≠ d3) {off : Nat} {s : State}
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 off) 16) :
    WP isa (.block (bcast src d0 d1 d2 d3 off)) s fun s' =>
      (∀ l q, q < 4 →
        vw s' d0 l q = dword (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 off) 128) 0 ∧
        vw s' d1 l q = dword (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 off) 128) 1 ∧
        vw s' d2 l q = dword (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 off) 128) 2 ∧
        vw s' d3 l q = dword (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 off) 128) 3) ∧
      (∀ r l, r ≠ src → r ≠ d0 → r ≠ d1 → r ≠ d2 → r ≠ d3 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [bcast, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, State.load128, hin,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left', VOp.exec_gpr, VOp.exec_mem,
    VOp.exec_rd, VOp.exec_wr, State.setV_gpr, State.setV_mem, State.setV_rd, State.setV_wr]
  refine ⟨fun l q hq => ?_, fun r l n n0 n1 n2 n3 => ?_, trivial, trivial, trivial, trivial⟩
  · simp only [vw, lane_vpshufd256, State.lane_setV256, h0, h1, h2, h3, e01, e02, e03, e12, e13,
      e23, e01.symm, e02.symm, e03.symm, e12.symm, e13.symm, e23.symm, h0.symm, h1.symm, h2.symm,
      ite_true, ite_false, ite_self,
      shuf_00 _ hq, shuf_55 _ hq, shuf_aa _ hq, shuf_ff _ hq, and_self]
  · simp only [lane_vpshufd256, State.lane_setV256, n, n0, n1, n2, n3, ite_false]

/-! ## The counters, the third row and the mask -/

def incs : List Instr :=
  [.vmovdquLoad .l256 .xmm13 (at_ .rcx incOff), .vop (.vbin .vpaddd .l256 .xmm8 .xmm8 .xmm13)]

theorem incs_ok {buf : Addr} {s : State} (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr)
    (hc : Consts s.mem buf) :
    WP isa (.block incs) s fun s' =>
      (∀ l q, l < 2 → q < 4 → vw s' .xmm8 l q = vw s .xmm8 l q + BitVec.ofNat 32 (4 * l + q)) ∧
      (∀ r l, r ≠ .xmm8 → r ≠ .xmm13 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i1 := in_buf (rs := s.rd) hb (d := incOff) (n := 32) (by decide)
  apply WP.of_runBlock
  simp only [incs, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hrcx, State.load256, i1,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left', VOp.exec_gpr, VOp.exec_mem,
    VOp.exec_rd, VOp.exec_wr, State.setV_gpr, State.setV_mem, State.setV_rd, State.setV_wr]
  refine ⟨fun l q hl hq => ?_, fun r l n8 n13 => ?_, trivial, trivial, trivial, trivial⟩
  · simp only [vw, lane_vbin256, State.lane_setV256, reduceCtorEq, ite_true, ite_false, VBinOp.sse,
      dword_paddd _ _ hq, dword_load256 _ _ hl hq]
    rw [add_ofNat]; exact congrArg _ (hc.inc l q hl hq)
  · simp only [lane_vbin256, State.lane_setV256, n8, n13, ite_false]

def row2 : List Instr :=
  [.vbroadcasti128 .xmm14 (at_ .rdi 32),
   .vop (.vpshufd .l256 .xmm12 .xmm14 0x00), .vop (.vpshufd .l256 .xmm13 .xmm14 0x55),
   .vop (.vpshufd .l256 .xmm15 .xmm14 0xaa), .vmovdquStore .l256 (at_ .rcx (slotOff 10)) .xmm15,
   .vop (.vpshufd .l256 .xmm15 .xmm14 0xff), .vmovdquStore .l256 (at_ .rcx (slotOff 11)) .xmm15]

theorem row2_ok {st buf : Addr} {s : State} (hrdi : s.gpr .rdi = st) (hrcx : s.gpr .rcx = buf)
    (hst : stR st ∈ s.wr) (hb : bufR buf ∈ s.wr) :
    WP isa (.block row2) s fun s' =>
      (∀ l q, l < 2 → q < 4 →
        vw s' .xmm12 l q = dword (s.mem.readW (st + BitVec.ofNat 64 32) 128) 0 ∧
        vw s' .xmm13 l q = dword (s.mem.readW (st + BitVec.ofNat 64 32) 128) 1 ∧
        s'.mem.readW (buf + BitVec.ofNat 64 (slotOff 10 + (16 * l + 4 * q))) 32 =
          dword (s.mem.readW (st + BitVec.ofNat 64 32) 128) 2 ∧
        s'.mem.readW (buf + BitVec.ofNat 64 (slotOff 11 + (16 * l + 4 * q))) 32 =
          dword (s.mem.readW (st + BitVec.ofNat 64 32) 128) 3) ∧
      (∀ r l, r ≠ .xmm12 → r ≠ .xmm13 → r ≠ .xmm14 → r ≠ .xmm15 → s'.lane r l = s.lane r l) ∧
      (∃ y₁ y₂, s'.mem = W2 s.mem buf 10 y₁ y₂) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i2 := in_st (rs := s.rd) hst (d := 32) (n := 16) (by omega)
  have o10 := out_buf hb (d := slotOff 10) (n := 32) (by decide)
  have o11 := out_buf hb (d := slotOff 10 + 32) (n := 32) (by decide)
  have s11 : slotOff 11 = slotOff 10 + 32 := rfl
  apply WP.of_runBlock
  simp only [row2, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hrdi, hrcx, State.load128,
    State.store256_eq, i2, o10, o11, ite_true, Option.map_some, Option.some.injEq, exists_eq_left',
    VOp.exec_gpr, VOp.exec_mem, VOp.exec_rd, VOp.exec_wr, State.setV_gpr, State.setV_mem,
    State.setV_rd, State.setV_wr, State.setMem_gpr, State.setMem_mem, State.setMem_rd,
    State.setMem_wr, s11]
  refine ⟨fun l q hl hq => ?_, fun r l n12 n13 n14 n15 => ?_, ⟨_, _, rfl⟩, trivial, trivial, trivial⟩
  · have hx : 16 * l + 4 * q + 4 ≤ 32 := by omega
    rw [W2_first _ _ (i := 10) (by decide) _ _ hx, W2_second _ _ 10 _ _ hx, extract_ymm _ _ hl hq,
      extract_ymm _ _ hl hq]
    simp only [vw, lane_vpshufd256, State.lane_setV256, State.setMem_lane, reduceCtorEq, ite_true,
      ite_false, ite_self, shuf_00 _ hq, shuf_55 _ hq, shuf_aa _ hq, shuf_ff _ hq, and_self]
  · simp only [lane_vpshufd256, State.lane_setV256, State.setMem_lane, n12, n13, n14, n15, ite_false]

theorem mask_ok {buf : Addr} {s : State} (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr)
    (hc : Consts s.mem buf) :
    WP isa (.block [.vmovdquLoad .l256 .xmm15 (at_ .rcx rot16Off)]) s fun s' =>
      (∀ l, s'.lane .xmm15 l = rot16Mask) ∧ (∀ r l, r ≠ .xmm15 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i1 := in_buf (rs := s.rd) hb (d := rot16Off) (n := 32) (by decide)
  have l16 : (s.mem.readW (buf + BitVec.ofNat 64 rot16Off) 256).extractLsb' 0 128 = rot16Mask := hc.lo16
  have h16 : (s.mem.readW (buf + BitVec.ofNat 64 rot16Off) 256).extractLsb' 128 128 = rot16Mask :=
    hc.hi16
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hrcx, State.load256, i1,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left', State.setV_gpr, State.setV_mem,
    State.setV_rd, State.setV_wr]
  exact ⟨fun l => by simp only [State.lane_setV256, ite_true, l16, h16, ite_self],
    fun r l n => by simp only [State.lane_setV256, n, ite_false], trivial, trivial, trivial, trivial⟩

/-! ## The whole setup -/

theorem setup_eq : setup =
    bcast .xmm12 .xmm0 .xmm1 .xmm2 .xmm3 0 ++ (bcast .xmm12 .xmm4 .xmm5 .xmm6 .xmm7 16 ++
    (bcast .xmm12 .xmm8 .xmm9 .xmm10 .xmm11 48 ++ (incs ++ (row2 ++
    ([.vmovdquLoad .l256 .xmm15 (at_ .rcx rot16Off)] : List Instr))))) := rfl

theorem setup_ok {st buf : Addr} {s : State} (hrdi : s.gpr .rdi = st) (hrcx : s.gpr .rcx = buf)
    (hst : stR st ∈ s.wr) (hb : bufR buf ∈ s.wr) (hc : Consts s.mem buf) :
    WP isa (.block setup) s fun s' =>
      Holds buf false (fun j => ctr (stateAt s.mem st) j) s' ∧ (∀ l, s'.lane .xmm15 l = rot16Mask) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∃ y₁ y₂, s'.mem = W2 s.mem buf 10 y₁ y₂ := by
  have row : ∀ r, r < 4 → InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * r)) 16 :=
    fun r hr => hrdi ▸ in_st hst (by omega)
  rw [setup_eq]
  refine WP.block_append (WP.mono (bcast_ok (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (row 0 (by decide)))
    fun s₁ ⟨a₁, f₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.block_append (WP.mono (bcast_ok (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [g₁, rd₁, wr₁]; exact row 1 (by decide)))
    fun s₂ ⟨a₂, f₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.block_append (WP.mono (bcast_ok (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [g₂, g₁, rd₂, rd₁, wr₂, wr₁]; exact row 3 (by decide)))
    fun s₃ ⟨a₃, f₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  have e₃ : s₃.gpr = s.gpr ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr :=
    ⟨by rw [g₃, g₂, g₁], by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  refine WP.block_append (WP.mono (incs_ok (by rw [e₃.1, hrcx]) (by rw [e₃.2.2.2]; exact hb)
    (by rw [e₃.2.1]; exact hc)) fun s₄ ⟨a₄, f₄, g₄, m₄, rd₄, wr₄⟩ => ?_)
  refine WP.block_append (WP.mono (row2_ok (st := st) (buf := buf) (by rw [g₄, e₃.1, hrdi]) (by rw [g₄, e₃.1, hrcx])
    (by rw [wr₄, e₃.2.2.2]; exact hst) (by rw [wr₄, e₃.2.2.2]; exact hb))
    fun s₅ ⟨a₅, f₅, ⟨y₁, y₂, m₅⟩, g₅, rd₅, wr₅⟩ => ?_)
  refine WP.mono (mask_ok (by rw [g₅, g₄, e₃.1, hrcx]) (by rw [wr₅, wr₄, e₃.2.2.2]; exact hb)
    (by rw [m₅, m₄, e₃.2.1]; exact hc.w2 (by decide) y₁ y₂)) fun s₆ ⟨a₆, f₆, g₆, m₆, rd₆, wr₆⟩ => ?_
  refine ⟨fun k hk l q hl hq => ?_, a₆, by rw [g₆, g₅, g₄, e₃.1], by rw [rd₆, rd₅, rd₄, e₃.2.2.1],
    by rw [wr₆, wr₅, wr₄, e₃.2.2.2], ⟨y₁, y₂, by rw [m₆, m₅, m₄, e₃.2.1]⟩⟩
  have R : ∀ r (hr : r < 4) i (hi : i < 4),
      dword (s.mem.readW (st + BitVec.ofNat 64 (16 * r)) 128) i = (stateAt s.mem st)[4 * r + i]'(by omega) :=
    fun r hr i hi => dword_row s.mem st hr hi
  have R0 := R 0 (by decide); have R1 := R 1 (by decide)
  have R2 := R 2 (by decide); have R3 := R 3 (by decide)
  simp only [Nat.reduceMul, Nat.zero_add] at R0 R1 R2 R3
  obtain ⟨b₀, b₁, b₂, b₃⟩ := a₁ l q hq
  obtain ⟨b₄, b₅, b₆, b₇⟩ := a₂ l q hq
  obtain ⟨b₈, b₉, b₁₀, b₁₁⟩ := a₃ l q hq
  obtain ⟨c₈, c₉, c₁₀, c₁₁⟩ := a₅ l q hl hq
  have b₁₂ := a₄ l q hl hq
  simp only [hrdi, g₁, g₂, m₁, m₂] at b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  simp only [m₄, e₃.2.1] at c₈ c₉ c₁₀ c₁₁
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨
      k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
  all_goals
    simp (disch := decide) only [inReg, vreg, reduceCtorEq, or_self, or_false, false_or,
      Nat.reduceEqDiff, ite_true, ite_false, Bool.false_eq_true, Bool.not_false, vw, f₆, f₅, f₄,
      f₃, f₂, b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, b₉, b₁₀, b₁₁, b₁₂, c₈, c₉, c₁₀, c₁₁, R0, R1, R2,
      R3, ctr_get _ _ _ hk, m₆]

end VG.Proof.ChaCha20.X86_64.Avx2
