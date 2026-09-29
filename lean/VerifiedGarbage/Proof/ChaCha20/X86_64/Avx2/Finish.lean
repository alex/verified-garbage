import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Setup

/-!
# ChaCha20 on x86-64 with AVX2: the output

Untrusted: everything here is checked by Lean. The rounds' result plus the
input states, transposed into blocks and XORed into 512 bytes of data.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx2

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt serialize)
open VG.Proof.ChaCha20

/-! ## Adding a row of the input state -/

theorem addRow_eq (row : Nat) (x0 x1 x2 x3 : XReg) : addRow row [x0, x1, x2, x3] =
    [.vbroadcasti128 .xmm14 (at_ .rdi (16 * row)),
     .vop (.vpshufd .l256 .xmm15 .xmm14 0x00), .vop (.vbin .vpaddd .l256 x0 x0 .xmm15),
     .vop (.vpshufd .l256 .xmm15 .xmm14 0x55), .vop (.vbin .vpaddd .l256 x1 x1 .xmm15),
     .vop (.vpshufd .l256 .xmm15 .xmm14 0xaa), .vop (.vbin .vpaddd .l256 x2 x2 .xmm15),
     .vop (.vpshufd .l256 .xmm15 .xmm14 0xff), .vop (.vbin .vpaddd .l256 x3 x3 .xmm15)] := rfl

theorem addRow_ok {row : Nat} {x0 x1 x2 x3 : XReg} (e01 : x0 ≠ x1) (e02 : x0 ≠ x2) (e03 : x0 ≠ x3)
    (e12 : x1 ≠ x2) (e13 : x1 ≠ x3) (e23 : x2 ≠ x3) (h0 : x0 ≠ .xmm14) (h1 : x1 ≠ .xmm14)
    (h2 : x2 ≠ .xmm14) (h3 : x3 ≠ .xmm14) (k0 : x0 ≠ .xmm15) (k1 : x1 ≠ .xmm15) (k2 : x2 ≠ .xmm15)
    (k3 : x3 ≠ .xmm15) {s : State}
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * row)) 16) :
    WP isa (.block (addRow row [x0, x1, x2, x3])) s fun s' =>
      (∀ l q, q < 4 →
        vw s' x0 l q = vw s x0 l q + dword (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (16 * row)) 128) 0 ∧
        vw s' x1 l q = vw s x1 l q + dword (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (16 * row)) 128) 1 ∧
        vw s' x2 l q = vw s x2 l q + dword (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (16 * row)) 128) 2 ∧
        vw s' x3 l q = vw s x3 l q + dword (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (16 * row)) 128) 3) ∧
      (∀ r l, r ≠ x0 → r ≠ x1 → r ≠ x2 → r ≠ x3 → r ≠ .xmm14 → r ≠ .xmm15 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  rw [addRow_eq]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, State.load128, hin,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left', VOp.exec_gpr, VOp.exec_mem,
    VOp.exec_rd, VOp.exec_wr, State.setV_gpr, State.setV_mem, State.setV_rd, State.setV_wr]
  refine ⟨fun l q hq => ?_, fun r l n0 n1 n2 n3 n14 n15 => ?_, trivial, trivial, trivial, trivial⟩
  · simp only [vw, lane_vpshufd256, lane_vbin256, State.lane_setV256, VBinOp.sse, e01, e02, e03,
      e12, e13, e23, e01.symm, e02.symm, e03.symm, e12.symm, e13.symm, e23.symm, h0, h1, h2, h3,
      k0, k1, k2, k3, h0.symm, h1.symm, h2.symm, k0.symm, k1.symm, k2.symm,
      reduceCtorEq, ite_true, ite_false, ite_self, dword_paddd _ _ hq, shuf_00 _ hq,
      shuf_55 _ hq, shuf_aa _ hq, shuf_ff _ hq, and_self]
  · simp only [lane_vpshufd256, lane_vbin256, State.lane_setV256, n0, n1, n2, n3, n14, n15,
      ite_false]

/-! ## Transposing -/

theorem transpose_ok {x0 x1 x2 x3 : XReg} (e01 : x0 ≠ x1) (e02 : x0 ≠ x2) (e03 : x0 ≠ x3)
    (e12 : x1 ≠ x2) (e13 : x1 ≠ x3) (e23 : x2 ≠ x3)
    (h0 : x0 ≠ .xmm12 ∧ x0 ≠ .xmm13 ∧ x0 ≠ .xmm14 ∧ x0 ≠ .xmm15)
    (h1 : x1 ≠ .xmm12 ∧ x1 ≠ .xmm13 ∧ x1 ≠ .xmm14 ∧ x1 ≠ .xmm15)
    (h2 : x2 ≠ .xmm12 ∧ x2 ≠ .xmm13 ∧ x2 ≠ .xmm14 ∧ x2 ≠ .xmm15)
    (h3 : x3 ≠ .xmm12 ∧ x3 ≠ .xmm13 ∧ x3 ≠ .xmm14 ∧ x3 ≠ .xmm15) {s : State} :
    WP isa (.block (transpose x0 x1 x2 x3)) s fun s' =>
      (∀ l,
        s'.lane x0 l = ofDwords (vw s x0 l 0) (vw s x1 l 0) (vw s x2 l 0) (vw s x3 l 0) ∧
        s'.lane x1 l = ofDwords (vw s x0 l 1) (vw s x1 l 1) (vw s x2 l 1) (vw s x3 l 1) ∧
        s'.lane x2 l = ofDwords (vw s x0 l 2) (vw s x1 l 2) (vw s x2 l 2) (vw s x3 l 2) ∧
        s'.lane x3 l = ofDwords (vw s x0 l 3) (vw s x1 l 3) (vw s x2 l 3) (vw s x3 l 3)) ∧
      (∀ r l, r ≠ x0 → r ≠ x1 → r ≠ x2 → r ≠ x3 → r ≠ .xmm12 → r ≠ .xmm13 → r ≠ .xmm14 →
        r ≠ .xmm15 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨a0, b0, c0, d0⟩ := h0; obtain ⟨a1, b1, c1, d1⟩ := h1
  obtain ⟨a2, b2, c2, d2⟩ := h2; obtain ⟨a3, b3, c3, d3⟩ := h3
  apply WP.of_runBlock
  simp only [transpose, v, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
    exists_eq_left', VOp.exec_gpr, VOp.exec_mem, VOp.exec_rd, VOp.exec_wr]
  refine ⟨fun l => ?_, fun r l n0 n1 n2 n3 n12 n13 n14 n15 => ?_, trivial, trivial, trivial, trivial⟩
  · simp only [vw, lane_vbin256, VBinOp.sse, e01, e02, e03, e12, e13, e23, e01.symm, e02.symm,
      e03.symm, e12.symm, e13.symm, e23.symm, a0, b0, c0, d0, a1, b1, c1, d1, a2, b2, c2, d2, a3, b3,
      c3, d3, a0.symm, b0.symm, c0.symm, d0.symm, b1.symm, d1.symm,
      b2.symm, d2.symm, reduceCtorEq, ite_true,
      ite_false, punpcklqdq_eq, punpckhqdq_eq, dword_punpckldq, dword_punpckhdq, dword_ofDwords_0,
      dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, and_self]
  · simp only [lane_vbin256, n0, n1, n2, n3, n12, n13, n14, n15, ite_false]

/-! ## XORing 16 bytes into the data -/

/-- The 512 bytes of data of one iteration. -/
abbrev dR5 (a : Addr) : Region := ⟨a, 512⟩

theorem dR5_contains (a : Addr) {d n : Nat} (h : d + n ≤ 512) :
    (dR5 a).Contains (a + BitVec.ofNat 64 d) n := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat a (by omega)]; exact h

/-- Every access within the 512 bytes at `a` is permitted by `ws`. -/
def DWin (ws : List Region) (a : Addr) : Prop :=
  ∀ off n, off + n ≤ 512 → InRegions ws (a + BitVec.ofNat 64 off) n

theorem State.xmm_lane (s : State) (r : XReg) : s.xmm r = s.lane r 0 := by
  simp [State.lane]

/-- A byte of the data after a 16-byte write at offset `off`. -/
theorem byte_write16 (m : Mem) (a : Addr) (v : BitVec 128) {off k : Nat} (ho : off + 16 ≤ 512)
    (hk : k < 512) : (m.writeW (a + BitVec.ofNat 64 off) v) (a + BitVec.ofNat 64 k) =
      if off ≤ k ∧ k < off + 16 then byte v (k - off) else m (a + BitVec.ofNat 64 k) := by
  by_cases h : off ≤ k ∧ k < off + 16
  · rw [ite_eq_left h, show a + BitVec.ofNat 64 k = a + BitVec.ofNat 64 off + BitVec.ofNat 64 (k - off) by
      rw [add_ofNat, Nat.add_sub_cancel' h.1]]
    exact writeW_byte _ _ _ (by omega) (by omega)
  · rw [ite_eq_right h]
    refine writeW_byte_off _ _ _ _ ?_
    bv_omega

theorem xor16_ok {x : XReg} (hx : x ≠ .xmm12) {off : Nat} (ho : off + 16 ≤ 512) {a : Addr}
    {s : State} (hrsi : s.gpr .rsi = a) (hw : DWin s.wr a) :
    WP isa (.block (xor16 x off)) s fun s' =>
      (∀ k < 512, s'.mem (a + BitVec.ofNat 64 k) = if off ≤ k ∧ k < off + 16 then
        s.mem (a + BitVec.ofNat 64 k) ^^^ byte (s.lane x 0) (k - off) else s.mem (a + BitVec.ofNat 64 k)) ∧
      Frame [dR5 a] s.mem s'.mem ∧
      (∀ r l, r ≠ .xmm12 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have c := dR5_contains a ho
  have o1 : InRegions s.wr (a + BitVec.ofNat 64 off) 16 := hw off 16 ho
  have i1 : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 off) 16 :=
    let ⟨r, hr, hc⟩ := o1; ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.of_runBlock
  simp only [xor16, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hrsi, State.load128,
    State.store128_eq, i1, o1, ite_true, Option.map_some, Option.some.injEq,
    exists_eq_left', VOp.exec_gpr, VOp.exec_mem, VOp.exec_rd, VOp.exec_wr, State.setV_gpr,
    State.setV_mem, State.setV_rd, State.setV_wr, State.setMem_gpr, State.setMem_mem,
    State.setMem_rd, State.setMem_wr, State.xmm_lane, lane_vbin128, State.lane_setV128, hx,
    ite_false, VBinOp.sse, XBinOp.eval]
  refine ⟨fun k hk => ?_, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c,
    fun r l hr => ?_, trivial, trivial, trivial⟩
  · rw [byte_write16 _ _ _ ho hk]
    by_cases h : off ≤ k ∧ k < off + 16
    · simp only [h.1, h.2, and_self, ite_true, byte]
      rw [BitVec.extractLsb'_xor, byte_readW _ _ (by omega), add_ofNat, Nat.add_sub_cancel' h.1]
    · simp only [h, ite_false]
  · simp only [State.setMem_lane, lane_vbin128, State.lane_setV128, hr, ite_false]

/-! ## XORing a row of the eight blocks -/

/-- Row `row` of blocks `i` and `i + 4`, from lanes 0 and 1 of `x`. -/
def piece (row : Nat) (x : XReg) (i : Nat) : List Instr :=
  xor16 x (64 * i + 16 * row) ++ [.vop (.vextracti128 .xmm13 x 1)] ++ xor16 .xmm13 (64 * (i + 4) + 16 * row)

theorem piece_ok {row i : Nat} (hrow : row < 4) (hi : i < 4) {x : XReg} (hx12 : x ≠ .xmm12)
    {a : Addr} {s : State} (hrsi : s.gpr .rsi = a) (hw : DWin s.wr a) :
    WP isa (.block (piece row x i)) s fun s' =>
      (∀ k < 512, s'.mem (a + BitVec.ofNat 64 k) =
        if (k / 64 = i ∨ k / 64 = i + 4) ∧ k % 64 / 16 = row then
          s.mem (a + BitVec.ofNat 64 k) ^^^ byte (s.lane x (k / 64 / 4)) (k % 16)
        else s.mem (a + BitVec.ofNat 64 k)) ∧
      Frame [dR5 a] s.mem s'.mem ∧
      (∀ r l, r ≠ .xmm12 → r ≠ .xmm13 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.block_append (WP.block_append (WP.mono (xor16_ok hx12 (by omega) hrsi hw)
    fun s₁ ⟨m₁, f₁, l₁, g₁, r₁, w₁⟩ => ?_))
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  refine WP.mono (xor16_ok (x := .xmm13) (by decide) (off := 64 * (i + 4) + 16 * row) (a := a) (by omega)
    (by rw [VOp.exec_gpr, g₁, hrsi]) (by rw [VOp.exec_wr, w₁]; exact hw))
    fun s₃ ⟨m₃, f₃, l₃, g₃, r₃, w₃⟩ => ?_
  simp only [VOp.exec_gpr, VOp.exec_mem, VOp.exec_rd, VOp.exec_wr, lane_vextracti128_1, ite_true,
    l₁ x 1 hx12] at m₃ f₃ l₃ g₃ r₃ w₃
  refine ⟨fun k hk => ?_, f₁.trans f₃, fun r l h12 h13 => ?_, g₃.trans g₁, r₃.trans r₁, w₃.trans w₁⟩
  · rw [m₃ k hk, m₁ k hk]
    by_cases h1 : 64 * i + 16 * row ≤ k ∧ k < 64 * i + 16 * row + 16
    · have h2 : ¬ (64 * (i + 4) + 16 * row ≤ k ∧ k < 64 * (i + 4) + 16 * row + 16) := by omega
      have hc : (k / 64 = i ∨ k / 64 = i + 4) ∧ k % 64 / 16 = row := by omega
      rw [ite_eq_right h2, ite_eq_left h1, ite_eq_left hc, show k / 64 / 4 = 0 by omega,
        show k - (64 * i + 16 * row) = k % 16 by omega]
    · by_cases h2 : 64 * (i + 4) + 16 * row ≤ k ∧ k < 64 * (i + 4) + 16 * row + 16
      · have hc : (k / 64 = i ∨ k / 64 = i + 4) ∧ k % 64 / 16 = row := by omega
        rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left hc, show k / 64 / 4 = 1 by omega,
          show k - (64 * (i + 4) + 16 * row) = k % 16 by omega]
      · have hc : ¬ ((k / 64 = i ∨ k / 64 = i + 4) ∧ k % 64 / 16 = row) := by omega
        rw [ite_eq_right h2, ite_eq_right h1, ite_eq_right hc]
  · rw [l₃ r l h12, ite_eq_right h13, l₁ r l h12]

theorem xorRow_eq (row : Nat) (x0 x1 x2 x3 : XReg) : xorRow row [x0, x1, x2, x3] =
    piece row x0 0 ++ (piece row x1 1 ++ (piece row x2 2 ++ piece row x3 3)) := by
  simp only [xorRow, piece, List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.getD_cons_zero, List.getD_cons_succ,
    List.append_assoc]

theorem xorRow_ok {row : Nat} (hrow : row < 4) {x0 x1 x2 x3 : XReg}
    (h0 : x0 ≠ .xmm12 ∧ x0 ≠ .xmm13) (h1 : x1 ≠ .xmm12 ∧ x1 ≠ .xmm13)
    (h2 : x2 ≠ .xmm12 ∧ x2 ≠ .xmm13) (h3 : x3 ≠ .xmm12 ∧ x3 ≠ .xmm13) {a : Addr} {s : State}
    (hrsi : s.gpr .rsi = a) (hw : DWin s.wr a) :
    WP isa (.block (xorRow row [x0, x1, x2, x3])) s fun s' =>
      (∀ k < 512, s'.mem (a + BitVec.ofNat 64 k) =
        if k % 64 / 16 = row then
          s.mem (a + BitVec.ofNat 64 k) ^^^
            byte (s.lane ([x0, x1, x2, x3].getD (k / 64 % 4) .xmm0) (k / 64 / 4)) (k % 16)
        else s.mem (a + BitVec.ofNat 64 k)) ∧
      Frame [dR5 a] s.mem s'.mem ∧
      (∀ r l, r ≠ .xmm12 → r ≠ .xmm13 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [xorRow_eq]
  refine WP.block_append (WP.mono (piece_ok hrow (i := 0) (by omega) h0.1 hrsi hw)
    fun s₁ ⟨m₁, f₁, l₁, g₁, r₁, w₁⟩ => ?_)
  refine WP.block_append (WP.mono (piece_ok hrow (i := 1) (a := a) (by omega) h1.1 (by rw [g₁, hrsi])
    (by rw [w₁]; exact hw)) fun s₂ ⟨m₂, f₂, l₂, g₂, r₂, w₂⟩ => ?_)
  refine WP.block_append (WP.mono (piece_ok hrow (i := 2) (a := a) (by omega) h2.1 (by rw [g₂, g₁, hrsi])
    (by rw [w₂, w₁]; exact hw)) fun s₃ ⟨m₃, f₃, l₃, g₃, r₃, w₃⟩ => ?_)
  refine WP.mono (piece_ok hrow (i := 3) (a := a) (by omega) h3.1 (by rw [g₃, g₂, g₁, hrsi])
    (by rw [w₃, w₂, w₁]; exact hw)) fun s₄ ⟨m₄, f₄, l₄, g₄, r₄, w₄⟩ => ?_
  have e1 : ∀ l, s₁.lane x1 l = s.lane x1 l := fun l => l₁ _ l h1.1 h1.2
  have e2 : ∀ l, s₂.lane x2 l = s.lane x2 l := fun l => (l₂ _ l h2.1 h2.2).trans (l₁ _ l h2.1 h2.2)
  have e3 : ∀ l, s₃.lane x3 l = s.lane x3 l := fun l =>
    ((l₃ _ l h3.1 h3.2).trans (l₂ _ l h3.1 h3.2)).trans (l₁ _ l h3.1 h3.2)
  refine ⟨fun k hk => ?_, ((f₁.trans f₂).trans f₃).trans f₄, fun r l n12 n13 => ?_,
    by rw [g₄, g₃, g₂, g₁], by rw [r₄, r₃, r₂, r₁], by rw [w₄, w₃, w₂, w₁]⟩
  · rw [m₄ k hk, m₃ k hk, m₂ k hk, m₁ k hk, e1, e2, e3]
    rcases (by omega : k / 64 = 0 ∨ k / 64 = 1 ∨ k / 64 = 2 ∨ k / 64 = 3 ∨
      k / 64 = 4 ∨ k / 64 = 5 ∨ k / 64 = 6 ∨ k / 64 = 7) with h | h | h | h | h | h | h | h <;>
      simp [h]
  · rw [l₄ r l n12 n13, l₃ r l n12 n13, l₂ r l n12 n13, l₁ r l n12 n13]

/-! ## A row of the eight blocks, into the data -/

theorem byte_ofDwords (a0 a1 a2 a3 : Word) (b : Nat) :
    byte (ofDwords a0 a1 a2 a3) b = (dword (ofDwords a0 a1 a2 a3) (b / 4)).extractLsb' (8 * (b % 4)) 8 := by
  rw [byte, dword_eq, extract_extract _ _ _ _ _ (by omega), show 32 * (b / 4) + 8 * (b % 4) = 8 * b by omega]

/-- Byte `k % 64` of a serialized block, in row `row`. -/
theorem serialize_row (S : CState) {k row : Nat} (hrow : row < 4) (hk : k % 64 / 16 = row) :
    (serialize S).getD (k % 64) 0 =
      byte (ofDwords S[4 * row] S[4 * row + 1] S[4 * row + 2] S[4 * row + 3]) (k % 16) := by
  rw [serialize_getD _ (by omega), byte_ofDwords, show k % 64 % 4 = k % 16 % 4 by omega]
  rcases (by omega : k % 16 / 4 = 0 ∨ k % 16 / 4 = 1 ∨ k % 16 / 4 = 2 ∨ k % 16 / 4 = 3) with h | h | h | h
  · have e : k % 64 / 4 = 4 * row := by omega
    simp only [h, e, dword_ofDwords_0]
  · have e : k % 64 / 4 = 4 * row + 1 := by omega
    simp only [h, e, dword_ofDwords_1]
  · have e : k % 64 / 4 = 4 * row + 2 := by omega
    simp only [h, e, dword_ofDwords_2]
  · have e : k % 64 / 4 = 4 * row + 3 := by omega
    simp only [h, e, dword_ofDwords_3]

/-- The registers `x0 … x3` hold row `row` of the blocks `B 0, …, B 7`. -/
def RowIn (row : Nat) (x0 x1 x2 x3 : XReg) (B : Nat → CState) (s : State) : Prop :=
  ∀ l q, l < 2 → q < 4 → (hrow : row < 4) →
    vw s x0 l q = (B (4 * l + q))[4 * row] ∧ vw s x1 l q = (B (4 * l + q))[4 * row + 1] ∧
    vw s x2 l q = (B (4 * l + q))[4 * row + 2] ∧ vw s x3 l q = (B (4 * l + q))[4 * row + 3]

theorem rowOut_ok {row : Nat} (hrow : row < 4) {x0 x1 x2 x3 : XReg} (e01 : x0 ≠ x1) (e02 : x0 ≠ x2)
    (e03 : x0 ≠ x3) (e12 : x1 ≠ x2) (e13 : x1 ≠ x3) (e23 : x2 ≠ x3)
    (h0 : x0 ≠ .xmm12 ∧ x0 ≠ .xmm13 ∧ x0 ≠ .xmm14 ∧ x0 ≠ .xmm15)
    (h1 : x1 ≠ .xmm12 ∧ x1 ≠ .xmm13 ∧ x1 ≠ .xmm14 ∧ x1 ≠ .xmm15)
    (h2 : x2 ≠ .xmm12 ∧ x2 ≠ .xmm13 ∧ x2 ≠ .xmm14 ∧ x2 ≠ .xmm15)
    (h3 : x3 ≠ .xmm12 ∧ x3 ≠ .xmm13 ∧ x3 ≠ .xmm14 ∧ x3 ≠ .xmm15) {B : Nat → CState} {a : Addr}
    {s : State} (hB : RowIn row x0 x1 x2 x3 B s) (hrsi : s.gpr .rsi = a) (hw : DWin s.wr a) :
    WP isa (.block (transpose x0 x1 x2 x3 ++ xorRow row [x0, x1, x2, x3])) s fun s' =>
      (∀ k < 512, s'.mem (a + BitVec.ofNat 64 k) =
        if k % 64 / 16 = row then
          s.mem (a + BitVec.ofNat 64 k) ^^^ (serialize (B (k / 64))).getD (k % 64) 0
        else s.mem (a + BitVec.ofNat 64 k)) ∧
      Frame [dR5 a] s.mem s'.mem ∧
      (∀ r l, r ≠ x0 → r ≠ x1 → r ≠ x2 → r ≠ x3 → r ≠ .xmm12 → r ≠ .xmm13 → r ≠ .xmm14 →
        r ≠ .xmm15 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.block_append (WP.mono (transpose_ok e01 e02 e03 e12 e13 e23 h0 h1 h2 h3)
    fun s₁ ⟨lt, lo, g₁, m₁, r₁, w₁⟩ => ?_)
  refine WP.mono (xorRow_ok hrow (a := a) ⟨h0.1, h0.2.1⟩ ⟨h1.1, h1.2.1⟩ ⟨h2.1, h2.2.1⟩ ⟨h3.1, h3.2.1⟩
    (by rw [g₁]; exact hrsi) (by rw [w₁]; exact hw)) fun s₂ ⟨m₂, f₂, l₂, g₂, r₂, w₂⟩ => ?_
  rw [m₁] at m₂ f₂
  refine ⟨fun k hk => ?_, f₂, fun r l n0 n1 n2 n3 n12 n13 n14 n15 => ?_, g₂.trans g₁, r₂.trans r₁,
    w₂.trans w₁⟩
  · rw [m₂ k hk]
    by_cases hr : k % 64 / 16 = row
    · rw [ite_eq_left hr, ite_eq_left hr, serialize_row _ hrow hr]
      obtain ⟨l, q, hl, hq, e⟩ : ∃ l q, l < 2 ∧ q < 4 ∧ k / 64 = 4 * l + q :=
        ⟨k / 64 / 4, k / 64 % 4, by omega, by omega, by omega⟩
      rw [e, show (4 * l + q) / 4 = l by omega, show (4 * l + q) % 4 = q by omega]
      obtain ⟨b0, b1, b2, b3⟩ := hB l q hl hq hrow
      rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl
      · rw [List.getD_cons_zero, (lt l).1, b0, b1, b2, b3]
      · rw [List.getD_cons_succ, List.getD_cons_zero, (lt l).2.1, b0, b1, b2, b3]
      · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero, (lt l).2.2.1, b0, b1, b2, b3]
      · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero,
          (lt l).2.2.2, b0, b1, b2, b3]
    · rw [ite_eq_right hr, ite_eq_right hr]
  · rw [l₂ r l n12 n13, lo r l n0 n1 n2 n3 n12 n13 n14 n15]

/-! ## The third row, through the slots -/

@[simp] theorem State.setMem_ymm (s : State) (m : Mem) (r : XReg) : (s.setMem m).ymm r = s.ymm r := by
  cases s; rfl

def store89 : List Instr :=
  [.vmovdquStore .l256 (at_ .rcx (slotOff 8)) .xmm12, .vmovdquStore .l256 (at_ .rcx (slotOff 9)) .xmm13]

/-- Words 8–11 of the eight states `vs`, in their slots. -/
def Slots (buf : Addr) (vs : Nat → CState) (m : Mem) : Prop :=
  ∀ r l q, (hr : r < 4) → l < 2 → q < 4 →
    m.readW (buf + BitVec.ofNat 64 (slotOff (8 + r) + (16 * l + 4 * q))) 32 = (vs (4 * l + q))[8 + r]

theorem store89_ok {buf : Addr} {vs : Nat → CState} {s : State} (h : Holds buf false vs s)
    (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr) :
    WP isa (.block store89) s fun s' =>
      Slots buf vs s'.mem ∧ (∀ r l, s'.lane r l = s.lane r l) ∧ Frame [slotsR buf] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o8 := out_buf hb (d := slotOff 8) (n := 32) (by decide)
  have o9 := out_buf hb (d := slotOff 8 + 32) (n := 32) (by decide)
  have s9 : slotOff 9 = slotOff 8 + 32 := rfl
  apply WP.of_runBlock
  simp only [store89, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hrcx, State.store256_eq,
    o8, o9, s9, ite_true, Option.some.injEq, exists_eq_left', State.setMem_gpr, State.setMem_mem,
    State.setMem_rd, State.setMem_wr, State.setMem_lane, State.setMem_ymm]
  refine ⟨fun r l q hr hl hq => ?_, fun r l => trivial, W2_frame buf (i := 8) (by decide) _ _
    (Frame.refl _ _), trivial, trivial, trivial⟩
  have hx : 16 * l + 4 * q + 4 ≤ 32 := by omega
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl
  · have e := h 8 (by decide) l q hl hq
    simp only [inReg, vreg, vw, Bool.not_false] at e
    simp only [Nat.add_zero]
    rw [W2_first _ _ (i := 8) (by decide) _ _ hx, extract_ymm _ _ hl hq]; exact e
  · have e := h 9 (by decide) l q hl hq
    simp only [inReg, vreg, ite_true, vw, or_true, Bool.not_false] at e
    simp only [Nat.reduceAdd, s9]
    rw [W2_second _ _ 8 _ _ hx, extract_ymm _ _ hl hq]; exact e
  · have e := h 10 (by decide) l q hl hq
    simp only [inReg, Nat.reduceEqDiff, or_false, ite_true, ite_false,
      Bool.false_eq_true] at e
    simp only [Nat.reduceAdd]
    rw [W2_other _ _ (i := 8) (by decide) _ _ (d := slotOff 10 + (16 * l + 4 * q))
      (by simp only [slotOff]; omega) (by simp only [slotOff]; omega)]; exact e
  · have e := h 11 (by decide) l q hl hq
    simp only [inReg, Nat.reduceEqDiff, or_false, or_true, ite_true, ite_false,
      Bool.false_eq_true] at e
    simp only [Nat.reduceAdd]
    rw [W2_other _ _ (i := 8) (by decide) _ _ (d := slotOff 11 + (16 * l + 4 * q))
      (by simp only [slotOff]; omega) (by simp only [slotOff]; omega)]; exact e

def load4 : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rcx (slotOff 8)), .vmovdquLoad .l256 .xmm1 (at_ .rcx (slotOff 9)),
   .vmovdquLoad .l256 .xmm2 (at_ .rcx (slotOff 10)), .vmovdquLoad .l256 .xmm3 (at_ .rcx (slotOff 11))]

theorem load4_ok {buf : Addr} {vs : Nat → CState} {s : State} (h : Slots buf vs s.mem)
    (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr) :
    WP isa (.block load4) s fun s' =>
      RowIn 2 .xmm0 .xmm1 .xmm2 .xmm3 vs s' ∧
      (∀ r l, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i8 := in_buf (rs := s.rd) hb (d := slotOff 8) (n := 32) (by decide)
  have i9 := in_buf (rs := s.rd) hb (d := slotOff 9) (n := 32) (by decide)
  have i10 := in_buf (rs := s.rd) hb (d := slotOff 10) (n := 32) (by decide)
  have i11 := in_buf (rs := s.rd) hb (d := slotOff 11) (n := 32) (by decide)
  apply WP.of_runBlock
  simp only [load4, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hrcx, State.load256, i8,
    i9, i10, i11, ite_true, Option.map_some, Option.some.injEq, exists_eq_left', State.setV_gpr,
    State.setV_mem, State.setV_rd, State.setV_wr]
  refine ⟨fun l q hl hq _ => ?_, fun r l n0 n1 n2 n3 => ?_, trivial, trivial, trivial, trivial⟩
  · have h0 := h 0 l q (by decide) hl hq
    have h1 := h 1 l q (by decide) hl hq
    have h2 := h 2 l q (by decide) hl hq
    have h3 := h 3 l q (by decide) hl hq
    simp only [Nat.reduceAdd, Nat.add_zero] at h0 h1 h2 h3
    simp only [vw, State.lane_setV256, reduceCtorEq, ite_true, ite_false, dword_load256 _ _ hl hq,
      add_ofNat, Nat.reduceMul, Nat.reduceAdd, h0, h1, h2, h3, and_self]
  · simp only [State.lane_setV256, n0, n1, n2, n3, ite_false]

/-! ## Adding the input state -/

/-- Row `row` of the input state `S`, read 128 bits at a time at `st`. -/
def RowS (row : Nat) (S : CState) (m : Mem) (st : Addr) : Prop :=
  (hrow : row < 4) →
    dword (m.readW (st + BitVec.ofNat 64 (16 * row)) 128) 0 = S[4 * row] ∧
    dword (m.readW (st + BitVec.ofNat 64 (16 * row)) 128) 1 = S[4 * row + 1] ∧
    dword (m.readW (st + BitVec.ofNat 64 (16 * row)) 128) 2 = S[4 * row + 2] ∧
    dword (m.readW (st + BitVec.ofNat 64 (16 * row)) 128) 3 = S[4 * row + 3]

theorem rowS_of (m : Mem) (st : Addr) (row : Nat) : RowS row (stateAt m st) m st := fun hrow =>
  ⟨dword_row m st hrow (i := 0) (by decide), dword_row m st hrow (i := 1) (by decide),
    dword_row m st hrow (i := 2) (by decide), dword_row m st hrow (i := 3) (by decide)⟩

/-- Block `j` of the eight, before the input state is added: `vs j` plus `ctr S j`. -/
abbrev plus (vs : Nat → CState) (S : CState) (j : Nat) : CState := Vector.zipWith (· + ·) (vs j) (ctr S j)

theorem ctr_ne12 (S : CState) (j : Nat) {k : Nat} (hk : k < 16) (h : k ≠ 12) : (ctr S j)[k] = S[k] := by
  rw [ctr_get _ _ _ hk, ite_eq_right h]

theorem addRow_in {row : Nat} (h3 : row ≠ 3) {x0 x1 x2 x3 : XReg} (e01 : x0 ≠ x1)
    (e02 : x0 ≠ x2) (e03 : x0 ≠ x3) (e12 : x1 ≠ x2) (e13 : x1 ≠ x3) (e23 : x2 ≠ x3)
    (h0 : x0 ≠ .xmm14) (h1 : x1 ≠ .xmm14) (h2 : x2 ≠ .xmm14) (h3' : x3 ≠ .xmm14) (k0 : x0 ≠ .xmm15)
    (k1 : x1 ≠ .xmm15) (k2 : x2 ≠ .xmm15) (k3 : x3 ≠ .xmm15) {vs : Nat → CState} {S : CState}
    {s : State} (hin : RowIn row x0 x1 x2 x3 vs s) (hS : RowS row S s.mem (s.gpr .rdi))
    (hrd : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * row)) 16) :
    WP isa (.block (addRow row [x0, x1, x2, x3])) s fun s' =>
      RowIn row x0 x1 x2 x3 (plus vs S) s' ∧
      (∀ r l, r ≠ x0 → r ≠ x1 → r ≠ x2 → r ≠ x3 → r ≠ .xmm14 → r ≠ .xmm15 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (addRow_ok e01 e02 e03 e12 e13 e23 h0 h1 h2 h3' k0 k1 k2 k3 hrd)
    fun _ ⟨ha, hl, hg, hm, hr, hw⟩ => ⟨fun l q hl' hq hrow' => by
      obtain ⟨a0, a1, a2, a3⟩ := ha l q hq
      obtain ⟨b0, b1, b2, b3⟩ := hin l q hl' hq hrow'
      obtain ⟨c0, c1, c2, c3⟩ := hS hrow'
      rw [a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3]
      simp only [plus, Vector.getElem_zipWith]
      rw [ctr_ne12 _ _ _ (by omega), ctr_ne12 _ _ _ (by omega), ctr_ne12 _ _ _ (by omega),
        ctr_ne12 _ _ _ (by omega)]
      exact ⟨rfl, rfl, rfl, rfl⟩, hl, hg, hm, hr, hw⟩

def incAdd : List Instr :=
  [.vmovdquLoad .l256 .xmm15 (at_ .rcx incOff), v .vpaddd .xmm8 .xmm8 .xmm15]

theorem incAdd_ok {buf : Addr} {s : State} (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr)
    (hc : ∀ l q, l < 2 → q < 4 →
      s.mem.readW (buf + BitVec.ofNat 64 (192 + (16 * l + 4 * q))) 32 = BitVec.ofNat 32 (4 * l + q)) :
    WP isa (.block incAdd) s fun s' =>
      (∀ l q, l < 2 → q < 4 → vw s' .xmm8 l q = vw s .xmm8 l q + BitVec.ofNat 32 (4 * l + q)) ∧
      (∀ r l, r ≠ .xmm8 → r ≠ .xmm15 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i1 := in_buf (rs := s.rd) hb (d := incOff) (n := 32) (by decide)
  apply WP.of_runBlock
  simp only [incAdd, v, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hrcx, State.load256, i1,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left', VOp.exec_gpr, VOp.exec_mem,
    VOp.exec_rd, VOp.exec_wr, State.setV_gpr, State.setV_mem, State.setV_rd, State.setV_wr]
  refine ⟨fun l q hl hq => ?_, fun r l n8 n15 => ?_, trivial, trivial, trivial, trivial⟩
  · simp only [vw, lane_vbin256, State.lane_setV256, reduceCtorEq, ite_true, ite_false, VBinOp.sse,
      dword_paddd _ _ hq, dword_load256 _ _ hl hq]
    rw [add_ofNat]; exact congrArg _ (hc l q hl hq)
  · simp only [lane_vbin256, State.lane_setV256, n8, n15, ite_false]

theorem addRow3_in {buf : Addr} {vs : Nat → CState} {S : CState} {s : State}
    (hin : RowIn 3 .xmm8 .xmm9 .xmm10 .xmm11 vs s) (hS : RowS 3 S s.mem (s.gpr .rdi))
    (hrd : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * 3)) 16)
    (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr)
    (hc : ∀ l q, l < 2 → q < 4 →
      s.mem.readW (buf + BitVec.ofNat 64 (192 + (16 * l + 4 * q))) 32 = BitVec.ofNat 32 (4 * l + q)) :
    WP isa (.block (addRow 3 ([.xmm8, .xmm9, .xmm10, .xmm11] : List XReg) ++ incAdd)) s fun s' =>
      RowIn 3 .xmm8 .xmm9 .xmm10 .xmm11 (plus vs S) s' ∧
      (∀ r l, r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 → r ≠ .xmm14 → r ≠ .xmm15 →
        s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.block_append (WP.mono (addRow_ok (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hrd) fun s₁ ⟨ha, hl, hg, hm, hr, hw⟩ => ?_)
  refine WP.mono (incAdd_ok (by rw [hg, hrcx]) (by rw [hw]; exact hb) (by rw [hm]; exact hc))
    fun s₂ ⟨ia, il, ig, im, ir, iw⟩ => ⟨fun l q hl' hq _ => ?_, fun r l n8 n9 n10 n11 n14 n15 => ?_,
      ig.trans hg, im.trans hm, ir.trans hr, iw.trans hw⟩
  · obtain ⟨a0, a1, a2, a3⟩ := ha l q hq
    obtain ⟨b0, b1, b2, b3⟩ := hin l q hl' hq (by decide)
    obtain ⟨c0, c1, c2, c3⟩ := hS (by decide)
    have jl : ∀ r, r ≠ .xmm8 → r ≠ .xmm15 → vw s₂ r l q = vw s₁ r l q := fun r h8 h15 => by
      simp only [vw]; rw [il r l h8 h15]
    rw [ia l q hl' hq, jl .xmm9 (by decide) (by decide), jl .xmm10 (by decide) (by decide),
      jl .xmm11 (by decide) (by decide), a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3]
    simp only [plus, Vector.getElem_zipWith]
    rw [ctr_get _ _ _ (by decide), ite_eq_left (by decide), ctr_ne12 _ _ _ (by decide),
      ctr_ne12 _ _ _ (by decide), ctr_ne12 _ _ _ (by decide), BitVec.add_assoc]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [il r l n8 n15, hl r l n8 n9 n10 n11 n14 n15]

/-! ## What survives the steps -/

/-- `buf[128, 320)`: the constants, never written after the prologue. -/
abbrev hiR (buf : Addr) : Region := ⟨buf + BitVec.ofNat 64 128, 192⟩

theorem hiR_contains (buf : Addr) {d n : Nat} (h₁ : 128 ≤ d) (h₂ : d + n ≤ 320) :
    (hiR buf).Contains (buf + BitVec.ofNat 64 d) n := by
  simp only [Region.Contains]
  rw [show buf + BitVec.ofNat 64 d - (buf + BitVec.ofNat 64 128) = BitVec.ofNat 64 (d - 128) by
    bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem hiR_sub (buf : Addr) : Region.Sub (hiR buf) (bufR buf) := by
  intro x hx; simp only [Region.Contains] at *; bv_omega

theorem slotsR_sub (buf : Addr) : Region.Sub (slotsR buf) (bufR buf) := Region.sub_prefix (by omega)

theorem hiR_slots (buf : Addr) : (hiR buf).Disjoint (slotsR buf) := by
  intro x h₁ h₂; simp only [Region.Contains] at *; bv_omega

theorem slots_contains (buf : Addr) {d n : Nat} (h : d + n ≤ 128) :
    (slotsR buf).Contains (buf + BitVec.ofNat 64 d) n := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat buf (by omega)]; exact h

theorem st_contains (st : Addr) {d n : Nat} (h : d + n ≤ 64) :
    (stR st).Contains (st + BitVec.ofNat 64 d) n := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat st (by omega)]; exact h

theorem rowS_frame {rs : List Region} {m m' : Mem} {st : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (stR st).Disjoint r) (row : Nat) : RowS row (stateAt m st) m' st := fun hrow => by
  have e : m'.readW (st + BitVec.ofNat 64 (16 * row)) 128 = m.readW (st + BitVec.ofNat 64 (16 * row)) 128 :=
    hf.readW (st_contains st (by omega)) hd (by decide)
  rw [e]; exact rowS_of m st row hrow

theorem slots_frame {rs : List Region} {m m' : Mem} {buf : Addr} {vs : Nat → CState}
    (h : Slots buf vs m) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotsR buf).Disjoint r) :
    Slots buf vs m' := fun r l q hr hl hq => by
  rw [hf.readW (slots_contains buf (by simp only [slotOff]; omega)) hd (by decide)]
  exact h r l q hr hl hq

/-- The counter increments in `buf[192, 224)`. -/
def Incs (buf : Addr) (m : Mem) : Prop :=
  ∀ l q, l < 2 → q < 4 →
    m.readW (buf + BitVec.ofNat 64 (192 + (16 * l + 4 * q))) 32 = BitVec.ofNat 32 (4 * l + q)

theorem incs_frame {rs : List Region} {m m' : Mem} {buf : Addr} (h : Incs buf m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (hiR buf).Disjoint r) : Incs buf m' := fun l q hl hq => by
  rw [hf.readW (hiR_contains buf (by omega) (by omega)) hd (by decide)]
  exact h l q hl hq

theorem RowIn.lanes {row : Nat} {x0 x1 x2 x3 : XReg} {B : Nat → CState} {s s' : State}
    (h : RowIn row x0 x1 x2 x3 B s) (e0 : ∀ l, s'.lane x0 l = s.lane x0 l)
    (e1 : ∀ l, s'.lane x1 l = s.lane x1 l) (e2 : ∀ l, s'.lane x2 l = s.lane x2 l)
    (e3 : ∀ l, s'.lane x3 l = s.lane x3 l) : RowIn row x0 x1 x2 x3 B s' := fun l q hl hq hrow => by
  simp only [vw, e0, e1, e2, e3]; exact h l q hl hq hrow

theorem holds_reg {buf : Addr} {vs : Nat → CState} {s : State} (h : Holds buf false vs s) {k : Nat}
    (hk : k < 16) (hk' : k < 8 ∨ 12 ≤ k) {l q : Nat} (hl : l < 2) (hq : q < 4) :
    vw s (vreg k) l q = (vs (4 * l + q))[k] := by
  have e := h k hk l q hl hq
  rwa [inReg_other _ hk', ite_eq_left rfl] at e

theorem holds_rows {buf : Addr} {vs : Nat → CState} {s : State} (h : Holds buf false vs s) :
    RowIn 0 .xmm0 .xmm1 .xmm2 .xmm3 vs s ∧ RowIn 1 .xmm4 .xmm5 .xmm6 .xmm7 vs s ∧
    RowIn 3 .xmm8 .xmm9 .xmm10 .xmm11 vs s :=
  ⟨fun _ _ hl hq _ => ⟨holds_reg h (k := 0) (by decide) (by decide) hl hq,
      holds_reg h (k := 1) (by decide) (by decide) hl hq, holds_reg h (k := 2) (by decide) (by decide) hl hq,
      holds_reg h (k := 3) (by decide) (by decide) hl hq⟩,
    fun _ _ hl hq _ => ⟨holds_reg h (k := 4) (by decide) (by decide) hl hq,
      holds_reg h (k := 5) (by decide) (by decide) hl hq, holds_reg h (k := 6) (by decide) (by decide) hl hq,
      holds_reg h (k := 7) (by decide) (by decide) hl hq⟩,
    fun _ _ hl hq _ => ⟨holds_reg h (k := 12) (by decide) (by decide) hl hq,
      holds_reg h (k := 13) (by decide) (by decide) hl hq,
      holds_reg h (k := 14) (by decide) (by decide) hl hq,
      holds_reg h (k := 15) (by decide) (by decide) hl hq⟩⟩

/-! ## The whole output -/

theorem finish_eq : finish =
    store89 ++ (addRow 0 ([.xmm0, .xmm1, .xmm2, .xmm3] : List XReg) ++
    ((transpose .xmm0 .xmm1 .xmm2 .xmm3 ++ xorRow 0 ([.xmm0, .xmm1, .xmm2, .xmm3] : List XReg)) ++
    (addRow 1 ([.xmm4, .xmm5, .xmm6, .xmm7] : List XReg) ++
    ((transpose .xmm4 .xmm5 .xmm6 .xmm7 ++ xorRow 1 ([.xmm4, .xmm5, .xmm6, .xmm7] : List XReg)) ++
    ((addRow 3 ([.xmm8, .xmm9, .xmm10, .xmm11] : List XReg) ++ incAdd) ++
    ((transpose .xmm8 .xmm9 .xmm10 .xmm11 ++
      xorRow 3 ([.xmm8, .xmm9, .xmm10, .xmm11] : List XReg)) ++
    (load4 ++ (addRow 2 ([.xmm0, .xmm1, .xmm2, .xmm3] : List XReg) ++
    (transpose .xmm0 .xmm1 .xmm2 .xmm3 ++
      xorRow 2 ([.xmm0, .xmm1, .xmm2, .xmm3] : List XReg)))))))))) := by
  simp only [finish, store89, load4, incAdd, List.append_assoc, List.cons_append, List.nil_append]

theorem finish_ok {st buf a : Addr} {vs : Nat → CState} {s : State} (hh : Holds buf false vs s)
    (hrdi : s.gpr .rdi = st) (hrcx : s.gpr .rcx = buf) (hrsi : s.gpr .rsi = a)
    (hwst : stR st ∈ s.wr) (hwb : bufR buf ∈ s.wr) (hwd : DWin s.wr a) (hinc : Incs buf s.mem)
    (dsd : (stR st).Disjoint (dR5 a)) (dsb : (stR st).Disjoint (bufR buf))
    (dbd : (bufR buf).Disjoint (dR5 a)) :
    WP isa (.block finish) s fun s' =>
      (∀ k < 512, s'.mem (a + BitVec.ofNat 64 k) = s.mem (a + BitVec.ofNat 64 k) ^^^
        (serialize (plus vs (stateAt s.mem st) (k / 64))).getD (k % 64) 0) ∧
      Frame [slotsR buf, dR5 a] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have sdd : ∀ r ∈ [slotsR buf, dR5 a], (stR st).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dsb.sub_right (slotsR_sub buf)
    · exact dsd
  have hdd : ∀ r ∈ [slotsR buf, dR5 a], (hiR buf).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hiR_slots buf
    · exact dbd.sub_left (hiR_sub buf)
  have ssd : ∀ r ∈ [dR5 a], (slotsR buf).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact dbd.sub_left (slotsR_sub buf)
  have sub₁ : ∀ r ∈ [slotsR buf], r ∈ [slotsR buf, dR5 a] := by simp
  have sub₂ : ∀ r ∈ [dR5 a], r ∈ [slotsR buf, dR5 a] := by simp
  have rdst : ∀ (t : State), t.gpr = s.gpr → t.rd = s.rd → t.wr = s.wr → ∀ row, row < 4 →
      InRegions (t.rd ++ t.wr) (t.gpr .rdi + BitVec.ofNat 64 (16 * row)) 16 := by
    intro t g r w row hrow
    rw [g, r, w, hrdi]; exact ⟨stR st, List.mem_append_right _ hwst, st_contains st (by omega)⟩
  obtain ⟨r0, r1, r3⟩ := holds_rows hh
  rw [finish_eq]
  -- Words 8 and 9 to their slots.
  refine WP.block_append (WP.mono (store89_ok hh hrcx hwb) fun s₁ ⟨sl₁, l₁, f₁, g₁, rd₁, wr₁⟩ => ?_)
  have G₁ := f₁.mono sub₁
  -- Row 0.
  refine WP.block_append (WP.mono (addRow_in (row := 0) (S := stateAt s.mem st) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (r0.lanes (l₁ _) (l₁ _) (l₁ _) (l₁ _)) (by rw [g₁, hrdi]; exact rowS_frame G₁ sdd 0)
    (rdst s₁ g₁ rd₁ wr₁ 0 (by decide))) fun s₂ ⟨a₂, l₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.block_append (WP.mono (rowOut_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a₂ (a := a) (by rw [g₂, g₁, hrsi])
    (by rw [wr₂, wr₁]; exact hwd)) fun s₃ ⟨d₃, f₃, l₃, g₃, rd₃, wr₃⟩ => ?_)
  rw [m₂] at f₃ d₃
  have G₃ := G₁.trans (f₃.mono sub₂)
  -- Row 1.
  refine WP.block_append (WP.mono (addRow_in (row := 1) (S := stateAt s.mem st) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (r1.lanes (fun l => by simp (disch := decide) only [l₃, l₂, l₁])
      (fun l => by simp (disch := decide) only [l₃, l₂, l₁])
      (fun l => by simp (disch := decide) only [l₃, l₂, l₁])
      (fun l => by simp (disch := decide) only [l₃, l₂, l₁]))
    (by rw [g₃, g₂, g₁, hrdi]; exact rowS_frame G₃ sdd 1)
    (rdst s₃ (by rw [g₃, g₂, g₁]) (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁]) 1 (by decide)))
    fun s₄ ⟨a₄, l₄, g₄, m₄, rd₄, wr₄⟩ => ?_)
  refine WP.block_append (WP.mono (rowOut_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a₄ (a := a)
    (by rw [g₄, g₃, g₂, g₁, hrsi]) (by rw [wr₄, wr₃, wr₂, wr₁]; exact hwd))
    fun s₅ ⟨d₅, f₅, l₅, g₅, rd₅, wr₅⟩ => ?_)
  rw [m₄] at f₅ d₅
  have G₅ := G₃.trans (f₅.mono sub₂)
  -- Row 3, with the counters.
  refine WP.block_append (WP.mono (addRow3_in (buf := buf) (S := stateAt s.mem st)
    (r3.lanes (fun l => by simp (disch := decide) only [l₅, l₄, l₃, l₂, l₁])
      (fun l => by simp (disch := decide) only [l₅, l₄, l₃, l₂, l₁])
      (fun l => by simp (disch := decide) only [l₅, l₄, l₃, l₂, l₁])
      (fun l => by simp (disch := decide) only [l₅, l₄, l₃, l₂, l₁]))
    (by rw [g₅, g₄, g₃, g₂, g₁, hrdi]; exact rowS_frame G₅ sdd 3)
    (rdst s₅ (by rw [g₅, g₄, g₃, g₂, g₁]) (by rw [rd₅, rd₄, rd₃, rd₂, rd₁])
      (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]) 3 (by decide))
    (by rw [g₅, g₄, g₃, g₂, g₁, hrcx]) (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact hwb)
    (incs_frame hinc G₅ hdd)) fun s₆ ⟨a₆, l₆, g₆, m₆, rd₆, wr₆⟩ => ?_)
  refine WP.block_append (WP.mono (rowOut_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a₆ (a := a)
    (by rw [g₆, g₅, g₄, g₃, g₂, g₁, hrsi]) (by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hwd))
    fun s₇ ⟨d₇, f₇, l₇, g₇, rd₇, wr₇⟩ => ?_)
  rw [m₆] at f₇ d₇
  have G₇ := G₅.trans (f₇.mono sub₂)
  have H₇ : Frame [dR5 a] s₁.mem s₇.mem := (f₃.trans f₅).trans f₇
  -- Row 2, from the slots.
  refine WP.block_append (WP.mono (load4_ok (slots_frame sl₁ H₇ ssd)
    (by rw [g₇, g₆, g₅, g₄, g₃, g₂, g₁, hrcx]) (by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hwb))
    fun s₈ ⟨a₈, l₈, g₈, m₈, rd₈, wr₈⟩ => ?_)
  refine WP.block_append (WP.mono (addRow_in (row := 2) (S := stateAt s.mem st) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a₈
    (by rw [g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁, hrdi, m₈]; exact rowS_frame G₇ sdd 2)
    (rdst s₈ (by rw [g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁]) (by rw [rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁])
      (by rw [wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]) 2 (by decide)))
    fun s₉ ⟨a₉, l₉, g₉, m₉, rd₉, wr₉⟩ => ?_)
  refine WP.mono (rowOut_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a₉ (a := a)
    (by rw [g₉, g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁, hrsi])
    (by rw [wr₉, wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hwd))
    fun s₁₀ ⟨d₁₀, f₁₀, _, g₁₀, rd₁₀, wr₁₀⟩ => ?_
  rw [m₉, m₈] at f₁₀ d₁₀
  refine ⟨fun k hk => ?_, G₇.trans (f₁₀.mono sub₂), by rw [g₁₀, g₉, g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁],
    by rw [rd₁₀, rd₉, rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₁₀, wr₉, wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  have e₁ : s₁.mem (a + BitVec.ofNat 64 k) = s.mem (a + BitVec.ofNat 64 k) :=
    f₁.bytes (R := dR5 a) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact (dbd.sub_left (slotsR_sub buf)).symm) (show 512 ≤ 2 ^ 64 by decide) hk
  rw [d₁₀ k hk, d₇ k hk, d₅ k hk, d₃ k hk, e₁]
  rcases (by omega : k % 64 / 16 = 0 ∨ k % 64 / 16 = 1 ∨ k % 64 / 16 = 2 ∨ k % 64 / 16 = 3)
    with h | h | h | h <;> simp only [h, Nat.reduceEqDiff, ite_true, ite_false]

end VG.Proof.ChaCha20.X86_64.Avx2
