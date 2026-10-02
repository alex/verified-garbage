import VerifiedGarbage.Proof.X448.X86_64.Decode
import VerifiedGarbage.Proof.X448.X86_64.Swap

/-!
# X448 on x86-64: storing decoded limb pairs

Each seven-byte chunk is split into two limbs and stored into both copies of
the input coordinate.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

def storePair (i : Nat) : List Instr :=
  [.mov .r8 (.reg .rax), .alu .and .r8 (.imm mask28),
    .store (sc (X1 + 16 * i)) .r8, .store (sc (X3 + 16 * i)) .r8,
    .shift .shr .rax 28, .store (sc (X1 + 16 * i + 8)) .rax,
    .store (sc (X3 + 16 * i + 8)) .rax]

def pairMem (m : Mem) (base : Addr) (i v : Nat) : Mem :=
  (((m.writeW (off base (X1 + 16 * i)) (BitVec.ofNat 64 (v % radix))).writeW
    (off base (X3 + 16 * i)) (BitVec.ofNat 64 (v % radix))).writeW
    (off base (X1 + 16 * i + 8)) (BitVec.ofNat 64 (v / radix))).writeW
    (off base (X3 + 16 * i + 8)) (BitVec.ofNat 64 (v / radix))

theorem storePair_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 8) :
    WP isa (.block (storePair i)) s fun t =>
      t.mem = pairMem s.mem base i (s.gpr .rax).toNat ∧ Keeps [.rax, .r8] s t := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 := fun _ hd => hs.write hd
  have low : s.gpr .rax &&& mask28.signExtend 64 = BitVec.ofNat 64 ((s.gpr .rax).toNat % radix) := by
    apply BitVec.eq_of_toNat_eq
    rw [and28, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide : radix < 2 ^ 64))]
  have high : s.gpr .rax >>> 28 = BitVec.ofNat 64 ((s.gpr .rax).toNat / radix) := by
    apply BitVec.eq_of_toNat_eq
    rw [shr28, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (s.gpr .rax).isLt)]
  apply WP.of_runBlock
  simp only [storePair, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execShift,
    ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.gpr_setFlags, RegUpd.wr_setFlags,
    RegUpd.mem_setFlags, State.store64, hs.rdi,
    w (X1 + 16 * i) (by simp only [X1, slot]; omega),
    w (X3 + 16 * i) (by simp only [X3, slot]; omega),
    w (X1 + 16 * i + 8) (by simp only [X1, slot]; omega),
    w (X3 + 16 * i + 8) (by simp only [X3, slot]; omega),
    Nat.reduceLeDiff, and_self, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [low, high]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]

theorem pairMem_limbs (m : Mem) (base : Addr) {i j v : Nat} (hi : i < 8) (hj : j < 16)
    (hv : v < radix * radix) :
    limbs (pairMem m base i v) base X1 j =
      (if j = 2 * i + 1 then v / radix else if j = 2 * i then v % radix else limbs m base X1 j) ∧
    limbs (pairMem m base i v) base X3 j =
      (if j = 2 * i + 1 then v / radix else if j = 2 * i then v % radix else limbs m base X3 j) := by
  have lo : (BitVec.ofNat 64 (v % radix)).toNat = v % radix := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide : radix < 2 ^ 64))]
  have high : (BitVec.ofNat 64 (v / radix)).toNat = v / radix := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans ((Nat.div_lt_iff_lt_mul (by decide)).mpr hv)
      (by decide : radix < 2 ^ 64))]
  let m₁ := (m.writeW (off base (X1 + 8 * (2 * i))) (BitVec.ofNat 64 (v % radix))).writeW
    (off base (X3 + 8 * (2 * i))) (BitVec.ofNat 64 (v % radix))
  have p₁ := pair_write (m := m) (base := base) (x := X1) (y := X3) (n := 2 * i)
    (by decide) (by decide) (by decide) (by omega) hj (BitVec.ofNat 64 (v % radix)) (BitVec.ofNat 64 (v % radix))
  have p₂ := pair_write (m := m₁) (base := base) (x := X1) (y := X3) (n := 2 * i + 1)
    (by decide) (by decide) (by decide) (by omega) hj (BitVec.ofNat 64 (v / radix)) (BitVec.ofNat 64 (v / radix))
  have index0 : 8 * (2 * i) = 16 * i := by omega
  have index1 : 8 * (2 * i + 1) = 16 * i + 8 := by omega
  simp only [m₁, index0, index1, ← Nat.add_assoc, lo, high] at p₁ p₂
  rw [p₁.1, p₁.2] at p₂
  exact p₂

theorem pairMem_outside (m : Mem) (base : Addr) {i : Nat} (hi : i < 8) (v : Nat) :
    Outside2 base X1 (16 * (i + 1)) X3 (16 * (i + 1)) m (pairMem m base i v) := by
  intro p hx hy
  simp only [pairMem]
  have x0 : X1 + 16 * i + 8 ≤ 8192 := by simp only [X1, slot]; omega
  have x1 : X1 + 16 * i + 8 + 8 ≤ 8192 := by simp only [X1, slot]; omega
  have y0 : X3 + 16 * i + 8 ≤ 8192 := by simp only [X3, slot]; omega
  have y1 : X3 + 16 * i + 8 + 8 ≤ 8192 := by simp only [X3, slot]; omega
  rw [writeW_outside _ _ _ y1 p (by omega), writeW_outside _ _ _ x1 p (by omega),
    writeW_outside _ _ _ y0 p (by omega), writeW_outside _ _ _ x0 p (by omega)]

theorem decodePair_ok {s : State} {base p : Addr} (hs : Scr s base) {i : Nat} (hi : i < 8)
    (hp : s.gpr .r10 = p) (hr : ∀ j < 7, InRegions (s.rd ++ s.wr) (off p (7 * i + j)) 1) :
    WP isa (.block (decodePair i)) s fun t =>
      t.mem = pairMem s.mem base i (chunk s.mem p i) ∧ Keeps [.rax, .rdx, .r8, .r9] s t := by
  change WP isa (.block (readSeven i ++ storePair i)) s _
  rw [WP.block_append_iff]
  refine WP.mono (readSeven_ok hp hr) fun t ⟨tv, tm, tk⟩ => ?_
  refine WP.mono (storePair_ok (hs.of_keeps tk (by decide)) hi) fun u ⟨um, uk⟩ => ?_
  refine ⟨?_, tk.trans (uk.mono ?_)⟩
  · rw [um, tv, tm]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide

end VG.Proof.X448.X86_64
