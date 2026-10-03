import VerifiedGarbage.Proof.Ed448.X86_64.ScalarMain
import VerifiedGarbage.Proof.X448.X86_64.Field

/-!
# Ed448 scalar multiply-add on x86-64

`vg_ed448_scalar_mul_add` reduces `k`, `s` and `r` (57 bytes each) modulo
`L` with the loop of `vg_ed448_scalar_reduce`, multiplies the first two
with X448's product scanning (`columns`) into `ACC`, reduces the product's
fourteen words with the same loop, adds the third and reduces once more.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Keeps Scr rv mv wv word off Outside ofs Saved saved_lt writeW_outside
  word_writeW_self contains_sc)
open VG.Impl.X448.X86_64 (W w sc at_ saved loads stores chain)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-- `reduce57`: the remainder of the 57 bytes at `rsi`, a buffer outside the
working space. -/
theorem reduce57_ok {s : State} {base : Addr} (hs : Scr s base)
    (hK : mv s.mem base KC 7 = wv kWords)
    (hR : (⟨s.gpr .rsi, 57⟩ : Region) ∈ s.rd ++ s.wr)
    (hfar : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rsi + BitVec.ofNat 64 i)) :
    WP isa reduce57 s fun t =>
      rem t = decodeLE (bytesAt s.mem (s.gpr .rsi) 57) % L ∧
      (∀ r, r ∉ bodyClob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base TMP 56 s.mem t.mem := by
  rw [reduce57]
  apply WP.seq
  refine WP.mono (init57_ok s ⟨_, hR, Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₁ ⟨v₁, b₁, k₁⟩ => ?_
  have hs₁ : Scr s₁ base := hs.of_keeps k₁ (by decide)
  have rsi₁ : s₁.gpr .rsi = s.gpr .rsi := k₁.1 _ (by decide)
  have v₁' : rem s₁ = decodeLE (bytesAt s₁.mem (s₁.gpr .rsi + BitVec.ofNat 64 (8 * 7))
      (57 - 8 * 7)) % L := by
    rw [v₁, k₁.2.1, rsi₁]
    refine (Nat.mod_eq_of_lt ?_).symm
    have := decodeLE_lt' (bytesAt s.mem (s.gpr .rsi + BitVec.ofNat 64 56) 1)
    rw [bytesAt_length] at this
    have : 256 < L := by decide +kernel
    omega
  refine WP.mono (scalarLoop_ok hs₁ (by rw [k₁.2.1]; exact hK) (len := 57) (n₀ := 7)
    (by decide) (by decide) ⟨by decide, b₁, v₁', fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩
    (fun k hk => by
      rw [rsi₁, k₁.2.2.1, k₁.2.2.2]
      exact ⟨_, hR, Offset.contains_base _ (d := 8 * k) (n := 8) (k := 57) (by omega) (by omega)⟩)
    (fun i hi => Or.inr (by rw [rsi₁]; have := hfar i hi; simp only [TMP]; omega)))
    fun t ⟨vt, gt, rdt, wrt, ot⟩ => ?_
  refine ⟨by rw [vt, rsi₁, k₁.2.1], fun r hr => ?_, by rw [rdt, k₁.2.2.1], by rw [wrt, k₁.2.2.2],
    by rw [← k₁.2.1]; exact ot⟩
  have sub : ∀ x ∈ Reg.rbx :: W, x ∈ bodyClob := by decide
  rw [gt r hr, k₁.1 r (fun h => hr (sub r h))]

open VG.Proof.X448.X86_64 (colX acc columns_ok mulCol_hc mulCol_hw mulCols_sum mv7 rvW val7
  zeroAcc_ok w_colX rdi_colX stable_sc loads_ok W_nodup W_len prod_lt)
/-- The product of `[SK]` and `[SS]` (each below `L`) into the fourteen words
at `ACC`. -/
theorem product_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block product) s fun t => mv t.mem base Impl.X448.X86_64.ACC 14 = mv s.mem base SK 7 * mv s.mem base SS 7 ∧
        (∀ r, r ∉ W ++ colX → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        Outside base Impl.X448.X86_64.ACC 112 s.mem t.mem := by
  rw [product, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_ok hs SS W W_nodup (by decide) (by rw [W_len]; decide))
    fun s1 ⟨w1, v1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zeroAcc_ok s1) fun s2 ⟨z2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  have m2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  refine WP.mono (columns_ok hs2 (fun i => .mem (sc (SK + 8 * i)))
    w (fun i => word s2.mem base (SK + 8 * i)) Impl.X448.X86_64.mulCol
    (fun s' g _ wr out i hi => by
      have hsS : Scr s' base := ⟨(g _ rdi_colX).trans hs2.rdi, wr ▸ hs2.wr, hs2.nowrap⟩
      have := stable_sc hsS rdi_colX (d := SK + 8 * i) (by simp only [SK]; omega)
      rwa [out.word (by simp only [Impl.X448.X86_64.ACC, SK]; omega)
        (by simp only [SK]; omega)] at this)
    w_colX mulCol_hc mulCol_hw z2 (7 + 7) (Nat.le_refl _)) fun t ⟨gt, rdt, wrt, ot, et, _⟩ => ?_
  have hx : val7 (fun i => (word s2.mem base (SK + 8 * i)).toNat) = mv s.mem base SK 7 := by
    rw [m2, mv7]
  have hy : val7 (fun j => (s2.gpr (w j)).toNat) = mv s.mem base SS 7 := by
    rw [← rvW, show rv s2 W = rv s1 W from k2.rv_eq (by decide), v1, W_len]
  rw [mulCols_sum, hx, hy] at et
  have l1 := Proof.X448.X86_64.mv_lt s.mem base SK 7
  have l2 := Proof.X448.X86_64.mv_lt s.mem base SS 7
  have hl := prod_lt l1 l2
  have h0 : rv t (acc (7 + 7)) = 0 := by
    rcases Nat.eq_zero_or_pos (rv t (acc (7 + 7))) with h | h
    · exact h
    · exfalso
      have := Nat.mul_le_mul_left (2 ^ (64 * (7 + 7))) h
      generalize 2 ^ (64 * (7 + 7)) = Q at *
      omega
  have e2 : mv t.mem base Impl.X448.X86_64.ACC (7 + 7) =
      mv s.mem base SK 7 * mv s.mem base SS 7 := by
    rw [h0] at et
    generalize 2 ^ (64 * (7 + 7)) = Q at et
    generalize mv t.mem base Impl.X448.X86_64.ACC (7 + 7) = A at et ⊢
    omega
  refine ⟨e2, fun r hr => ?_, rdt.trans (k2.2.2.1.trans k1.2.2.1),
    wrt.trans (k2.2.2.2.trans k1.2.2.2), by rw [← m2]; exact ot⟩
  simp only [List.mem_append, not_or] at hr
  have sub : ∀ x ∈ [Reg.r15, .rcx, .rbp], x ∈ colX := by decide
  rw [gt r hr.2, k2.1 r (fun h => hr.2 (sub r h)), k1.1 r hr.1]

theorem word_ww {m : Mem} {base : Addr} {d e : Nat} (v : BitVec 64) (h : e + 8 ≤ d ∨ d + 8 ≤ e)
    (hd : d + 8 < 2 ^ 64) (he : e + 8 < 2 ^ 64) :
    word (m.writeW (off base d) v) base e = word m base e :=
  (writeW_outside m base v hd).word h he

/-- The arguments to `[r8 + OUT]` … `[r8 + ARG_S]`, and `r8` into `rdi`. -/
theorem args_ok {s : State} {base : Addr} (hb : s.gpr .r8 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block saveArgs) s fun t =>
      word t.mem base OUT = s.gpr .rdi ∧ word t.mem base ARG_R = s.gpr .rsi ∧
      word t.mem base ARG_K = s.gpr .rdx ∧ word t.mem base ARG_S = s.gpr .rcx ∧
      Outside base OUT 32 s.mem t.mem ∧ t.gpr .rdi = base ∧
      (∀ r, r ≠ .rdi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hw, contains_sc hd⟩
  apply WP.of_runBlock
  simp only [saveArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, ea_at, hb, State.store64,
    w OUT (by decide), w ARG_R (by decide), w ARG_K (by decide), w ARG_S (by decide), ite_true,
    RegUpd.gpr_setReg_self, RegUpd.mem_setReg, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial, fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr], rfl, rfl⟩
  · rw [word_ww _ (by decide) (by decide) (by decide), word_ww _ (by decide) (by decide) (by decide),
      word_ww _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [word_ww _ (by decide) (by decide) (by decide), word_ww _ (by decide) (by decide) (by decide),
      word_writeW_self]
  · rw [word_ww _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [word_writeW_self]
  · exact (((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide))).trans
      (((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)))

/-- `rsi` from a word of the working space. -/
theorem loadRsi_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 8192) :
    WP isa (.block ([.mov .rsi (.mem (sc d))] : List Instr)) s fun t =>
      t.gpr .rsi = word s.mem base d ∧ Keeps [.rsi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    Proof.X448.X86_64.readSrc_sc hs hd, Option.map_some, RegUpd.gpr_setReg_self,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `r8–r14 += [SR]`, for a sum below `2^448`. -/
theorem addSR_ok {s : State} {base : Addr} (hs : Scr s base)
    (hlt : rem s + mv s.mem base SR 7 < 2 * L) :
    WP isa (.block (chain .add .adc W ((List.range 7).map fun i => .mem (sc (SR + 8 * i))))) s
      fun t => rem t = rem s + mv s.mem base SR 7 ∧ Keeps W s t := by
  have hc : chain .add .adc W ((List.range 7).map fun i => .mem (sc (SR + 8 * i))) =
      chain .add .adc (.r8 :: [.r9, .r10, .r11, .r12, .r13, .r14]) (.mem (sc 384) ::
        ([392, 400, 408, 416, 424, 432] : List Nat).map fun d => .mem (sc d)) := rfl
  rw [hc]
  refine WP.mono (Proof.X448.X86_64.add_chain_ok W s .r8 [.r9, .r10, .r11, .r12, .r13, .r14]
    (.mem (sc 384)) _ (word s.mem base 384)
    (([392, 400, 408, 416, 424, 432] : List Nat).map fun d => word s.mem base d)
    (fun _ h => h) W_nodup rfl (stable_sc hs (by decide) (by decide))
    (Proof.X448.X86_64.stable_scs hs (by decide) _ (by decide))) fun t ⟨c, _, et, kt⟩ => ?_
  have hv : wv (word s.mem base 384 :: ([392, 400, 408, 416, 424, 432] : List Nat).map
      fun d => word s.mem base d) = mv s.mem base SR 7 := rfl
  rw [hv, len7] at et
  refine ⟨?_, kt⟩
  have h2 : 2 * L < 2 ^ 448 := by decide +kernel
  have hc := Bool.toNat_le c
  show rv t (Reg.r8 :: [.r9, .r10, .r11, .r12, .r13, .r14]) =
    rv s (Reg.r8 :: [.r9, .r10, .r11, .r12, .r13, .r14]) + mv s.mem base SR 7
  change rv s (Reg.r8 :: [.r9, .r10, .r11, .r12, .r13, .r14]) + _ < _ at hlt
  generalize (2 : Nat) ^ 448 = M at et h2
  rcases Nat.lt_or_ge c.toNat 1 with h | h
  · have : c.toNat = 0 := by omega
    rw [this, Nat.mul_zero, Nat.add_zero] at et; exact et
  · have : M ≤ M * c.toNat := Nat.le_mul_of_pos_right _ h
    omega

/-- The loop over the product's words: `rsi = rdi + ACC`, a zero remainder and
`rbx = 112`. -/
theorem accInit_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block accInit) s fun t =>
      t.gpr .rsi = base + BitVec.ofNat 64 Impl.X448.X86_64.ACC ∧ rem t = 0 ∧
      t.gpr .rbx = BitVec.ofNat 64 112 ∧ Keeps (.rsi :: .rbx :: W) s t := by
  apply WP.of_runBlock
  simp only [accInit, zeroHigh, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, State.setReg32,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
      hs.rdi]
    rfl
  · simp only [rem, rv, W, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, ite_false,
      reduceCtorEq]
    rfl
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    rfl
  · simp only [W, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2,
      ite_false]

end VG.Proof.Ed448.X86_64
