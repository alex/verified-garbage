import VerifiedGarbage.Proof.X448.X86_64.Comba

/-!
# X448 on x86-64: the reduction of a product

`reduce o` takes the fourteen words `L + 2⁴⁴⁸ H` of a product at `ACC` to a
seven-word number congruent to it modulo `p` at `[o]`: `L + H`, plus
`H - H mod 2²²⁴`, plus `rot(H)` (`H` rotated by 224 bits), whose top word is
folded twice (`fold2`). `reduce_arith` is the congruence, as arithmetic.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64
open VG.Spec.X448 (P)

/-- `2⁴⁴⁸ H ≡ H + (H - H mod 2²²⁴) + rot(H)`, for `H`'s words `h₀, …, h₆`
and `h₃ = lo + 2³² hi` (`rax = h₃ - lo`). -/
theorem reduce_arith (L h0 h1 h2 h3 h4 h5 h6 lo hi rax : Nat) (hlo : lo + 2 ^ 32 * hi = h3)
    (hrax : rax + lo = h3) :
    (L + 2 ^ 448 * (h0 + 2 ^ 64 * (h1 + 2 ^ 64 * (h2 + 2 ^ 64 * (h3 + 2 ^ 64 * (h4 + 2 ^ 64 *
      (h5 + 2 ^ 64 * h6))))))) % P =
    (L + (h0 + 2 ^ 64 * (h1 + 2 ^ 64 * (h2 + 2 ^ 64 * (h3 + 2 ^ 64 * (h4 + 2 ^ 64 *
      (h5 + 2 ^ 64 * h6)))))) + 2 ^ 192 * rax + 2 ^ 256 * h4 + 2 ^ 320 * h5 + 2 ^ 384 * h6 + hi +
      2 ^ 32 * (h4 + 2 ^ 64 * (h5 + 2 ^ 64 * (h6 + 2 ^ 64 * (h0 + 2 ^ 64 * (h1 + 2 ^ 64 *
        (h2 + 2 ^ 64 * lo))))))) % P := by
  generalize hH : h0 + 2 ^ 64 * (h1 + 2 ^ 64 * (h2 + 2 ^ 64 * (h3 + 2 ^ 64 * (h4 + 2 ^ 64 *
      (h5 + 2 ^ 64 * h6))))) = H
  have hP := P_eq
  have e1 : 2 ^ 448 * H = P * H + (2 ^ 224 + 1) * H := by rw [hP, Nat.add_mul]
  generalize hK : hi + 2 ^ 32 * h4 + 2 ^ 96 * h5 + 2 ^ 160 * h6 = K
  have e2 : 2 ^ 448 * K = P * K + (2 ^ 224 + 1) * K := by rw [hP, Nat.add_mul]
  have e : L + 2 ^ 448 * H = (L + H + 2 ^ 192 * rax + 2 ^ 256 * h4 + 2 ^ 320 * h5 +
      2 ^ 384 * h6 + hi + 2 ^ 32 * (h4 + 2 ^ 64 * (h5 + 2 ^ 64 * (h6 + 2 ^ 64 * (h0 + 2 ^ 64 *
        (h1 + 2 ^ 64 * (h2 + 2 ^ 64 * lo))))))) + P * (H + K) := by
    rw [Nat.mul_add P H K]
    generalize P * H = PH at e1 ⊢
    generalize P * K = PK at e2 ⊢
    clear hP
    omega
  rw [e, Nat.add_mul_mod_self_left]

/-! ## The blocks of `reduce` -/

theorem mov32_ok (s : State) (r : Reg) (v : BitVec 32) :
    WP isa (.block [.mov32 r (.imm v)]) s fun s' => s'.gpr r = v.setWidth 64 ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r' hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [RegUpd.gpr_setReg_of_ne _ _ hr]

theorem toNat_setWidth32 (x : BitVec 64) : ((x.setWidth 32).setWidth 64).toNat = x.toNat % 2 ^ 32 := by
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

theorem toNat_setWidth_32_64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (by decide))

/-- `r = [d]`, split into its low half `t` and the rest `r`. -/
theorem splitLo_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 8192)
    {r t : Reg} (hrt : r ≠ t) :
    WP isa (.block [.mov r (.mem (sc d)), .mov32 t (.reg r), .alu .sub r (.reg t)]) s fun s' =>
      (s'.gpr t).toNat = (word s.mem base d).toNat % 2 ^ 32 ∧
      (s'.gpr r).toNat + (s'.gpr t).toNat = (word s.mem base d).toNat ∧
      Keeps [r, t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    load_sc hs hd, Option.map_some, Option.bind_some, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ hrt, State.setReg32, Option.some.injEq, exists_eq_left']
  have hx := toNat_setWidth32 (word s.mem base d)
  refine ⟨?_, ?_, fun r' hr => ?_, rfl, rfl, rfl⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hrt), RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_self, hx]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hrt), RegUpd.gpr_arithFlags,
      RegUpd.gpr_setReg_self, hx]
    have := sub_borrow (word s.mem base d) ((word s.mem base d).setWidth 32 |>.setWidth 64)
    rw [hx] at this
    have : ¬(word s.mem base d).toNat < (word s.mem base d).toNat % 2 ^ 32 :=
      Nat.not_lt.mpr (Nat.mod_le _ _)
    simp only [this, decide_false, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at *
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr.2,
      RegUpd.gpr_setReg_of_ne _ _ hr.1]

/-- `h₃` split into its low half `rdx` and the rest `rax`. -/
theorem splitH_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block [.mov .rax (.mem (sc (h 10))), .mov32 .rdx (.reg .rax),
      .alu .sub .rax (.reg .rdx)]) s fun s' =>
      (s'.gpr .rdx).toNat = (word s.mem base (h 10)).toNat % 2 ^ 32 ∧
      (s'.gpr .rax).toNat + (s'.gpr .rdx).toNat = (word s.mem base (h 10)).toNat ∧
      Keeps [.rax, .rdx] s s' :=
  splitLo_ok hs (by simp only [h, ACC]; omega) (by decide)

/-- The word 4 bytes into the word at `d`: its high half, and the low half of
the next. -/
theorem word_mid (m : Mem) (base : Addr) (d : Nat) :
    (word m base (d + 4)).toNat =
      (word m base d).toNat / 2 ^ 32 + 2 ^ 32 * ((word m base (d + 8)).toNat % 2 ^ 32) := by
  have e : ∀ e, (word m base e).toNat = X25519.leNum (Spec.X25519.bytesAt m (off base e) 4) +
      2 ^ 32 * X25519.leNum (Spec.X25519.bytesAt m (off base (e + 4)) 4) := fun e => by
    rw [word, ← X25519.leNum_bytesAt_64, show 8 = 4 + 4 from rfl, X25519.bytesAt_add,
      X25519.leNum_append, X25519.length_bytesAt, off, Offset.add_add]
    rfl
  have l : ∀ e, X25519.leNum (Spec.X25519.bytesAt m (off base e) 4) < 2 ^ 32 := fun e => by
    have := X25519.leNum_lt (Spec.X25519.bytesAt m (off base e) 4)
    rwa [X25519.length_bytesAt] at this
  rw [e d, e (d + 4), e (d + 8), show d + 4 + 4 = d + 8 by omega]
  have := l d; have := l (d + 4); have := l (d + 8); have := l (d + 8 + 4)
  omega

/-- The 32-bit word 4 bytes into the word at `d`: its high half. -/
theorem readW32_mid (m : Mem) (base : Addr) (d : Nat) :
    (m.readW (off base (d + 4)) 32).toNat = (word m base d).toNat / 2 ^ 32 := by
  rw [readW32, ← word, word_mid]
  have := (word m base d).isLt
  omega

/-- `rcx += [d]`'s low half, without overflow. -/
theorem addLo_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 8192)
    (hb : (s.gpr .rcx).toNat + (s.mem.readW (off base d) 32).toNat < 2 ^ 64) :
    WP isa (.block [.mov32 .rdx (.mem (sc d)), .alu .add .rcx (.reg .rdx)]) s fun s' =>
      (s'.gpr .rcx).toNat = (s.gpr .rcx).toNat + (s.mem.readW (off base d) 32).toNat ∧
      Keeps [.rcx, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    State.load32, ea_sc, hs.rdi, hs.read (d := d) (n := 4) (by omega), ite_true, Option.map_some,
    Option.bind_some, State.setReg32, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ (by decide : ¬Reg.rcx = Reg.rdx), Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_add, toNat_setWidth_32_64, Nat.mod_eq_of_lt hb]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr.2]

/-- `rot(H)` from its halves: `H`'s words `hⱼ = loⱼ + 2³² hiⱼ`. -/
theorem rot_arith (lo0 lo1 lo2 lo3 lo4 lo5 lo6 hi0 hi1 hi2 hi3 hi4 hi5 hi6 : Nat) :
    (hi3 + 2 ^ 32 * lo4) + 2 ^ 64 * ((hi4 + 2 ^ 32 * lo5) + 2 ^ 64 * ((hi5 + 2 ^ 32 * lo6) +
      2 ^ 64 * ((2 ^ 32 * lo0 + hi6) + 2 ^ 64 * ((hi0 + 2 ^ 32 * lo1) + 2 ^ 64 *
      ((hi1 + 2 ^ 32 * lo2) + 2 ^ 64 * (hi2 + 2 ^ 32 * lo3)))))) =
    hi3 + 2 ^ 32 * ((lo4 + 2 ^ 32 * hi4) + 2 ^ 64 * ((lo5 + 2 ^ 32 * hi5) + 2 ^ 64 *
      ((lo6 + 2 ^ 32 * hi6) + 2 ^ 64 * ((lo0 + 2 ^ 32 * hi0) + 2 ^ 64 * ((lo1 + 2 ^ 32 * hi1) +
      2 ^ 64 * ((lo2 + 2 ^ 32 * hi2) + 2 ^ 64 * lo3)))))) := by
  rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by decide]
  generalize 2 ^ 32 = C
  ring

/-- The registers the field arithmetic uses. -/
def clob : List Reg := [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem rvW_split (s : State) :
    rv s W = rv s [.r8, .r9, .r10] + 2 ^ 192 * rv s [.r11, .r12, .r13, .r14] := by
  simp only [rv, W]; omega

theorem rv5_split (s : State) :
    rv s [.r11, .r12, .r13, .r14, .r15] = rv s [.r11, .r12, .r13, .r14] +
      2 ^ 256 * (s.gpr .r15).toNat := by
  simp only [rv]; omega

theorem len64_1 {α : Type} (a : α) : 64 * [a].length = 64 := rfl
theorem len64_5 {α : Type} (a b c d e : α) : 64 * [a, b, c, d, e].length = 320 := rfl
theorem len64_7 {α : Type} (a b c d e f g : α) : 64 * [a, b, c, d, e, f, g].length = 448 := rfl

theorem mvH (m : Mem) (base : Addr) :
    mv m base (ACC + 56) 7 = (word m base (h 7)).toNat + 2 ^ 64 * ((word m base (h 8)).toNat +
      2 ^ 64 * ((word m base (h 9)).toNat + 2 ^ 64 * ((word m base (h 10)).toNat +
      2 ^ 64 * ((word m base (h 11)).toNat + 2 ^ 64 * ((word m base (h 12)).toNat +
      2 ^ 64 * (word m base (h 13)).toNat))))) := by
  simp only [mv, h, ACC, Nat.reduceAdd, Nat.reduceMul, Nat.mul_zero, Nat.add_zero]

/-- `reduce o`: `[o] ≡ L + 2⁴⁴⁸ H`, for the product `L + 2⁴⁴⁸ H` at `ACC`. -/
theorem reduce_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 56 ≤ ACC) :
    WP isa (.block (reduce o)) s fun s' =>
      fe s'.mem base o % P = (mv s.mem base ACC 7 + 2 ^ 448 * mv s.mem base (ACC + 56) 7) % P ∧
      (∀ r, r ∉ clob → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base o 56 s.mem s'.mem := by
  simp only [reduce, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (mov32_ok s .r15 0) fun s1 ⟨z1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hs1 ACC W W_nodup (by decide) (by decide)) fun s2 ⟨_, v2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  rw [WP.block_append_iff, show (List.range 7).map (fun i => Src.mem (sc (h (7 + i)))) =
    Src.mem (sc (h 7)) :: ([h 8, h 9, h 10, h 11, h 12, h 13].map fun d => Src.mem (sc d)) from rfl]
  refine WP.mono (add_chain_ok W s2 .r8 [.r9, .r10, .r11, .r12, .r13, .r14] _ _
    (word s2.mem base (h 7)) _ (fun _ h => h) W_nodup rfl
    (stable_sc hs2 (by decide) (by simp only [h, ACC]; omega))
    (stable_scs hs2 (by decide) _ (by simp only [h, ACC]; decide))) fun s3 ⟨c1, hc1, e3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  rw [show ([.alu .adc .r15 (.imm 0), .mov .rax (.mem (sc (h 10))), .mov32 .rdx (.reg .rax),
      .alu .sub .rax (.reg .rdx)] : List Instr) = [.alu .adc .r15 (.imm 0)] ++
      [.mov .rax (.mem (sc (h 10))), .mov32 .rdx (.reg .rax), .alu .sub .rax (.reg .rdx)] from rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (adcs_ok [.r15] s3 [.r15] [.imm 0] [0] s3 c1 (Keeps.refl _ _) (fun _ h => h)
    (by decide) rfl (.cons (stable_imm0 _ _) .nil) hc1) fun s4 ⟨c4, _, e4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (splitH_ok hs4) fun s5 ⟨d5, a5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (add_chain_ok [.r11, .r12, .r13, .r14, .r15] s5 .r11 [.r12, .r13, .r14, .r15]
    (.reg .rax) [.mem (sc (h 11)), .mem (sc (h 12)), .mem (sc (h 13)), .imm 0] (s5.gpr .rax)
    [word s5.mem base (h 11), word s5.mem base (h 12), word s5.mem base (h 13), 0] (fun _ h => h)
    (by decide) rfl (stable_reg s5 (by decide))
    (.cons (stable_sc hs5 (by decide) (by simp only [h, ACC]; omega))
      (.cons (stable_sc hs5 (by decide) (by simp only [h, ACC]; omega))
        (.cons (stable_sc hs5 (by decide) (by simp only [h, ACC]; omega))
          (.cons (stable_imm0 _ _) .nil))))) fun s6 ⟨c6, _, e6, k6⟩ => ?_
  have hs6 := hs5.of_keeps k6 (by decide)
  rw [WP.block_append_iff, show ([.mov .rcx (.mem (sc (h 6 + 4))), .mov32 .rdx (.reg .rcx),
      .alu .sub .rcx (.reg .rdx), .mov32 .rdx (.mem (sc (h 13 + 4))), .alu .add .rcx (.reg .rdx)] :
      List Instr) = [.mov .rcx (.mem (sc (h 6 + 4))), .mov32 .rdx (.reg .rcx),
      .alu .sub .rcx (.reg .rdx)] ++ [.mov32 .rdx (.mem (sc (h 13 + 4))), .alu .add .rcx (.reg .rdx)]
      from rfl, WP.block_append_iff]
  refine WP.mono (splitLo_ok hs6 (d := h 6 + 4) (by simp only [h, ACC]; omega) (r := .rcx)
    (t := .rdx) (by decide)) fun s7 ⟨d7, a7, k7⟩ => ?_
  have hs7 := hs6.of_keeps k7 (by decide)
  have g := fun {x y : State} {rs : List Reg} (k : Keeps rs x y) (r : Reg) (h : r ∉ rs) => k.1 r h
  -- Memory is only read until the stores.
  have m2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  have m4 : s4.mem = s.mem := k4.2.1.trans (k3.2.1.trans m2)
  have m5 : s5.mem = s.mem := k5.2.1.trans m4
  have m6 : s6.mem = s.mem := k6.2.1.trans m5
  have m7 : s7.mem = s.mem := k7.2.1.trans m6
  -- `rcx`: word 3 of `rot(H)`.
  have wm6 := word_mid s.mem base (h 6)
  rw [show h 6 + 8 = h 7 from rfl] at wm6
  have r7 : (s7.gpr .rcx).toNat = 2 ^ 32 * ((word s.mem base (h 7)).toNat % 2 ^ 32) := by
    rw [m6] at d7 a7
    have := Nat.div_lt_of_lt_mul (m := (word s.mem base (h 6)).toNat) (n := 2 ^ 32) (k := 2 ^ 32)
      (word s.mem base (h 6)).isLt
    omega
  have hi13 := readW32_mid s.mem base (h 13)
  have hb13 : (word s.mem base (h 13)).toNat / 2 ^ 32 < 2 ^ 32 :=
    Nat.div_lt_of_lt_mul (word s.mem base (h 13)).isLt
  have hl7 : (word s.mem base (h 7)).toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  refine WP.mono (addLo_ok hs7 (d := h 13 + 4) (by simp only [h, ACC]; omega)
    (by rw [r7, m7, hi13]; omega)) fun s8 ⟨e8, k8⟩ => ?_
  have hs8 := hs7.of_keeps k8 (by decide)
  have m8 : s8.mem = s.mem := k8.2.1.trans m7
  rw [m7, hi13, r7] at e8
  -- `+ rot(H)`
  rw [WP.block_append_iff]
  refine WP.mono (add_chain_ok W s8 .r8 [.r9, .r10, .r11, .r12, .r13, .r14] _ _
    (word s8.mem base (h 10 + 4)) [word s8.mem base (h 11 + 4), word s8.mem base (h 12 + 4),
      s8.gpr .rcx, word s8.mem base (h 7 + 4), word s8.mem base (h 8 + 4),
      word s8.mem base (h 9 + 4)] (fun _ h => h) W_nodup rfl
    (stable_sc hs8 (by decide) (by simp only [h, ACC]; omega))
    (.cons (stable_sc hs8 (by decide) (by simp only [h, ACC]; omega))
      (.cons (stable_sc hs8 (by decide) (by simp only [h, ACC]; omega))
        (.cons (stable_reg s8 (by decide))
          (.cons (stable_sc hs8 (by decide) (by simp only [h, ACC]; omega))
            (.cons (stable_sc hs8 (by decide) (by simp only [h, ACC]; omega))
              (.cons (stable_sc hs8 (by decide) (by simp only [h, ACC]; omega)) .nil)))))))
    fun s9 ⟨c9, hc9, e9, k9⟩ => ?_
  have hs9 := hs8.of_keeps k9 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (adcs_ok [.r15] s9 [.r15] [.imm 0] [0] s9 c9 (Keeps.refl _ _) (fun _ h => h)
    (by decide) rfl (.cons (stable_imm0 _ _) .nil) hc9) fun s10 ⟨c10, _, e10, k10⟩ => ?_
  have hs10 := hs9.of_keeps k10 (by decide)
  -- `r15` along the way, and the bounds that exclude overflow.
  have r15_3 : s3.gpr .r15 = 0 := by rw [g k3 _ (by decide), g k2 _ (by decide), z1]; rfl
  rw [len64_1] at e4
  simp only [rv, wv, r15_3, toNat_zero64] at e4
  have hc1 := Bool.toNat_le c1
  have r15_5 : (s5.gpr .r15).toNat = c1.toNat := by rw [g k5 _ (by decide)]; omega
  have l6 := rv_lt s6 [.r11, .r12, .r13, .r14]
  have l5 := rv_lt s5 [.r11, .r12, .r13, .r14]
  rw [len64_5] at e6
  rw [rv5_split, rv5_split, r15_5] at e6
  simp only [wv, toNat_zero64] at e6
  simp only [List.length_cons, List.length_nil] at l6 l5
  have hc6 : c6.toNat = 0 := by
    have := Bool.toNat_le c6
    have := (word s5.mem base (h 11)).isLt; have := (word s5.mem base (h 12)).isLt
    have := (word s5.mem base (h 13)).isLt; have := (s5.gpr .rax).isLt
    have := (s6.gpr .r15).isLt
    rcases Nat.lt_or_ge c6.toNat 1 with h | h
    · omega
    · exfalso; omega
  rw [len64_1] at e10
  simp only [rv, wv, toNat_zero64] at e10
  have r15_9 : s9.gpr .r15 = s6.gpr .r15 := by
    rw [g k9 _ (by decide), g k8 _ (by decide), g k7 _ (by decide)]
  rw [m5] at e6
  rw [m4] at d5 a5
  rw [len64_7, m2] at e3
  rw [len64_7, m8, W_lit] at e9
  rw [k1.2.1, show W.length = 7 from rfl] at v2
  -- The registers along the way.
  have w43 : rv s4 W = rv s3 W := k4.rv_eq (by decide)
  have w54 : rv s5 W = rv s4 W := k5.rv_eq (by decide)
  have w65 : rv s6 [.r8, .r9, .r10] = rv s5 [.r8, .r9, .r10] := k6.rv_eq (by decide)
  have w76 : rv s7 W = rv s6 W := k7.rv_eq (by decide)
  have w87 : rv s8 W = rv s7 W := k8.rv_eq (by decide)
  have sp5 := rvW_split s5
  have sp6 := rvW_split s6
  simp only [wv, List.map_cons, List.map_nil] at e3 e9 e6
  rw [W_lit] at e3
  -- `rot(H)`'s words.
  have mid := fun d => word_mid s.mem base d
  have M10 := mid (h 10); have M11 := mid (h 11); have M12 := mid (h 12)
  have M7 := mid (h 7); have M8 := mid (h 8); have M9 := mid (h 9)
  rw [show h 10 + 8 = h 11 from rfl] at M10
  rw [show h 11 + 8 = h 12 from rfl] at M11
  rw [show h 12 + 8 = h 13 from rfl] at M12
  rw [show h 7 + 8 = h 8 from rfl] at M7
  rw [show h 8 + 8 = h 9 from rfl] at M8
  rw [show h 9 + 8 = h 10 from rfl] at M9
  have rot := rot_arith ((word s.mem base (h 7)).toNat % 2 ^ 32)
    ((word s.mem base (h 8)).toNat % 2 ^ 32) ((word s.mem base (h 9)).toNat % 2 ^ 32)
    ((word s.mem base (h 10)).toNat % 2 ^ 32) ((word s.mem base (h 11)).toNat % 2 ^ 32)
    ((word s.mem base (h 12)).toNat % 2 ^ 32) ((word s.mem base (h 13)).toNat % 2 ^ 32)
    ((word s.mem base (h 7)).toNat / 2 ^ 32) ((word s.mem base (h 8)).toNat / 2 ^ 32)
    ((word s.mem base (h 9)).toNat / 2 ^ 32) ((word s.mem base (h 10)).toNat / 2 ^ 32)
    ((word s.mem base (h 11)).toNat / 2 ^ 32) ((word s.mem base (h 12)).toNat / 2 ^ 32)
    ((word s.mem base (h 13)).toNat / 2 ^ 32)
  simp only [Nat.mod_add_div] at rot
  rw [← M10, ← M11, ← M12, ← M7, ← M8, ← M9, ← e8] at rot
  -- The whole sum, before the folds.
  have tot : rv s10 W + 2 ^ 448 * (s10.gpr .r15).toNat =
      mv s.mem base ACC 7 + ((word s.mem base (h 7)).toNat + 2 ^ 64 * ((word s.mem base (h 8)).toNat +
        2 ^ 64 * ((word s.mem base (h 9)).toNat + 2 ^ 64 * ((word s.mem base (h 10)).toNat +
        2 ^ 64 * ((word s.mem base (h 11)).toNat + 2 ^ 64 * ((word s.mem base (h 12)).toNat +
        2 ^ 64 * (word s.mem base (h 13)).toNat)))))) + 2 ^ 192 * (s5.gpr .rax).toNat +
      2 ^ 256 * (word s.mem base (h 11)).toNat + 2 ^ 320 * (word s.mem base (h 12)).toNat +
      2 ^ 384 * (word s.mem base (h 13)).toNat + (word s.mem base (h 10)).toNat / 2 ^ 32 +
      2 ^ 32 * ((word s.mem base (h 11)).toNat + 2 ^ 64 * ((word s.mem base (h 12)).toNat +
        2 ^ 64 * ((word s.mem base (h 13)).toNat + 2 ^ 64 * ((word s.mem base (h 7)).toNat +
        2 ^ 64 * ((word s.mem base (h 8)).toNat + 2 ^ 64 * ((word s.mem base (h 9)).toNat +
        2 ^ 64 * ((word s.mem base (h 10)).toNat % 2 ^ 32))))))) := by
    have w10 : rv s10 W = rv s9 W := k10.rv_eq (by decide)
    -- the first two additions
    have S6 : rv s6 W + 2 ^ 448 * (s6.gpr .r15).toNat = mv s.mem base ACC 7 +
        ((word s.mem base (h 7)).toNat + 2 ^ 64 * ((word s.mem base (h 8)).toNat +
        2 ^ 64 * ((word s.mem base (h 9)).toNat + 2 ^ 64 * ((word s.mem base (h 10)).toNat +
        2 ^ 64 * ((word s.mem base (h 11)).toNat + 2 ^ 64 * ((word s.mem base (h 12)).toNat +
        2 ^ 64 * (word s.mem base (h 13)).toNat)))))) + 2 ^ 192 * (s5.gpr .rax).toNat +
        2 ^ 256 * (word s.mem base (h 11)).toNat + 2 ^ 320 * (word s.mem base (h 12)).toNat +
        2 ^ 384 * (word s.mem base (h 13)).toNat := by
      omega_using [e3, e4, e6, v2, w43, w54, w65, sp5, sp6, hc6, r15_5, hc1]
    have r6 : (s6.gpr .r15).toNat ≤ 2 := by
      have b1 := rv_lt s6 W; rw [len_W] at b1
      have b2 := mv_lt s.mem base ACC 7
      rw [show 64 * 7 = 448 from rfl] at b2
      have b7 := (word s.mem base (h 7)).isLt; have b8 := (word s.mem base (h 8)).isLt
      have b9 := (word s.mem base (h 9)).isLt; have b10 := (word s.mem base (h 10)).isLt
      have b11 := (word s.mem base (h 11)).isLt; have b12 := (word s.mem base (h 12)).isLt
      have b13 := (word s.mem base (h 13)).isLt; have ba := (s5.gpr .rax).isLt
      omega_using [S6, b1, b2, b7, b8, b9, b10, b11, b12, b13, ba]
    have c10z : (s10.gpr .r15).toNat = (s6.gpr .r15).toNat + c9.toNat := by
      rw [r15_9] at e10
      have b9 := Bool.toNat_le c9; have b10 := Bool.toNat_le c10
      omega_using [e10, r6, b9, b10]
    rw [w10, c10z]
    simp only [Nat.mul_zero, Nat.add_zero] at e9
    rw [w87, w76, rot] at e9
    generalize (word s.mem base (h 10)).toNat / 2 ^ 32 = HI at e9 ⊢
    generalize (word s.mem base (h 10)).toNat % 2 ^ 32 = LO at e9 ⊢
    omega_using [S6, e9]
  have hsum : (s10.gpr .r15).toNat < 4 := by
    have hHI : (word s.mem base (h 10)).toNat / 2 ^ 32 < 2 ^ 32 :=
      Nat.div_lt_of_lt_mul (word s.mem base (h 10)).isLt
    have hLO : (word s.mem base (h 10)).toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    generalize (word s.mem base (h 10)).toNat / 2 ^ 32 = HI at tot hHI
    generalize (word s.mem base (h 10)).toNat % 2 ^ 32 = LO at tot hLO
    have b1 := rv_lt s10 W; rw [len_W] at b1
    have b2 := mv_lt s.mem base ACC 7
    rw [show 64 * 7 = 448 from rfl] at b2
    have b7 := (word s.mem base (h 7)).isLt; have b8 := (word s.mem base (h 8)).isLt
    have b9 := (word s.mem base (h 9)).isLt; have b10 := (word s.mem base (h 10)).isLt
    have b11 := (word s.mem base (h 11)).isLt; have b12 := (word s.mem base (h 12)).isLt
    have b13 := (word s.mem base (h 13)).isLt; have ba := (s5.gpr .rax).isLt
    omega_using [tot, b1, b2, b7, b8, b9, b10, b11, b12, b13, ba, hHI, hLO]
  rw [WP.block_append_iff]
  refine WP.mono (fold2_ok s10 (by omega)) fun s11 ⟨e11, k11⟩ => ?_
  have hs11 := hs10.of_keeps k11 (by decide)
  refine WP.mono (stores_ok hs11 o W (by rw [show W.length = 7 from rfl]; simp only [ACC] at ho; omega)) fun s12 ⟨e12, o12, g12, rd12, wr12⟩ => ?_
  rw [show W.length = 7 from rfl] at e12 o12
  have K : Keeps clob s s11 := (k1.mono (by decide)).trans <| (k2.mono (by decide)).trans <|
    (k3.mono (by decide)).trans <| (k4.mono (by decide)).trans <| (k5.mono (by decide)).trans <|
    (k6.mono (by decide)).trans <| (k7.mono (by decide)).trans <| (k8.mono (by decide)).trans <|
    (k9.mono (by decide)).trans <| (k10.mono (by decide)).trans (k11.mono (by decide))
  refine ⟨?_, fun r hr => (g12 r).trans (K.1 r hr), rd12.trans K.2.2.1, wr12.trans K.2.2.2,
    by rw [← K.2.1]; exact o12⟩
  · show mv s12.mem base o 7 % P = _
    rw [e12, e11, tot, mvH]
    refine (reduce_arith _ _ _ _ _ _ _ _ _ _ _ ?_ ?_).symm
    · exact Nat.mod_add_div _ _
    · rw [← d5]; exact a5

end VG.Proof.X448.X86_64
