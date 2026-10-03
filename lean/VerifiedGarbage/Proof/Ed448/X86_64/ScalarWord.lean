import VerifiedGarbage.Impl.Ed448.X86_64.Scalar
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.X448.X86_64.Freeze

/-!
# Ed448 scalar arithmetic on x86-64: one word

`wordFold` turns the remainder `r < L` in `r8–r14` and the next word `w` in
`rax` into `l + h c` for `2^64 r + w = h 2^446 + l` (`fold_words`), and
`csub` reduces a value below `2L` modulo `L`. Each block is checked against
the numbers it computes, with X448's carry chains, multiply-accumulate steps
and selection.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Keeps Scr rv mv wv word off Outside stable_reg stable_imm0
  add_chain_ok mulSteps_ok LdStable stores_ok sel_ok stable_scs mask)
open VG.Impl.X448.X86_64 (W w sc stores chain)
open VG.Spec.Ed448 (L)

/-- The remainder: the seven words of `r8–r14`. -/
abbrev rem (s : State) : Nat := rv s W

theorem rem_eq (s : State) : rem s = (s.gpr .r8).toNat + 2 ^ 64 * ((s.gpr .r9).toNat + 2 ^ 64 *
    ((s.gpr .r10).toNat + 2 ^ 64 * ((s.gpr .r11).toNat + 2 ^ 64 * ((s.gpr .r12).toNat + 2 ^ 64 *
    ((s.gpr .r13).toNat + 2 ^ 64 * (s.gpr .r14).toNat))))) := by
  simp only [rem, rv, W]; omega

theorem rem_split (s : State) : rem s = rv s [.r8, .r9, .r10, .r11] +
    2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * rv s [.r12, .r13, .r14] := by
  simp only [rem, rv, W]; omega

theorem rotr62 (x : BitVec 64) (h : x.toNat < 2 ^ 62) : (x.rotateRight 62).toNat = 4 * x.toNat := by
  rw [BitVec.toNat_rotateRight]
  simp only [Nat.reduceMod, Nat.reduceSub, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.div_eq_of_lt h, Nat.zero_or, Nat.mod_eq_of_lt (by omega)]
  omega

theorem shr62 (x : BitVec 64) : (x >>> 62).toNat = x.toNat / 2 ^ 62 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem and62 (x : BitVec 64) : (x &&& 0x3fffffffffffffff).toNat = x.toNat % 2 ^ 62 := by
  rw [BitVec.toNat_and, show (0x3fffffffffffffff : BitVec 64).toNat = 2 ^ 62 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-- `foldPrep`: `h` into `rcx`, `l` into `r8–r14`, `rbp = 0`. -/
theorem foldPrep_ok (s : State) (h6 : (s.gpr .r14).toNat < 2 ^ 62) :
    WP isa (.block foldPrep) s fun t =>
      (t.gpr .rcx).toNat = (s.gpr .r13).toNat / 2 ^ 62 + 4 * (s.gpr .r14).toNat ∧
      t.gpr .r8 = s.gpr .rax ∧ t.gpr .r9 = s.gpr .r8 ∧ t.gpr .r10 = s.gpr .r9 ∧
      t.gpr .r11 = s.gpr .r10 ∧ t.gpr .r12 = s.gpr .r11 ∧ t.gpr .r13 = s.gpr .r12 ∧
      (t.gpr .r14).toNat = (s.gpr .r13).toNat % 2 ^ 62 ∧ t.gpr .rbp = 0 ∧
      Keeps [.rcx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14] s t := by
  apply WP.of_runBlock
  simp only [foldPrep, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    execShift, execAlu, State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, show 1 ≤ 62 ∧ 62 ≤ 63 by decide, and_self, ite_true, ite_false,
    reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, and62 _, rfl, fun r hr => ?_,
    rfl, rfl, rfl⟩
  · have := (s.gpr .r13).isLt
    rw [BitVec.toNat_add, shr62, rotr62 _ h6, Nat.mod_eq_of_lt (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2, ite_false]

theorem cWords_val : wv cWords = cL := by decide

theorem ldStable_imm (X : List Reg) (s : State) (v : BitVec 64) :
    LdStable X s (.movImm64 .rax v) v := fun _ _ _ _ _ => rfl

theorem ldStable_cWords (X : List Reg) (s : State) :
    List.Forall₂ (LdStable X s) (cWords.map (.movImm64 .rax ·)) cWords :=
  .cons (ldStable_imm _ _ _) <| .cons (ldStable_imm _ _ _) <| .cons (ldStable_imm _ _ _) <|
    .cons (ldStable_imm _ _ _) .nil

/-- `foldMul`: `r8–r14 += rcx · c`, for `rbp = 0` and a sum below `2^448`. -/
theorem foldMul_ok (s : State) (hb : s.gpr .rbp = 0)
    (hlt : rem s + (s.gpr .rcx).toNat * cL < 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64) :
    WP isa (.block foldMul) s fun t =>
      rem t = rem s + (s.gpr .rcx).toNat * cL ∧
      Keeps [.rax, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14] s t := by
  rw [foldMul, WP.block_append_iff]
  refine WP.mono (mulSteps_ok [.rax, .rdx, .rbp, .r8, .r9, .r10, .r11] s [.r8, .r9, .r10, .r11] _
    cWords s (Keeps.refl _ _) (by decide) (by decide) (by decide) rfl (ldStable_cWords _ _))
    fun a ⟨ea, ka⟩ => ?_
  refine WP.mono (add_chain_ok [.r12, .r13, .r14] a .r12 [.r13, .r14] (.reg .rbp) [.imm 0, .imm 0]
    (a.gpr .rbp) [0, 0] (fun _ h => h) (by decide) rfl (stable_reg a (by decide))
    (.cons (stable_imm0 _ _) (.cons (stable_imm0 _ _) .nil))) fun t ⟨c, _, et, kt⟩ => ?_
  refine ⟨?_, (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  have g4 : rv t [.r8, .r9, .r10, .r11] = rv a [.r8, .r9, .r10, .r11] :=
    kt.rv_eq (by decide)
  have a3 : rv a [.r12, .r13, .r14] = rv s [.r12, .r13, .r14] := ka.rv_eq (by decide)
  rw [cWords_val, hb] at ea
  rw [a3] at et
  have l3 := Proof.X448.X86_64.rv_lt t [.r12, .r13, .r14]
  have hc := Bool.toNat_le c
  simp only [wv, Proof.X448.X86_64.toNat_zero64, List.length_cons, List.length_nil] at ea et l3
  rw [rem_split, rem_split, g4]
  rw [rem_split] at hlt
  generalize rv a [.r8, .r9, .r10, .r11] = A4 at *
  generalize rv s [.r8, .r9, .r10, .r11] = S4 at *
  generalize rv t [.r12, .r13, .r14] = T3 at *
  generalize rv s [.r12, .r13, .r14] = S3 at *
  generalize (s.gpr .rcx).toNat * cL = H at *
  generalize (a.gpr .rbp).toNat = B at *
  generalize c.toNat = C at *
  omega

/-- The registers `wordFold` changes. -/
def foldClob : List Reg := [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14]

/-- `wordFold`: from the remainder `r < L` and the next word `w` in `rax`, a value
below `2L` congruent to `2^64 r + w`. -/
theorem wordFold_ok (s : State) (hr : rem s < L) :
    WP isa (.block wordFold) s fun t => rem t < 2 * L ∧
      rem t % L = ((s.gpr .rax).toNat + 2 ^ 64 * rem s) % L ∧ Keeps foldClob s t := by
  have hw := (s.gpr .rax).isLt
  have h0 := (s.gpr .r8).isLt; have h1 := (s.gpr .r9).isLt; have h2 := (s.gpr .r10).isLt
  have h3 := (s.gpr .r11).isLt; have h4 := (s.gpr .r12).isLt; have h5 := (s.gpr .r13).isLt
  have h6 := (s.gpr .r14).isLt
  rw [rem_eq] at hr
  obtain ⟨h6', hh, hlt, hmod⟩ := fold_words _ _ _ _ _ _ _ _ hw h0 h1 h2 h3 h4 h5 h6 hr
  rw [wordFold, WP.block_append_iff]
  refine WP.mono (foldPrep_ok s h6') fun a ⟨ac, a8, a9, a10, a11, a12, a13, a14, abp, ka⟩ => ?_
  have ra : rem a = (s.gpr .rax).toNat + 2 ^ 64 * ((s.gpr .r8).toNat + 2 ^ 64 *
      ((s.gpr .r9).toNat + 2 ^ 64 * ((s.gpr .r10).toNat + 2 ^ 64 * ((s.gpr .r11).toNat +
      2 ^ 64 * ((s.gpr .r12).toNat + 2 ^ 64 * ((s.gpr .r13).toNat % 2 ^ 62)))))) := by
    rw [rem_eq, a8, a9, a10, a11, a12, a13, a14]
  have hb : rem a + (a.gpr .rcx).toNat * cL <
      2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by
    have : 2 * L < 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by
      decide +kernel
    rw [ra, ac]; omega
  refine WP.mono (foldMul_ok a abp hb) fun t ⟨et, kt⟩ => ?_
  rw [et, ra, ac]
  refine ⟨hlt, ?_, (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [hmod, rem_eq]

theorem kWords_val : wv kWords = 2 ^ 448 - L := by decide +kernel

theorem kWords_lit : kWords = [0xdc873d6d54a7bb0d, 0xde933d8d723a70aa, 0x3bb124b65129c96f,
    0x8335dc16, 0, 0, 0xc000000000000000] := rfl

theorem sbbMask_ok (s : State) {c : Bool} (hc : s.cf = some c) :
    WP isa (.block [.alu .sbb .r15 (.reg .r15)]) s fun s' =>
      s'.gpr .r15 = mask c ∧ Keeps [.r15] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, hc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, Option.some.injEq,
    exists_eq_left', BitVec.sub_self]
  refine ⟨by cases c <;> decide, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- The registers `csub` changes. -/
def csubClob : List Reg := [.rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The offsets of `K`'s words but the first. -/
def kOffs : List Nat := [136, 144, 152, 160, 168, 176]

theorem csub_eq : csub = stores TMP W ++ (chain .add .adc W (.mem (sc 128) :: kOffs.map
    fun d => .mem (sc d)) ++ (([.alu .sbb .r15 (.reg .r15)] : List Instr) ++
    (List.range 7).flatMap fun i =>
      [.mov .rax (.mem (sc (TMP + 8 * i))), .alu .xor (w i) (.reg .rax),
        .alu .and (w i) (.reg .r15), .alu .xor (w i) (.reg .rax)])) := rfl

theorem len7 : 64 * [Reg.r8, .r9, .r10, .r11, .r12, .r13, .r14].length = 448 := rfl

/-- `csub`: `r8–r14` (below `2L`) modulo `L`, with `K` at `KC`; only `TMP`
is written. -/
theorem csub_ok {s : State} {base : Addr} (hs : Scr s base) (hK : mv s.mem base KC 7 = wv kWords)
    (hx : rem s < 2 * L) :
    WP isa (.block csub) s fun t => rem t = rem s % L ∧
      (∀ r, r ∉ csubClob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base TMP 56 s.mem t.mem := by
  rw [csub_eq, WP.block_append_iff]
  refine WP.mono (stores_ok hs TMP W (by decide)) fun a ⟨va, oa, ga, rda, wra⟩ => ?_
  have hsa : Scr a base := ⟨(ga _).trans hs.rdi, wra ▸ hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (add_chain_ok W a .r8 [.r9, .r10, .r11, .r12, .r13, .r14]
    (.mem (sc 128)) (kOffs.map fun d => .mem (sc d))
    (word a.mem base 128) (kOffs.map fun d => word a.mem base d)
    (fun _ h => h) Proof.X448.X86_64.W_nodup rfl
    (Proof.X448.X86_64.stable_sc hsa (by decide) (by decide))
    (stable_scs hsa (by decide) kOffs (by decide))) fun b ⟨c, hc, eb, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sbbMask_ok b hc) fun d ⟨md, kd⟩ => ?_
  have hsb : Scr b base := hsa.of_keeps kb (by decide)
  have hsd : Scr d base := hsb.of_keeps kd (by decide)
  refine WP.mono (sel_ok hsd (a := TMP) (by decide) md) fun t ⟨wt, kt, mt⟩ => ?_
  have hlt := Proof.X448.X86_64.rv_lt b W
  have hkv : wv (word a.mem base 128 :: kOffs.map fun d => word a.mem base d) = 2 ^ 448 - L := by
    have hmv : mv a.mem base KC 7 = mv s.mem base KC 7 :=
      oa.mv (Or.inl (by decide)) (by simp only [KC]; omega)
    rw [← kWords_val, ← hK, ← hmv]
    rfl
  rw [hkv, len7, show rv a (Reg.r8 :: [.r9, .r10, .r11, .r12, .r13, .r14]) = rem a from rfl,
    show rem a = rem s from Proof.X448.X86_64.rv_congr fun r _ => ga r] at eb
  rw [Proof.X448.X86_64.len_W] at hlt
  have hsel : rem t = if c then rv b [.r8, .r9, .r10, .r11, .r12, .r13, .r14] else rem s := by
    have mm : d.mem = a.mem := kd.2.1.trans kb.2.1
    cases c with
    | false =>
      rw [ite_eq_right Bool.false_ne_true]
      show rv t W = rv s W
      rw [Proof.X448.X86_64.rvW, ← va, Proof.X448.X86_64.W_len, Proof.X448.X86_64.mv7]
      exact Proof.X448.X86_64.val7_congr fun i hi => by
        rw [wt i hi, ite_eq_right Bool.false_ne_true, mm]
    | true =>
      rw [ite_eq_left rfl]
      show rv t W = rv b W
      rw [Proof.X448.X86_64.rvW, Proof.X448.X86_64.rvW]
      exact Proof.X448.X86_64.val7_congr fun i hi => by
        rw [wt i hi, ite_eq_left rfl, kd.1 _ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          exact Proof.X448.X86_64.w_ne_r15 i hi)]
  have h2L : 2 * L ≤ 2 ^ 448 := by decide +kernel
  refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [hsel]
    generalize (2 : Nat) ^ 448 = M at hlt eb h2L
    exact csub_nat h2L hx hlt eb
  · simp only [csubClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kt.1 r (by simp [W, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1]), kd.1 r (by simp [hr.2.2.2.2.2.2.2.2]),
      kb.1 r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1]), ga r]
  · rw [kt.2.1, kd.2.2.1, kb.2.2.1, rda]
  · rw [kt.2.2, kd.2.2.2, kb.2.2.2, wra]
  · rw [mt, kd.2.1, kb.2.1]; exact oa

end VG.Proof.Ed448.X86_64
