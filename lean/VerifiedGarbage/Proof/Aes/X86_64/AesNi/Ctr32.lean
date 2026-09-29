import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# AES-NI counter mode: the whole function

Untrusted: everything here is checked by Lean. `ctr32_verified` proves
`Impl.Aes.X86_64.AesNi.ctr32` against `ctr32X86_64`. The loops keep, after
`c` blocks, the counter block `inc₃₂ᶜ(CB)` in `xmm9` and the first `c` data
blocks encrypted; the eight-block and one-block bodies are the same code
for different lists of registers (`blocks_ok`).
-/

namespace VG.Proof.Aes.X86_64.AesNi

open VG VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ ctrs xorData aes regs8 body8 body1 ctrLoad ctrStore ctr32)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq blockAt_store)
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev sp : Addr := s₀.gpr .rdi
abbrev nr : Nat := (s₀.gpr .rsi).toNat
abbrev cp : Addr := s₀.gpr .rdx
abbrev dp : Addr := s₀.gpr .rcx
abbrev nb : Nat := (s₀.gpr .r8).toNat
abbrev sR : Region := ⟨sp s₀, 240⟩
abbrev cR : Region := ⟨cp s₀, 16⟩
abbrev dR : Region := ⟨dp s₀, 16 * nb s₀⟩
abbrev scrR : Region := ⟨s₀.gpr .r9, 2048⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- The key schedule. -/
abbrev sch : List Byte := Spec.Aes.bytesAt s₀.mem (sp s₀) (16 * (nr s₀ + 1))
/-- `CIPH_K`. -/
abbrev ciph : Block → Block := aesWith (nr s₀) (sch s₀)
abbrev cb : Block := blockAt s₀.mem (cp s₀)
/-- Block `k` of the data, and where it starts. -/
abbrev bAddr (k : Nat) : Addr := dp s₀ + BitVec.ofNat 64 (16 * k)
abbrev blk (k : Nat) : Block := blockAt s₀.mem (bAddr s₀ k)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [sR s₀]
  wr : s₀.wr = [cR s₀, dR s₀, scrR s₀]
  s_c : (sR s₀).Disjoint (cR s₀)
  s_d : (sR s₀).Disjoint (dR s₀)
  s_scr : (sR s₀).Disjoint (scrR s₀)
  c_d : (cR s₀).Disjoint (dR s₀)
  c_scr : (cR s₀).Disjoint (scrR s₀)
  d_scr : (dR s₀).Disjoint (scrR s₀)
  ret_c : (retR s₀).Disjoint (cR s₀)
  ret_d : (retR s₀).Disjoint (dR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  wrap : (dp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64
  rounds : nr s₀ = 10 ∨ nr s₀ = 12 ∨ nr s₀ = 14

theorem pre_of (s₀ : State) (h : ctr32X86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem keys (j : Nat) (hj : j ≤ 14) :
    InRegions (s₀.rd ++ s₀.wr) (sp s₀ + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 16 :=
  ⟨sR s₀, by simp [hp.rd], by rw [ofInt_natCast]; exact contains_offset (by omega) (by omega)⟩

/-- Block `k` is in the data. -/
theorem in_blk {k : Nat} (hk : k < nb s₀) : (dR s₀).Contains (bAddr s₀ k) 16 :=
  contains_offset (by omega) (by have := hp.wrap; omega)

theorem out_blk {k : Nat} (hk : k < nb s₀) : InRegions s₀.wr (bAddr s₀ k) 16 :=
  ⟨dR s₀, by simp [hp.wr], hp.in_blk hk⟩

/-- Memory that the data does not overlap. -/
theorem sch_frame {m : Mem} (hf : Frame [dR s₀] s₀.mem m) :
    Spec.Aes.bytesAt m (sp s₀) (16 * (nr s₀ + 1)) = sch s₀ := by
  have hn : 16 * (nr s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  simp only [sch, Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact hf.bytes (R := ⟨sp s₀, 16 * (nr s₀ + 1)⟩) (by
    simp only [List.mem_singleton, forall_eq]
    exact hp.s_d.sub_left (Region.sub_prefix hn)) (by show 16 * (nr s₀ + 1) ≤ 2 ^ 64; omega) hi

end Pre

/-! ## The loop invariant -/

/-- After `c` blocks, with `rcx` and `r8` at block `p`. -/
structure Inv (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ nb s₀
  x9 : s.xmm .xmm9 = Nat.repeat inc32 c (cb s₀)
  x10 : s.xmm .xmm10 = revMask
  x11 : s.xmm .xmm11 = one
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  r10 : s.gpr .r10 = sp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  rcx : s.gpr .rcx = bAddr s₀ p
  r8 : s.gpr .r8 = BitVec.ofNat 64 (nb s₀ - p)
  frame : Frame [dR s₀] s₀.mem s.mem
  blocks : ∀ k < nb s₀,
    blockAt s.mem (bAddr s₀ k) = if k < c then blk s₀ k ^^^ ciph s₀ (Nat.repeat inc32 k (cb s₀))
      else blk s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem regs_nodup (rs : List XReg) (h : rs = regs8 ∨ rs = [.xmm0]) :
    rs.Nodup ∧ .xmm8 ∉ rs ∧ ∀ r ∈ rs, r ≠ .xmm9 ∧ r ≠ .xmm10 ∧ r ≠ .xmm11 := by
  rcases h with rfl | rfl <;> decide

/-- Blocks `c … c + n − 1` of the data are in the data. -/
theorem run_in {d a : Addr} {nb c n : Nat} (hw : d.toNat + 16 * nb ≤ 2 ^ 64) (hc : c + n ≤ nb)
    (ha : (a - (d + BitVec.ofNat 64 (16 * c))).toNat < 16 * n) : (a - d).toNat < 16 * nb := by
  rw [off_toNat _ _ (by omega)] at ha
  have := (a - d).isLt
  omega

/-- Block `k` of the data is not in blocks `c … c + n − 1`. -/
theorem run_sep {d a : Addr} {nb c n k : Nat} (hw : d.toNat + 16 * nb ≤ 2 ^ 64) (hk : k < nb)
    (hc : c + n ≤ nb) (hn : ¬ (c ≤ k ∧ k < c + n))
    (h₁ : (a - (d + BitVec.ofNat 64 (16 * k))).toNat < 16)
    (h₂ : (a - (d + BitVec.ofNat 64 (16 * c))).toNat < 16 * n) : False := by
  rw [off_toNat _ _ (by omega)] at h₁ h₂
  have := (a - d).isLt
  omega

/-- The counter blocks, AES and the XOR into the data, for the blocks
`c … c + N - 1` (`N` the number of registers). -/
theorem blocks_ok {s₀ : State} (hp : Pre s₀) (rs : List XReg) (hrs : rs = regs8 ∨ rs = [.xmm0])
    (tail : List Instr) {Q : State → Prop} {c : Nat} (hc : c + rs.length ≤ nb s₀) {s : State}
    (hI : Inv s₀ c c s) (hQ : ∀ s', Inv s₀ (c + rs.length) c s' → WP isa (.block tail) s' Q) :
    WP isa (.seq (.block (ctrs rs)) (.seq (aes rs) (.block (xorData rs 0 ++ tail)))) s Q := by
  obtain ⟨hnd, h8, hx⟩ := regs_nodup rs hrs
  have hlen : 0 < rs.length := by rcases hrs with rfl | rfl <;> decide
  have hw := hp.wrap
  refine WP.seq (WP.mono (ctrs_ok rs s hnd hx hI.x10 hI.x11) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_)
  rw [hI.x9, rep_add] at c₁
  have ek : ∀ k (h : k < rs.length),
      s₁.xmm rs[k] = XBinOp.eval .pshufb (Nat.repeat inc32 (c + k) (cb s₀)) revMask := by
    intro k h; rw [e₁ k h, hI.x9, rep_add]
  have hg₁ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r10 → s₁.gpr r = s₀.gpr r :=
    fun r h1 h2 h3 h4 => by rw [f₁.gpr, hI.gpr r h1 h2 h3 h4]
  have hK : Keys (nr s₀) (sch s₀) s₁ :=
    ⟨by rw [f₁.mem, f₁.gpr, hI.gpr .rdi (by decide) (by decide) (by decide) (by decide),
        hp.sch_frame hI.frame],
      by rcases hp.rounds with h | h | h <;> omega,
      fun j hj => by
        rw [f₁.rd, f₁.wr, f₁.gpr, hI.rd, hI.wr, hI.gpr .rdi (by decide) (by decide) (by decide)
          (by decide)]
        exact hp.keys j (by rcases hp.rounds with h | h | h <;> omega)⟩
  refine WP.seq (WP.mono (aes_ok rs hnd h8 hp.rounds s₁ hK
    (by rw [hg₁ .rsi (by decide) (by decide) (by decide) (by decide)]; simp)
    (by rw [f₁.gpr, hI.r10, hI.gpr .rdi (by decide) (by decide) (by decide) (by decide)]))
    fun s₂ ⟨e₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ k (h : k < rs.length), XBinOp.eval .pshufb (s₂.xmm rs[k]) revMask =
      ciph s₀ (Nat.repeat inc32 (c + k) (cb s₀)) := fun k h =>
    (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h), ek k h])).symm
  have hrcx₂ : s₂.gpr .rcx = bAddr s₀ c := by rw [f₂.gpr, f₁.gpr, hI.rcx]
  have hrcxN : (s₂.gpr .rcx).toNat = (dp s₀).toNat + 16 * c := by
    rw [hrcx₂, bAddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have addr : ∀ k, s₂.gpr .rcx + BitVec.ofInt 64 ((16 * (0 + k) : Nat) : Int) = bAddr s₀ (c + k) :=
    fun k => by
      rw [hrcx₂, ofInt_natCast, bAddr, bAddr, BitVec.add_assoc, ← BitVec.ofNat_add,
        show 16 * c + 16 * (0 + k) = 16 * (c + k) by omega]
  have addr' : ∀ k, s₂.gpr .rcx + BitVec.ofNat 64 (16 * (0 + k)) = bAddr s₀ (c + k) :=
    fun k => by rw [← addr, ofInt_natCast]
  rw [WP.block_append_iff]
  refine WP.mono (xorData_ok rs 0 s₂ hnd h8 (fun k hk => by
      rw [addr, f₂.wr, f₁.wr, hI.wr]; exact hp.out_blk (by omega)) (by rw [hrcxN]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => hQ s₃ ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂] at b₃ fr₃
  rw [hrcx₂, Nat.mul_zero, BitVec.add_zero] at fr₃
  simp only [addr'] at b₃
  have kx : ∀ r, r ≠ .xmm8 → r ≠ .xmm9 → r ∉ rs → s₃.xmm r = s.xmm r := fun r h8' h9 hr => by
    rw [x₃ r h8' hr, f₂.xmm r (by simp [h8', hr]), f₁.xmm r (by simp [h9, hr])]
  refine ⟨Nat.le_trans (by omega) hc, ?_, ?_, ?_, fun r h1 h2 h3 h4 => by rw [g₃, f₂.gpr, hg₁ r h1 h2 h3 h4], ?_,
    by rw [g₃, hrcx₂], by rw [g₃, f₂.gpr, f₁.gpr, hI.r8], ?_, ?_, by rw [rd₃, f₂.rd, f₁.rd, hI.rd],
    by rw [wr₃, f₂.wr, f₁.wr, hI.wr]⟩
  · rw [x₃ _ (by decide) (fun h => (hx _ h).1 rfl), f₂.xmm _ (by
      simp only [List.mem_cons, not_or]; exact ⟨by decide, fun h => (hx _ h).1 rfl⟩), c₁]
  · rw [kx _ (by decide) (by decide) (fun h => (hx _ h).2.1 rfl), hI.x10]
  · rw [kx _ (by decide) (by decide) (fun h => (hx _ h).2.2 rfl), hI.x11]
  · rw [g₃, f₂.gpr, f₁.gpr, hI.r10]
  · -- The data written is only in the data.
    refine hI.frame.trans (fr₃.sub fun r hr => ⟨dR s₀, List.mem_singleton_self _, fun a ha => ?_⟩)
    simp only [List.mem_singleton] at hr
    subst hr
    exact run_in hw hc ha
  · intro k hk
    have out : ¬ (c ≤ k ∧ k < c + rs.length) → blockAt s₃.mem (bAddr s₀ k) = blockAt s.mem (bAddr s₀ k) :=
      fun hn => blockAt_frame fr₃ fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        intro a h₁ h₂
        exact run_sep hw hk hc hn h₁ h₂
    by_cases hlo : k < c
    · rw [out (by omega), hI.blocks k hk]
      simp only [hlo, show k < c + rs.length by omega, ite_true]
    · by_cases hhi : k < c + rs.length
      · obtain ⟨j, rfl⟩ : ∃ j, k = c + j := ⟨k - c, by omega⟩
        have hj : j < rs.length := by omega
        rw [b₃ j hj, hI.blocks _ hk, ks j hj]
        simp only [hlo, hhi, ite_false, ite_true]
      · rw [out (by omega), hI.blocks k hk]
        simp only [hlo, hhi, ite_false]

theorem beq_ofNat_zero {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 k ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

theorem nb_lt {s₀ : State} (hp : Pre s₀) : 16 * nb s₀ ≤ 2 ^ 64 := by have := hp.wrap; omega

/-- The eight-block body. -/
theorem body8_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c + 8 ≤ nb s₀) {s : State}
    (hI : Inv s₀ c c s) :
    WP isa body8 s fun s' => Inv s₀ (c + 8) (c + 8) s' ∧ s'.cf = some (decide (nb s₀ - (c + 8) < 8)) := by
  have hn := nb_lt hp
  refine blocks_ok hp regs8 (.inl rfl) _ hc hI fun s₁ hI₁ => ?_
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hrcx := hI₁.rcx
  have hr8 := hI₁.r8
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, ite_true, ite_false, e128, e8, hrcx, hr8,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hsub : BitVec.ofNat 64 (nb s₀ - c) - 8 = BitVec.ofNat 64 (nb s₀ - (c + 8)) := by
    have := (s₀.gpr .r8).isLt; bv_omega
  refine ⟨{ hI₁ with
    gpr := fun r h1 h2 h3 h4 => by simp [h2, h3, hI₁.gpr r h1 h2 h3 h4]
    r10 := by simp [hI₁.r10]
    rcx := by simp (config := {decide := true}) only [bAddr, ite_false, ite_true]; bv_omega
    r8 := by simp only [ite_true, reduceCtorEq, ite_false]; exact hsub }, ?_⟩
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show nb s₀ - (c + 8) < 2 ^ 64 by omega),
    show (8 : BitVec 64).toNat = 8 from rfl]

/-- The one-block body. -/
theorem body1_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < nb s₀) {s : State}
    (hI : Inv s₀ c c s) :
    WP isa body1 s fun s' => Inv s₀ (c + 1) (c + 1) s' ∧
      s'.zf = some (decide (nb s₀ - (c + 1) = 0)) := by
  have hn := nb_lt hp
  refine blocks_ok hp [.xmm0] (.inr rfl) _ hc hI fun s₁ hI₁ => ?_
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  have hrcx := hI₁.rcx
  have hr8 := hI₁.r8
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, ite_false, e16, e1, hrcx, hr8,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hsub : BitVec.ofNat 64 (nb s₀ - c) - 1 = BitVec.ofNat 64 (nb s₀ - (c + 1)) := by
    have := (s₀.gpr .r8).isLt; bv_omega
  refine ⟨{ hI₁ with
    gpr := fun r h1 h2 h3 h4 => by simp [h2, h3, hI₁.gpr r h1 h2 h3 h4]
    r10 := by simp [hI₁.r10]
    rcx := by simp (config := {decide := true}) only [bAddr, ite_false, ite_true]; bv_omega
    r8 := by simp only [ite_true, reduceCtorEq, ite_false]; exact hsub }, ?_⟩
  rw [hsub, beq_ofNat_zero (by omega)]

/-! ## The prologue and the epilogue -/

theorem ctrLoad_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block ctrLoad) s₀ fun s => Inv s₀ 0 0 s ∧ s.cf = some (decide (nb s₀ < 8)) := by
  have hin : InRegions (s₀.rd ++ s₀.wr) (cp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 :=
    ⟨cR s₀, by simp [hp.wr], by rw [ofInt_natCast]; exact contains_offset (by omega) (by omega)⟩
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  apply WP.of_runBlock
  simp only [ctrLoad, Impl.Aes.X86_64.AesNi.const, List.cons_append, List.nil_append]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setXmm, State.setReg, State.load128,
    ea_at, hin, ite_true, ite_false, movq_const, e8, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨Nat.zero_le _, ?_, rfl, rfl, fun r h1 h2 h3 h4 => by simp [h1, h4], ?_, ?_, ?_,
    Frame.refl _ _, fun k _ => by simp, rfl, rfl⟩, ?_⟩ <;>
    try simp (config := {decide := true}) only [ite_true, ite_false]
  · rw [ofInt_natCast]
    simp only [BitVec.add_zero]
    exact (blockAt_eq _ _).symm
  · simp only [nr, sp]; bv_omega
  · simp [bAddr]
  · simp [nb]
  · simp

theorem test_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c c s) :
    WP isa (.block [.alu .test .r8 (.reg .r8)]) s fun s' =>
      Inv s₀ c c s' ∧ s'.zf = some (decide (nb s₀ - c = 0)) := by
  have hn := nb_lt hp
  have hr8 := hI.r8
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, hr8, BitVec.and_self, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨{ hI with }, by rw [beq_ofNat_zero (by omega)]⟩

theorem ctrStore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (nb s₀) (nb s₀) s) :
    WP isa (.block ctrStore) s fun s' => gprPreserved s₀ s' ∧ ctr32X86_64.post s₀ s' := by
  have hrdx : s.gpr .rdx = cp s₀ := hI.gpr .rdx (by decide) (by decide) (by decide) (by decide)
  have hout : InRegions s.wr (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 :=
    ⟨cR s₀, by simp [hI.wr, hp.wr], by
      rw [hrdx, ofInt_natCast]; exact contains_offset (by omega) (by omega)⟩
  have h10 := hI.x10
  have h9 := hI.x9
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ctrStore, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, State.setXmm, State.store128, ea_at, hout, ite_true, h10, h9,
    Option.some.injEq, exists_eq_left']
  rw [hrdx, ofInt_natCast]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  have sep : ∀ {r : Region}, r.Disjoint (cR s₀) → ∀ {a : Addr} {n : Nat}, r.Contains a n →
      Mem.Sep a n (cp s₀) 16 := fun h _ _ ha => h.sep ha (Region.contains_self _ _)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hI.gpr r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · rw [Mem.readW_writeW_sep (sep hp.ret_c (Region.contains_self _ _)) (by decide),
      hI.frame.readW (Region.contains_self _ _) (by simpa using hp.ret_d) (by decide)]
  · apply List.ext_getElem
    · simp [blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream]
    · intro k h₁ h₂
      have hk : k < nb s₀ := by simpa [blocksAt] using h₁
      have := hI.blocks k hk
      simp only [hk, ite_true] at this
      simp only [blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream, List.getElem_map, List.getElem_range,
        List.getElem_zipWith, List.length_map, List.length_range]
      rw [blockAt_writeW_sep _ _ (by
        refine sep (hp.c_d.symm) ?_
        exact hp.in_blk hk), this]
  · exact blockAt_store _ _ _

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ctr32 s₀ fun s' => gprPreserved s₀ s' ∧ ctr32X86_64.post s₀ s' := by
  have hn := nb_lt hp
  refine WP.seq (WP.mono (ctrLoad_ok hp) fun s₁ ⟨hI₁, hcf⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ c, nb s₀ - c < 8 ∧ Inv s₀ c c s) ?_ fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (nb s₀ < 8)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨0, by simpa using h, hI₁⟩
    · let I8 : Nat → State → Prop := fun m s => ∃ c, m = nb s₀ - c ∧ c + 8 ≤ nb s₀ ∧ Inv s₀ c c s
      have hstep : ∀ m s, I8 m s → WP isa body8 s (fun s' =>
          (eval .ae s' = some false ∧ ∃ c, nb s₀ - c < 8 ∧ Inv s₀ c c s') ∨
          (eval .ae s' = some true ∧ ∃ m' < m, I8 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (body8_ok hp hc hI) fun s' ⟨hI', hcf'⟩ => ?_
        by_cases hlt : nb s₀ - (c + 8) < 8
        · exact .inl ⟨by simp [eval, hcf', hlt], c + 8, hlt, hI'⟩
        · exact .inr ⟨by simp [eval, hcf', hlt], nb s₀ - (c + 8), by omega, c + 8, rfl, by omega, hI'⟩
      exact WP.loop (M := isa) I8 hstep (nb s₀) s₁ ⟨0, rfl, by simpa using h, hI₁⟩
  refine WP.seq (WP.mono (test_ok hp hI₂) fun s₃ ⟨hI₃, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (nb s₀) (nb s₀)) ?_ fun s₄ hI₄ => ctrStore_ok hp hI₄)
  refine WP.ite (decide (nb s₀ - c = 0)) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have : c = nb s₀ := by have := hI₃.le; simp at h; omega
    exact WP.block_nil (this ▸ hI₃)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = nb s₀ - c ∧ c < nb s₀ ∧ Inv s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa body1 s (fun s' =>
        (eval .ne s' = some false ∧ Inv s₀ (nb s₀) (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (body1_ok hp hc hI) fun s' ⟨hI', hzf'⟩ => ?_
      by_cases hlast : nb s₀ - (c + 1) = 0
      · have : c + 1 = nb s₀ := by omega
        exact .inl ⟨by simp [eval, hzf', hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [eval, hzf', hlast], nb s₀ - (c + 1), by omega, c + 1, rfl, by omega, hI'⟩
    have hlt : c < nb s₀ := by have := hI₃.le; simp at h; omega
    exact WP.loop (M := isa) I1 hstep (nb s₀ - c) s₃ ⟨c, rfl, hlt, hI₃⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x3000 | .r9 => 0x4000
    | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2048⟩]

theorem ctr32_verified : Verified X86_64.target ctr32 ctr32X86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9]) ?_
      (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, satState] at h₁ h₂
      bv_omega

end VG.Proof.Aes.X86_64.AesNi
