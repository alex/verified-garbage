import VerifiedGarbage.Proof.Sha3.Arm.Call
import VerifiedGarbage.Proof.Sha3.SqueezeFrom

/-!
# The SHA-3 sponge on ARMv7: `squeeze`

Untrusted: everything here is checked by Lean. The same structure as the
AArch64 proof (`VG.Proof.Sha3.AArch64.Stream.Squeeze`), with the prologue
and epilogue of `absorb` (`VG.Proof.Sha3.Arm.Stream.Absorb`).
-/

namespace VG.Proof.Sha3.Arm.Stream.Squeeze

open VG VG.Arm VG.Impl.Sha3.Arm.Stream
open VG.Proof.Sha3.Arm (saveA_ok restoreA_ok saveMemA_frame SSaved ssaved_ok saveMemA_ssaved
  restore_eq call_ok covers_of preserved_cases ofNat32_succ sub_ofNat32 ofNat32_beq_zero sub_beq_zero32
  beq_zero32 ofNat_toNat32 sub_imm0 arg_in argByte_eq addr_toNat)
open VG.Proof.Sha512.Arm (A A_eq contains_A)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_subs wp_cmp wp_ldrb
  wp_strb wp_ldrSp eval_eq eval_ne)
open VG.Proof.Sha3 (byteOf byteOf_stateAt iterF iterF_succ length_squeezeFrom squeezeFrom_getElem
  squeezeFrom_iterF stateAt_congr writeW8_self writeW8_other div_mod_eq contains_offset sub_offset)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev rt : Nat := (s₀.gpr .r1).toNat
abbrev pos₀ : Nat := (s₀.gpr .r2).toNat
abbrev op : BitVec 32 := s₀.gpr .r3
abbrev outn : Nat := (stackArg s₀ 0).toNat
abbrev scr : BitVec 32 := stackArg s₀ 1
abbrev stA : Addr := State.addr (st s₀)
abbrev oA : Addr := State.addr (op s₀)
abbrev SR : Region := ⟨stA s₀, 200⟩
abbrev OR : Region := ⟨oA s₀, outn s₀⟩
abbrev CR : Region := ⟨State.addr (scr s₀), 640⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 8⟩
/-- The initial state. -/
abbrev S₀ : Spec.Sha3.State := stateAt s₀.mem (stA s₀)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [SR s₀, OR s₀, CR s₀]
  st_o : (SR s₀).Disjoint (OR s₀)
  st_c : (SR s₀).Disjoint (CR s₀)
  o_c : (OR s₀).Disjoint (CR s₀)
  a_st : (argR s₀).Disjoint (SR s₀)
  a_o : (argR s₀).Disjoint (OR s₀)
  a_c : (argR s₀).Disjoint (CR s₀)
  st_fit : (s₀.gpr .r0).toNat + 200 ≤ 2 ^ 32
  o_fit : (s₀.gpr .r3).toNat + outn s₀ ≤ 2 ^ 32
  c_fit : (scr s₀).toNat + 640 ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32
  rate : rt s₀ ∈ rates
  pos_le : pos₀ s₀ ≤ rt s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.squeezeArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem Pre.rate_pos {s₀ : State} (hp : Pre s₀) :
    0 < rt s₀ ∧ rt s₀ ≤ 200 ∧ 72 ≤ (s₀.gpr .r1).toNat ∧ (s₀.gpr .r1).toNat ≤ 168 := by
  have h : 72 ≤ (s₀.gpr .r1).toNat ∧ (s₀.gpr .r1).toNat ≤ 168 := Proof.Sha3.rate_bounds hp.rate
  show 0 < (s₀.gpr .r1).toNat ∧ (s₀.gpr .r1).toNat ≤ 200 ∧ _
  omega

theorem Pre.arg {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 2) :
    InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 :=
  ⟨argR s₀, by simp [hp.rd], arg_in (n := 2) hp.sp_fit hk⟩

theorem outn_lt (s₀ : State) : outn s₀ < 2 ^ 32 := (stackArg s₀ 0).isLt

/-! ## The loop invariant -/

/-- After `i` bytes of output, `k` permutations and `pos` bytes of the
current block: `pos₀ + i = rate * k + pos`. -/
structure Inv (s₀ : State) (i k pos : Nat) (s : State) : Prop where
  i_le : i ≤ outn s₀
  hi : pos₀ s₀ + i = rt s₀ * k + pos
  pos_le : pos ≤ rt s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r0 : s.gpr .r0 = st s₀
  r1 : s.gpr .r1 = scr s₀
  r4 : s.gpr .r4 = s₀.gpr .r1
  r5 : s.gpr .r5 = BitVec.ofNat 32 pos
  r6 : s.gpr .r6 = op s₀ + BitVec.ofNat 32 i
  r7 : s.gpr .r7 = BitVec.ofNat 32 (outn s₀ - i)
  hi8 : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], s.gpr r = s₀.gpr r
  frame : Frame [SR s₀, OR s₀, CR s₀] s₀.mem s.mem
  saved : SSaved (scr s₀) s₀.gpr s.mem
  state : stateAt s.mem (stA s₀) = iterF k (S₀ s₀)
  out : ∀ j < i, s.mem (oA s₀ + BitVec.ofNat 64 j) =
    byteOf (iterF ((pos₀ s₀ + j) / rt s₀) (S₀ s₀)) ((pos₀ s₀ + j) % rt s₀)

theorem Inv.of_flags {s₀ : State} {i k pos : Nat} {s s' : State} (h : Inv s₀ i k pos s)
    (u : Fupd s s') : Inv s₀ i k pos s' where
  i_le := h.i_le
  hi := h.hi
  pos_le := h.pos_le
  rd := u.rd.trans h.rd
  wr := u.wr.trans h.wr
  sp := u.sp.trans h.sp
  r0 := by rw [u.gpr]; exact h.r0
  r1 := by rw [u.gpr]; exact h.r1
  r4 := by rw [u.gpr]; exact h.r4
  r5 := by rw [u.gpr]; exact h.r5
  r6 := by rw [u.gpr]; exact h.r6
  r7 := by rw [u.gpr]; exact h.r7
  hi8 := fun r hr => by rw [u.gpr]; exact h.hi8 r hr
  frame := by rw [u.mem]; exact h.frame
  saved := by rw [u.mem]; exact h.saved
  state := by rw [u.mem]; exact h.state
  out := by rw [u.mem]; exact h.out

/-! ## The prologue -/

theorem setup_eq : setup = .ldrSp .r12 4 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++
    ([.mov .r4 (.reg .r1), .mov .r1 (.reg .r12), .mov .r5 (.reg .r2), .mov .r6 (.reg .r3),
      .ldrSp .r7 0, .cmp .r7 (.imm 0)] : List Instr)) := rfl

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block setup) s₀ fun s => Inv s₀ 0 0 (pos₀ s₀) s ∧ s.z = decide (outn s₀ = 0) := by
  have fC := hp.c_fit
  rw [setup_eq]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (hp.arg (by omega)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = scr s₀ := u₁.gpr
  refine saveA_ok saved s₁ _ (fun p hp' => ⟨(ssaved_ok p hp').2.2.1, ?_⟩)
    fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · rw [u₁.wr, h12, hp.wr]
    exact ⟨CR s₀, by simp, contains_A fC (by have := ssaved_ok p hp'; omega)⟩
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ => ?_
  have hm : s₆.mem = saveMemA s₀.mem (scr s₀) s₁.gpr saved := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem, h12]
  have hf : Frame [regR (scr s₀) 640] s₀.mem s₆.mem := by
    rw [hm]; exact saveMemA_frame fC _ _ _ fun p hp' => by have := ssaved_ok p hp'; omega
  have ha : s₆.mem.readW (stackArgAddr s₀ 0) 32 = stackArg s₀ 0 :=
    hf.readW (r := ⟨stackArgAddr s₀ 0, 4⟩) (Region.contains_self _ _)
      (by simpa using hp.a_c.sub_left (Region.sub_prefix (by omega))) (by decide)
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide)
    (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]
        exact hp.arg (by omega)) fun s₇ u₇ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₈ u₈ hz => WP.block_nil ?_
  have g : ∀ r, r ≠ .r12 → r ≠ .r4 → r ≠ .r1 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₈.gpr r = s₀.gpr r :=
    fun r h12 h4 h1 h5 h6 h7 => by
      rw [u₈.gpr, u₇.other r h7, u₆.other r h6, u₅.other r h5, u₄.other r h1, u₃.other r h4, g₂,
        u₁.other r h12]
  have h7 : s₈.gpr .r7 = stackArg s₀ 0 := by rw [u₈.gpr, u₇.gpr, ha]
  have hsf : stateAt s₈.mem (stA s₀) = S₀ s₀ := by
    rw [u₈.mem, u₇.mem]
    exact stateAt_congr fun i hi =>
      hf.bytes (R := SR s₀) (by simpa using hp.st_c.sub_right (Region.sub_prefix (Nat.le_refl _)))
        (by simp) hi
  refine ⟨{
    i_le := Nat.zero_le _, hi := (by omega), pos_le := hp.pos_le, rd := ?_, wr := ?_, sp := ?_,
    r0 := g .r0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    r1 := ?_, r4 := ?_, r5 := ?_, r6 := ?_,
    r7 := (by rw [h7, Nat.sub_zero]; exact (ofNat_toNat32 _).symm), hi8 := fun r hr => ?_,
    frame := ?_, saved := ?_, state := hsf, out := fun j hj => absurd hj (Nat.not_lt_zero _) }, ?_⟩
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  · rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), g₂, h12]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide)]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
    exact (ofNat_toNat32 _).symm
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
    rw [BitVec.add_zero]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [u₈.mem, u₇.mem]; exact hf.mono (by simp)
  · rw [u₈.mem, u₇.mem, hm]
    exact (saveMemA_ssaved _ fC _).of_gpr fun r hr => u₁.other r hr
  · rw [hz, u₇.gpr, ha]; simp only [sub_imm0]; rw [beq_zero32]

/-! ## One iteration -/

theorem hi_ok : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∈ preserved ∧ r ≠ .lr ∧ r ≠ .r5 := by decide

/-- A permutation, at the end of a block. -/
theorem permute_ok {s₀ : State} (hp : Pre s₀) {i k : Nat} {s : State} (hI : Inv s₀ i k (rt s₀) s) :
    WP isa (.seq (.block [.mov .r5 (.imm 0)]) permuteCall) s (Inv s₀ i (k + 1) 0) := by
  have hn := outn_lt s₀
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil ?_)
  refine call_ok (st := st s₀) (scr := scr s₀) (by rw [u₂.other _ (by decide), hI.r0])
    (by rw [u₂.other _ (by decide), hI.r1]) hp.st_fit (by have := hp.c_fit; omega)
    (hp.st_c.sub_right (Region.sub_prefix (by omega)))
    (by rw [u₂.wr, hI.wr, hp.wr]; exact covers_of (N := 640) (by omega) (by simp) (by simp))
    fun s₃ rd₃ wr₃ sp₃ cs₃ r0₃ r1₃ f₃ e₃ => ?_
  have hd : ∀ r ∈ [regR (st s₀) 200, regR (scr s₀) 512], (OR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.st_o.symm
    · exact hp.o_c.sub_right (Region.sub_prefix (by omega))
  refine {
    i_le := hI.i_le, hi := (by rw [hI.hi, Nat.mul_succ]; rfl), pos_le := Nat.zero_le _,
    rd := rd₃.trans (u₂.rd.trans hI.rd), wr := wr₃.trans (u₂.wr.trans hI.wr),
    sp := sp₃.trans (u₂.sp.trans hI.sp), r0 := r0₃, r1 := r1₃, r4 := ?_, r5 := ?_, r6 := ?_, r7 := ?_,
    hi8 := fun r hr => ?_, frame := ?_, saved := ?_, state := ?_, out := fun j hj => ?_ }
  · rw [cs₃ _ (by decide) (by decide), u₂.other _ (by decide), hI.r4]
  · rw [cs₃ _ (by decide) (by decide), u₂.gpr]; rfl
  · rw [cs₃ _ (by decide) (by decide), u₂.other _ (by decide), hI.r6]
  · rw [cs₃ _ (by decide) (by decide), u₂.other _ (by decide), hI.r7]
  · rw [cs₃ r (hi_ok r hr).1 (hi_ok r hr).2.1, u₂.other r (hi_ok r hr).2.2]; exact hI.hi8 r hr
  · refine hI.frame.trans ?_
    rw [← u₂.mem]
    refine f₃.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨SR s₀, by simp, fun _ h => h⟩
    · exact ⟨CR s₀, by simp, Region.sub_prefix (by omega)⟩
  · exact SSaved.frame hp.c_fit hp.st_c (by rw [u₂.mem]; exact hI.saved) f₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      exact hr
  · rw [e₃, u₂.mem, hI.state, iterF_succ]
  · refine Eq.trans (f₃.bytes (R := OR s₀) hd (by simp; omega)
      (by have := hI.i_le; omega : j < outn s₀)) ?_
    rw [u₂.mem]; exact hI.out j hj

theorem store_regs : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∉ [Reg.r3, .r2, .r6, .r5, .r7] := by decide

/-- Copying one byte of the state to the output. -/
theorem store_ok {s₀ : State} (hp : Pre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hlt : pos < rt s₀) (hi : i < outn s₀) :
    WP isa (.block [.dp .add .r3 .r0 (.reg .r5), .ldrb .r2 .r3 0, .strb .r2 .r6 0,
      .dp .add .r6 .r6 (.imm 1), .dp .add .r5 .r5 (.imm 1), .subs .r7 .r7 (.imm 1)]) s fun s' =>
      Inv s₀ (i + 1) k (pos + 1) s' ∧ s'.z = decide (outn s₀ - (i + 1) = 0) := by
  have ⟨hr0, hr200, _, hr168⟩ := hp.rate_pos
  have hn := outn_lt s₀
  have fS : (st s₀).toNat + 200 ≤ 2 ^ 32 := hp.st_fit
  have fO : (op s₀).toNat + outn s₀ ≤ 2 ^ 32 := hp.o_fit
  have fC := hp.c_fit
  have hpos : pos < 200 := by omega
  refine wp_add (op2_reg _ _) fun s₁ u₁ => ?_
  have ea : State.addr (s₁.gpr .r3 + BitVec.ofNat 32 0) = stA s₀ + BitVec.ofNat 64 pos := by
    rw [u₁.gpr, hI.r0, hI.r5, BitVec.add_zero]
    exact addr_add (by omega)
  refine wp_ldrb (a := stA s₀ + BitVec.ofNat 64 pos) (by decide) ea
    ⟨SR s₀, by simp [u₁.rd, u₁.wr, hI.rd, hI.wr, hp.rd, hp.wr], contains_offset (by omega) (by omega)⟩
    fun s₂ u₂ => ?_
  refine wp_strb (a := oA s₀ + BitVec.ofNat 64 i) (by decide)
    (by rw [u₂.other .r6 (by decide), u₁.other .r6 (by decide), hI.r6, BitVec.add_zero]
        exact addr_add (by omega))
    ⟨OR s₀, by simp [u₂.wr, u₁.wr, hI.wr, hp.wr], contains_offset (by omega) (by omega)⟩
    fun s₃ g₃ => ?_
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_subs (op2_imm (by decide)) fun s₆ u₆ hz => WP.block_nil ?_
  have g : ∀ r, r ∉ [Reg.r3, .r2, .r6, .r5, .r7] → s₆.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h3, h2, h6, h5, h7⟩ := hr
    rw [u₆.other r h7, u₅.other r h5, u₄.other r h6, g₃.gpr, u₂.other r h2, u₁.other r h3]
  have hb : s.mem (stA s₀ + BitVec.ofNat 64 pos) = byteOf (iterF k (S₀ s₀)) pos := by
    rw [← hI.state, byteOf_stateAt _ _ (by omega)]
  have hm : s₆.mem = s.mem.writeW (oA s₀ + BitVec.ofNat 64 i) (byteOf (iterF k (S₀ s₀)) pos) := by
    rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.gpr, u₂.mem, u₁.mem,
      BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq, hb]
  have hfw : Frame [OR s₀] s.mem s₆.mem := by
    rw [hm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))
  have h7 : s₅.gpr .r7 = BitVec.ofNat 32 (outn s₀ - i) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r7]
  have e1 : BitVec.ofNat 32 (outn s₀ - i) - 1 = BitVec.ofNat 32 (outn s₀ - (i + 1)) := by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat32 (by omega), Nat.sub_sub]
  refine ⟨{
    i_le := (by omega), hi := (by have := hI.hi; omega), pos_le := (by omega), rd := ?_, wr := ?_,
    sp := ?_, r0 := (by rw [g .r0 (by decide), hI.r0]), r1 := (by rw [g .r1 (by decide), hI.r1]),
    r4 := (by rw [g .r4 (by decide), hI.r4]), r5 := ?_, r6 := ?_, r7 := (by rw [u₆.gpr, h7, e1]),
    hi8 := fun r hr => (by rw [g r (store_regs r hr)]; exact hI.hi8 r hr),
    frame := hI.frame.trans (hfw.mono (by simp)), saved := ?_, state := ?_, out := fun j hj => ?_ },
    by rw [hz, h7, e1, ofNat32_beq_zero (by omega)]⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, hI.sp]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r5, ofNat32_succ]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r6, BitVec.add_assoc, ofNat32_succ]
  · refine hI.saved.keep fun d hd₁ hd₂ => hfw.readW (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    rw [List.mem_singleton.mp hr]
    refine hp.o_c.symm.sub_left ?_
    rw [A_eq (by omega)]; exact sub_offset (by omega) (by omega)
  · rw [stateAt_congr fun j hj => hfw.bytes (R := SR s₀) (by simpa using hp.st_o) (by simp) hj]
    exact hI.state
  · rw [hm]
    by_cases e : j = i
    · subst e
      obtain ⟨d, m⟩ := div_mod_eq (k := k) hr0 hlt
      rw [writeW8_self, hI.hi, d, m]
    · rw [writeW8_other _ _ (by intro h'; apply e; bv_omega)]
      exact hI.out j (by omega)

/-- The whole body. -/
theorem body_ok {s₀ : State} (hp : Pre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hi : i < outn s₀) :
    WP isa squeezeBody s fun s' =>
      ∃ k' pos', Inv s₀ (i + 1) k' pos' s' ∧ s'.z = decide (outn s₀ - (i + 1) = 0) := by
  have ⟨hr0, _, _, hr168⟩ := hp.rate_pos
  unfold squeezeBody
  refine WP.seq (wp_cmp (op2_reg _ _) fun s₁ u₁ hz => WP.block_nil ?_)
  have hI₁ := hI.of_flags u₁
  have hz' : s₁.z = decide (pos = rt s₀) := by
    rw [hz, hI.r5, hI.r4, sub_beq_zero32 (by have := hI.pos_le; omega)]
  refine WP.seq (WP.mono (Q := fun s => ∃ k' pos', Inv s₀ i k' pos' s ∧ pos' < rt s₀) ?_
    fun s₂ ⟨k', pos', hI₂, hlt⟩ => WP.mono (store_ok hp hI₂ hlt hi) fun s' h => ⟨k', pos' + 1, h⟩)
  refine WP.ite (decide (pos = rt s₀)) (by show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz'])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    exact WP.mono (permute_ok hp hI₁) fun s' h => ⟨k + 1, 0, h, hr0⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil (M := isa) ⟨k, pos, hI₁, by have := hI.pos_le; omega⟩

/-! ## The epilogue -/

/-- The epilogue's postcondition. -/
def Post (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.squeezeArm.post s₀ s'

theorem hi_not_saved : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∉ saved.map Prod.fst ∧ r ≠ .r0 := by decide

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {k pos : Nat} {s : State}
    (hI : Inv s₀ (outn s₀) k pos s) : WP isa (.block epilogue) s (Post s₀) := by
  have ⟨hr0, hr200, _, hr168⟩ := hp.rate_pos
  have fC := hp.c_fit
  have hpl := hI.pos_le
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  rw [restore_eq, ← List.append_nil (saved.map _)]
  refine restoreA_ok saved s₁ _ (by decide) (fun p hp' => ⟨(ssaved_ok p hp').1, (ssaved_ok p hp').2.2.1,
    ?_⟩) fun s' ho hr hm => WP.block_nil ⟨fun r hr' => ?_, ?_, ?_, fun d => ?_⟩
  · rw [u₁.rd, u₁.wr, u₁.other .r1 (by decide), hI.rd, hI.wr, hI.r1, hp.wr]
    exact ⟨CR s₀, by simp, contains_A fC (by have := ssaved_ok p hp'; omega)⟩
  · rcases preserved_cases r hr' with ⟨p, hp', rfl⟩ | hr''
    · rw [ho p hp', u₁.other .r1 (by decide), hI.r1, u₁.mem]; exact hI.saved p hp'
    · rw [hr r (hi_not_saved r hr'').1, u₁.other r (hi_not_saved r hr'').2]; exact hI.hi8 r hr''
  · show bytesAt s'.mem (oA s₀) (outn s₀) =
      Spec.Sha3.squeezeFrom (rt s₀) (S₀ s₀) (pos₀ s₀) (outn s₀)
    rw [hm, u₁.mem]
    refine List.ext_getElem (by rw [length_squeezeFrom hr0 hr200]; simp [bytesAt]) fun j h₁ _ => ?_
    have hj : j < outn s₀ := by simpa [bytesAt] using h₁
    rw [squeezeFrom_getElem hr0 hr200 _ hj]
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    exact hI.out j hj
  · rw [hr .r0 (by decide), u₁.gpr, hI.r5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hpl
  · show Spec.Sha3.squeezeFrom (rt s₀) (stateAt s'.mem (stA s₀)) (s'.gpr .r0).toNat d =
      Spec.Sha3.squeezeFrom (rt s₀) (S₀ s₀) (pos₀ s₀ + outn s₀) d
    rw [hm, u₁.mem, hI.state, hr .r0 (by decide), u₁.gpr, hI.r5, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), squeezeFrom_iterF hr0 hr200, ← hI.hi]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa squeeze s₀ (Post s₀) := by
  have hl := outn_lt s₀
  unfold squeeze
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ k pos, Inv s₀ (outn s₀) k pos s) ?_
    fun s₂ ⟨k, pos, hI₂⟩ => epilogue_ok hp hI₂)
  refine WP.ite (decide (outn s₀ = 0)) (by show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (M := isa) ⟨0, pos₀ s₀, hb ▸ hI⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa)
      (fun n s => ∃ i k pos, n = outn s₀ - i ∧ i < outn s₀ ∧ Inv s₀ i k pos s) ?_ (outn s₀) s₁
      ⟨0, 0, pos₀ s₀, by omega, by omega, hI⟩
    rintro n s ⟨i, k, pos, rfl, hi, hI⟩
    refine WP.mono (body_ok hp hI hi) fun s' ⟨k', pos', hI', hz'⟩ => ?_
    by_cases he : outn s₀ - (i + 1) = 0
    · refine .inl ⟨by show VG.Arm.eval .ne s' = _; rw [eval_ne, hz', decide_eq_true he]; rfl,
        k', pos', ?_⟩
      rwa [show i + 1 = outn s₀ by omega] at hI'
    · exact .inr ⟨by show VG.Arm.eval .ne s' = _; rw [eval_ne, hz', decide_eq_false he]; rfl,
        outn s₀ - (i + 1), by omega, i + 1, k', pos', rfl, by omega, hI'⟩

/-! ## Constant time -/

/-- The initial taint: the register arguments are public, `r0` points at the
state, and the 8 bytes of stack arguments are public, the second one
pointing at the scratch space. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [200, 0, 640], bases := [(.r0, 0)],
    argLen := 8, argBases := [(4, 2)] }

theorem wf₀ {s : State} (h : Proof.Sha3.squeezeArm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hp := pre_of h
  have hst := hp.st_fit; have hso := hp.o_fit; have hsc := hp.c_fit
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩, ?_, fun _ => ⟨hp.sp_fit, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true]
    exact ⟨⟨hp.st_o, hp.st_c⟩, hp.o_c⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    simp [VG.Arm.Taint.region, hp.wr]
  · have e : (⟨State.addr s.sp, 8⟩ : Region) = argR s := by simp [stackArgAddr]
    simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.a_st
    · exact hp.a_o
    · exact hp.a_c
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.squeezeArm.pre s₁) (h₂ : Proof.Sha3.squeezeArm.pre s₂)
    (hpub : Proof.Sha3.squeezeArm.pub s₁ s₂) : VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0, a1⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [SR, OR, CR, stA, oA, outn, scr, st, op, p0, p3, a0, a1]
  · simp only [τ₀] at hk
    rw [argByte_eq hp₁.sp_fit hk, argByte_eq hp₂.sp_fit hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : k / 4 = 0 ∨ k / 4 = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

/-- A state satisfying the precondition (with no output, and the scratch space at 0). -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 72 | .r3 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x4000, 8⟩]
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩, ⟨0, 640⟩]

theorem squeeze_verified : Verified Arm.target squeeze Proof.Sha3.squeezeArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · exact VG.Taint.constantTime (A := VG.Arm.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
      (by taint_decide)
  · have e : ∀ k, stackArg sat k = 0 := fun k => by
      simp [stackArg, sat, Mem.readW, Mem.read]
    refine ⟨sat, ?_⟩
    simp only [Proof.Sha3.squeezeArm, e]
    refine ⟨by simp [sat, stackArgAddr]; decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide,
      by decide, by decide, by decide, by decide⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, sat, stackArgAddr, State.addr] at h₁ h₂
      bv_omega

end VG.Proof.Sha3.Arm.Stream.Squeeze
