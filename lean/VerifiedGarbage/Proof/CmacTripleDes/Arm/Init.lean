import VerifiedGarbage.Proof.CmacTripleDes.Arm.Update
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Keys

/-!
# TDEA-CMAC on ARMv7: `vg_cmac_triple_des_init`

Untrusted: everything here is checked by Lean. `initPre` saves the
registers and stores the three DES keys, as the high and low words of
big-endian integers, at bytes `[88, 112)` of the scratch buffer; each
iteration of the loop then writes one DES key's sixteen round keys
(`KInv`); the zero block is encrypted with them and doubled twice, a word
at a time, into the subkeys.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.CmacTripleDes.Arm VG.Proof.CmacTripleDes VG.Proof.Cmac
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr op2_lsl wp_mov wp_add wp_sub wp_and wp_orr
  wp_subs wp_cmp wp_ldr wp_str wp_rev saveMem saveList_ok sub_beq)

/-! ## Words -/

/-- A round key's words: the high one's upper half is zero. -/
theorem append_of_hi (hi lo : BitVec 32) (h : hi >>> 16 = 0) :
    hi ++ lo = (hi.setWidth 16 ++ lo).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro q hq
  rw [BitVec.getLsbD_append, BitVec.getLsbD_setWidth, decide_eq_true hq, Bool.true_and, BitVec.getLsbD_append]
  by_cases h32 : q < 32
  · rw [ite_eq_left h32, ite_eq_left h32]
  · rw [ite_eq_right h32, ite_eq_right h32, BitVec.getLsbD_setWidth]
    by_cases h48 : q - 32 < 16
    · rw [decide_eq_true h48, Bool.true_and]
    · rw [decide_eq_false h48, Bool.false_and]
      have := congrArg (fun x => x.getLsbD (q - 48)) h
      simp only [BitVec.getLsbD_ushiftRight] at this
      rw [show 16 + (q - 48) = q - 32 by omega] at this
      exact this.trans (by simp)

/-- Shifting the 64-bit integer `hi:lo` left by one, a word at a time. -/
theorem shl_append (hi lo : BitVec 32) : (hi <<< 1 ||| lo >>> 31) ++ lo <<< 1 = (hi ++ lo) <<< 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  have h64 : i < 64 := by omega
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight]
  by_cases h0 : i = 0
  · subst h0; simp
  by_cases h32 : i < 32
  · simp [h32, h0, h64, show i - 1 < 32 by omega]
  by_cases h32' : i = 32
  · subst h32'; simp
  · have h1 : ¬ (i - 1 < 32) := by omega
    have h2 : ¬ (31 + (i - 32) < 32) := by omega
    simp [h32, h1, h0, h64, show i - 32 < 32 by omega, show i - 1 - 32 = i - 32 - 1 by omega,
      show ¬ (i - 32 < 1) by omega, BitVec.getLsbD_of_ge lo (31 + (i - 32)) (by omega)]

theorem shr31 (x : BitVec 32) : x >>> 31 = if x.msb then 1 else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, BitVec.msb_eq_getLsbD_last]
  by_cases h0 : i = 0
  · subst h0; split <;> simp_all
  · rw [BitVec.getLsbD_of_ge x _ (by omega)]
    split <;> simp [BitVec.getLsbD_one, BitVec.getLsbD_zero, h0]

/-- `dbl` doubles `hi:lo` (`dbl64`). -/
theorem dbl_append (hi lo : BitVec 32) :
    (hi <<< 1 ||| lo >>> 31) ++ (lo <<< 1 ^^^ (((0 : BitVec 32) - (hi >>> 31)) &&& (0x1b : BitVec 32))) =
      dbl64 (hi ++ lo) := by
  have hm : (hi ++ lo).msb = hi.msb := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_append]; simp
  have hc : ((0 : BitVec 32) - (if hi.msb then (1 : BitVec 32) else 0)) &&& (0x1b : BitVec 32) =
      if hi.msb then 0x1b else 0 := by split <;> rfl
  rw [dbl64, hm, ← shl_append, shr31 hi, hc]
  split
  · rw [show (0x1b : BitVec 64) = (0 : BitVec 32) ++ (0x1b : BitVec 32) from rfl, BitVec.xor_append]
    simp
  · rw [show (0 : BitVec 64) = (0 : BitVec 32) ++ (0 : BitVec 32) from rfl, BitVec.xor_append]
    simp

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev K : BitVec 32 := s₀.gpr .r0
abbrev Kl : Nat := (s₀.gpr .r1).toNat
abbrev O : BitVec 32 := s₀.gpr .r2
abbrev Sc : BitVec 32 := s₀.gpr .r3

abbrev ikeyR : Region := ⟨State.addr (K s₀), Kl s₀⟩
abbrev outR : Region := ⟨State.addr (O s₀), 400⟩
abbrev iscrR : Region := ⟨State.addr (Sc s₀), 640⟩

/-- The key's bytes. -/
abbrev keyB : List Byte := Spec.Aes.bytesAt s₀.mem (State.addr (K s₀)) (Kl s₀)

/-- DES key `j`, as a big-endian integer. -/
abbrev kw (j : Nat) : BitVec 64 :=
  byteRev64 (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 (keyOff (Kl s₀) j)) 64)

/-- What the function changes after saving the registers. -/
abbrev ichg : List Region :=
  [⟨State.addr (Sc s₀), 52⟩, ⟨State.addr (Sc s₀) + BitVec.ofNat 64 88, 28⟩, outR s₀]

end

/-- The precondition, by name. -/
structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [ikeyR s₀]
  wr : s₀.wr = [outR s₀, iscrR s₀]
  key_out : (ikeyR s₀).Disjoint (outR s₀)
  key_scr : (ikeyR s₀).Disjoint (iscrR s₀)
  out_scr : (outR s₀).Disjoint (iscrR s₀)
  key_fit : (K s₀).toNat + Kl s₀ ≤ 2 ^ 32
  out_fit : (O s₀).toNat + 400 ≤ 2 ^ 32
  scr_fit : (Sc s₀).toNat + 640 ≤ 2 ^ 32
  valid : Kl s₀ = 16 ∨ Kl s₀ = 24

theorem IPre.of {s₀ : State} (h : initArm.pre s₀) : IPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨a, b, c, d, e, f, g, h, i⟩

/-- After the round keys of `i` DES keys. -/
structure KInv (s₀ : State) (i : Nat) (s : State) : Prop where
  r10 : s.gpr .r10 = Sc s₀
  r4 : s.gpr .r4 = Sc s₀ + BitVec.ofNat 32 (88 + 8 * i)
  r2 : s.gpr .r2 = O s₀ + BitVec.ofNat 32 (128 * i)
  r5 : s.gpr .r5 = BitVec.ofNat 32 (3 - i)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keys : ∀ j < 3, s.mem.readW (State.addr (Sc s₀) + BitVec.ofNat 64 (88 + 8 * j)) 32 ++
    s.mem.readW (State.addr (Sc s₀) + BitVec.ofNat 64 (92 + 8 * j)) 32 = kw s₀ j
  sched : ∀ n < 16 * i, s.mem.readW (State.addr (O s₀) + BitVec.ofNat 64 (8 * n)) 64 =
    (Spec.TripleDes.expandKey (keyB s₀)).getD n 0
  frame : Frame [⟨State.addr (Sc s₀) + BitVec.ofNat 64 88, 24⟩, ⟨State.addr (O s₀), 384⟩]
    (savedMem s₀ (Sc s₀)) s.mem

/-! ## Regions -/

theorem keyOff_le {s₀ : State} (hp : IPre s₀) {j : Nat} (hj : j < 3) : keyOff (Kl s₀) j + 8 ≤ Kl s₀ := by
  simp only [keyOff]; rcases hp.valid with h | h <;> rw [h] <;> split <;> omega

section
variable {s₀ : State} (hp : IPre s₀)
include hp

theorem IPre.inScr {d n : Nat} (h : d + n ≤ 640) (hn : 0 < n) :
    InRegions s₀.wr (State.addr (Sc s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := iscrR s₀) (by simp) (Offset.contains_base _ h (by have := hp.scr_fit; omega))

theorem IPre.inOut {d n : Nat} (h : d + n ≤ 400) (hn : 0 < n) :
    InRegions s₀.wr (State.addr (O s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := outR s₀) (by simp) (Offset.contains_base _ h (by have := hp.out_fit; omega))

theorem IPre.inKey {d n : Nat} (h : d + n ≤ Kl s₀) (hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (K s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := ikeyR s₀) (by simp) (Offset.contains_base _ h (by have := hp.key_fit; omega))

theorem IPre.scrAddr {d : Nat} (h : d < 640) :
    State.addr (Sc s₀ + BitVec.ofNat 32 d) = State.addr (Sc s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.scr_fit; omega)

theorem IPre.keyAddr {d : Nat} (h : d < Kl s₀) :
    State.addr (K s₀ + BitVec.ofNat 32 d) = State.addr (K s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.key_fit; omega)

/-- The key is unchanged while only the scratch buffer changes. -/
theorem IPre.keyRead {m : Mem} (hf : Frame [iscrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ Kl s₀) :
    m.readW (State.addr (K s₀) + BitVec.ofNat 64 d) 32 = s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨State.addr (K s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.key_scr.sub_left (Offset.sub_base _ hd)) (by decide)

omit hp in
/-- DES key `j` from its two words. -/
theorem kw_eq (j : Nat) :
    rev (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 (keyOff (Kl s₀) j)) 32) ++
      rev (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 (keyOff (Kl s₀) j + 4)) 32) = kw s₀ j := by
  rw [rev_eq, rev_eq, byteRev32_append, kw, readW64_split, Offset.add_add]

end

/-! ## The prologue -/

/-- A word of the key, byte-reversed, to the scratch buffer. -/
theorem keyWord_wp {s₀ : State} (hp : IPre s₀) {s : State} {d o : Nat} {rest : List Instr} {Q : State → Prop}
    (hd : d + 4 ≤ Kl s₀) (hd' : d < 4096) (ho : o + 4 ≤ 640)
    (h0 : s.gpr .r0 = K s₀) (h10 : s.gpr .r10 = Sc s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hf : Frame [iscrR s₀] s₀.mem s.mem)
    (k : ∀ s', (∀ r, r ≠ .r4 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = s.mem.writeW (State.addr (Sc s₀) + BitVec.ofNat 64 o)
        (rev (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 d) 32)) → WP isa (.block rest) s' Q) :
    WP isa (.block (keyWord d o ++ rest)) s Q := by
  show WP isa (.block (.ldr .r4 .r0 d :: .rev .r4 .r4 :: .str .r4 .r10 o :: rest)) s Q
  refine wp_ldr hd' (by rw [h0, hp.keyAddr (by omega)]) (by rw [hrd, hwr]; exact hp.inKey hd (by decide))
    fun s₁ u₁ => wp_rev fun s₂ u₂ => ?_
  refine wp_str (by omega) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h10, hp.scrAddr (by omega)])
    (by rw [u₂.wr, u₁.wr, hwr]; exact hp.inScr ho (by decide)) fun s₃ w₃ => k s₃ (fun r hr => ?_)
    (by rw [w₃.rd, u₂.rd, u₁.rd]) (by rw [w₃.wr, u₂.wr, u₁.wr]) (by rw [w₃.sp, u₂.sp, u₁.sp]) ?_
  · rw [w₃.gpr, u₂.other _ hr, u₁.other _ hr]
  · rw [w₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, hp.keyRead hf hd]

/-- A byte offset of the scratch buffer in its bytes `[88, 112)`. -/
theorem keysC {S : Addr} {d : Nat} (h₁ : 88 ≤ d) (h₂ : d + 4 ≤ 112) :
    (⟨S + BitVec.ofNat 64 88, 24⟩ : Region).Contains (S + BitVec.ofNat 64 d) (32 / 8) := by
  rw [show S + BitVec.ofNat 64 d = S + BitVec.ofNat 64 88 + BitVec.ofNat 64 (d - 88) from
    (Offset.add_add_eq _ (by omega)).symm]
  exact Offset.contains_base _ (by omega) (by omega)

theorem initPre_wp {s₀ : State} (hp : IPre s₀) : WP isa initPre s₀ (KInv s₀ 0) := by
  have sf := hp.scr_fit
  have sf' : (s₀.gpr .r3).toNat + 640 ≤ 2 ^ 32 := hp.scr_fit
  have kl : 16 ≤ Kl s₀ := by rcases hp.valid with h | h <;> omega
  rw [show initPre = .seq (.block (saved.map (fun p => Instr.str p.1 .r3 p.2) ++
      (mov .r10 .r3 :: (keyWord 0 88 ++ (keyWord 4 92 ++ (keyWord 8 96 ++ (keyWord 12 100 ++
        ([.cmp .r1 (.imm 16)] : List Instr))))))))
      (.seq (.ite .eq (.block [.ldr .r4 .r0 0, .ldr .r5 .r0 4]) (.block [.ldr .r4 .r0 16, .ldr .r5 .r0 20]))
        (.block [.rev .r4 .r4, .rev .r5 .r5, .str .r4 .r10 104, .str .r5 .r10 108,
          .dp .add .r4 .r10 (.imm 88), .mov .r5 (.imm 3)])) from rfl]
  refine WP.seq ?_
  refine saveList_ok saved s₀ _ (fun p hp' => ?_) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · have hb := saved_bound p hp'
    exact ⟨by omega, by omega, hp.inScr (by omega) (by decide)⟩
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => ?_
  have m₂ : s₂.mem = savedMem s₀ (Sc s₀) := by rw [u₂.mem, m₁]; rfl
  have g₂ : ∀ r, r ≠ .r10 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [u₂.other _ hr, g₁]
  have r10₂ : s₂.gpr .r10 = Sc s₀ := by rw [u₂.gpr, g₁]
  have rd₂ : s₂.rd = s₀.rd := by rw [u₂.rd, rd₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, wr₁]
  have sp₂ : s₂.sp = s₀.sp := by rw [u₂.sp, sp₁]
  have sv : Frame [iscrR s₀] s₀.mem (savedMem s₀ (Sc s₀)) := (savedMem_frame s₀ (Sc s₀)).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨iscrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  have scrC : ∀ d, d + 4 ≤ 640 → (iscrR s₀).Contains (State.addr (Sc s₀) + BitVec.ofNat 64 d) (32 / 8) :=
    fun d hd => Offset.contains_base _ hd (by omega)
  -- The four words of the first two DES keys.
  refine keyWord_wp hp (by omega) (by decide) (by decide) (g₂ _ (by decide)) r10₂ rd₂ wr₂ (by rw [m₂]; exact sv)
    fun s₃ g₃ rd₃ wr₃ sp₃ m₃ => ?_
  have F₃ : Frame [iscrR s₀] s₀.mem s₃.mem := by
    rw [m₃, m₂]; exact sv.writeW (List.mem_singleton_self _) _ (scrC 88 (by decide))
  refine keyWord_wp hp (by omega) (by decide) (by decide) (by rw [g₃ _ (by decide), g₂ _ (by decide)])
    (by rw [g₃ _ (by decide), r10₂]) (by rw [rd₃, rd₂]) (by rw [wr₃, wr₂]) F₃ fun s₄ g₄ rd₄ wr₄ sp₄ m₄ => ?_
  have F₄ : Frame [iscrR s₀] s₀.mem s₄.mem := by
    rw [m₄]; exact F₃.writeW (List.mem_singleton_self _) _ (scrC 92 (by decide))
  refine keyWord_wp hp (by omega) (by decide) (by decide)
    (by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide)]) (by rw [g₄ _ (by decide), g₃ _ (by decide), r10₂])
    (by rw [rd₄, rd₃, rd₂]) (by rw [wr₄, wr₃, wr₂]) F₄ fun s₅ g₅ rd₅ wr₅ sp₅ m₅ => ?_
  have F₅ : Frame [iscrR s₀] s₀.mem s₅.mem := by
    rw [m₅]; exact F₄.writeW (List.mem_singleton_self _) _ (scrC 96 (by decide))
  refine keyWord_wp hp (by omega) (by decide) (by decide)
    (by rw [g₅ _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide)])
    (by rw [g₅ _ (by decide), g₄ _ (by decide), g₃ _ (by decide), r10₂])
    (by rw [rd₅, rd₄, rd₃, rd₂]) (by rw [wr₅, wr₄, wr₃, wr₂]) F₅ fun s₆ g₆ rd₆ wr₆ sp₆ m₆ => ?_
  have F₆ : Frame [iscrR s₀] s₀.mem s₆.mem := by
    rw [m₆]; exact F₅.writeW (List.mem_singleton_self _) _ (scrC 100 (by decide))
  have g₆' : ∀ r, r ≠ .r4 → r ≠ .r10 → s₆.gpr r = s₀.gpr r := fun r h4 h10 => by
    rw [g₆ _ h4, g₅ _ h4, g₄ _ h4, g₃ _ h4, g₂ _ h10]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, rd₄, rd₃, rd₂]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄, wr₃, wr₂]
  have sp₆' : s₆.sp = s₀.sp := by rw [sp₆, sp₅, sp₄, sp₃, sp₂]
  refine wp_cmp (op2_imm (by decide)) fun s₇ f₇ z₇ => WP.block_nil ?_
  have r1 : s₀.gpr .r1 = BitVec.ofNat 32 (Kl s₀) := by simp [Kl]
  have ev : isa.eval .eq s₇ = some (decide (Kl s₀ = 16)) := by
    show some s₇.z = _
    rw [z₇, g₆' _ (by decide) (by decide), r1, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      sub_beq (s₀.gpr .r1).isLt (by decide)]
  -- The third DES key.
  have third : ∀ d, d + 8 ≤ Kl s₀ → d + 4 < 4096 →
      WP isa (.block [.ldr .r4 .r0 d, .ldr .r5 .r0 (d + 4)]) s₇ fun s₈ =>
        s₈.gpr .r4 = s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 d) 32 ∧
        s₈.gpr .r5 = s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 (d + 4)) 32 ∧
        (∀ r, r ≠ .r4 → r ≠ .r5 → s₈.gpr r = s₇.gpr r) ∧ s₈.mem = s₆.mem ∧ s₈.rd = s₀.rd ∧
        s₈.wr = s₀.wr ∧ s₈.sp = s₀.sp := by
    intro d hd hl
    have r0₇ : s₇.gpr .r0 = K s₀ := by rw [f₇.gpr, g₆' _ (by decide) (by decide)]
    refine wp_ldr (by omega) (by rw [r0₇, hp.keyAddr (by omega)])
      (by rw [f₇.rd, f₇.wr, rd₆', wr₆']; exact hp.inKey (by omega) (by decide)) fun s₈ u₈ => ?_
    refine wp_ldr (by omega) (by rw [u₈.other _ (by decide), r0₇, hp.keyAddr (by omega)])
      (by rw [u₈.rd, u₈.wr, f₇.rd, f₇.wr, rd₆', wr₆']; exact hp.inKey (by omega) (by decide))
      fun s₉ u₉ => WP.block_nil ⟨?_, ?_, fun r h4 h5 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₉.other _ (by decide), u₈.gpr, f₇.mem, hp.keyRead F₆ (by omega)]
    · rw [u₉.gpr, u₈.mem, f₇.mem, hp.keyRead F₆ (by omega)]
    · rw [u₉.other _ h5, u₈.other _ h4]
    · rw [u₉.mem, u₈.mem, f₇.mem]
    · rw [u₉.rd, u₈.rd, f₇.rd, rd₆']
    · rw [u₉.wr, u₈.wr, f₇.wr, wr₆']
    · rw [u₉.sp, u₈.sp, f₇.sp, sp₆']
  refine WP.seq (WP.mono (Q := fun (s₈ : State) =>
      s₈.gpr .r4 = s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 (keyOff (Kl s₀) 2)) 32 ∧
      s₈.gpr .r5 = s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 (keyOff (Kl s₀) 2 + 4)) 32 ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → s₈.gpr r = s₇.gpr r) ∧ s₈.mem = s₆.mem ∧ s₈.rd = s₀.rd ∧
      s₈.wr = s₀.wr ∧ s₈.sp = s₀.sp) ?_ fun s₈ h₈ => ?_)
  · by_cases h16 : Kl s₀ = 16
    · refine WP.ite true (by rw [ev]; simp [h16]) (fun _ => ?_) (fun h => by cases h)
      have := third 0 (by omega) (by decide)
      rwa [show keyOff (Kl s₀) 2 = 0 by simp [keyOff, h16]]
    · refine WP.ite false (by rw [ev]; simp [h16]) (fun h => by cases h) (fun _ => ?_)
      have h24 : Kl s₀ = 24 := by rcases hp.valid with h | h <;> omega
      have := third 16 (by omega) (by decide)
      rwa [show keyOff (Kl s₀) 2 = 16 by simp [keyOff, h24]]
  obtain ⟨ax₄, ax₅, g₈, m₈, rd₈, wr₈, sp₈⟩ := h₈
  have r10₈ : s₈.gpr .r10 = Sc s₀ := by
    rw [g₈ _ (by decide) (by decide), f₇.gpr, g₆ _ (by decide), g₅ _ (by decide), g₄ _ (by decide),
      g₃ _ (by decide), r10₂]
  refine wp_rev fun s₉ u₉ => wp_rev fun s₁₀ u₁₀ => ?_
  have r10₁₀ : s₁₀.gpr .r10 = Sc s₀ := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), r10₈]
  refine wp_str (a := State.addr (Sc s₀) + BitVec.ofNat 64 104) (by decide) (by rw [r10₁₀, hp.scrAddr (by decide)])
    (by rw [u₁₀.wr, u₉.wr, wr₈]; exact hp.inScr (by decide) (by decide)) fun s₁₁ w₁₁ => ?_
  refine wp_str (a := State.addr (Sc s₀) + BitVec.ofNat 64 108) (by decide)
    (by rw [w₁₁.gpr, r10₁₀, hp.scrAddr (by decide)])
    (by rw [w₁₁.wr, u₁₀.wr, u₉.wr, wr₈]; exact hp.inScr (by decide) (by decide)) fun s₁₂ w₁₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₁₃ u₁₃ => wp_mov (op2_imm (by decide)) fun s₁₄ u₁₄ => WP.block_nil ?_
  have mem₁₄ : s₁₄.mem = ((((((savedMem s₀ (Sc s₀)).writeW (State.addr (Sc s₀) + BitVec.ofNat 64 88)
      (rev (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 0) 32))).writeW
      (State.addr (Sc s₀) + BitVec.ofNat 64 92) (rev (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 4) 32))).writeW
      (State.addr (Sc s₀) + BitVec.ofNat 64 96) (rev (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 8) 32))).writeW
      (State.addr (Sc s₀) + BitVec.ofNat 64 100)
        (rev (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 12) 32))).writeW
      (State.addr (Sc s₀) + BitVec.ofNat 64 104)
        (rev (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 (keyOff (Kl s₀) 2)) 32))).writeW
      (State.addr (Sc s₀) + BitVec.ofNat 64 108)
        (rev (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 (keyOff (Kl s₀) 2 + 4)) 32)) := by
    rw [u₁₄.mem, u₁₃.mem, w₁₂.mem, w₁₁.mem, w₁₁.gpr, u₁₀.gpr, u₁₀.other .r4 (by decide), u₉.gpr,
      u₁₀.mem, u₉.mem, u₉.other .r5 (by decide), ax₄, ax₅, m₈, m₆, m₅, m₄, m₃, m₂]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun n hn => absurd hn (by omega), ?_⟩
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), w₁₂.gpr, w₁₁.gpr, r10₁₀]
  · rw [u₁₄.other _ (by decide), u₁₃.gpr, w₁₂.gpr, w₁₁.gpr, r10₁₀]; rfl
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), w₁₂.gpr, w₁₁.gpr, u₁₀.other _ (by decide),
      u₉.other _ (by decide), g₈ _ (by decide) (by decide), f₇.gpr, g₆' _ (by decide) (by decide), add0]
  · rw [u₁₄.gpr]; rfl
  · rw [u₁₄.sp, u₁₃.sp, w₁₂.sp, w₁₁.sp, u₁₀.sp, u₉.sp, sp₈]
  · rw [u₁₄.rd, u₁₃.rd, w₁₂.rd, w₁₁.rd, u₁₀.rd, u₉.rd, rd₈]
  · rw [u₁₄.wr, u₁₃.wr, w₁₂.wr, w₁₁.wr, u₁₀.wr, u₉.wr, wr₈]
  · rw [mem₁₄, ← kw_eq (s₀ := s₀) j]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · rw [show keyOff (Kl s₀) 0 = 0 by simp [keyOff]]
      simp (disch := decide) only [readW_writeW_far, Mem.readW_writeW_self32]
    · rw [show keyOff (Kl s₀) 1 = 8 by simp [keyOff]]
      simp (disch := decide) only [readW_writeW_far, Mem.readW_writeW_self32]
    · simp (disch := decide) only [readW_writeW_far, Mem.readW_writeW_self32]
  · rw [mem₁₄]
    have c : ∀ d, 88 ≤ d → d + 4 ≤ 112 → (⟨State.addr (Sc s₀) + BitVec.ofNat 64 88, 24⟩ : Region).Contains
        (State.addr (Sc s₀) + BitVec.ofNat 64 d) (32 / 8) := fun d h₁ h₂ => keysC h₁ h₂
    exact ((((((Frame.refl _ _).writeW (by simp) _ (c 88 (by decide) (by decide))).writeW (by simp) _
      (c 92 (by decide) (by decide))).writeW (by simp) _ (c 96 (by decide) (by decide))).writeW (by simp) _
      (c 100 (by decide) (by decide))).writeW (by simp) _ (c 104 (by decide) (by decide))).writeW (by simp) _
      (c 108 (by decide) (by decide))

/-! ## The round keys -/

theorem keyStep_ok {s₀ : State} (hp : IPre s₀) {i : Nat} (hi : i < 3) {s : State} (h : KInv s₀ i s) :
    WP isa (.block keysBody) s fun s' => KInv s₀ (i + 1) s' ∧ s'.z = decide (3 - (i + 1) = 0) := by
  have sf := hp.scr_fit
  have of := hp.out_fit
  have rdwr : s.rd ++ s.wr = [ikeyR s₀, outR s₀, iscrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have scrIn : ∀ d, d + 4 ≤ 640 → InRegions (s.rd ++ s.wr) (State.addr (Sc s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact in_rw (r := iscrR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  rw [keysBody, List.append_assoc]
  refine wp_ldr (a := State.addr (Sc s₀) + BitVec.ofNat 64 (88 + 8 * i)) (by decide)
    (by rw [h.r4, add0, hp.scrAddr (by omega)]) (scrIn _ (by omega)) fun s₁ u₁ => ?_
  refine wp_ldr (a := State.addr (Sc s₀) + BitVec.ofNat 64 (92 + 8 * i)) (by decide)
    (by rw [u₁.other _ (by decide), h.r4, Straight.add_ofNat_ofNat, hp.scrAddr (by omega),
      show 88 + 8 * i + 4 = 92 + 8 * i by omega])
    (by rw [u₁.rd, u₁.wr]; exact scrIn _ (by omega)) fun s₂ u₂ => ?_
  have ax₂ : s₂.gpr .r0 ++ s₂.gpr .r1 = kw s₀ i := by
    rw [u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, h.keys i hi]
  have g₂ : ∀ r, r ≠ .r0 → r ≠ .r1 → s₂.gpr r = s.gpr r := fun r h0 h1 => by rw [u₂.other _ h1, u₁.other _ h0]
  have r2₂ : s₂.gpr .r2 = O s₀ + BitVec.ofNat 32 (128 * i) := by rw [g₂ _ (by decide) (by decide), h.r2]
  have wr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr, h.wr]
  have oA : State.addr (O s₀ + BitVec.ofNat 32 (128 * i)) = State.addr (O s₀) + BitVec.ofNat 64 (128 * i) :=
    addr_add (by omega)
  have r2n : (O s₀ + BitVec.ofNat 32 (128 * i)).toNat = (O s₀).toNat + 128 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have wA : ∀ k < 32, wordAddr (s₂.gpr .r2) k = State.addr (O s₀) + BitVec.ofNat 64 (128 * i + 4 * k) :=
    fun k hk => by
      rw [r2₂, wordAddr_eq _ (by rw [r2n]; omega), oA, Offset.add_add]
  have hok : Ok kCfg s₂ := by
    refine ⟨fun k hk => ?_, fun k hk => absurd hk (by simp [kCfg]), ?_, fun k _ j hj => absurd hj (by simp [kCfg])⟩
    · rw [show kCfg.base = .r2 from rfl, wA k hk, wr₂]
      exact hp.inOut (by simp only [kCfg] at hk; omega) (by decide)
    · show (s₂.gpr .r2).toNat + 4 * 32 ≤ 2 ^ 32
      rw [r2₂, r2n]; omega
  obtain ⟨s₃, run₃, rk₃, hi₃, rd₃, wr₃, sp₃, g₃, f₃⟩ := roundKeys_ok hok
  show WP isa (.block (roundKeys ++ ([.dp .add .r2 .r2 (.imm 128), .dp .add .r4 .r4 (.imm 8),
    .subs .r5 .r5 (.imm 1)] : List Instr))) s₂ _
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_subs (op2_imm (by decide)) fun s₆ u₆ z₆ => WP.block_nil ?_
  have gk : ∀ r, r ∉ kWrites → r ≠ .r0 → r ≠ .r1 → s₃.gpr r = s.gpr r := fun r hk h0 h1 => by
    rw [g₃ r hk, g₂ r h0 h1]
  have slotR : slotRegion kCfg s₂ = ⟨State.addr (O s₀) + BitVec.ofNat 64 (128 * i), 128⟩ := by
    simp only [slotRegion]; rw [show kCfg.base = .r2 from rfl, r2₂, oA]; rfl
  rw [slotR, u₂.mem, u₁.mem] at f₃
  have m₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  have r5₃ : s₃.gpr .r5 = BitVec.ofNat 32 (3 - i) := by rw [gk _ (by decide) (by decide) (by decide), h.r5]
  have dec : BitVec.ofNat 32 (3 - i) - 1 = BitVec.ofNat 32 (3 - (i + 1)) := ofNat_sub_one (by omega) (by omega)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun n hn => ?_, ?_⟩, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      gk _ (by decide) (by decide) (by decide), h.r10]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), gk _ (by decide) (by decide) (by decide), h.r4,
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, Straight.add_ofNat_ofNat,
      show 88 + 8 * i + 8 = 88 + 8 * (i + 1) by omega]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, gk _ (by decide) (by decide) (by decide), h.r2,
      show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, Straight.add_ofNat_ofNat,
      show 128 * i + 128 = 128 * (i + 1) by omega]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), r5₃, dec]
  · rw [u₆.sp, u₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp, h.sp]
  · rw [u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd, h.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, wr₃, wr₂]
  · rw [m₆, ← h.keys j hj]
    have keep : ∀ d, 88 ≤ d → d + 4 ≤ 112 → s₃.mem.readW (State.addr (Sc s₀) + BitVec.ofNat 64 d) 32 =
        s.mem.readW (State.addr (Sc s₀) + BitVec.ofNat 64 d) 32 := fun d h₁ h₂ => by
      rw [f₃.readW (r := ⟨State.addr (Sc s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.out_scr.sub_left (Offset.sub_base _ (by omega))).symm.sub_left (Offset.sub_base _ (by omega)))
        (by decide)]
    rw [keep _ (by omega) (by omega), keep _ (by omega) (by omega)]
  · rw [m₆]
    by_cases hn' : n < 16 * i
    · rw [← h.sched n hn', f₃.readW (r := ⟨State.addr (O s₀) + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)]
    · obtain ⟨j, rfl⟩ : ∃ j, n = 16 * i + j := ⟨n - 16 * i, by omega⟩
      have hj : j < 16 := by omega
      have hk := keyOff_le hp hi
      rw [readW64_split, Offset.add_add, show 8 * (16 * i + j) + 4 = 128 * i + 4 * (2 * j + 1) by omega,
        ← wA (2 * j + 1) (by omega), show 8 * (16 * i + j) = 128 * i + 4 * (2 * j) by omega, ← wA (2 * j) (by omega),
        append_of_hi _ _ (hi₃ j hj), rk₃ j hj, ax₂, kw, expandKey_getD _ hi hj, Proof.Cmac.bytesAt_length,
        decode_bytesAt _ _ hk]
  · rw [m₆]
    exact h.frame.trans (f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr (O s₀), 384⟩, by simp, Offset.sub_base _ (by omega)⟩)
  · rw [z₆, u₅.other _ (by decide), u₄.other _ (by decide), r5₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      sub_beq (by omega) (by decide)]
    simp only [decide_eq_decide]; omega

theorem keys_ok {s₀ : State} (hp : IPre s₀) {s : State} (h : KInv s₀ 0 s) :
    WP isa (.loop (.block keysBody) .ne) s (KInv s₀ 3) := by
  refine WP.loop (M := isa) (body := .block keysBody) (c := .ne) (Q := KInv s₀ 3)
    (fun (n : Nat) (t : State) => ∃ i, n = 3 - i ∧ i < 3 ∧ KInv s₀ i t) ?_ 3 s ⟨0, rfl, by decide, h⟩
  rintro n t ⟨i, rfl, hi, ht⟩
  refine WP.mono (keyStep_ok hp hi ht) fun t' ⟨h', z'⟩ => ?_
  by_cases hz : i + 1 = 3
  · left
    refine ⟨by rw [eval_ne, z']; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [eval_ne, z']; simp; omega, 3 - (i + 1), by omega, i + 1, rfl, by omega, h'⟩

/-! ## The subkeys -/

/-- `dbl d` doubles `r0:r1` and stores it, as bytes, at `[r2 + d]`. -/
theorem dbl_wp {s : State} {d : Nat} {a : Addr} {rest : List Instr} {Q : State → Prop} (hd : d + 4 < 4096)
    (ha : State.addr (s.gpr .r2 + BitVec.ofNat 32 d) = a)
    (ha4 : State.addr (s.gpr .r2 + BitVec.ofNat 32 (d + 4)) = a + BitVec.ofNat 64 4)
    (w0 : InRegions s.wr a 4) (w4 : InRegions s.wr (a + BitVec.ofNat 64 4) 4)
    (k : ∀ s', s'.gpr .r0 ++ s'.gpr .r1 = dbl64 (s.gpr .r0 ++ s.gpr .r1) →
      s'.mem = (s.mem.writeW a (rev (s'.gpr .r0))).writeW (a + BitVec.ofNat 64 4) (rev (s'.gpr .r1)) →
      (∀ r, r ∉ [Reg.r0, .r1, .r3, .r4] → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      WP isa (.block rest) s' Q) :
    WP isa (.block (dbl d ++ rest)) s Q := by
  show WP isa (.block (.mov .r3 (.shifted .r0 .lsr 31) :: .mov .r4 (.imm 0) :: .dp .sub .r3 .r4 (.reg .r3) ::
    .dp .and .r3 .r3 (.imm 0x1b) :: .mov .r4 (.shifted .r1 .lsr 31) :: .mov .r0 (.shifted .r0 .lsl 1) ::
    .dp .orr .r0 .r0 (.reg .r4) :: .mov .r1 (.shifted .r1 .lsl 1) :: .dp .eor .r1 .r1 (.reg .r3) ::
    .rev .r3 .r0 :: .str .r3 .r2 d :: .rev .r3 .r1 :: .str .r3 .r2 (d + 4) :: rest)) s Q
  refine wp_mov (op2_lsr (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_sub (op2_reg _ _) fun s₃ u₃ => wp_and (op2_imm (by decide)) fun s₄ u₄ =>
    wp_mov (op2_lsr (by decide)) fun s₅ u₅ => wp_mov (op2_lsl (by decide)) fun s₆ u₆ =>
    wp_orr (op2_reg _ _) fun s₇ u₇ => wp_mov (op2_lsl (by decide)) fun s₈ u₈ =>
    wp_eor (op2_reg _ _) fun s₉ u₉ => wp_rev fun s₁₀ u₁₀ => ?_
  have g₁₀ : ∀ r, r ∉ [Reg.r0, .r1, .r3, .r4] → s₁₀.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₁₀.other _ hr.2.2.1, u₉.other _ hr.2.1, u₈.other _ hr.2.1, u₇.other _ hr.1, u₆.other _ hr.1,
      u₅.other _ hr.2.2.2, u₄.other _ hr.2.2.1, u₃.other _ hr.2.2.1, u₂.other _ hr.2.2.2, u₁.other _ hr.2.2.1]
  have m₁₀ : s₁₀.mem = s.mem := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have wr₁₀ : s₁₀.wr = s.wr := by
    rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have r2₁₀ : s₁₀.gpr .r2 = s.gpr .r2 := g₁₀ _ (by decide)
  refine wp_str (by omega) (by rw [r2₁₀, ha]) (by rw [wr₁₀]; exact w0) fun s₁₁ w₁₁ => wp_rev fun s₁₂ u₁₂ => ?_
  refine wp_str (by omega) (by rw [u₁₂.other _ (by decide), w₁₁.gpr, r2₁₀, ha4])
    (by rw [u₁₂.wr, w₁₁.wr, wr₁₀]; exact w4) fun s₁₃ w₁₃ => ?_
  have r0f : s₁₃.gpr .r0 = s₉.gpr .r0 := by
    rw [w₁₃.gpr, u₁₂.other _ (by decide), w₁₁.gpr, u₁₀.other _ (by decide)]
  have r1f : s₁₃.gpr .r1 = s₉.gpr .r1 := by
    rw [w₁₃.gpr, u₁₂.other _ (by decide), w₁₁.gpr, u₁₀.other _ (by decide)]
  refine k s₁₃ ?_ ?_ (fun r hr => ?_) ?_ ?_ ?_
  · have a3 : s₈.gpr .r3 = ((0 : BitVec 32) - (s.gpr .r0 >>> 31)) &&& (0x1b : BitVec 32) := by
      rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
        u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr]
    have a0 : s₉.gpr .r0 = s.gpr .r0 <<< 1 ||| s.gpr .r1 >>> 31 := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₆.other _ (by decide), u₅.gpr,
        u₅.other _ (by decide), u₄.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
        u₁.other _ (by decide)]
    have a1 : s₉.gpr .r1 = s.gpr .r1 <<< 1 ^^^ (((0 : BitVec 32) - (s.gpr .r0 >>> 31)) &&& (0x1b : BitVec 32)) := by
      rw [u₉.gpr, a3, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    rw [r0f, r1f, a0, a1, dbl_append]
  · rw [w₁₃.mem, u₁₂.mem, w₁₁.mem, m₁₀, u₁₂.gpr, w₁₁.gpr, u₁₀.gpr, u₁₀.other _ (by decide), r0f, r1f]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [w₁₃.gpr, u₁₂.other _ hr.2.2.1, w₁₁.gpr, g₁₀ _ (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
  · rw [w₁₃.rd, u₁₂.rd, w₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [w₁₃.wr, u₁₂.wr, w₁₁.wr, wr₁₀]
  · rw [w₁₃.sp, u₁₂.sp, w₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initArm.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ initArm.post s₀ s' := by
  have hp := IPre.of h0
  have sf := hp.scr_fit
  have of := hp.out_fit
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (keys_ok hp h₁) fun s₂ h₂ => ?_)
  have rdwr₂ : s₂.rd ++ s₂.wr = [ikeyR s₀, outR s₀, iscrR s₀] := by rw [h₂.rd, h₂.wr, hp.rd, hp.wr]; rfl
  -- The key schedule is in place.
  have hsch₂ : Spec.TripleDes.scheduleAt s₂.mem (State.addr (O s₀)) = Spec.TripleDes.expandKey (keyB s₀) := by
    apply Vector.ext
    intro n hn
    rw [← vgetD _ hn 0, ← vgetD _ hn 0, scheduleAt_getD _ _ hn, h₂.sched n (by omega)]
  refine WP.seq ?_
  refine wp_str (a := State.addr (Sc s₀) + BitVec.ofNat 64 112) (by decide) (by rw [h₂.r10, hp.scrAddr (by decide)])
    (by rw [h₂.wr]; exact hp.inScr (by decide) (by decide)) fun s₃ w₃ => ?_
  refine wp_sub (op2_imm (by decide)) fun s₄ u₄ => wp_mov (op2_imm (by decide)) fun s₅ u₅ =>
    wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have g₆ : ∀ r, r ∉ [Reg.r0, .r1, .r9] → s₆.gpr r = s₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.1, u₅.other _ hr.1, u₄.other _ hr.2.2, w₃.gpr]
  have r9₆ : s₆.gpr .r9 = O s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, w₃.gpr, h₂.r2,
      show (384 : BitVec 32) = BitVec.ofNat 32 (128 * 3) from rfl, BitVec.add_sub_cancel]
  have r10₆ : s₆.gpr .r10 = Sc s₀ := by rw [g₆ _ (by decide), h₂.r10]
  have ax₆ : s₆.gpr .r0 ++ s₆.gpr .r1 = (0 : BitVec 64) := by rw [u₆.other _ (by decide), u₅.gpr, u₆.gpr]; rfl
  have m₆ : s₆.mem = s₂.mem.writeW (State.addr (Sc s₀) + BitVec.ofNat 64 112) (O s₀ + BitVec.ofNat 32 384) := by
    rw [u₆.mem, u₅.mem, u₄.mem, w₃.mem, h₂.r2]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, w₃.rd, h₂.rd]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, w₃.wr, h₂.wr]
  have c112 : (iscrR s₀).Contains (State.addr (Sc s₀) + BitVec.ofNat 64 112) (32 / 8) :=
    Offset.contains_base _ (by decide) (by omega)
  have F₆ : Frame [iscrR s₀] s₂.mem s₆.mem := by
    rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c112
  have outScr : ∀ r ∈ [iscrR s₀], (⟨State.addr (O s₀), 384⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.out_scr.sub_left (Region.sub_prefix (by decide))
  have hsch₆ : sch s₆ = Spec.TripleDes.expandKey (keyB s₀) := by
    show Spec.TripleDes.scheduleAt s₆.mem (State.addr (s₆.gpr .r9)) = _
    rw [r9₆, scheduleAt_frame F₆ outScr, hsch₂]
  have bp : BlockPre s₆ :=
    { sched := ⟨400, by rw [r9₆, rd₆, wr₆, hp.rd, hp.wr]; simp, by decide, by rw [r9₆]; exact of⟩
      scr := ⟨640, by rw [r10₆, wr₆, hp.wr]; simp, by decide, by rw [r10₆]; exact sf⟩
      disj := by
        rw [r9₆, r10₆]
        exact (hp.out_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (block_ok bp) fun s₇ ⟨same₇, r9₇, ax₇⟩ => ?_)
  rw [ax₆, hsch₆] at ax₇
  have r10₇ : s₇.gpr .r10 = Sc s₀ := by rw [same₇.r10, r10₆]
  have xR₆ : xR s₆ = ⟨State.addr (Sc s₀), 52⟩ := by rw [xR, r10₆]
  have f₇ : Frame [⟨State.addr (Sc s₀), 52⟩] s₆.mem s₇.mem := by rw [← xR₆]; exact same₇.frame
  have wr₇ : s₇.wr = s₀.wr := by rw [same₇.wr, wr₆]
  have rd₇ : s₇.rd = s₀.rd := by rw [same₇.rd, rd₆]
  show WP isa (.block (.ldr .r2 .r10 112 :: (dbl 0 ++ (dbl 8 ++ restore)))) s₇ _
  refine wp_ldr (a := State.addr (Sc s₀) + BitVec.ofNat 64 112) (by decide) (by rw [r10₇, hp.scrAddr (by decide)])
    (by rw [rd₇, wr₇, hp.rd, hp.wr]
        exact in_rw (r := iscrR s₀) (by simp) (Offset.contains_base _ (by decide) (by omega))) fun s₈ u₈ => ?_
  have r2₈ : s₈.gpr .r2 = O s₀ + BitVec.ofNat 32 384 := by
    rw [u₈.gpr, f₇.readW (r := ⟨State.addr (Sc s₀) + BitVec.ofNat 64 112, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by decide) (by omega)) (by decide), m₆, Mem.readW_writeW_self32]
  have oA : ∀ d, d < 16 → State.addr (O s₀ + BitVec.ofNat 32 384 + BitVec.ofNat 32 d) =
      State.addr (O s₀) + BitVec.ofNat 64 (384 + d) := fun d hd => by
    rw [Straight.add_ofNat_ofNat, addr_add (by omega)]
  have wO : ∀ d, d + 4 ≤ 16 → InRegions s₈.wr (State.addr (O s₀) + BitVec.ofNat 64 (384 + d)) 4 := fun d hd => by
    rw [u₈.wr, wr₇]; exact hp.inOut (by omega) (by decide)
  have a4 : ∀ d, State.addr (O s₀) + BitVec.ofNat 64 (384 + d) + BitVec.ofNat 64 4 =
      State.addr (O s₀) + BitVec.ofNat 64 (384 + d + 4) := fun d => Offset.add_add _ _ _
  refine dbl_wp (a := State.addr (O s₀) + BitVec.ofNat 64 (384 + 0)) (by decide) (by rw [r2₈, oA 0 (by decide)])
    (by rw [r2₈, oA 4 (by decide), a4]) (wO 0 (by decide)) (by rw [a4]; exact wO 4 (by decide))
    fun s₉ ax₉ m₉ g₉ rd₉ wr₉ sp₉ => ?_
  refine dbl_wp (a := State.addr (O s₀) + BitVec.ofNat 64 (384 + 8)) (by decide)
    (by rw [g₉ _ (by decide), r2₈, oA 8 (by decide)]) (by rw [g₉ _ (by decide), r2₈, oA 12 (by decide), a4])
    (by rw [wr₉]; exact wO 8 (by decide)) (by rw [wr₉, a4]; exact wO 12 (by decide))
    fun s₁₀ ax₁₀ m₁₀ g₁₀ rd₁₀ wr₁₀ sp₁₀ => ?_
  have r10₁₀ : s₁₀.gpr .r10 = Sc s₀ := by rw [g₁₀ _ (by decide), g₉ _ (by decide), u₈.other _ (by decide), r10₇]
  have rdwr₁₀ : s₁₀.rd ++ s₁₀.wr = [ikeyR s₀, outR s₀, iscrR s₀] := by
    rw [rd₁₀, wr₁₀, rd₉, wr₉, u₈.rd, u₈.wr, same₇.rd, same₇.wr, u₆.rd, u₅.rd, u₄.rd, w₃.rd, u₆.wr, u₅.wr, u₄.wr,
      w₃.wr, rdwr₂]
  -- What changed since the registers were saved.
  have oC : ∀ d, d + 4 ≤ 16 → (outR s₀).Contains (State.addr (O s₀) + BitVec.ofNat 64 (384 + d)) (32 / 8) :=
    fun d hd => Offset.contains_base _ (by omega) (by omega)
  have F₁₀ : Frame (ichg s₀) (savedMem s₀ (Sc s₀)) s₁₀.mem := by
    have F₂ : Frame (ichg s₀) (savedMem s₀ (Sc s₀)) s₂.mem := h₂.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr (Sc s₀) + BitVec.ofNat 64 88, 28⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨outR s₀, by simp, Region.sub_prefix (by decide)⟩
    have F₆' : Frame (ichg s₀) (savedMem s₀ (Sc s₀)) s₆.mem := by
      rw [m₆]
      refine F₂.writeW (r := ⟨State.addr (Sc s₀) + BitVec.ofNat 64 88, 28⟩) (by simp) _ ?_
      rw [show State.addr (Sc s₀) + BitVec.ofNat 64 112 = State.addr (Sc s₀) + BitVec.ofNat 64 88 +
        BitVec.ofNat 64 (112 - 88) from (Offset.add_add_eq _ (by omega)).symm]
      exact Offset.contains_base _ (by decide) (by decide)
    have F₇ : Frame (ichg s₀) (savedMem s₀ (Sc s₀)) s₇.mem :=
      F₆'.trans (f₇.mono fun r hr => by simp at hr; simp [hr])
    rw [m₁₀, m₉, u₈.mem, a4, a4]
    exact (((F₇.writeW (by simp) _ (oC 0 (by decide))).writeW (by simp) _ (oC 4 (by decide))).writeW (by simp) _
      (oC 8 (by decide))).writeW (by simp) _ (oC 12 (by decide))
  refine WP.mono (restore_ok r10₁₀ (by omega) fun d h₁' h₂' => by
      rw [rdwr₁₀]; exact in_rw (r := iscrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    fun s' ⟨hl, sp', m', _, _⟩ => ⟨restored (S := Sc s₀) (fun d h₁' h₂' => ?_) hl ?_, ?_, ?_⟩
  · refine F₁₀.readW (r := ⟨State.addr (Sc s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact (hp.out_scr.sub_right (Offset.sub_base _ (by omega))).symm
  · rw [sp', sp₁₀, sp₉, u₈.sp, same₇.sp, u₆.sp, u₅.sp, u₄.sp, w₃.sp, h₂.sp]
  -- The key schedule.
  · show Spec.TripleDes.scheduleAt s'.mem (State.addr (O s₀)) = Spec.TripleDes.expandKey (keyB s₀)
    rw [m', ← hsch₂]
    refine scheduleAt_frame (rs := [iscrR s₀, ⟨State.addr (O s₀) + BitVec.ofNat 64 384, 16⟩]) ?_ fun r hr => ?_
    · have c : ∀ d, d + 4 ≤ 16 → (⟨State.addr (O s₀) + BitVec.ofNat 64 384, 16⟩ : Region).Contains
          (State.addr (O s₀) + BitVec.ofNat 64 (384 + d)) (32 / 8) := fun d hd => by
        rw [← Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
      rw [m₁₀, m₉, u₈.mem, a4, a4]
      exact ((((F₆.mono (by simp)).trans (f₇.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨iscrR s₀, by simp, Region.sub_prefix (by decide)⟩)).writeW (by simp) _ (c 0 (by decide))).writeW
        (by simp) _ (c 4 (by decide))).writeW (by simp) _ (c 8 (by decide)) |>.writeW (by simp) _ (c 12 (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.out_scr.sub_left (Region.sub_prefix (by decide))
      · exact Offset.base_disjoint _ (by decide) (by omega)
  -- The subkeys.
  · show Spec.Aes.bytesAt s'.mem (State.addr (O s₀) + BitVec.ofNat 64 384) 16 =
      (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (keyB s₀))) 8).1 ++
        (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (keyB s₀))) 8).2
    rw [subkeys_tdes, m', bytesAt_split, ← le8_readW, ← le8_readW, readW64_split, readW64_split, m₁₀, m₉, u₈.mem]
    simp (disch := decide) only [Offset.add_add, readW_writeW_far, Mem.readW_writeW_self32]
    rw [rev_eq, rev_eq, rev_eq, rev_eq, byteRev32_append, byteRev32_append, ax₁₀, ax₉,
      u₈.other .r0 (by decide), u₈.other .r1 (by decide), ax₇]

end VG.Proof.CmacTripleDes.Arm
