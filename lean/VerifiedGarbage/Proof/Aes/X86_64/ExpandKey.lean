import VerifiedGarbage.Impl.Aes.X86_64.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Ctr32
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Aes.Contract

/-!
# The AES key expansion on x86-64

Untrusted: everything here is checked by Lean.

`subAll` (`toBs`, the S-box, `fromBs`) applies the S-box to every byte of
the eight words (`subAll_wp`, from the bitsliced layers' lemmas); each
word of the schedule is then a few scalar instructions around it
(`word_ok`), and the loop over the words keeps the schedule's bytes so far
equal to the specification's (`WInv`).
-/

namespace VG.Proof.Aes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Aes.X86_64 VG.Proof.Aes
open VG.Spec.Aes (sbox xtimes subBytes subWord rotWord rcon xorWord)

/-! ## The S-box on every byte -/

/-- The four states that the words hold, as `InRel` relates them. -/
def stOf (Q : Nat → BitVec 64) (b : Nat) : Spec.Aes.State :=
  Vector.ofFn fun i => (Q (b + 4 * (i.1 / 8))).extractLsb' (8 * (i.1 % 8)) 8

theorem inRel_stOf (Q : Nat → BitVec 64) : InRel Q (stOf Q) := by
  intro b hb i hi j hj
  rw [getD_eq _ hi, stOf, Vector.getElem_ofFn, BitVec.getLsbD_extractLsb']
  simp [hj]

theorem subAll_wp {s : State} (hok : Ok linCfg s) {P : State → Prop}
    (h : ∀ s', (∀ k < 8, ∀ t < 8, (Q s' k).extractLsb' (8 * t) 8 = sbox ((Q s k).extractLsb' (8 * t) 8)) →
      s'.rd = s.rd → s'.wr = s.wr → (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) →
      Frame [⟨s.gpr sb, 8 * 48⟩] s.mem s'.mem → P s') :
    WP isa (.block subAll) s P := by
  simp only [subAll]
  repeat rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₁, hs₁, h₁, rd₁, wr₁, o₁, f₁⟩ := toBs_ok hok
  refine WP.of_runBlock ⟨s₁, hs₁, ?_⟩
  have hb₁ : s₁.gpr sb = s.gpr sb := o₁ sb (by decide)
  have ok₁ : Ok linCfg s₁ := hok.congr hb₁ hb₁ rd₁ wr₁
  obtain ⟨s₂, hs₂, h₂, rd₂, wr₂, o₂, f₂⟩ := sbox_ok (s := s₁) ok₁
  refine WP.of_runBlock ⟨s₂, hs₂, ?_⟩
  have hb₂ : s₂.gpr sb = s.gpr sb := (o₂ sb (by decide)).trans hb₁
  have ok₂ : Ok linCfg s₂ := hok.congr hb₂ hb₂ (rd₂.trans rd₁) (wr₂.trans wr₁)
  obtain ⟨s₃, hs₃, h₃, rd₃, wr₃, o₃, f₃⟩ := fromBs_ok ok₂
  refine WP.of_runBlock ⟨s₃, hs₃, ?_⟩
  have hin := in_of_bs h₃ (bs_subBytes h₂ (bs_of_in h₁ (inRel_stOf (Q s))))
  refine h s₃ (fun k hk t ht => ?_) (rd₃.trans (rd₂.trans rd₁)) (wr₃.trans (wr₂.trans wr₁))
    (fun r hr => (o₃ r hr).trans ((o₂ r hr).trans (o₁ r hr))) ?_
  · refine byte_ext fun j hj => ?_
    have := hin (k % 4) (by omega) (t + 8 * (k / 4)) (by omega) j hj
    rw [show k % 4 + 4 * ((t + 8 * (k / 4)) / 8) = k by omega,
      show 8 * ((t + 8 * (k / 4)) % 8) + j = 8 * t + j by omega] at this
    rw [BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and, this, getD_eq _ (by omega)]
    simp only [subBytes, Vector.getElem_map, stOf, Vector.getElem_ofFn]
    rw [show k % 4 + 4 * ((t + 8 * (k / 4)) / 8) = k by omega,
      show (t + 8 * (k / 4)) % 8 = t by omega]
  · have e₁ : slotRegion linCfg s = ⟨s.gpr sb, 8 * 48⟩ := rfl
    have e₂ : slotRegion sboxCfg s₁ = ⟨s.gpr sb, 8 * 48⟩ := by
      simp only [slotRegion, sboxCfg, hb₁]
    have e₃ : slotRegion linCfg s₂ = ⟨s.gpr sb, 8 * 48⟩ := by
      simp only [slotRegion, linCfg, hb₂]
    rw [e₁] at f₁; rw [e₂] at f₂; rw [e₃] at f₃
    exact (f₁.trans f₂).trans f₃

/-! ## The scalar blocks -/

theorem wordLoad_ok {s : State}
    (ha : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 (-4)) 4) :
    ∃ s', runBlock isa [.mov32 .rax (.mem { base := .rdx, disp := -4 }), .alu .cmp .rdi (.reg .rsi)] s =
        some s' ∧
      s'.gpr .rax = (s.mem.readW (s.gpr .rdx + BitVec.ofInt 64 (-4)) 32).setWidth 64 ∧
      s'.zf = some (s.gpr .rdi - s.gpr .rsi == 0) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, readSrc32, State.load32, State.ea, State.setReg32, State.setReg, ha, ite_true,
      Option.map_some, Option.bind_some]
    rfl, ?_⟩
  refine ⟨by simp [arithFlags, State.setFlags], by simp [arithFlags, State.setFlags],
    fun r hr => by simp [arithFlags, State.setFlags, hr], rfl, rfl, rfl⟩

/-- The round constant after one more round. -/
def rcNext (v : BitVec 64) : BitVec 64 :=
  (v + v ^^^ (0 - (v >>> 7) &&& (0x1b : BitVec 32).signExtend 64)) &&& (0xff : BitVec 32).signExtend 64

theorem rotTail_ok {s : State} {b : Addr} (hb : s.gpr sb = b)
    (hr : InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 (8 * 54)) 8)
    (hw : InRegions s.wr (b + BitVec.ofNat 64 (8 * 54)) 8) :
    ∃ s', runBlock isa rotTail s = some s' ∧
      s'.gpr .rax = (((s.gpr .rax).setWidth 32).rotateRight 8).setWidth 64 ^^^
        s.mem.readW (b + BitVec.ofNat 64 (8 * 54)) 64 ∧
      s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (8 * 54))
        (rcNext (s.mem.readW (b + BitVec.ofNat 64 (8 * 54)) 64)) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [rotTail, rconSlot, movS, movR, shrI, imm, xorR, st, slotAt, q,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift, execShift32, readSrc,
      State.load64, State.store64, State.ea, ofInt_nat, State.setReg32, State.setReg, State.setFlags,
      arithFlags, hb, hr, hw, ite_true, ite_false, Option.map_some, Option.bind_some]
    rfl, ?_⟩
  refine ⟨by simp, by simp [rcNext], fun r h1 h2 h3 h4 => by simp [h1, h2, h3, h4], rfl, rfl⟩

theorem cmpImm_ok (s : State) (r : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [.alu .cmp r (.imm v)] s = some s' ∧ s'.zf = some (s.gpr r - v.signExtend 64 == 0) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some]; rfl, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem wordStore_ok {s : State}
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdx + s.gpr .rsi) 4) (hw : InRegions s.wr (s.gpr .rdx) 4) :
    ∃ s', runBlock isa [.alu32 .xor .rax (.mem { base := .rdx, index := some .rsi }),
        .store32 (at_ .rdx 0) .rax, .alu .add .rdx (.imm 4), .alu .add .rdi (.imm 4)] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .rdx)
        ((s.gpr .rax).setWidth 32 ^^^ s.mem.readW (s.gpr .rdx + s.gpr .rsi) 32) ∧
      s'.gpr .rdx = s.gpr .rdx + 4 ∧ s'.gpr .rdi = s.gpr .rdi + 4 ∧
      s'.zf = some (s.gpr .rdi + 4 == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rdi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e1 : s.gpr .rdx + s.gpr .rsi * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = s.gpr .rdx + s.gpr .rsi := by
    simp
  have e2 : s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int) = s.gpr .rdx := by simp
  refine ⟨_, by
    simp (config := {decide := true}) only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      execAlu32, readSrc, readSrc32, State.load32, State.store32, State.ea, e1, e2, State.setReg32,
      State.setReg, State.setFlags, arithFlags, hr, hw, ite_true, ite_false, Option.bind_some,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨rfl, by simp, by simp, by simp, fun r h1 h2 h3 => by simp [h1, h2, h3], rfl, rfl⟩

theorem movRdi_ok (s : State) :
    ∃ s', runBlock isa [movR .rdi .rsi] s = some s' ∧ s'.gpr .rdi = s.gpr .rsi ∧
      (∀ r, r ≠ .rdi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [movR, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some]; rfl, ?_⟩
  exact ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem decR8_ok (s : State) :
    ∃ s', runBlock isa [.alu .sub .r8 (.imm 1)] s = some s' ∧ s'.gpr .r8 = s.gpr .r8 - 1 ∧
      s'.zf = some (s.gpr .r8 - 1 == 0) ∧
      (∀ r, r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some]; rfl, ?_⟩
  simp only [State.setReg, arithFlags, State.setFlags, show (1 : BitVec 32).signExtend 64 = 1 by decide]
  exact ⟨by simp, by simp, fun r h => by simp [h], trivial, trivial, trivial⟩


/-! ## Bytes -/

/-- The round constant slot's value: `x^k`. -/
def rcW (k : Nat) : BitVec 64 := (Nat.repeat xtimes k (1 : Byte)).setWidth 64

theorem rcNext_rcW : ∀ k < 10, rcNext (rcW k) = rcW (k + 1) := by decide

theorem rcW_byte (k : Nat) {t : Nat} (ht : t < 4) :
    (rcW k).extractLsb' (8 * t) 8 = if t = 0 then Nat.repeat xtimes k 1 else 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [rcW, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  split
  · subst_vars; simp [hj]; intro; omega
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp

theorem xor32_byte (x : BitVec 64) (y : BitVec 32) {t : Nat} (ht : t < 4) :
    (x.setWidth 32 ^^^ y).extractLsb' (8 * t) 8 = x.extractLsb' (8 * t) 8 ^^^ y.extractLsb' (8 * t) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_setWidth]
  simp [hj, show 8 * t + j < 32 by omega]

theorem rot_byte (x c : BitVec 64) {t : Nat} (ht : t < 4) :
    ((((x.setWidth 32).rotateRight 8).setWidth 64) ^^^ c).extractLsb' (8 * t) 8 =
      x.extractLsb' (8 * ((t + 1) % 4)) 8 ^^^ c.extractLsb' (8 * t) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_rotateRight]
  simp only [hj, decide_true, Bool.true_and, show 8 * t + j < 64 by omega]
  by_cases h : t < 3
  · rw [ite_eq_left ((show 8 * t + j < 32 - 8 % 32 by omega)),
      show 8 % 32 + (8 * t + j) = 8 * ((t + 1) % 4) + j by omega]
    simp [show 8 * ((t + 1) % 4) + j < 32 by omega]
  · rw [ite_eq_right ((show ¬ 8 * t + j < 32 - 8 % 32 by omega)),
      show 8 * t + j - (32 - 8 % 32) = 8 * ((t + 1) % 4) + j by omega]
    simp [show 8 * ((t + 1) % 4) + j < 32 by omega]
    intro; omega

theorem ld_byte (m : Mem) (a : Addr) {t : Nat} (ht : t < 4) :
    ((m.readW a 32).setWidth 64).extractLsb' (8 * t) 8 = m (a + BitVec.ofNat 64 t) := by
  rw [Mem.readW_byte m a ht]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  simp [hj, show 8 * t + j < 32 by omega]
  intro; omega

theorem st_byte (m : Mem) (a : Addr) (v : BitVec 32) {t : Nat} (ht : t < 4) :
    m.writeW a v (a + BitVec.ofNat 64 t) = v.extractLsb' (8 * t) 8 := by
  rw [Mem.readW_byte (m.writeW a v) a ht, Mem.readW_writeW_self32]

/-! ## Address and flag arithmetic -/

theorem ofNat_beq_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
  by_cases h : x = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 x ≠ 0 := by
      intro h'; apply h
      have := congrArg BitVec.toNat h'
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
    simp only [h, decide_false, beq_eq_false_iff_ne]; exact this

theorem addr_m4 (S : Addr) {i : Nat} (hi : 1 ≤ i) (h : 4 * i < 2 ^ 64) :
    S + BitVec.ofNat 64 (4 * i) + BitVec.ofInt 64 (-4) = S + BitVec.ofNat 64 (4 * (i - 1)) := by
  rw [show BitVec.ofInt 64 (-4) = 0 - 4 by decide]
  bv_omega

theorem diff_beq (K x : Nat) (hx : x < 2 ^ 64) :
    (0 - BitVec.ofNat 64 K + BitVec.ofNat 64 x - (0 - BitVec.ofNat 64 K) == 0) = decide (x = 0) := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel, ofNat_beq_zero hx]

theorem cmp16 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (0 - BitVec.ofNat 64 a + BitVec.ofNat 64 b - (-16 : BitVec 32).signExtend 64 == 0) =
      decide (b + 16 = a) := by
  rw [show (-16 : BitVec 32).signExtend 64 = 0 - 16 by decide]
  by_cases h : b + 16 = a
  · simp only [h, decide_true, beq_iff_eq]; bv_omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]; bv_omega

theorem cmp32 {a : Nat} (ha : a < 2 ^ 32) :
    (0 - BitVec.ofNat 64 a - (-32 : BitVec 32).signExtend 64 == 0) = decide (a = 32) := by
  rw [show (-32 : BitVec 32).signExtend 64 = 0 - 32 by decide]
  by_cases h : a = 32
  · simp only [h, decide_true, beq_iff_eq]; bv_omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]; bv_omega

theorem addr_back (S : Addr) {i n : Nat} (h : n ≤ i) :
    S + BitVec.ofNat 64 (4 * i) + (0 - BitVec.ofNat 64 (4 * n)) = S + BitVec.ofNat 64 (4 * (i - n)) := by
  bv_omega

theorem rdx_step (S : Addr) (i : Nat) :
    S + BitVec.ofNat 64 (4 * i) + 4 = S + BitVec.ofNat 64 (4 * (i + 1)) := by
  rw [BitVec.add_assoc, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
  rfl

theorem rdi_beq {K x : Nat} (hx : x + 4 ≤ K) (hK : K < 2 ^ 32) :
    (0 - BitVec.ofNat 64 K + BitVec.ofNat 64 x + 4 == 0) = decide (x + 4 = K) := by
  by_cases h : x + 4 = K
  · simp only [h, decide_true, beq_iff_eq]; bv_omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]; bv_omega

theorem ofNat_sub_ofNat_eight {x : Nat} (h : 8 ≤ x) :
    BitVec.ofNat 64 x - 8 = BitVec.ofNat 64 (x - 8) := by
  bv_omega

theorem rdi_add (K x : Nat) :
    0 - BitVec.ofNat 64 K + BitVec.ofNat 64 x + 4 = 0 - BitVec.ofNat 64 K + BitVec.ofNat 64 (x + 4) := by
  rw [BitVec.add_assoc, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]


theorem div_pred_zero {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (hi : nk ≤ i) (h : i % nk = 0) :
    (i - 1) / nk + 1 = i / nk := by
  rcases h3 with rfl | rfl | rfl <;> omega

theorem div_pred_ne {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (h : i % nk ≠ 0) :
    (i - 1) / nk = i / nk := by
  rcases h3 with rfl | rfl | rfl <;> omega

theorem rot_lt {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (hn : i < 4 * (nk + 7)) (h : i % nk = 0) :
    (i - 1) / nk < 10 := by
  rcases h3 with rfl | rfl | rfl <;> omega

/-! ## One word -/

/-- The setting of the word loop: the schedule at `S`, the scratch buffer
at `B`, and the key `kl` of `nk` words. -/
structure WSetup (s₀ : State) (S B : Addr) (kl : List Byte) (nk : Nat) : Prop where
  nk3 : nk = 4 ∨ nk = 6 ∨ nk = 8
  len : kl.length = 4 * nk
  sch : (⟨S, 240⟩ : Region) ∈ s₀.wr
  scr : (⟨B, 512⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨S, 240⟩ ⟨B, 512⟩

/-- Before word `i`. -/
structure WInv (s₀ : State) (S B : Addr) (kl : List Byte) (nk i : Nat) (s : State) : Prop where
  hi : nk ≤ i
  hn : i < 4 * (nk + 7)
  rdx : s.gpr .rdx = S + BitVec.ofNat 64 (4 * i)
  rsi : s.gpr .rsi = 0 - BitVec.ofNat 64 (4 * nk)
  rdi : s.gpr .rdi = 0 - BitVec.ofNat 64 (4 * nk) + BitVec.ofNat 64 (4 * (i % nk))
  r8 : s.gpr .r8 = BitVec.ofNat 64 (4 * (nk + 7) - i)
  r9 : s.gpr .r9 = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sched : ∀ k < 4 * i, s.mem (S + BitVec.ofNat 64 k) = (kw kl nk (k / 4)).getD (k % 4) 0
  rc : s.mem.readW (B + BitVec.ofNat 64 (8 * 54)) 64 = rcW ((i - 1) / nk)
  saved : Saved s₀ B s.mem
  frame : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem s.mem

/-- After the last word. -/
structure WDone (s₀ : State) (S B : Addr) (kl : List Byte) (nk : Nat) (s : State) : Prop where
  r9 : s.gpr .r9 = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sched : ∀ k < 16 * (nk + 7), s.mem (S + BitVec.ofNat 64 k) = (kw kl nk (k / 4)).getD (k % 4) 0
  saved : Saved s₀ B s.mem
  frame : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem s.mem

/-- `temp` computed (in the low 32 bits of `rax`), from `s`. -/
structure Mid (B : Addr) (kl : List Byte) (nk i : Nat) (s s' : State) : Prop where
  temp : ∀ t < 4, (s'.gpr .rax).extractLsb' (8 * t) 8 = (kTemp nk i (kw kl nk (i - 1))).getD t 0
  keep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨B, 8 * 48⟩, ⟨B + BitVec.ofNat 64 (8 * 54), 8⟩] s.mem s'.mem
  rc : s'.mem.readW (B + BitVec.ofNat 64 (8 * 54)) 64 = rcW (i / nk)

theorem slot_disj (B : Addr) : Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * 54), 8⟩ ⟨B, 8 * 48⟩ :=
  off_disjoint_base B (by decide) (by decide)

/-- `SUBWORD(ROTWORD(temp)) ⊕ Rcon`, and the next round constant. -/
theorem rot_wp {s₀ : State} {S B : Addr} {kl : List Byte} {nk i : Nat} (hs : WSetup s₀ S B kl nk)
    {s : State} (hi : WInv s₀ S B kl nk i s) {s₁ : State}
    (hw : ∀ t < 4, (s₁.gpr .rax).extractLsb' (8 * t) 8 = (kw kl nk (i - 1)).getD t 0)
    (hok : Ok linCfg s₁) (hb₁ : s₁.gpr sb = B) (hwS : (⟨B, 512⟩ : Region) ∈ s₁.wr)
    (o₁ : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r) (m₁ : s₁.mem = s.mem) (rd₁ : s₁.rd = s.rd)
    (wr₁ : s₁.wr = s.wr) (h0 : i % nk = 0) :
    WP isa (.block rotWordStep) s₁ (Mid B kl nk i s) := by
  have h3 := hs.nk3
  have hi1 := hi.hi
  have hn := hi.hn
  have hlen := kw_length hs.len (by omega) (i - 1)
  simp only [rotWordStep]
  rw [WP.block_append_iff (M := isa)]
  refine subAll_wp hok fun s₂ h₂ rd₂ wr₂ o₂ f₂ => ?_
  have hb₂ : s₂.gpr sb = B := (o₂ sb (by decide)).trans hb₁
  have i54 : InRegions s₂.wr (B + BitVec.ofNat 64 (8 * 54)) 8 :=
    in_off (by rw [wr₂]; exact hwS) (by omega) (by omega)
  have r54 : InRegions (s₂.rd ++ s₂.wr) (B + BitVec.ofNat 64 (8 * 54)) 8 := by
    obtain ⟨r, hr, hc⟩ := i54; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain ⟨s₃, hs₃, rax₃, m₃, o₃, rd₃, wr₃⟩ := rotTail_ok hb₂ r54 i54
  refine WP.of_runBlock ⟨s₃, hs₃, ?_⟩
  rw [hb₁] at f₂
  have rc₂ : s₂.mem.readW (B + BitVec.ofNat 64 (8 * 54)) 64 = rcW ((i - 1) / nk) := by
    rw [f₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact slot_disj B) (by decide), m₁, hi.rc]
  refine ⟨fun t ht => ?_, fun r hr => ?_, rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_, ?_⟩
  · rw [rax₃, rot_byte _ _ ht, show s₂.gpr .rax = Q s₂ 0 from rfl, h₂ 0 (by omega) _ (by omega), show Q s₁ 0 = s₁.gpr .rax from rfl,
      hw _ (by omega), rc₂, rcW_byte _ ht]
    simp only [kTemp, h0, ite_true]
    rw [xorWord_getD (by simp [subWord, rotWord_length hlen]) (by rfl) ht,
      subWord_getD (by rw [rotWord_length hlen]; exact ht), rotWord_getD hlen ht, rcon_getD _ ht,
      ← div_pred_zero h3 hi1 h0, Nat.add_sub_cancel]
  · have hq : ∀ r ∈ [Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9], r ≠ .rax ∧ r ≠ .rbx ∧ r ≠ .rcx ∧ r ≠ .rbp := by
      decide
    obtain ⟨a1, a2, a3, a4⟩ := hq r (not_sboxWrites r hr)
    rw [o₃ r a1 a2 a3 a4, o₂ r hr, o₁ r a1]
  · rw [m₃, ← m₁]
    refine Frame.writeW (r := ⟨B + BitVec.ofNat 64 (8 * 54), 8⟩) ?_ (by simp) _ (Region.contains_self _ _)
    exact f₂.mono (by simp)
  · rw [m₃, Mem.readW_writeW_self64, rc₂, rcNext_rcW _ (rot_lt h3 hn h0), div_pred_zero h3 hi1 h0]

theorem temp_wp {s₀ : State} {S B : Addr} {kl : List Byte} {nk i : Nat} (hs : WSetup s₀ S B kl nk)
    {s : State} (hi : WInv s₀ S B kl nk i s) {s₁ : State}
    (rax₁ : s₁.gpr .rax = (s.mem.readW (S + BitVec.ofNat 64 (4 * (i - 1))) 32).setWidth 64)
    (zf₁ : s₁.zf = some (decide (i % nk = 0))) (o₁ : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r)
    (m₁ : s₁.mem = s.mem) (rd₁ : s₁.rd = s.rd) (wr₁ : s₁.wr = s.wr) :
    WP isa (.ite .e (.block rotWordStep)
        (.seq (.block [.alu .cmp .rdi (.imm (-16))])
          (.ite .e (.seq (.block [.alu .cmp .rsi (.imm (-32))]) (.ite .e (.block subAll) (.block [])))
            (.block [])))) s₁ (Mid B kl nk i s) := by
  have h3 := hs.nk3
  have hnk : 0 < nk := by omega
  have hi1 := hi.hi
  have hn := hi.hn
  have hwS : (⟨B, 512⟩ : Region) ∈ s₁.wr := by rw [wr₁, hi.wr]; exact hs.scr
  have hb₁ : s₁.gpr sb = B := by rw [show sb = .r9 from rfl, o₁ .r9 (by decide), hi.r9]
  -- The bytes of `w[i − 1]`.
  have hw : ∀ t < 4, (s₁.gpr .rax).extractLsb' (8 * t) 8 = (kw kl nk (i - 1)).getD t 0 := by
    intro t ht
    rw [rax₁, ld_byte _ _ ht, BitVec.add_assoc, ← BitVec.ofNat_add, hi.sched _ (by omega),
      show (4 * (i - 1) + t) / 4 = i - 1 by omega, show (4 * (i - 1) + t) % 4 = t by omega]
  have hlen := kw_length hs.len hnk (i - 1)
  have hok : Ok linCfg s₁ := Ok.of_region hwS (by simp only [linCfg]; exact hb₁.symm)
    (by simp [linCfg]) (by simp [linCfg]) rfl
  have mid_of : ∀ s', s'.gpr .rax = s₁.gpr .rax → (∀ r, r ∉ sboxWrites → s'.gpr r = s₁.gpr r) →
      s'.mem = s.mem → s'.rd = s₁.rd → s'.wr = s₁.wr → i % nk ≠ 0 →
      kTemp nk i (kw kl nk (i - 1)) = kw kl nk (i - 1) → Mid B kl nk i s s' := by
    intro s' hrax hk hm hrd hwr hne ht
    refine ⟨fun t htt => by rw [hrax, hw t htt, ht], fun r hr => (hk r hr).trans (o₁ r ?_),
      hrd.trans rd₁, hwr.trans wr₁, by rw [hm]; exact Frame.refl _ _, ?_⟩
    · intro h; subst h; exact hr (by decide)
    · rw [hm, hi.rc, div_pred_ne h3 hne]
  refine WP.ite (decide (i % nk = 0)) (by simp [X86_64.eval, zf₁]) (fun hb => ?_) (fun hb => ?_)
  · exact rot_wp hs hi hw hok hb₁ hwS o₁ m₁ rd₁ wr₁ (by simpa using hb)
  · have h0 : i % nk ≠ 0 := by simpa using hb
    obtain ⟨s₄, hs₄, zf₄, g₄, m₄, rd₄, wr₄⟩ := cmpImm_ok s₁ .rdi (-16)
    refine WP.seq (WP.of_runBlock ⟨s₄, hs₄, ?_⟩)
    have e₄ : (s₁.gpr .rdi - (-16 : BitVec 32).signExtend 64 == 0) = decide (4 * (i % nk) + 16 = 4 * nk) := by
      rw [o₁ .rdi (by decide), hi.rdi, cmp16 (by omega) (by have := Nat.mod_lt i hnk; omega)]
    refine WP.ite (decide (4 * (i % nk) + 16 = 4 * nk)) (by rw [← e₄]; simp [X86_64.eval, zf₄])
      (fun hb₄ => ?_) (fun hb₄ => ?_)
    · have h4 : 4 * (i % nk) + 16 = 4 * nk := by simpa using hb₄
      obtain ⟨s₅, hs₅, zf₅, g₅, m₅, rd₅, wr₅⟩ := cmpImm_ok s₄ .rsi (-32)
      refine WP.seq (WP.of_runBlock ⟨s₅, hs₅, ?_⟩)
      have e₅ : (s₄.gpr .rsi - (-32 : BitVec 32).signExtend 64 == 0) = decide (4 * nk = 32) := by
        rw [g₄, o₁ .rsi (by decide), hi.rsi, cmp32 (by omega)]
      refine WP.ite (decide (4 * nk = 32)) (by rw [← e₅]; simp [X86_64.eval, zf₅])
        (fun hb₅ => ?_) (fun hb₅ => ?_)
      · -- `SUBWORD(temp)`.
        have h8 : nk = 8 := by simp at hb₅; omega
        have ok₅ : Ok linCfg s₅ := hok.congr (by rw [g₅, g₄]) (by rw [g₅, g₄]) (rd₅.trans rd₄)
          (wr₅.trans wr₄)
        refine subAll_wp ok₅ fun s₆ h₆ rd₆ wr₆ o₆ f₆ => ?_
        rw [g₅, g₄, hb₁, m₅, m₄, m₁] at f₆
        refine ⟨fun t ht => ?_, fun r hr => ?_, by rw [rd₆, rd₅, rd₄, rd₁], by rw [wr₆, wr₅, wr₄, wr₁],
          f₆.mono (by simp), ?_⟩
        · rw [show s₆.gpr .rax = Q s₆ 0 from rfl, h₆ 0 (by omega) _ (by omega),
            show Q s₅ 0 = s₁.gpr .rax by simp only [Q]; rw [g₅, g₄]; rfl, hw _ ht]
          rw [kTemp, ite_eq_right h0, ite_eq_left (show nk > 6 ∧ i % nk = 4 by omega),
            subWord_getD (by rw [hlen]; exact ht)]
        · rw [o₆ r hr, g₅, g₄, o₁ r (fun h => by subst h; exact hr (by decide))]
        · rw [f₆.readW (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact slot_disj B) (by decide), hi.rc,
            div_pred_ne h3 h0]
      · have h8 : nk ≠ 8 := by simp at hb₅; omega
        refine WP.block_nil (mid_of s₅ (by rw [g₅, g₄]) (fun r _ => by rw [g₅, g₄])
          (by rw [m₅, m₄, m₁]) (by rw [rd₅, rd₄]) (by rw [wr₅, wr₄]) h0 ?_)
        rw [kTemp, ite_eq_right h0, ite_eq_right (show ¬ (nk > 6 ∧ i % nk = 4) by omega)]
    · have h4 : 4 * (i % nk) + 16 ≠ 4 * nk := by simpa using hb₄
      refine WP.block_nil (mid_of s₄ (by rw [g₄]) (fun r _ => by rw [g₄]) (by rw [m₄, m₁]) rd₄ wr₄ h0 ?_)
      rw [kTemp, ite_eq_right h0, ite_eq_right (show ¬ (nk > 6 ∧ i % nk = 4) by omega)]


theorem writeW32_other {m : Mem} {a x : Addr} (v : BitVec 32) (h : Region.Disjoint ⟨x, 1⟩ ⟨a, 4⟩) :
    m.writeW a v x = m x :=
  Mem.write_apply (out_of_disj h (Region.contains_self _ _) (Region.contains_self _ _))

/-- The memory after word `i` is stored. -/
def storeMem (s₂ : State) (S : Addr) (nk i : Nat) : Mem :=
  s₂.mem.writeW (S + BitVec.ofNat 64 (4 * i))
    ((s₂.gpr .rax).setWidth 32 ^^^ s₂.mem.readW (S + BitVec.ofNat 64 (4 * (i - nk))) 32)

theorem store_facts {s₀ : State} {S B : Addr} {kl : List Byte} {nk i : Nat} (hs : WSetup s₀ S B kl nk)
    {s s₂ : State} (hi : WInv s₀ S B kl nk i s) (hm : Mid B kl nk i s s₂) :
    (∀ k < 4 * (i + 1), storeMem s₂ S nk i (S + BitVec.ofNat 64 k) = (kw kl nk (k / 4)).getD (k % 4) 0) ∧
    Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem (storeMem s₂ S nk i) ∧ Saved s₀ B (storeMem s₂ S nk i) ∧
    (storeMem s₂ S nk i).readW (B + BitVec.ofNat 64 (8 * 54)) 64 = rcW (i / nk) := by
  have h3 := hs.nk3
  have hnk : 0 < nk := by omega
  have hi1 := hi.hi
  have hn := hi.hn
  have fS : ∀ k < 240, s₂.mem (S + BitVec.ofNat 64 k) = s.mem (S + BitVec.ofNat 64 k) := fun k hk =>
    hm.frame.bytes (R := ⟨S, 240⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.sep.sub_right (Region.sub_prefix (by decide))
      · exact hs.sep.sub_right (off_sub_base B (by decide) (by decide))) (by simp) hk
  have sched' : ∀ k < 4 * (i + 1), storeMem s₂ S nk i (S + BitVec.ofNat 64 k) = (kw kl nk (k / 4)).getD (k % 4) 0 := by
    intro k hk
    unfold storeMem
    by_cases hki : k < 4 * i
    · rw [writeW32_other _ (off_disjoint S (Or.inl (by omega)) (by omega) (by omega)), fS k (by omega),
        hi.sched k hki]
    · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 4 ∧ k = 4 * i + t := ⟨k - 4 * i, by omega, by omega⟩
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, st_byte _ _ _ ht, xor32_byte _ _ ht, hm.temp t ht,
        ← Mem.readW_byte _ _ ht, BitVec.add_assoc, ← BitVec.ofNat_add, fS _ (by omega),
        hi.sched _ (by omega), show (4 * (i - nk) + t) / 4 = i - nk by omega,
        show (4 * (i - nk) + t) % 4 = t by omega, show (4 * i + t) / 4 = i by omega,
        show (4 * i + t) % 4 = t by omega, kw_step kl hnk hi1,
        xorWord_getD (kw_length hs.len hnk _) (kTemp_length (kw_length hs.len hnk _)) ht, BitVec.xor_comm]
  have fr : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem (storeMem s₂ S nk i) := by
    unfold storeMem
    refine Frame.writeW (hi.frame.trans (hm.frame.sub fun r hr => ?_)) (r := ⟨S, 240⟩) (by simp) _
      (c_off S (by omega) (by omega))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨B, 512⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨⟨B, 512⟩, by simp, off_sub_base B (by decide) (by decide)⟩
  have hdS : ∀ r ∈ [(⟨S + BitVec.ofNat 64 (4 * i), 4⟩ : Region)],
      Region.Disjoint ⟨B + BitVec.ofNat 64 384, 48⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have d1 : Region.Disjoint ⟨S, 240⟩ ⟨B + BitVec.ofNat 64 384, 48⟩ :=
      hs.sep.sub_right (off_sub_base B (x := 384) (lx := 48) (ly := 512) (by decide) (by decide))
    have d2 : Region.Disjoint ⟨S + BitVec.ofNat 64 (4 * i), 4⟩ ⟨B + BitVec.ofNat 64 384, 48⟩ :=
      d1.sub_left (off_sub_base S (x := 4 * i) (lx := 4) (ly := 240) (by omega) (by decide))
    exact d2.symm
  have sv : Saved s₀ B (storeMem s₂ S nk i) := by
    unfold storeMem
    refine saved_frame (saved_frame hi.saved hm.frame fun r hr => ?_)
      (Frame.writeW (Frame.refl [⟨S + BitVec.ofNat 64 (4 * i), 4⟩] _) (by simp) _
        (Region.contains_self _ _)) hdS
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact off_disjoint_base B (by decide) (by decide)
    · exact off_disjoint B (Or.inl (by decide)) (by decide) (by decide)
  have rc : (storeMem s₂ S nk i).readW (B + BitVec.ofNat 64 (8 * 54)) 64 = rcW (i / nk) := by
    rw [storeMem, Mem.readW_writeW_sep ((hs.sep.sub_right (off_sub_base B (by decide) (by decide))).symm.sep
      (Region.contains_self _ _) (c_off S (by omega) (by omega))) (by decide), hm.rc]
  exact ⟨sched', fr, sv, rc⟩

theorem word_ok {s₀ : State} {S B : Addr} {kl : List Byte} {nk i : Nat} (hs : WSetup s₀ S B kl nk)
    {s : State} (hi : WInv s₀ S B kl nk i s) :
    WP isa wordBody s fun s' =>
      (s'.zf = some false ∧ WInv s₀ S B kl nk (i + 1) s') ∨
      (s'.zf = some true ∧ WDone s₀ S B kl nk s') := by
  have h3 := hs.nk3
  have hnk : 0 < nk := by omega
  have hi1 := hi.hi
  have hn := hi.hn
  have hmod := Nat.mod_lt i hnk
  unfold wordBody
  refine WP.seq ?_
  have hrS : (⟨S, 240⟩ : Region) ∈ s.rd ++ s.wr := List.mem_append_right _ (by rw [hi.wr]; exact hs.sch)
  obtain ⟨s₁, hs₁, rax₁, zf₁, o₁, m₁, rd₁, wr₁⟩ := wordLoad_ok (s := s) (by
    rw [hi.rdx, addr_m4 S (by omega) (by omega)]; exact in_off hrS (by omega) (by omega))
  refine WP.of_runBlock ⟨s₁, hs₁, ?_⟩
  rw [hi.rdx, addr_m4 S (by omega) (by omega)] at rax₁
  rw [hi.rdi, hi.rsi, diff_beq _ _ (by omega)] at zf₁
  have zf₁' : s₁.zf = some (decide (i % nk = 0)) := by rw [zf₁]; simp
  refine WP.seq (WP.mono (temp_wp hs hi rax₁ zf₁' o₁ m₁ rd₁ wr₁) fun s₂ hm => ?_)
  have k₂ : ∀ r ∈ [Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9], s₂.gpr r = s.gpr r := fun r hr => by
    exact hm.keep r (fun h => by revert hr; revert h; revert r; decide)
  have rdx₂ := (k₂ .rdx (by simp)).trans hi.rdx
  have rsi₂ := (k₂ .rsi (by simp)).trans hi.rsi
  have rdi₂ := (k₂ .rdi (by simp)).trans hi.rdi
  have hwS : (⟨S, 240⟩ : Region) ∈ s₂.wr := by rw [hm.wr, hi.wr]; exact hs.sch
  -- `w[i] := w[i − Nk] ⊕ temp`.
  refine WP.seq ?_
  obtain ⟨s₃, hs₃, m₃, rdx₃, rdi₃, zf₃, o₃, rd₃, wr₃⟩ := wordStore_ok (s := s₂)
    (by rw [rdx₂, rsi₂, addr_back S hi1]; exact in_off (List.mem_append_right _ hwS) (by omega) (by omega))
    (by rw [rdx₂]; exact in_off hwS (by omega) (by omega))
  refine WP.of_runBlock ⟨s₃, hs₃, ?_⟩
  rw [rdi₂, rdi_beq (by omega) (by omega)] at zf₃
  rw [rdx₂, rsi₂, addr_back S hi1] at m₃
  -- `rdi := 4 ((i + 1) mod Nk) − 4 Nk`.
  refine WP.seq (WP.mono (Q := fun (s₄ : State) =>
      s₄.gpr .rdi = 0 - BitVec.ofNat 64 (4 * nk) + BitVec.ofNat 64 (4 * ((i + 1) % nk)) ∧
      (∀ r, r ≠ .rdi → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr) ?_
    fun s₄ ⟨rdi₄, o₄, m₄, rd₄, wr₄⟩ => ?_)
  · refine WP.ite (decide (4 * (i % nk) + 4 = 4 * nk)) (by simp [X86_64.eval, zf₃])
      (fun hb => ?_) (fun hb => ?_)
    · obtain ⟨s₄, hs₄, rdi₄, o₄, m₄, rd₄, wr₄⟩ := movRdi_ok s₃
      refine WP.of_runBlock ⟨s₄, hs₄, ?_, o₄, m₄, rd₄, wr₄⟩
      have h1 : (i + 1) % nk = 0 := by
        have : i % nk + 1 = nk := by simp at hb; omega
        rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < nk by omega), this, Nat.mod_self]
      rw [rdi₄, o₃ .rsi (by decide) (by decide) (by decide), rsi₂, h1, Nat.mul_zero]
      simp
    · refine WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
      have h1 : (i + 1) % nk = i % nk + 1 := by
        have : i % nk + 1 < nk := by simp at hb; omega
        rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < nk by omega), Nat.mod_eq_of_lt this]
      rw [rdi₃, rdi₂, rdi_add, h1, Nat.mul_add, Nat.mul_one]
  -- `r8 := r8 − 1`.
  obtain ⟨s₅, hs₅, r8₅, zf₅, o₅, m₅, rd₅, wr₅⟩ := decR8_ok s₄
  refine WP.of_runBlock ⟨s₅, hs₅, ?_⟩
  have r8₄ : s₄.gpr .r8 = BitVec.ofNat 64 (4 * (nk + 7) - i) := by
    rw [o₄ .r8 (by decide), o₃ .r8 (by decide) (by decide) (by decide), k₂ .r8 (by simp), hi.r8]
  rw [r8₄, ofNat_sub_one (by omega)] at r8₅ zf₅
  rw [ofNat_beq_zero (by omega)] at zf₅
  have gk : ∀ r ∈ [Reg.rsp, .rsi, .r9], s₅.gpr r = s.gpr r := fun r hr => by
    rw [o₅ r (by revert hr; revert r; decide), o₄ r (by revert hr; revert r; decide),
      o₃ r (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide),
      k₂ r (by revert hr; revert r; decide)]
  have mem₅ : s₅.mem = storeMem s₂ S nk i := by rw [m₅, m₄, m₃]; rfl
  -- The scratch buffer's changes are outside the schedule.
  obtain ⟨sched', fr, sv, rc⟩ := store_facts hs hi hm
  rw [← mem₅] at sched' fr sv rc
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := (gk .rsp (by simp)).trans hi.rsp
  have r9₅ : s₅.gpr .r9 = B := (gk .r9 (by simp)).trans hi.r9
  have rd : s₅.rd = s₀.rd := by rw [rd₅, rd₄, rd₃, hm.rd, hi.rd]
  have wr : s₅.wr = s₀.wr := by rw [wr₅, wr₄, wr₃, hm.wr, hi.wr]
  by_cases hl : 4 * (nk + 7) - i - 1 = 0
  · refine .inr ⟨by rw [zf₅, hl]; rfl, r9₅, rsp₅, rd, wr, fun k hk => sched' k (by omega), sv, fr⟩
  · refine .inl ⟨by rw [zf₅]; simp [hl], ⟨by omega, by omega, ?_, ?_, ?_, ?_, r9₅, rsp₅, rd, wr, sched',
      by rw [Nat.add_sub_cancel]; exact rc, sv, fr⟩⟩
    · rw [o₅ _ (by decide), o₄ _ (by decide), rdx₃, rdx₂, rdx_step]
    · exact (gk .rsi (by simp)).trans hi.rsi
    · rw [o₅ _ (by decide), rdi₄]
    · rw [r8₅, Nat.sub_sub]


/-! ## The loop over the words -/

theorem words_ok {s₀ : State} {S B : Addr} {kl : List Byte} {nk : Nat} (hs : WSetup s₀ S B kl nk)
    {s : State} (hi : WInv s₀ S B kl nk nk s) :
    WP isa (.loop wordBody .ne) s (WDone s₀ S B kl nk) := by
  refine WP.loop (M := isa) (fun k s => ∃ i, k = 4 * (nk + 7) - i ∧ WInv s₀ S B kl nk i s)
    (fun k s ⟨i, hk, hi⟩ => WP.mono (word_ok hs hi) fun s' h => ?_) _ s ⟨nk, rfl, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inr ⟨by simp [X86_64.eval, z], _, by have := hi.hn; omega, i + 1, rfl, d⟩
  · exact .inl ⟨by simp [X86_64.eval, z], d⟩

/-! ## Copying the key -/

theorem copyBody_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 8)
    (hw : InRegions s.wr (s.gpr .rdx) 8) :
    ∃ s', runBlock isa copyBody s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .rdx) (s.mem.readW (s.gpr .rdi) 64) ∧
      s'.gpr .rdi = s.gpr .rdi + 8 ∧ s'.gpr .rdx = s.gpr .rdx + 8 ∧ s'.gpr .rsi = s.gpr .rsi - 8 ∧
      s'.zf = some (s.gpr .rsi - 8 == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e1 : s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int) = s.gpr .rdi := by simp
  have e2 : s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int) = s.gpr .rdx := by simp
  refine ⟨_, by
    simp (config := {decide := true}) only [copyBody, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.load64, State.store64, State.ea, e1, e2, State.setReg,
      State.setFlags, arithFlags, hr, hw, ite_true, ite_false, Option.map_some, Option.bind_some]
    rfl, ?_⟩
  refine ⟨rfl, by simp, by simp, by simp, by simp, fun r h1 h2 h3 h4 => by simp [h1, h2, h3, h4], rfl, rfl⟩

theorem st64_byte (m : Mem) (a : Addr) (v : BitVec 64) {t : Nat} (ht : t < 8) :
    m.writeW a v (a + BitVec.ofNat 64 t) = v.extractLsb' (8 * t) 8 := by
  simp only [Mem.writeW, Mem.write, Mem.sub_ofNat_toNat a (show t < 2 ^ 64 by omega),
    show t < 64 / 8 by omega, ite_true, BitVec.setWidth_eq]

theorem ld64_byte (m : Mem) (a : Addr) {t : Nat} (ht : t < 8) :
    (m.readW a 64).extractLsb' (8 * t) 8 = m (a + BitVec.ofNat 64 t) := by
  rw [← Mem.extractLsb'_read m a (n := 8) ht]
  rfl

theorem writeW64_other {m : Mem} {a x : Addr} (v : BitVec 64) (h : Region.Disjoint ⟨x, 1⟩ ⟨a, 8⟩) :
    m.writeW a v x = m x :=
  Mem.write_apply (out_of_disj h (Region.contains_self _ _) (Region.contains_self _ _))

/-- The key's bytes. -/
theorem bytesAt_getD (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) :
    (Spec.Aes.bytesAt m p n).getD k 0 = m (p + BitVec.ofNat 64 k) := by
  simp [Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, hk]

/-- During the copy, after `c` words. -/
structure CInv (s₀ : State) (S B P : Addr) (K c : Nat) (s : State) : Prop where
  hc : 8 * c < K
  rdi : s.gpr .rdi = P + BitVec.ofNat 64 (8 * c)
  rdx : s.gpr .rdx = S + BitVec.ofNat 64 (8 * c)
  rsi : s.gpr .rsi = BitVec.ofNat 64 (K - 8 * c)
  r8 : s.gpr .r8 = BitVec.ofNat 64 K
  r9 : s.gpr .r9 = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  copied : ∀ k < 8 * c, s.mem (S + BitVec.ofNat 64 k) = s₀.mem (P + BitVec.ofNat 64 k)
  saved : Saved s₀ B s.mem
  frame : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem s.mem

/-- After the copy. -/
structure CDone (s₀ : State) (S B P : Addr) (K : Nat) (s : State) : Prop where
  rdx : s.gpr .rdx = S + BitVec.ofNat 64 K
  rsi : s.gpr .rsi = 0
  r8 : s.gpr .r8 = BitVec.ofNat 64 K
  r9 : s.gpr .r9 = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  copied : ∀ k < K, s.mem (S + BitVec.ofNat 64 k) = s₀.mem (P + BitVec.ofNat 64 k)
  saved : Saved s₀ B s.mem
  frame : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem s.mem

/-- The setting of the copy: the key (`K` bytes at `P`) is outside what is written. -/
structure CSetup (s₀ : State) (S B P : Addr) (K : Nat) : Prop where
  hK : K = 16 ∨ K = 24 ∨ K = 32
  key : (⟨P, K⟩ : Region) ∈ s₀.rd
  sch : (⟨S, 240⟩ : Region) ∈ s₀.wr
  scr : (⟨B, 512⟩ : Region) ∈ s₀.wr
  dS : Region.Disjoint ⟨P, K⟩ ⟨S, 240⟩
  dB : Region.Disjoint ⟨P, K⟩ ⟨B, 512⟩
  sep : Region.Disjoint ⟨S, 240⟩ ⟨B, 512⟩

theorem copy_ok {s₀ : State} {S B P : Addr} {K : Nat} (hs : CSetup s₀ S B P K) {c : Nat} {s : State}
    (hi : CInv s₀ S B P K c s) :
    WP isa (.block copyBody) s fun s' =>
      (s'.zf = some false ∧ CInv s₀ S B P K (c + 1) s') ∨ (s'.zf = some true ∧ CDone s₀ S B P K s') := by
  have hK := hs.hK
  have hc := hi.hc
  have hc8 : 8 * c + 8 ≤ K := by rcases hK with rfl | rfl | rfl <;> omega
  obtain ⟨s', hs', m', rdi', rdx', rsi', zf', o', rd', wr'⟩ := copyBody_ok (s := s)
    (by rw [hi.rdi]; exact in_off (List.mem_append_left _ (by rw [hi.rd]; exact hs.key)) hc8 (by omega))
    (by rw [hi.rdx]; exact in_off (by rw [hi.wr]; exact hs.sch) (by omega) (by omega))
  refine WP.of_runBlock ⟨s', hs', ?_⟩
  rw [hi.rsi, ofNat_sub_ofNat_eight (show 8 ≤ K - 8 * c by omega), ofNat_beq_zero (by omega)] at zf'
  rw [hi.rsi, ofNat_sub_ofNat_eight (show 8 ≤ K - 8 * c by omega)] at rsi'
  rw [hi.rdi, hi.rdx] at m'
  have copied : ∀ k < 8 * (c + 1), s'.mem (S + BitVec.ofNat 64 k) = s₀.mem (P + BitVec.ofNat 64 k) := by
    intro k hk
    rw [m']
    by_cases hkc : k < 8 * c
    · rw [writeW64_other _ (off_disjoint S (Or.inl (by omega)) (by omega) (by omega)), hi.copied k hkc]
    · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 8 ∧ k = 8 * c + t := ⟨k - 8 * c, by omega, by omega⟩
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, st64_byte _ _ _ ht, ld64_byte _ _ ht, BitVec.add_assoc,
        ← BitVec.ofNat_add]
      exact hi.frame.bytes (R := ⟨P, K⟩) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hs.dS
        · exact hs.dB) (by simp only; omega) (show 8 * c + t < K by omega)
  have fr : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem s'.mem := by
    rw [m']
    exact Frame.writeW hi.frame (r := ⟨S, 240⟩) (by simp) _ (c_off S (by omega) (by omega))
  have sv : Saved s₀ B s'.mem := by
    rw [m']
    refine saved_frame hi.saved (Frame.writeW (Frame.refl [⟨S + BitVec.ofNat 64 (8 * c), 8⟩] _) (by simp) _
      (Region.contains_self _ _)) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have d1 : Region.Disjoint ⟨S, 240⟩ ⟨B + BitVec.ofNat 64 384, 48⟩ :=
      hs.sep.sub_right (off_sub_base B (x := 384) (lx := 48) (ly := 512) (by decide) (by decide))
    exact (d1.sub_left (off_sub_base S (x := 8 * c) (lx := 8) (ly := 240) (by omega) (by decide))).symm
  have r8' : s'.gpr .r8 = BitVec.ofNat 64 K := by rw [o' _ (by decide) (by decide) (by decide) (by decide), hi.r8]
  have r9' : s'.gpr .r9 = B := by rw [o' _ (by decide) (by decide) (by decide) (by decide), hi.r9]
  have rsp' : s'.gpr .rsp = s₀.gpr .rsp := by
    rw [o' _ (by decide) (by decide) (by decide) (by decide), hi.rsp]
  by_cases hl : K - 8 * c - 8 = 0
  · refine .inr ⟨by rw [zf', hl]; rfl, ?_, ?_, r8', r9', rsp', rd'.trans hi.rd, wr'.trans hi.wr,
      fun k hk => copied k (by omega), sv, fr⟩
    · rw [rdx', hi.rdx, BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
        ← BitVec.ofNat_add, show 8 * c + 8 = K by omega]
    · rw [rsi', hl]; rfl
  · refine .inl ⟨by rw [zf']; simp [hl], ⟨by omega, ?_, ?_, ?_, r8', r9', rsp', rd'.trans hi.rd,
      wr'.trans hi.wr, copied, sv, fr⟩⟩
    · rw [rdi', hi.rdi, BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
        ← BitVec.ofNat_add, Nat.mul_succ]
    · rw [rdx', hi.rdx, BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
        ← BitVec.ofNat_add, Nat.mul_succ]
    · rw [rsi', show K - 8 * (c + 1) = K - 8 * c - 8 by omega]

theorem copyLoop_ok {s₀ : State} {S B P : Addr} {K : Nat} (hs : CSetup s₀ S B P K) {s : State}
    (hi : CInv s₀ S B P K 0 s) :
    WP isa (.loop (.block copyBody) .ne) s (CDone s₀ S B P K) := by
  refine WP.loop (M := isa) (fun k s => ∃ c, k = K - 8 * c ∧ CInv s₀ S B P K c s)
    (fun k s ⟨c, hk, hc⟩ => WP.mono (copy_ok hs hc) fun s' h => ?_) _ s ⟨0, rfl, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inr ⟨by simp [X86_64.eval, z], _, by have := hc.hc; omega, c + 1, rfl, d⟩
  · exact .inl ⟨by simp [X86_64.eval, z], d⟩


/-! ## Setting up the word loop -/

theorem kw_getD_key (kl : List Byte) {nk k : Nat} (hk : k < 4 * nk) :
    (kw kl nk (k / 4)).getD (k % 4) 0 = kl.getD k 0 := by
  rw [kw_key kl (show k / 4 < nk by omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  simp [show k % 4 < 4 by omega, Nat.div_add_mod]

theorem wordSetup_ok {s : State} {b : Addr} (hb : s.gpr sb = b)
    (hw : InRegions s.wr (b + BitVec.ofNat 64 (8 * 54)) 8) :
    ∃ s', runBlock isa wordSetup s = some s' ∧
      s'.gpr .rsi = s.gpr .rsi - s.gpr .r8 ∧ s'.gpr .rdi = s.gpr .rsi - s.gpr .r8 ∧
      s'.gpr .r8 = (s.gpr .r8 >>> 2) + (s.gpr .r8 >>> 2) + (s.gpr .r8 >>> 2) + 28 ∧
      s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (8 * 54)) (1 : BitVec 64) ∧
      (∀ r, r ≠ .rsi → r ≠ .rdi → r ≠ .r8 → r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [wordSetup, rconSlot, movR, shrI, imm, st, slotAt,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift, readSrc, State.store64,
      State.ea, ofInt_nat, State.setReg, State.setFlags, arithFlags, hb, hw, ite_true, ite_false,
      Option.map_some, Option.bind_some]
    rfl, ?_⟩
  refine ⟨by simp, by simp, by simp, rfl, fun r h1 h2 h3 h4 => by simp [h1, h2, h3, h4], rfl, rfl⟩

theorem r8_setup {K : Nat} (hK : K = 16 ∨ K = 24 ∨ K = 32) :
    (BitVec.ofNat 64 K >>> 2) + (BitVec.ofNat 64 K >>> 2) + (BitVec.ofNat 64 K >>> 2) + 28 =
      BitVec.ofNat 64 (4 * (K / 4 + 7) - K / 4) := by
  rcases hK with rfl | rfl | rfl <;> decide

/-! ## The prologue -/

theorem movR_ok (s : State) (d r : Reg) :
    ∃ s', runBlock isa [movR d r] s = some s' ∧ s'.gpr d = s.gpr r ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [movR, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some]; rfl, ?_⟩
  exact ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem prologue_wp {s₀ : State} {S B P : Addr} {K : Nat} (hs : CSetup s₀ S B P K)
    (hS : s₀.gpr .rdx = S) (hB : s₀.gpr .rcx = B) (hP : s₀.gpr .rdi = P)
    (hKr : s₀.gpr .rsi = BitVec.ofNat 64 K) :
    WP isa (.block ([movR .r9 .rcx] ++ saveRegs ++ [movR .r8 .rsi])) s₀ (CInv s₀ S B P K 0) := by
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  obtain ⟨s₁, h₁, r9₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₀ .r9 .rcx
  refine WP.of_runBlock ⟨s₁, h₁, ?_⟩
  obtain ⟨s₂, h₂, sv₂, g₂, rd₂, wr₂, f₂⟩ := save_ok (s := s₁) (b := B) (n := 512)
    (by rw [wr₁]; exact hs.scr) (by rw [show sb = .r9 from rfl, r9₁, hB]) (by decide)
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  obtain ⟨s₃, h₃, r8₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .r8 .rsi
  refine WP.of_runBlock ⟨s₃, h₃, ?_⟩
  have g : ∀ r, r ≠ .r8 → r ≠ .r9 → s₃.gpr r = s₀.gpr r := fun r h8 h9 => by
    rw [o₃ r h8, g₂, o₁ r h9]
  have hK := hs.hK
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁],
    fun k hk => by omega, ?_, ?_⟩
  · rw [g _ (by decide) (by decide), hP]; simp
  · rw [g _ (by decide) (by decide), hS]; simp
  · rw [g _ (by decide) (by decide), hKr]; simp
  · rw [r8₃, g₂, o₁ _ (by decide), hKr]
  · rw [o₃ _ (by decide), g₂, r9₁, hB]
  · rw [g _ (by decide) (by decide)]
  · intro i hi
    rw [m₃, sv₂ i hi, o₁ _ (by revert hi; revert i; decide)]
  · rw [m₃, ← m₁]
    exact f₂.sub fun r hr => ⟨⟨B, 512⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩

/-! ## The whole function -/

theorem ek_correct {s₀ : State} (hp : Proof.Aes.expandKeyX86_64.pre s₀) :
    WP isa Impl.Aes.X86_64.expandKey s₀ fun s' =>
      gprPreserved s₀ s' ∧ Proof.Aes.expandKeyX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, dRS, dRB, hK⟩ := hp
  have hs : CSetup s₀ (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rdi) (s₀.gpr .rsi).toNat :=
    ⟨hK, by rw [hrd]; simp, by rw [hwr]; simp, by rw [hwr]; simp, dKS, dKB, dSB⟩
  generalize hS : s₀.gpr .rdx = S at hs dSB dRS
  generalize hB : s₀.gpr .rcx = B at hs dSB dRB
  generalize hP : s₀.gpr .rdi = P at hs dKS dKB
  generalize hK' : (s₀.gpr .rsi).toNat = K at hs hK dKS dKB
  have hKr : s₀.gpr .rsi = BitVec.ofNat 64 K := by rw [← hK']; simp
  have hK4 : K = 4 * (K / 4) := by omega
  unfold Impl.Aes.X86_64.expandKey
  refine WP.seq (WP.mono (prologue_wp hs hS hB hP hKr) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (copyLoop_ok hs h₁) fun s₂ h₂ => ?_)
  refine WP.seq ?_
  obtain ⟨s₃, hs₃, rsi₃, rdi₃, r8₃, m₃, o₃, rd₃, wr₃⟩ := wordSetup_ok (s := s₂) (b := B)
    (by rw [show sb = .r9 from rfl, h₂.r9]) (in_off (by rw [h₂.wr]; exact hs.scr) (by omega) (by omega))
  refine WP.of_runBlock ⟨s₃, hs₃, ?_⟩
  have hlen : (Spec.Aes.bytesAt s₀.mem P K).length = K := by simp [Spec.Aes.bytesAt]
  have ws : WSetup s₀ S B (Spec.Aes.bytesAt s₀.mem P K) (K / 4) :=
    ⟨by omega, by rw [hlen]; exact hK4, hs.sch, hs.scr, dSB⟩
  have d54 : Region.Disjoint ⟨S, 240⟩ ⟨B + BitVec.ofNat 64 (8 * 54), 8⟩ :=
    dSB.sub_right (off_sub_base B (by decide) (by decide))
  have wi : WInv s₀ S B (Spec.Aes.bytesAt s₀.mem P K) (K / 4) (K / 4) s₃ :=
    { hi := Nat.le_refl _
      hn := by omega
      rdx := by
        rw [o₃ _ (by decide) (by decide) (by decide) (by decide), h₂.rdx, ← hK4]
      rsi := by rw [rsi₃, h₂.rsi, h₂.r8, ← hK4]
      rdi := by rw [rdi₃, h₂.rsi, h₂.r8, Nat.mod_self, Nat.mul_zero, ← hK4]; simp
      r8 := by rw [r8₃, h₂.r8, r8_setup hK]
      r9 := by rw [o₃ _ (by decide) (by decide) (by decide) (by decide), h₂.r9]
      rsp := by rw [o₃ _ (by decide) (by decide) (by decide) (by decide), h₂.rsp]
      rd := rd₃.trans h₂.rd
      wr := wr₃.trans h₂.wr
      sched := fun k hk => by
        rw [m₃, writeW64_other _ (d54.sub_left (off_sub_base S (by omega) (by decide))),
          h₂.copied k (by omega), ← bytesAt_getD s₀.mem P (show k < K by omega),
          kw_getD_key _ (by omega)]
      rc := by
        rw [m₃, Mem.readW_writeW_self64, Nat.div_eq_of_lt (by omega)]
        rfl
      saved := by
        rw [m₃]
        refine saved_frame h₂.saved (Frame.writeW (Frame.refl [⟨B + BitVec.ofNat 64 (8 * 54), 8⟩] _)
          (by simp) _ (Region.contains_self _ _)) fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        exact off_disjoint B (Or.inl (by decide)) (by decide) (by decide)
      frame := by
        rw [m₃]
        exact Frame.writeW h₂.frame (r := ⟨B, 512⟩) (by simp) _ (c_off B (by omega) (by omega)) }
  refine WP.seq (WP.mono (words_ok ws wi) fun s₄ h₄ => ?_)
  obtain ⟨s₅, hs₅, rg₅, o₅, f₅⟩ := restore_ok (s := s₄) (b := B) (n := 512)
    (by rw [h₄.wr]; exact hs.scr) (by rw [show sb = .r9 from rfl, h₄.r9]) (by decide) h₄.saved
  refine WP.of_runBlock ⟨s₅, hs₅, ?_⟩
  have fAll : Frame [⟨S, 240⟩, ⟨B, 512⟩] s₀.mem s₅.mem :=
    h₄.frame.trans (f₅.sub fun r hr => ⟨⟨B, 512⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩)
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by
    rw [o₅ _ (fun i hi => by revert hi; revert i; decide), h₄.rsp]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rg₅ 0 (by omega)
    · exact rg₅ 1 (by omega)
    · exact rsp₅
    · exact rg₅ 2 (by omega)
    · exact rg₅ 3 (by omega)
    · exact rg₅ 4 (by omega)
    · exact rg₅ 5 (by omega)
  · refine fAll.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dRS
    · exact dRB
  · show Spec.Aes.bytesAt s₅.mem (s₀.gpr .rdx) (16 * (Spec.Aes.rounds ((s₀.gpr .rsi).toNat / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat)
    rw [hS, hP, hK']
    have lhs : ∀ n, Spec.Aes.bytesAt s₅.mem S n = (List.range n).map fun k => s₅.mem (S + BitVec.ofNat 64 k) :=
      fun _ => rfl
    rw [lhs, Spec.Aes.expandKey, hlen, Spec.Aes.rounds,
      show 16 * (K / 4 + 6 + 1) = 4 * (4 * (K / 4 + 6 + 1)) by omega]
    refine flatten_expandWords ws.len (by omega) _ _ fun k hk => ?_
    exact (f₅.bytes (R := ⟨S, 240⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dSB.sub_right (Region.sub_prefix (by decide))) (by simp) (show k < 240 by omega)).trans
      (h₄.sched k (by omega))


/-- A state satisfying the precondition. -/
def ekSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 240⟩, ⟨0x3000, 512⟩]

theorem expandKey_correct (s : State) (hs : Proof.Aes.expandKeyX86_64.pre s) :
    ∃ t s', Exec isa Impl.Aes.X86_64.expandKey s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.expandKeyX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := ek_correct hs
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem expandKey_ct : ConstantTime isa Proof.Aes.expandKeyX86_64.pre Proof.Aes.expandKeyX86_64.pub
    Impl.Aes.X86_64.expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem expandKey_verified :
    Verified X86_64.target Impl.Aes.X86_64.expandKey (Spec.Aes.expandKeyContract X86_64.abi) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Spec.Aes.expandKeyContract, Spec.Aes.expandKeySig, Proof.Aes.expandKeyX86_64,
      X86_64.abi, X86_64.argRegs] [Proof.Aes.X86_64.ekSatState] using Proof.Aes.X86_64.ekSatState)

end VG.Proof.Aes.X86_64
