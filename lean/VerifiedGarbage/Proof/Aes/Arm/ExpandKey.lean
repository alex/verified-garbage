import VerifiedGarbage.Impl.Aes.Arm.ExpandKey
import VerifiedGarbage.Proof.Aes.Arm.Ctr32
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Spec.Aes.Contract

/-!
# The AES key expansion on ARMv7

`subAll` (`ortho`, the S-box, `ortho`, with the loop registers kept in
slots meanwhile) applies the S-box to every byte of the eight words
(`subAll_wp`, from the bitsliced layers' lemmas); each word of the
schedule is then a few scalar instructions around it (`word_ok`), and the
loop over the words keeps the schedule's bytes so far equal to the
specification's (`WInv`).
-/

namespace VG.Proof.Aes

open VG.Arm in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
32-bit ARM contract for `vg_aes_expand_key(key = r0, key_len = r1,
schedule = r2, scratch = r3)`: writes the key schedule of the
`key_len`-byte key at `key` to `schedule`.

The code may read `key` (`key_len` bytes) and read and write `schedule`
(240 bytes) and `scratch` (512 bytes, whose contents on exit are
unspecified). These may not overlap each other or wrap around the end of the
(32-bit) address space. `key_len` is 16, 24 or 32. The pointers and
`key_len` are public; the key is secret. -/
def expandKeyArm : Contract Arm.isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let sched : Region := ⟨State.addr (s.gpr .r2), 240⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 512⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧
    key.Disjoint sched ∧ key.Disjoint scratch ∧ sched.Disjoint scratch ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 240 ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + 512 ≤ 2 ^ 32 ∧
    ((s.gpr .r1).toNat = 16 ∨ (s.gpr .r1).toNat = 24 ∨ (s.gpr .r1).toNat = 32)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r2)) (16 * (Spec.Aes.rounds ((s.gpr .r1).toNat / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3

end VG.Proof.Aes

namespace VG.Proof.Aes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr op2_lsl wp_mov wp_add wp_sub wp_subs
  wp_cmp wp_orr wp_and wp_ldr wp_str)
open VG.Proof.Aes (getD_eq byte_ext kw kTemp kw_step kw_key kw_length kTemp_length xorWord_getD
  subWord_getD rotWord_getD rotWord_length rcon_getD flatten_expandWords)
open VG.Spec.Aes (sbox xtimes subBytes subWord rotWord rcon xorWord)

/-! ## The S-box on every byte -/

/-- The two states that the words hold, as `InRel` relates them. -/
def stOf (Q : Nat → BitVec 32) (b : Nat) : Spec.Aes.State :=
  Vector.ofFn fun i => (Q (2 * (i.1 / 4) + b)).extractLsb' (8 * (i.1 % 4)) 8

theorem inRel_stOf (Q : Nat → BitVec 32) : InRel Q (stOf Q) := by
  intro b hb i hi j hj
  rw [getD_eq _ hi, stOf, Vector.getElem_ofFn, BitVec.getLsbD_extractLsb']
  simp [hj]

section
variable {is : List Instr} {s : State} {Q' : State → Prop} {b : BitVec 32} {L : Nat}

theorem slot_in' {rs : List Region} (hr : (⟨State.addr b, L⟩ : Region) ∈ rs)
    (hfit : b.toNat + L ≤ 2 ^ 32) {k : Nat} (hk : 4 * k + 4 ≤ L) : InRegions rs (slotA (State.addr b) k) 4 := by
  rw [← slot_addr' hfit hk]; exact in_off hr hfit (by omega) (by omega)

theorem wp_ldS' {t : Reg} {k : Nat} (hb : s.gpr sb = b) (hscr : (⟨State.addr b, L⟩ : Region) ∈ s.wr)
    (hfit : b.toNat + L ≤ 2 ^ 32) (hk : 4 * k + 4 ≤ L) (hk' : 4 * k < 4096)
    (c : ∀ s', Upd s s' t (s.mem.readW (slotA (State.addr b) k) 32) → WP isa (.block is) s' Q') :
    WP isa (.block (ldS t k :: is)) s Q' :=
  wp_ldr hk' (by rw [hb]; exact slot_addr' hfit hk) (slot_in' (List.mem_append_right _ hscr) hfit hk) c

theorem wp_stS' {t : Reg} {k : Nat} (hb : s.gpr sb = b) (hscr : (⟨State.addr b, L⟩ : Region) ∈ s.wr)
    (hfit : b.toNat + L ≤ 2 ^ 32) (hk : 4 * k + 4 ≤ L) (hk' : 4 * k < 4096)
    (c : ∀ s', Mupd s s' (s.mem.writeW (slotA (State.addr b) k) (s.gpr t)) → WP isa (.block is) s' Q') :
    WP isa (.block (stS k t :: is)) s Q' :=
  wp_str hk' (by rw [hb]; exact slot_addr' hfit hk) (slot_in' hscr hfit hk) c

end

/-- The registers `subAll` may change: the state's. -/
def qRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7]

theorem lslot_frame (B : Addr) {k : Nat} (h1 : 42 ≤ k) (h2 : k < 46) :
    (⟨B + BitVec.ofNat 64 168, 16⟩ : Region).Contains (slotA B k) (32 / 8) := by
  simp only [Region.Contains, slotA]
  rw [show B + BitVec.ofNat 64 (4 * k) - (B + BitVec.ofNat 64 168) = BitVec.ofNat 64 (4 * k - 168) by
    bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem subAll_wp {s : State} {b : BitVec 32} (hb : s.gpr sb = b)
    (hscr : (⟨State.addr b, 512⟩ : Region) ∈ s.wr) (hfit : b.toNat + 512 ≤ 2 ^ 32) {P : State → Prop}
    (h : ∀ s', (∀ k < 8, ∀ t < 4, (Q s' k).extractLsb' (8 * t) 8 = sbox ((Q s k).extractLsb' (8 * t) 8)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → (∀ r, r ∉ qRegs → s'.gpr r = s.gpr r) →
      Frame [⟨State.addr b, 128⟩, ⟨State.addr b + BitVec.ofNat 64 168, 16⟩] s.mem s'.mem → P s') :
    WP isa (.block subAll) s P := by
  simp only [subAll, loopRegs, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
    List.nil_append]
  let B := State.addr b
  refine wp_stS' hb hscr hfit (by decide) (by decide) fun s₁ u₁ => ?_
  refine wp_stS' (u₁.gpr ▸ hb) (u₁.wr ▸ hscr) hfit (by decide) (by decide) fun s₂ u₂ => ?_
  refine wp_stS' (u₂.gpr ▸ u₁.gpr ▸ hb) (u₂.wr ▸ u₁.wr ▸ hscr) hfit (by decide) (by decide)
    fun s₃ u₃ => ?_
  refine wp_stS' (u₃.gpr ▸ u₂.gpr ▸ u₁.gpr ▸ hb) (u₃.wr ▸ u₂.wr ▸ u₁.wr ▸ hscr) hfit (by decide)
    (by decide) fun s₄ u₄ => ?_
  have g₄ : s₄.gpr = s.gpr := by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have m₄ : s₄.mem = (((s.mem.writeW (slotA B 42) (s.gpr .r10)).writeW (slotA B 43) (s.gpr .r11)).writeW
      (slotA B 44) (s.gpr .r12)).writeW (slotA B 45) (s.gpr .lr) := by
    simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr, B]
  rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₅, hs₅, h₅, rd₅, wr₅, sp₅, o₅, m₅⟩ := ortho_ok' s₄
  refine WP.of_runBlock ⟨s₅, hs₅, ?_⟩
  have hb₅ : s₅.gpr sb = b := by rw [o₅ _ (by decide), g₄, hb]
  rw [WP.block_append_iff (M := isa)]
  have ok₅ : Ok sboxCfg s₅ := Ok.of_off (off := 0) (by rw [wr₅, wr₄]; exact hscr) hfit
    (by show s₅.gpr sb = _; rw [hb₅]; simp) (by simp [sboxCfg]) rfl
  obtain ⟨s₆, hs₆, h₆, rd₆, wr₆, sp₆, o₆, f₆⟩ := sbox_ok ok₅
  refine WP.of_runBlock ⟨s₆, hs₆, ?_⟩
  rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₇, hs₇, h₇, rd₇, wr₇, sp₇, o₇, m₇⟩ := ortho_ok' s₆
  refine WP.of_runBlock ⟨s₇, hs₇, ?_⟩
  have hb₇ : s₇.gpr sb = b := by rw [o₇ _ (by decide), o₆ _ (by decide), hb₅]
  have wr₇' : s₇.wr = s.wr := by rw [wr₇, wr₆, wr₅, wr₄]
  have f₆' : Frame [⟨B, 128⟩] s₅.mem s₆.mem := by
    have := f₆; simp only [slotRegion, sboxCfg, hb₅] at this; exact this
  have lslot : ∀ k, 42 ≤ k → k < 46 → s₇.mem.readW (slotA B k) 32 = s₄.mem.readW (slotA B k) 32 := by
    intro k h1 h2
    rw [m₇, f₆'.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (scr_disj (lx := 128) (y := 4 * k) (ly := 4) _ (by omega) (by omega)).symm) (by decide), m₅]
  refine wp_ldS' hb₇ (by rw [wr₇']; exact hscr) hfit (by decide) (by decide) fun s₈ u₈ => ?_
  refine wp_ldS' (by rw [u₈.other _ (by decide), hb₇]) (by rw [u₈.wr, wr₇']; exact hscr) hfit
    (by decide) (by decide) fun s₉ u₉ => ?_
  refine wp_ldS' (by rw [u₉.other _ (by decide), u₈.other _ (by decide), hb₇])
    (by rw [u₉.wr, u₈.wr, wr₇']; exact hscr) hfit (by decide) (by decide) fun s₁₀ u₁₀ => ?_
  refine wp_ldS' (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), hb₇])
    (by rw [u₁₀.wr, u₉.wr, u₈.wr, wr₇']; exact hscr) hfit (by decide) (by decide) fun s₁₁ u₁₁ => ?_
  refine WP.block_nil (h s₁₁ (fun k hk t ht => ?_) ?_ ?_ ?_ (fun r hr => ?_) ?_)
  · have hin := in_of_bs h₇ (bs_subBytes h₆ (bs_of_in h₅ (inRel_stOf (Q s₄))))
    have gq : ∀ i < 8, Q s₁₁ i = Q s₇ i := fun i hi => by
      have : q i ≠ .r10 ∧ q i ≠ .r11 ∧ q i ≠ .r12 ∧ q i ≠ .lr := by revert hi; revert i; decide
      simp only [Q]
      rw [u₁₁.other _ this.2.2.2, u₁₀.other _ this.2.2.1, u₉.other _ this.2.1, u₈.other _ this.1]
    refine byte_ext fun j hj => ?_
    have := hin (k % 2) (by omega) (4 * (k / 2) + t) (by omega) j hj
    rw [show 2 * ((4 * (k / 2) + t) / 4) + k % 2 = k by omega,
      show 8 * ((4 * (k / 2) + t) % 4) + j = 8 * t + j by omega] at this
    rw [BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and, gq k hk, this, getD_eq _ (by omega)]
    simp only [subBytes, Vector.getElem_map, stOf, Vector.getElem_ofFn]
    rw [show 2 * ((4 * (k / 2) + t) / 4) + k % 2 = k by omega,
      show (4 * (k / 2) + t) % 4 = t by omega]
    simp only [Q, g₄]
  · rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, rd₇, rd₆, rd₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇']
  · rw [u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, sp₇, sp₆, sp₅, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · have e₁ : s₇.mem.readW (slotA B 42) 32 = s.gpr .r10 := by
      rw [lslot 42 (by omega) (by omega), m₄, readW_writeW_slot _ _ (by decide) (by decide) (by decide),
        readW_writeW_slot _ _ (by decide) (by decide) (by decide),
        readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    have e₂ : s₇.mem.readW (slotA B 43) 32 = s.gpr .r11 := by
      rw [lslot 43 (by omega) (by omega), m₄, readW_writeW_slot _ _ (by decide) (by decide) (by decide),
        readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    have e₃ : s₇.mem.readW (slotA B 44) 32 = s.gpr .r12 := by
      rw [lslot 44 (by omega) (by omega), m₄, readW_writeW_slot _ _ (by decide) (by decide) (by decide),
        Mem.readW_writeW_self32]
    have e₄ : s₇.mem.readW (slotA B 45) 32 = s.gpr .lr := by
      rw [lslot 45 (by omega) (by omega), m₄, Mem.readW_writeW_self32]
    by_cases h10 : r = .r10
    · subst h10; rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, e₁]
    by_cases h11 : r = .r11
    · subst h11; rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.mem, e₂]
    by_cases h12 : r = .r12
    · subst h12; rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.mem, u₈.mem, e₃]
    by_cases hlr : r = .lr
    · subst hlr; rw [u₁₁.gpr, u₁₀.mem, u₉.mem, u₈.mem, e₄]
    have hl : r ∉ layerWrites := by
      revert hr h10 h11 h12 hlr; cases r <;> simp [qRegs, layerWrites]
    have ho : r ∉ orthoWrites := by
      revert hr h10 h11 h12 hlr; cases r <;> simp [qRegs, orthoWrites]
    rw [u₁₁.other _ hlr, u₁₀.other _ h12, u₉.other _ h11, u₈.other _ h10, o₇ r ho, o₆ r hl, o₅ r ho, g₄]
  · rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, m₇]
    refine Frame.trans ?_ ((f₆'.trans (Frame.refl _ _)).mono (by simp [B]))
    rw [m₅, m₄]
    have hm : (⟨B + BitVec.ofNat 64 168, 16⟩ : Region) ∈
        [(⟨B, 128⟩ : Region), ⟨B + BitVec.ofNat 64 168, 16⟩] := by simp
    exact ((((Frame.refl _ _).writeW hm _ (lslot_frame _ (by decide) (by decide))).writeW hm _
      (lslot_frame _ (by decide) (by decide))).writeW hm _ (lslot_frame _ (by decide) (by decide))).writeW
      hm _ (lslot_frame _ (by decide) (by decide))

/-! ## One instruction at a time -/

section
variable {is : List Instr} {s : State} {Q' : State → Prop}

theorem op2_ror {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .ror n).eval s = some ((s.gpr r).rotateRight n) := by
  simp [Op2.eval, h]

theorem wp_eor' {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q') :
    WP isa (.block (.dp .eor d n o :: is)) s Q' :=
  VG.Proof.MdStream.Arm.WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho])
    (k _ (Upd.setReg _ _ _))

theorem wp_mul {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n * s.gpr m) → WP isa (.block is) s' Q') :
    WP isa (.block (.mul d n m :: is)) s Q' :=
  VG.Proof.MdStream.Arm.WP.cons rfl (k _ (Upd.setReg _ _ _))

end

/-! ## The scalar blocks -/

/-- The round constant after one more round. -/
def rcNext (v : BitVec 32) : BitVec 32 := ((v <<< 1) ^^^ (v >>> 7) * 0x1b) &&& 0xff

/-- `ROTWORD(q 0) ⊕ Rcon`, and the next round constant. -/
theorem rotTail_wp {s : State} {b : BitVec 32} (hb : s.gpr sb = b)
    (hscr : (⟨State.addr b, 512⟩ : Region) ∈ s.wr) (hfit : b.toNat + 512 ≤ 2 ^ 32) {P : State → Prop}
    (h : ∀ s', s'.gpr (q 0) = (s.gpr (q 0)).rotateRight 8 ^^^ s.mem.readW (slotA (State.addr b) rconSlot) 32 →
      s'.mem = s.mem.writeW (slotA (State.addr b) rconSlot)
        (rcNext (s.mem.readW (slotA (State.addr b) rconSlot) 32)) →
      (∀ r, r ∉ qRegs → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → P s') :
    WP isa (.block rotTail) s P := by
  simp only [rotTail]
  refine wp_mov (op2_ror (by decide)) fun s₁ u₁ => ?_
  refine wp_ldS' (by rw [u₁.other _ (by decide), hb]) (by rw [u₁.wr]; exact hscr) hfit (by decide)
    (by decide) fun s₂ u₂ => ?_
  refine wp_eor' (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₄ u₄ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₅ u₅ => ?_
  refine wp_mul fun s₆ u₆ => ?_
  refine wp_mov (op2_lsl (by decide)) fun s₇ u₇ => ?_
  refine wp_eor' (op2_reg _ _) fun s₈ u₈ => ?_
  refine wp_and (op2_imm (by decide)) fun s₉ u₉ => ?_
  have hb₉ : s₉.gpr sb = b := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hb]
  refine wp_stS' hb₉ (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hscr)
    hfit (by decide) (by decide) fun s₁₀ u₁₀ => WP.block_nil (h s₁₀ ?_ ?_ (fun r hr => ?_) ?_ ?_ ?_)
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.gpr, u₂.gpr, u₁.mem]
  · have hv : s₂.gpr (q 1) = s.mem.readW (slotA (State.addr b) rconSlot) 32 := by rw [u₂.gpr, u₁.mem]
    have v₆ : s₆.gpr (q 1) = s.mem.readW (slotA (State.addr b) rconSlot) 32 := by
      rw [u₆.other (q 1) (by decide), u₅.other (q 1) (by decide), u₄.other (q 1) (by decide),
        u₃.other (q 1) (by decide), hv]
    have v₇ : s₇.gpr (q 2) = (s.mem.readW (slotA (State.addr b) rconSlot) 32 >>> 7) * 0x1b := by
      rw [u₇.other (q 2) (by decide), u₆.gpr, u₅.gpr, u₅.other (q 2) (by decide), u₄.gpr,
        u₃.other (q 1) (by decide), hv]
    rw [u₁₀.mem, u₉.gpr, u₈.gpr, u₇.gpr, v₆, v₇, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem,
      u₂.mem, u₁.mem, rcNext]
  · have : r ≠ q 0 ∧ r ≠ q 1 ∧ r ≠ q 2 ∧ r ≠ q 3 := by revert hr; cases r <;> simp [qRegs, q]
    rw [u₁₀.gpr, u₉.other _ this.2.1, u₈.other _ this.2.1, u₇.other _ this.2.1, u₆.other _ this.2.2.1,
      u₅.other _ this.2.2.2, u₄.other _ this.2.2.1, u₃.other _ this.1, u₂.other _ this.2.1, u₁.other _ this.1]
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-! ## Bytes -/

/-- The round constant slot's value: `x^k`. -/
def rcW (k : Nat) : BitVec 32 := (Nat.repeat xtimes k (1 : Byte)).setWidth 32

theorem rcNext_rcW : ∀ k < 10, rcNext (rcW k) = rcW (k + 1) := by decide

theorem rcW_zero : rcW 0 = 1 := by decide

theorem rcW_byte (k : Nat) {t : Nat} (ht : t < 4) :
    (rcW k).extractLsb' (8 * t) 8 = if t = 0 then Nat.repeat xtimes k 1 else 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [rcW, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  split
  · subst_vars; simp [hj]; intro; omega
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp

theorem xor_byte (x y : BitVec 32) (t : Nat) :
    (x ^^^ y).extractLsb' (8 * t) 8 = x.extractLsb' (8 * t) 8 ^^^ y.extractLsb' (8 * t) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [hj]

theorem rot_byte (x : BitVec 32) {t : Nat} (ht : t < 4) :
    (x.rotateRight 8).extractLsb' (8 * t) 8 = x.extractLsb' (8 * ((t + 1) % 4)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight]
  simp only [hj, decide_true, Bool.true_and]
  by_cases h : t < 3
  · rw [ite_eq_left ((show 8 * t + j < 32 - 8 % 32 by omega)),
      show 8 % 32 + (8 * t + j) = 8 * ((t + 1) % 4) + j by omega]
  · rw [ite_eq_right ((show ¬ 8 * t + j < 32 - 8 % 32 by omega)),
      show 8 * t + j - (32 - 8 % 32) = 8 * ((t + 1) % 4) + j by omega]
    simp [show 8 * t + j < 32 by omega]

theorem ld_byte (m : Mem) (a : Addr) {t : Nat} (ht : t < 4) :
    (m.readW a 32).extractLsb' (8 * t) 8 = m (a + BitVec.ofNat 64 t) :=
  (Mem.readW_byte m a ht).symm


/-! ## Arithmetic -/

theorem chk_beq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (((BitVec.ofNat 32 a - 4) ||| (BitVec.ofNat 32 b - 8)) - 0 == 0) = decide (a = 4 ∧ b = 8) := by
  have e0 : ∀ x : BitVec 32, x - (0 : BitVec 32) = x := fun x => by bv_omega
  rw [e0]
  by_cases h : a = 4 ∧ b = 8
  · obtain ⟨rfl, rfl⟩ := h
    decide
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro heq
    obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp heq
    apply h; constructor <;> bv_omega

theorem next_beq {a n : Nat} (ha : a < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 a + 1 - BitVec.ofNat 32 n == 0) = decide (a + 1 = n) := by
  by_cases h : a + 1 = n
  · simp only [h, decide_true, beq_iff_eq]; bv_omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]; bv_omega

theorem div_pred_zero {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (hi : nk ≤ i) (h : i % nk = 0) :
    (i - 1) / nk + 1 = i / nk := by
  rcases h3 with rfl | rfl | rfl <;> omega

theorem div_pred_ne {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (h : i % nk ≠ 0) :
    (i - 1) / nk = i / nk := by
  rcases h3 with rfl | rfl | rfl <;> omega

theorem rot_lt {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (hn : i < 4 * (nk + 7)) (h : i % nk = 0) :
    (i - 1) / nk < 10 := by
  rcases h3 with rfl | rfl | rfl <;> omega

theorem sub_scr' (B : Addr) {x lx : Nat} (h : x + lx ≤ 512) :
    Region.Sub ⟨B + BitVec.ofNat 64 x, lx⟩ ⟨B, 512⟩ := by
  intro a h₁
  simp only [Region.Contains] at h₁ ⊢
  have : (BitVec.ofNat 64 x).toNat = x := by simp; omega
  bv_omega

/-! ## One word -/

/-- The setting of the word loop: the schedule at `S`, the scratch buffer
at `B`, and the key `kl` of `nk` words. -/
structure WSetup (s₀ : State) (S B : BitVec 32) (kl : List Byte) (nk : Nat) : Prop where
  nk3 : nk = 4 ∨ nk = 6 ∨ nk = 8
  len : kl.length = 4 * nk
  sch : (⟨State.addr S, 240⟩ : Region) ∈ s₀.wr
  scr : (⟨State.addr B, 512⟩ : Region) ∈ s₀.wr
  fitS : S.toNat + 240 ≤ 2 ^ 32
  fitB : B.toNat + 512 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨State.addr S, 240⟩ ⟨State.addr B, 512⟩

/-- Before word `i`. -/
structure WInv (s₀ : State) (S B : BitVec 32) (kl : List Byte) (nk i : Nat) (s : State) : Prop where
  hi : nk ≤ i
  hn : i < 4 * (nk + 7)
  r10 : s.gpr .r10 = S + BitVec.ofNat 32 (4 * i)
  r9 : s.gpr .r9 = S + BitVec.ofNat 32 (4 * (i - nk))
  r12 : s.gpr .r12 = BitVec.ofNat 32 nk
  r11 : s.gpr .r11 = BitVec.ofNat 32 (i % nk)
  lr : s.gpr .lr = BitVec.ofNat 32 (4 * (nk + 7) - i)
  r8 : s.gpr sb = B
  temp : ∀ t < 4, (s.gpr (q 0)).extractLsb' (8 * t) 8 = (kw kl nk (i - 1)).getD t 0
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  sched : ∀ k < 4 * i, s.mem (State.addr S + BitVec.ofNat 64 k) = (kw kl nk (k / 4)).getD (k % 4) 0
  rc : s.mem.readW (slotA (State.addr B) rconSlot) 32 = rcW ((i - 1) / nk)
  saved : Saved s₀ (State.addr B) s.mem
  frame : Frame [⟨State.addr S, 240⟩, ⟨State.addr B, 512⟩] s₀.mem s.mem

/-- After the last word. -/
structure WDone (s₀ : State) (S B : BitVec 32) (kl : List Byte) (nk : Nat) (s : State) : Prop where
  r8 : s.gpr sb = B
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  sched : ∀ k < 16 * (nk + 7), s.mem (State.addr S + BitVec.ofNat 64 k) = (kw kl nk (k / 4)).getD (k % 4) 0
  saved : Saved s₀ (State.addr B) s.mem
  frame : Frame [⟨State.addr S, 240⟩, ⟨State.addr B, 512⟩] s₀.mem s.mem

/-- `temp` computed (in `q 0`), from `s`. -/
structure Mid (B : BitVec 32) (kl : List Byte) (nk i : Nat) (s s' : State) : Prop where
  temp : ∀ t < 4, (s'.gpr (q 0)).extractLsb' (8 * t) 8 = (kTemp nk i (kw kl nk (i - 1))).getD t 0
  keep : ∀ r, r ∉ qRegs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨State.addr B, 128⟩, ⟨State.addr B + BitVec.ofNat 64 164, 20⟩] s.mem s'.mem
  rc : s'.mem.readW (slotA (State.addr B) rconSlot) 32 = rcW (i / nk)

theorem WInv.fupd {s₀ : State} {S B : BitVec 32} {kl : List Byte} {nk i : Nat} {s s' : State}
    (hi : WInv s₀ S B kl nk i s) (f : Fupd s s') : WInv s₀ S B kl nk i s' :=
  { hi with
    r10 := by rw [f.gpr]; exact hi.r10, r9 := by rw [f.gpr]; exact hi.r9
    r12 := by rw [f.gpr]; exact hi.r12, r11 := by rw [f.gpr]; exact hi.r11
    lr := by rw [f.gpr]; exact hi.lr, r8 := by rw [f.gpr]; exact hi.r8
    temp := by rw [f.gpr]; exact hi.temp, rd := by rw [f.rd]; exact hi.rd
    wr := by rw [f.wr]; exact hi.wr, sp := by rw [f.sp]; exact hi.sp
    sched := by rw [f.mem]; exact hi.sched, rc := by rw [f.mem]; exact hi.rc
    saved := by rw [f.mem]; exact hi.saved, frame := by rw [f.mem]; exact hi.frame }

theorem rc_off_frame (B : Addr) : ∀ r ∈ [(⟨B, 128⟩ : Region), ⟨B + BitVec.ofNat 64 168, 16⟩],
    Region.Disjoint ⟨slotA B rconSlot, 32 / 8⟩ r := by
  rw [show slotA B rconSlot = B + BitVec.ofNat 64 164 from rfl]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (scr_disj (lx := 128) (y := 164) (ly := 4) _ (by omega) (by omega)).symm
  · exact off_disjoint _ (by omega) (by omega) (by omega)

theorem subAll_frame {B : Addr} {m m' : Mem}
    (h : Frame [⟨B, 128⟩, ⟨B + BitVec.ofNat 64 168, 16⟩] m m') :
    Frame [⟨B, 128⟩, ⟨B + BitVec.ofNat 64 164, 20⟩] m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨B + BitVec.ofNat 64 164, 20⟩, by simp, off_sub _ (by omega) (by omega) (by omega)⟩

/-- `SUBWORD(ROTWORD(temp)) ⊕ Rcon`, and the next round constant. -/
theorem rot_wp {s₀ : State} {S B : BitVec 32} {kl : List Byte} {nk i : Nat} (hs : WSetup s₀ S B kl nk)
    {s : State} (hi : WInv s₀ S B kl nk i s) (h0 : i % nk = 0) :
    WP isa (.block rotWordStep) s (Mid B kl nk i s) := by
  have h3 := hs.nk3
  have hi1 := hi.hi
  have hn := hi.hn
  have hlen := kw_length hs.len (by omega) (i - 1)
  have hscr : (⟨State.addr B, 512⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hs.scr
  simp only [rotWordStep]
  rw [WP.block_append_iff (M := isa)]
  refine subAll_wp hi.r8 hscr hs.fitB fun s₂ h₂ rd₂ wr₂ sp₂ o₂ f₂ => ?_
  have rc₂ : s₂.mem.readW (slotA (State.addr B) rconSlot) 32 = rcW ((i - 1) / nk) := by
    rw [f₂.readW (Region.contains_self _ _) (rc_off_frame _) (by decide), hi.rc]
  refine rotTail_wp (by rw [o₂ _ (by decide), hi.r8]) (by rw [wr₂]; exact hscr) hs.fitB
    fun s₃ q₃ m₃ o₃ rd₃ wr₃ sp₃ => ⟨fun t ht => ?_, fun r hr => (o₃ r hr).trans (o₂ r hr),
      rd₃.trans rd₂, wr₃.trans wr₂, sp₃.trans sp₂, ?_, ?_⟩
  · rw [q₃, xor_byte, rot_byte _ ht, h₂ 0 (by omega) _ (by omega), hi.temp _ (by omega), rc₂,
      rcW_byte _ ht]
    simp only [kTemp, h0, ite_true]
    rw [xorWord_getD (by simp [subWord, rotWord_length hlen]) (by rfl) ht,
      subWord_getD (by rw [rotWord_length hlen]; exact ht), rotWord_getD hlen ht, rcon_getD _ ht,
      ← div_pred_zero h3 hi1 h0, Nat.add_sub_cancel]
  · rw [m₃]
    refine Frame.writeW (r := ⟨State.addr B + BitVec.ofNat 64 164, 20⟩) (subAll_frame f₂) (by simp) _ ?_
    simp only [Region.Contains, slotA, rconSlot]
    rw [show State.addr B + BitVec.ofNat 64 (4 * 41) - (State.addr B + BitVec.ofNat 64 164) = 0 by
      bv_omega]
    decide
  · rw [m₃, Mem.readW_writeW_self32, rc₂, rcNext_rcW _ (rot_lt h3 hn h0), div_pred_zero h3 hi1 h0]

theorem temp_wp {s₀ : State} {S B : BitVec 32} {kl : List Byte} {nk i : Nat} (hs : WSetup s₀ S B kl nk)
    {s : State} (hi : WInv s₀ S B kl nk i s) (hz : s.z = (s.gpr .r11 - 0 == 0)) :
    WP isa (.ite .eq (.block rotWordStep)
      (.seq (.block [.dp .sub (q 1) .r11 (.imm 4), .dp .sub (q 2) .r12 (.imm 8),
          .dp .orr (q 1) (q 1) (.reg (q 2)), .cmp (q 1) (.imm 0)])
        (.ite .eq (.block subAll) (.block [])))) s (Mid B kl nk i s) := by
  have h3 := hs.nk3
  have hnk : 0 < nk := by omega
  have hmod := Nat.mod_lt i hnk
  have hlen := kw_length hs.len hnk (i - 1)
  have e0 : ∀ x : BitVec 32, x - (0 : BitVec 32) = x := fun x => by bv_omega
  have hev : Arm.eval .eq s = some (decide (i % nk = 0)) := by
    simp only [Arm.eval, hz, hi.r11, e0, VG.Proof.MdStream.Arm.ofNat_beq_zero (show i % nk < 2 ^ 32 by omega)]
  refine WP.ite _ hev (fun hb => rot_wp hs hi (by simpa using hb)) (fun hb => ?_)
  have h0 : i % nk ≠ 0 := by simpa using hb
  refine WP.seq (wp_sub (op2_imm (by decide)) fun s₁ u₁ => wp_sub (op2_imm (by decide)) fun s₂ u₂ =>
    wp_orr (op2_reg _ _) fun s₃ u₃ => wp_cmp (op2_imm (by decide)) fun s₄ f₄ z₄ => WP.block_nil ?_)
  have hev₄ : Arm.eval .eq s₄ = some (decide (i % nk = 4 ∧ nk = 8)) := by
    simp only [Arm.eval, z₄, u₃.gpr, u₂.gpr, u₂.other (q 1) (by decide), u₁.gpr, u₁.other .r12 (by decide),
      hi.r11, hi.r12]
    rw [chk_beq (by omega) (by omega)]
  have g₄ : ∀ r, r ∉ qRegs → s₄.gpr r = s.gpr r := fun r hr => by
    have : r ≠ q 1 ∧ r ≠ q 2 := by revert hr; cases r <;> simp [qRegs, q]
    rw [f₄.gpr, u₃.other _ this.1, u₂.other _ this.2, u₁.other _ this.1]
  have hq0 : s₄.gpr (q 0) = s.gpr (q 0) := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have m₄ : s₄.mem = s.mem := by rw [f₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₄ : s₄.rd = s.rd := by rw [f₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₄ : s₄.wr = s.wr := by rw [f₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp₄ : s₄.sp = s.sp := by rw [f₄.sp, u₃.sp, u₂.sp, u₁.sp]
  refine WP.ite _ hev₄ (fun hb₄ => ?_) (fun hb₄ => ?_)
  · -- `SUBWORD(temp)`.
    have h8 : nk = 8 ∧ i % nk = 4 := by simp at hb₄; omega
    refine subAll_wp (by rw [g₄ _ (by decide), hi.r8]) (by rw [wr₄, hi.wr]; exact hs.scr) hs.fitB
      fun s₅ h₅ rd₅ wr₅ sp₅ o₅ f₅ => ?_
    rw [m₄] at f₅
    refine ⟨fun t ht => ?_, fun r hr => (o₅ r hr).trans (g₄ r hr), rd₅.trans rd₄, wr₅.trans wr₄,
      sp₅.trans sp₄, subAll_frame f₅, ?_⟩
    · rw [h₅ 0 (by omega) _ ht, show Q s₄ 0 = s₄.gpr (q 0) from rfl, hq0, hi.temp _ ht]
      rw [kTemp, ite_eq_right h0, ite_eq_left (show nk > 6 ∧ i % nk = 4 by omega),
        subWord_getD (by rw [hlen]; exact ht)]
    · rw [f₅.readW (Region.contains_self _ _) (rc_off_frame _) (by decide), hi.rc, div_pred_ne h3 h0]
  · have h8 : ¬ (nk > 6 ∧ i % nk = 4) := by simp at hb₄; omega
    refine WP.block_nil ⟨fun t ht => ?_, g₄, rd₄, wr₄, sp₄, by rw [m₄]; exact Frame.refl _ _, ?_⟩
    · rw [hq0, hi.temp _ ht, kTemp, ite_eq_right h0, ite_eq_right h8]
    · rw [m₄, hi.rc, div_pred_ne h3 h0]

/-- The memory after word `i` is stored. -/
def storeMem (s₂ : State) (S : Addr) (nk i : Nat) : Mem :=
  s₂.mem.writeW (S + BitVec.ofNat 64 (4 * i))
    (s₂.gpr (q 0) ^^^ s₂.mem.readW (S + BitVec.ofNat 64 (4 * (i - nk))) 32)

theorem sched_addr {S : BitVec 32} (hfit : S.toNat + 240 ≤ 2 ^ 32) {k : Nat} (hk : k < 240) :
    State.addr (S + BitVec.ofNat 32 k) = State.addr S + BitVec.ofNat 64 k := addr_add (by omega)

theorem c_off240 (SA : Addr) {x n : Nat} (h : x + n ≤ 240) :
    (⟨SA, 240⟩ : Region).Contains (SA + BitVec.ofNat 64 x) n := by
  simp only [Region.Contains]
  rw [show SA + BitVec.ofNat 64 x - SA = BitVec.ofNat 64 x by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem saved_frame {s₀ : State} {B : Addr} {m m' : Mem} {rs : List Region} (h : Saved s₀ B m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨B + BitVec.ofNat 64 128, 36⟩ r) :
    Saved s₀ B m' := fun i hi => by
  rw [← h i hi]
  refine hf.readW ?_ hd (by decide)
  simp only [Region.Contains, slotA]
  rw [show B + BitVec.ofNat 64 (4 * (32 + i)) - (B + BitVec.ofNat 64 128) = BitVec.ofNat 64 (4 * i) by
    bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem store_facts {s₀ : State} {S B : BitVec 32} {kl : List Byte} {nk i : Nat}
    (hs : WSetup s₀ S B kl nk) {s s₂ : State} (hi : WInv s₀ S B kl nk i s) (hm : Mid B kl nk i s s₂) :
    (∀ k < 4 * (i + 1), storeMem s₂ (State.addr S) nk i (State.addr S + BitVec.ofNat 64 k) =
      (kw kl nk (k / 4)).getD (k % 4) 0) ∧
    Frame [⟨State.addr S, 240⟩, ⟨State.addr B, 512⟩] s₀.mem (storeMem s₂ (State.addr S) nk i) ∧
    Saved s₀ (State.addr B) (storeMem s₂ (State.addr S) nk i) ∧
    (storeMem s₂ (State.addr S) nk i).readW (slotA (State.addr B) rconSlot) 32 = rcW (i / nk) := by
  have h3 := hs.nk3
  have hnk : 0 < nk := by omega
  have hi1 := hi.hi
  have hn := hi.hn
  have hsub : ∀ r ∈ [(⟨(State.addr B), 128⟩ : Region), ⟨(State.addr B) + BitVec.ofNat 64 164, 20⟩], Region.Sub r ⟨(State.addr B), 512⟩ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by decide)
    · exact sub_scr' _ (by omega)
  have fS : ∀ k < 240, s₂.mem ((State.addr S) + BitVec.ofNat 64 k) = s.mem ((State.addr S) + BitVec.ofNat 64 k) := fun k hk =>
    hm.frame.bytes (R := ⟨(State.addr S), 240⟩) (fun r hr => hs.sep.sub_right (hsub r hr)) (by simp) hk
  have sched' : ∀ k < 4 * (i + 1),
      storeMem s₂ (State.addr S) nk i ((State.addr S) + BitVec.ofNat 64 k) = (kw kl nk (k / 4)).getD (k % 4) 0 := by
    intro k hk
    unfold storeMem
    by_cases hki : k < 4 * i
    · rw [writeW32_other _ (off_disjoint (State.addr S) (Or.inl (by omega)) (by omega) (by omega)), fS k (by omega),
        hi.sched k hki]
    · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 4 ∧ k = 4 * i + t := ⟨k - 4 * i, by omega, by omega⟩
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, st_byte _ _ _ ht, xor_byte, hm.temp t ht,
        ← Mem.readW_byte _ _ ht, BitVec.add_assoc, ← BitVec.ofNat_add, fS _ (by omega),
        hi.sched _ (by omega), show (4 * (i - nk) + t) / 4 = i - nk by omega,
        show (4 * (i - nk) + t) % 4 = t by omega, show (4 * i + t) / 4 = i by omega,
        show (4 * i + t) % 4 = t by omega, kw_step kl hnk hi1,
        xorWord_getD (kw_length hs.len hnk _) (kTemp_length (kw_length hs.len hnk _)) ht, BitVec.xor_comm]
  have fr : Frame [⟨(State.addr S), 240⟩, ⟨(State.addr B), 512⟩] s₀.mem (storeMem s₂ (State.addr S) nk i) := by
    unfold storeMem
    refine Frame.writeW (hi.frame.trans (hm.frame.sub fun r hr => ⟨⟨(State.addr B), 512⟩, by simp, hsub r hr⟩))
      (r := ⟨(State.addr S), 240⟩) (by simp) _ (c_off240 (State.addr S) (by omega))
  have d1 : Region.Disjoint ⟨(State.addr S), 240⟩ ⟨(State.addr B) + BitVec.ofNat 64 128, 36⟩ :=
    hs.sep.sub_right (sub_scr' _ (by omega))
  have sv : Saved s₀ (State.addr B) (storeMem s₂ (State.addr S) nk i) := by
    unfold storeMem
    refine saved_frame (saved_frame hi.saved hm.frame fun r hr => ?_)
      (Frame.writeW (Frame.refl [⟨(State.addr S) + BitVec.ofNat 64 (4 * i), 4⟩] _) (by simp) _
        (Region.contains_self _ _)) fun r hr => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (scr_disj (lx := 128) (y := 128) (ly := 36) _ (by omega) (by omega)).symm
      · exact off_disjoint _ (by omega) (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact (d1.sub_left (VG.Proof.MdStream.Arm.sub_offset (by omega) (by omega))).symm
  have rc : (storeMem s₂ (State.addr S) nk i).readW (slotA (State.addr B) rconSlot) 32 = rcW (i / nk) := by
    have hsl : Region.Sub ⟨slotA (State.addr B) rconSlot, 32 / 8⟩ ⟨State.addr B, 512⟩ :=
      sub_scr' (x := 164) (lx := 4) _ (by omega)
    rw [storeMem, Mem.readW_writeW_sep ((hs.sep.sub_right hsl).symm.sep
      (Region.contains_self _ _) (c_off240 (State.addr S) (x := 4 * i) (n := 4) (by omega))) (by decide),
      hm.rc]
  exact ⟨sched', fr, sv, rc⟩

theorem add_four (S : BitVec 32) (a : Nat) : S + BitVec.ofNat 32 a + 4 = S + BitVec.ofNat 32 (a + 4) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

theorem word_ok {s₀ : State} {S B : BitVec 32} {kl : List Byte} {nk i : Nat} (hs : WSetup s₀ S B kl nk)
    {s : State} (hi : WInv s₀ S B kl nk i s) :
    WP isa wordBody s fun s' =>
      (Arm.eval .ne s' = some false ∧ WDone s₀ S B kl nk s') ∨
      (Arm.eval .ne s' = some true ∧ WInv s₀ S B kl nk (i + 1) s') := by
  have h3 := hs.nk3
  have hnk : 0 < nk := by omega
  have hi1 := hi.hi
  have hn := hi.hn
  have hmod := Nat.mod_lt i hnk
  have hfS := hs.fitS
  unfold wordBody
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil ?_)
  have hi₁ := hi.fupd f₁
  refine WP.seq (WP.mono (temp_wp hs hi₁ (by rw [z₁, f₁.gpr])) fun s₂ hm => ?_)
  have r9₂ : s₂.gpr .r9 = S + BitVec.ofNat 32 (4 * (i - nk)) := (hm.keep _ (by simp [qRegs])).trans hi₁.r9
  have r10₂ : s₂.gpr .r10 = S + BitVec.ofNat 32 (4 * i) := (hm.keep _ (by simp [qRegs])).trans hi₁.r10
  have r11₂ : s₂.gpr .r11 = BitVec.ofNat 32 (i % nk) := (hm.keep _ (by simp [qRegs])).trans hi₁.r11
  have r12₂ : s₂.gpr .r12 = BitVec.ofNat 32 nk := (hm.keep _ (by simp [qRegs])).trans hi₁.r12
  have lr₂ : s₂.gpr .lr = BitVec.ofNat 32 (4 * (nk + 7) - i) := (hm.keep _ (by simp [qRegs])).trans hi₁.lr
  have r8₂ : s₂.gpr sb = B := (hm.keep _ (by simp [qRegs, sb])).trans hi₁.r8
  have hwS : (⟨State.addr S, 240⟩ : Region) ∈ s₂.wr := by rw [hm.wr, hi₁.wr]; exact hs.sch
  -- `w[i] := w[i − Nk] ⊕ temp`.
  refine WP.seq ?_
  refine wp_ldr (a := State.addr S + BitVec.ofNat 64 (4 * (i - nk))) (by omega)
    (by rw [r9₂, BitVec.add_zero, sched_addr hfS (by omega)])
    ⟨_, List.mem_append_right _ hwS, c_off240 _ (by omega)⟩ fun s₃ u₃ => ?_
  refine wp_eor' (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_str (a := State.addr S + BitVec.ofNat 64 (4 * i)) (by omega)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), r10₂, BitVec.add_zero, sched_addr hfS (by omega)])
    (by rw [u₄.wr, u₃.wr]; exact ⟨_, hwS, c_off240 _ (by omega)⟩) fun s₅ u₅ => ?_
  refine wp_add (op2_imm (by decide)) fun s₆ u₆ => wp_add (op2_imm (by decide)) fun s₇ u₇ =>
    wp_add (op2_imm (by decide)) fun s₈ u₈ => wp_cmp (op2_reg _ _) fun s₉ f₉ z₉ => WP.block_nil ?_
  have r11₉ : s₉.gpr .r11 = BitVec.ofNat 32 (i % nk) + 1 := by
    rw [f₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), r11₂]
  have r12₉ : s₉.gpr .r12 = BitVec.ofNat 32 nk := by
    rw [f₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), r12₂]
  have hev₉ : Arm.eval .eq s₉ = some (decide (i % nk + 1 = nk)) := by
    simp only [Arm.eval, z₉, u₈.gpr, u₇.other .r11 (by decide), u₆.other .r11 (by decide), u₅.gpr,
      u₄.other .r11 (by decide), u₃.other .r11 (by decide), r11₂, u₈.other .r12 (by decide),
      u₇.other .r12 (by decide), u₆.other .r12 (by decide), u₄.other .r12 (by decide),
      u₃.other .r12 (by decide), r12₂]
    rw [next_beq hmod (by omega)]
  -- `r11 := (i + 1) mod Nk`.
  refine WP.seq (WP.mono (Q := fun (s₁₀ : State) =>
      s₁₀.gpr .r11 = BitVec.ofNat 32 ((i + 1) % nk) ∧ (∀ r, r ≠ .r11 → s₁₀.gpr r = s₉.gpr r) ∧
      s₁₀.mem = s₉.mem ∧ s₁₀.rd = s₉.rd ∧ s₁₀.wr = s₉.wr ∧ s₁₀.sp = s₉.sp) ?_
    fun s₁₀ ⟨r11₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀, sp₁₀⟩ => ?_)
  · refine WP.ite _ hev₉ (fun hb => ?_) (fun hb => ?_)
    · refine wp_mov (op2_imm (by decide)) fun s₁₀ u₁₀ =>
        WP.block_nil ⟨?_, u₁₀.other, u₁₀.mem, u₁₀.rd, u₁₀.wr, u₁₀.sp⟩
      have h1 : (i + 1) % nk = 0 := by
        have : i % nk + 1 = nk := by simpa using hb
        rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < nk by omega), this, Nat.mod_self]
      rw [u₁₀.gpr, h1]; rfl
    · refine WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
      have h1 : (i + 1) % nk = i % nk + 1 := by
        have : i % nk + 1 < nk := by simp at hb; omega
        rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < nk by omega), Nat.mod_eq_of_lt this]
      rw [r11₉, h1, BitVec.ofNat_add]
      rfl
  -- `lr := lr − 1`.
  refine wp_subs (op2_imm (by decide)) fun s₁₁ u₁₁ z₁₁ => WP.block_nil ?_
  have lr₁₀ : s₁₀.gpr .lr = BitVec.ofNat 32 (4 * (nk + 7) - i) := by
    rw [o₁₀ _ (by decide), f₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), lr₂]
  have e : BitVec.ofNat 32 (4 * (nk + 7) - i) - 1 = BitVec.ofNat 32 (4 * (nk + 7) - i - 1) := by
    bv_omega
  have lr₁₁ : s₁₁.gpr .lr = BitVec.ofNat 32 (4 * (nk + 7) - i - 1) := by rw [u₁₁.gpr, lr₁₀, e]
  have hev : Arm.eval .ne s₁₁ = some (!decide (4 * (nk + 7) - i - 1 = 0)) := by
    simp only [Arm.eval, z₁₁, lr₁₀, e]
    rw [VG.Proof.MdStream.Arm.ofNat_beq_zero (by omega)]
  have mem₁₁ : s₁₁.mem = storeMem s₂ (State.addr S) nk i := by
    rw [u₁₁.mem, m₁₀, f₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.mem,
      u₃.other _ (by decide), storeMem]
  obtain ⟨sched', fr, sv, rc⟩ := store_facts hs hi₁ hm
  rw [← mem₁₁] at sched' fr sv rc
  have keep : ∀ r, r ≠ .lr → r ≠ .r11 → r ≠ .r10 → r ≠ .r9 → r ≠ q 0 → r ≠ q 1 →
      s₁₁.gpr r = s₂.gpr r := fun r h1 h2 h3 h4 h5 h6 => by
    rw [u₁₁.other _ h1, o₁₀ _ h2, f₉.gpr, u₈.other _ h2, u₇.other _ h3, u₆.other _ h4, u₅.gpr,
      u₄.other _ h5, u₃.other _ h6]
  have r8₁₁ : s₁₁.gpr sb = B := (keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans r8₂
  have rd : s₁₁.rd = s₀.rd := by
    rw [u₁₁.rd, rd₁₀, f₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, hm.rd, hi₁.rd]
  have wr : s₁₁.wr = s₀.wr := by
    rw [u₁₁.wr, wr₁₀, f₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, hm.wr, hi₁.wr]
  have sp : s₁₁.sp = s₀.sp := by
    rw [u₁₁.sp, sp₁₀, f₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, hm.sp, hi₁.sp]
  by_cases hl : 4 * (nk + 7) - i - 1 = 0
  · refine .inl ⟨hev.trans (by rw [hl]; rfl), r8₁₁, rd, wr, sp, fun k hk => sched' k (by omega), sv, fr⟩
  · refine .inr ⟨hev.trans (by simp [hl]), ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_, r8₁₁, ?_, rd, wr, sp,
      sched', by rw [Nat.add_sub_cancel]; exact rc, sv, fr⟩⟩
    · rw [u₁₁.other _ (by decide), o₁₀ _ (by decide), f₉.gpr, u₈.other _ (by decide), u₇.gpr,
        u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), r10₂, add_four,
        show 4 * i + 4 = 4 * (i + 1) by omega]
    · rw [u₁₁.other _ (by decide), o₁₀ _ (by decide), f₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), r9₂, add_four,
        show 4 * (i - nk) + 4 = 4 * (i + 1 - nk) by omega]
    · rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r12₂]
    · rw [u₁₁.other _ (by decide), r11₁₀]
    · rw [lr₁₁, Nat.sub_sub]
    · intro t ht
      have := sched' (4 * i + t) (by omega)
      rw [mem₁₁, storeMem, BitVec.ofNat_add, ← BitVec.add_assoc, st_byte _ _ _ ht,
        show (4 * i + t) / 4 = i by omega, show (4 * i + t) % 4 = t by omega] at this
      rw [u₁₁.other _ (by decide), o₁₀ _ (by decide), f₉.gpr, u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.gpr, u₃.other _ (by decide),
        this, Nat.add_sub_cancel]

/-! ## The loop over the words -/

theorem words_ok {s₀ : State} {S B : BitVec 32} {kl : List Byte} {nk : Nat} (hs : WSetup s₀ S B kl nk)
    {s : State} (hi : WInv s₀ S B kl nk nk s) :
    WP isa (.loop wordBody .ne) s (WDone s₀ S B kl nk) := by
  refine WP.loop (M := isa) (fun k s => ∃ i, k = 4 * (nk + 7) - i ∧ WInv s₀ S B kl nk i s)
    (fun k s ⟨i, hk, hi⟩ => WP.mono (word_ok hs hi) fun s' h => ?_) _ s ⟨nk, rfl, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, _, by have := hi.hn; omega, i + 1, rfl, d⟩



/-! ## Copying the key -/

theorem bytesAt_getD (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) :
    (Spec.Aes.bytesAt m p n).getD k 0 = m (p + BitVec.ofNat 64 k) := by
  simp [Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, hk]

/-- The setting of the copy: the key (`K` bytes at `P`) is outside what is written. -/
structure CSetup (s₀ : State) (S B P : BitVec 32) (K : Nat) : Prop where
  hK : K = 16 ∨ K = 24 ∨ K = 32
  key : (⟨State.addr P, K⟩ : Region) ∈ s₀.rd
  sch : (⟨State.addr S, 240⟩ : Region) ∈ s₀.wr
  scr : (⟨State.addr B, 512⟩ : Region) ∈ s₀.wr
  fitP : P.toNat + K ≤ 2 ^ 32
  fitS : S.toNat + 240 ≤ 2 ^ 32
  fitB : B.toNat + 512 ≤ 2 ^ 32
  dS : Region.Disjoint ⟨State.addr P, K⟩ ⟨State.addr S, 240⟩
  dB : Region.Disjoint ⟨State.addr P, K⟩ ⟨State.addr B, 512⟩
  sep : Region.Disjoint ⟨State.addr S, 240⟩ ⟨State.addr B, 512⟩

/-- During the copy, after `c` words. -/
structure CInv (s₀ : State) (S B P : BitVec 32) (K c : Nat) (s : State) : Prop where
  hc : 4 * c < K
  r9 : s.gpr .r9 = P + BitVec.ofNat 32 (4 * c)
  r10 : s.gpr .r10 = S + BitVec.ofNat 32 (4 * c)
  lr : s.gpr .lr = BitVec.ofNat 32 (K - 4 * c)
  r1 : s.gpr .r1 = BitVec.ofNat 32 K
  r8 : s.gpr sb = B
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  copied : ∀ k < 4 * c, s.mem (State.addr S + BitVec.ofNat 64 k) = s₀.mem (State.addr P + BitVec.ofNat 64 k)
  saved : Saved s₀ (State.addr B) s.mem
  frame : Frame [⟨State.addr S, 240⟩, ⟨State.addr B, 512⟩] s₀.mem s.mem

/-- After the copy: the last 4 bytes of the key are in `q 0`. -/
structure CDone (s₀ : State) (S B P : BitVec 32) (K : Nat) (s : State) : Prop where
  r10 : s.gpr .r10 = S + BitVec.ofNat 32 K
  r1 : s.gpr .r1 = BitVec.ofNat 32 K
  r8 : s.gpr sb = B
  last : ∀ t < 4, (s.gpr (q 0)).extractLsb' (8 * t) 8 = s₀.mem (State.addr P + BitVec.ofNat 64 (K - 4 + t))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  copied : ∀ k < K, s.mem (State.addr S + BitVec.ofNat 64 k) = s₀.mem (State.addr P + BitVec.ofNat 64 k)
  saved : Saved s₀ (State.addr B) s.mem
  frame : Frame [⟨State.addr S, 240⟩, ⟨State.addr B, 512⟩] s₀.mem s.mem

theorem copy_ok {s₀ : State} {S B P : BitVec 32} {K : Nat} (hs : CSetup s₀ S B P K) {c : Nat} {s : State}
    (hi : CInv s₀ S B P K c s) :
    WP isa (.block copyBody) s fun s' =>
      (Arm.eval .ne s' = some false ∧ CDone s₀ S B P K s') ∨
      (Arm.eval .ne s' = some true ∧ CInv s₀ S B P K (c + 1) s') := by
  have hK := hs.hK
  have hc := hi.hc
  have hc4 : 4 * c + 4 ≤ K := by rcases hK with rfl | rfl | rfl <;> omega
  have hfP := hs.fitP
  have hfS := hs.fitS
  simp only [copyBody]
  refine wp_ldr (a := State.addr P + BitVec.ofNat 64 (4 * c)) (by omega)
    (by rw [hi.r9, BitVec.add_zero, addr_add (by omega)])
    (by rw [← addr_add (by omega)]
        exact in_off (List.mem_append_left _ (by rw [hi.rd]; exact hs.key)) hfP hc4 (by omega))
    fun s₁ u₁ => ?_
  refine wp_str (a := State.addr S + BitVec.ofNat 64 (4 * c)) (by omega)
    (by rw [u₁.other _ (by decide), hi.r10, BitVec.add_zero, addr_add (by omega)])
    (by rw [u₁.wr, ← addr_add (by omega)]; exact in_off (by rw [hi.wr]; exact hs.sch) hfS (by omega) (by omega))
    fun s₂ u₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_add (op2_imm (by decide)) fun s₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun s₅ u₅ z₅ => WP.block_nil ?_
  have e : BitVec.ofNat 32 (K - 4 * c) - 4 = BitVec.ofNat 32 (K - 4 * c - 4) := by bv_omega
  have lr₅ : s₅.gpr .lr = BitVec.ofNat 32 (K - 4 * c - 4) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hi.lr, e]
  have hev : Arm.eval .ne s₅ = some (!decide (K - 4 * c - 4 = 0)) := by
    simp only [Arm.eval, z₅, u₄.other .lr (by decide), u₃.other .lr (by decide), u₂.gpr,
      u₁.other .lr (by decide), hi.lr, e]
    rw [VG.Proof.MdStream.Arm.ofNat_beq_zero (by omega)]
  have m₅ : s₅.mem = s.mem.writeW (State.addr S + BitVec.ofNat 64 (4 * c))
      (s.mem.readW (State.addr P + BitVec.ofNat 64 (4 * c)) 32) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]
  have q0₅ : s₅.gpr (q 0) = s.mem.readW (State.addr P + BitVec.ofNat 64 (4 * c)) 32 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr]
  have hkey : ∀ t < 4, s.mem (State.addr P + BitVec.ofNat 64 (4 * c + t)) =
      s₀.mem (State.addr P + BitVec.ofNat 64 (4 * c + t)) :=
    fun t ht => hi.frame.bytes (R := ⟨State.addr P, K⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.dS
      · exact hs.dB) (by simp only; omega) (show 4 * c + t < K by omega)
  have copied : ∀ k < 4 * (c + 1),
      s₅.mem (State.addr S + BitVec.ofNat 64 k) = s₀.mem (State.addr P + BitVec.ofNat 64 k) := by
    intro k hk
    rw [m₅]
    by_cases hkc : k < 4 * c
    · rw [writeW32_other _ (off_disjoint _ (Or.inl (by omega)) (by omega) (by omega)), hi.copied k hkc]
    · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 4 ∧ k = 4 * c + t := ⟨k - 4 * c, by omega, by omega⟩
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, st_byte _ _ _ ht, ld_byte _ _ ht, BitVec.add_assoc,
        ← BitVec.ofNat_add]
      exact hkey t ht
  have fr : Frame [⟨State.addr S, 240⟩, ⟨State.addr B, 512⟩] s₀.mem s₅.mem := by
    rw [m₅]
    exact Frame.writeW hi.frame (r := ⟨State.addr S, 240⟩) (by simp) _ (c_off240 _ (by omega))
  have sv : Saved s₀ (State.addr B) s₅.mem := by
    rw [m₅]
    refine saved_frame hi.saved (Frame.writeW
      (Frame.refl [⟨State.addr S + BitVec.ofNat 64 (4 * c), 4⟩] _) (by simp) _
      (Region.contains_self _ _)) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have d1 : Region.Disjoint ⟨State.addr S, 240⟩ ⟨State.addr B + BitVec.ofNat 64 128, 36⟩ :=
      hs.sep.sub_right (sub_scr' _ (by omega))
    exact (d1.sub_left (VG.Proof.MdStream.Arm.sub_offset (by omega) (by omega))).symm
  have r1₅ : s₅.gpr .r1 = BitVec.ofNat 32 K := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), hi.r1]
  have r8₅ : s₅.gpr sb = B := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), hi.r8]
  have r10₅ : s₅.gpr .r10 = S + BitVec.ofNat 32 (4 * (c + 1)) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hi.r10]
    bv_omega
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hi.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hi.wr]
  have sp₅ : s₅.sp = s₀.sp := by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hi.sp]
  by_cases hl : K - 4 * c - 4 = 0
  · refine .inl ⟨hev.trans (by rw [hl]; rfl), by rw [r10₅, show 4 * (c + 1) = K by omega], r1₅, r8₅,
      fun t ht => ?_, rd₅, wr₅, sp₅, fun k hk => copied k (by omega), sv, fr⟩
    rw [q0₅, ld_byte _ _ ht, BitVec.add_assoc, ← BitVec.ofNat_add, hkey t ht,
      show K - 4 + t = 4 * c + t by omega]
  · refine .inr ⟨hev.trans (by simp [hl]), ⟨by omega, ?_, r10₅, ?_, r1₅, r8₅, rd₅, wr₅, sp₅,
      copied, sv, fr⟩⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), hi.r9]
      bv_omega
    · rw [lr₅, show K - 4 * (c + 1) = K - 4 * c - 4 by omega]

theorem copyLoop_ok {s₀ : State} {S B P : BitVec 32} {K : Nat} (hs : CSetup s₀ S B P K) {s : State}
    (hi : CInv s₀ S B P K 0 s) :
    WP isa (.loop (.block copyBody) .ne) s (CDone s₀ S B P K) := by
  refine WP.loop (M := isa) (fun k s => ∃ c, k = K - 4 * c ∧ CInv s₀ S B P K c s)
    (fun k s ⟨c, hk, hc⟩ => WP.mono (copy_ok hs hc) fun s' h => ?_) _ s ⟨0, rfl, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, _, by have := hc.hc; omega, c + 1, rfl, d⟩

/-! ## Setting up the word loop -/

theorem kw_getD_key (kl : List Byte) {nk k : Nat} (hk : k < 4 * nk) :
    (kw kl nk (k / 4)).getD (k % 4) 0 = kl.getD k 0 := by
  rw [kw_key kl (show k / 4 < nk by omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  simp [show k % 4 < 4 by omega, Nat.div_add_mod]

/-! ## The prologue -/

theorem save_check3 :
    check (names 32) (saveCfg .r3) (fun _ => none) (saveRegs .r3) saveEnv savePost = true := by
  decide +kernel

theorem prologue_wp {s₀ : State} {S B P : BitVec 32} {K : Nat} (hs : CSetup s₀ S B P K)
    (hS : s₀.gpr .r2 = S) (hB : s₀.gpr .r3 = B) (hP : s₀.gpr .r0 = P)
    (hKr : s₀.gpr .r1 = BitVec.ofNat 32 K) :
    WP isa (.block (saveRegs .r3 ++ [movR sb .r3, movR .r9 .r0, movR .r10 .r2, movR .lr .r1])) s₀
      (CInv s₀ S B P K 0) := by
  rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₁, h₁, sv₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := save_ok (br := .r3) (by decide) hs.scr hs.fitB hB save_check3
  refine WP.of_runBlock ⟨s₁, h₁, ?_⟩
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
  have hK := hs.hK
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => by omega, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁, hP]; simp
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), g₁, hS]; simp
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁, hKr]; simp
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      g₁, hKr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁, hB]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]; exact sv₁
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    exact f₁.sub fun r hr => ⟨⟨State.addr B, 512⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩

/-! ## The whole function -/

theorem ek_correct {s₀ : State} (hp : Proof.Aes.expandKeyArm.pre s₀) :
    WP isa Impl.Aes.Arm.expandKey s₀ fun s' =>
      (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ Proof.Aes.expandKeyArm.post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fP, fS, fB, hK⟩ := hp
  have hs : CSetup s₀ (s₀.gpr .r2) (s₀.gpr .r3) (s₀.gpr .r0) (s₀.gpr .r1).toNat :=
    ⟨hK, by rw [hrd]; simp, by rw [hwr]; simp, by rw [hwr]; simp, fP, fS, fB, dKS, dKB, dSB⟩
  generalize hS : s₀.gpr .r2 = S at hs dSB fS
  generalize hB : s₀.gpr .r3 = B at hs dSB fB
  generalize hP : s₀.gpr .r0 = P at hs dKS dKB fP
  generalize hK' : (s₀.gpr .r1).toNat = K at hs hK dKS dKB fP
  have hKr : s₀.gpr .r1 = BitVec.ofNat 32 K := by rw [← hK']; simp
  have hK4 : K = 4 * (K / 4) := by omega
  unfold Impl.Aes.Arm.expandKey
  refine WP.seq (WP.mono (prologue_wp hs hS hB hP hKr) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (copyLoop_ok hs h₁) fun s₂ h₂ => ?_)
  refine WP.seq ?_
  simp only [wordSetup]
  refine wp_sub (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_lsr (by decide)) fun s₄ u₄ =>
    wp_mov (op2_imm (by decide)) fun s₅ u₅ => wp_add (op2_lsl (by decide)) fun s₆ u₆ =>
    wp_add (op2_imm (by decide)) fun s₇ u₇ => wp_mov (op2_imm (by decide)) fun s₈ u₈ => ?_
  have r8₈ : s₈.gpr sb = B := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), h₂.r8]
  have wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, h₂.wr]
  refine wp_stS' r8₈ (by rw [wr₈]; exact hs.scr) hs.fitB (by decide) (by decide) fun s₉ u₉ => WP.block_nil ?_
  have hlen : (Spec.Aes.bytesAt s₀.mem (State.addr P) K).length = K := by simp [Spec.Aes.bytesAt]
  have ws : WSetup s₀ S B (Spec.Aes.bytesAt s₀.mem (State.addr P) K) (K / 4) :=
    ⟨by omega, by rw [hlen]; exact hK4, hs.sch, hs.scr, hs.fitS, hs.fitB, dSB⟩
  have d41 : Region.Disjoint ⟨State.addr S, 240⟩ ⟨slotA (State.addr B) rconSlot, 32 / 8⟩ :=
    dSB.sub_right (sub_scr' (x := 164) (lx := 4) _ (by omega))
  have r1₂ := h₂.r1
  have wi : WInv s₀ S B (Spec.Aes.bytesAt s₀.mem (State.addr P) K) (K / 4) (K / 4) s₉ :=
    { hi := Nat.le_refl _
      hn := by omega
      r10 := by
        rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), h₂.r10, ← hK4]
      r9 := by
        rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, h₂.r10, r1₂, BitVec.add_sub_cancel,
          Nat.sub_self, Nat.mul_zero]; simp
      r12 := by
        rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), r1₂]
        rcases hK with rfl | rfl | rfl <;> decide
      r11 := by
        rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
          Nat.mod_self]; rfl
      lr := by
        rw [u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr,
          u₃.other _ (by decide), r1₂]
        rcases hK with rfl | rfl | rfl <;> decide
      r8 := by rw [u₉.gpr, r8₈]
      temp := fun t ht => by
        rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), h₂.last t ht,
          ← bytesAt_getD s₀.mem (State.addr P) (show K - 4 + t < K by omega),
          ← kw_getD_key _ (show K - 4 + t < 4 * (K / 4) by omega),
          show (K - 4 + t) / 4 = K / 4 - 1 by omega, show (K - 4 + t) % 4 = t by omega]
      rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, h₂.rd]
      wr := by rw [u₉.wr, wr₈]
      sp := by rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, h₂.sp]
      sched := fun k hk => by
        rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem,
          writeW32_other _ (d41.sub_left (VG.Proof.MdStream.Arm.sub_offset (by omega) (by omega))),
          h₂.copied k (by omega), ← bytesAt_getD s₀.mem (State.addr P) (show k < K by omega),
          kw_getD_key _ (by omega)]
      rc := by
        rw [u₉.mem, u₈.gpr, Mem.readW_writeW_self32, Nat.div_eq_of_lt (by omega), rcW_zero]
      saved := by
        rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
        refine saved_frame h₂.saved (Frame.writeW (Frame.refl [⟨slotA (State.addr B) rconSlot, 4⟩] _)
          (by simp) _ (Region.contains_self _ _)) fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        exact off_disjoint _ (Or.inl (by decide)) (by decide) (by decide)
      frame := by
        rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
        exact Frame.writeW h₂.frame (r := ⟨State.addr B, 512⟩) (by simp) _ (s_off (by decide) (by decide)) }
  refine WP.seq (WP.mono (words_ok ws wi) fun s₄ h₄ => ?_)
  refine wp_mov (op2_reg _ _) fun s₅ u₅ => ?_
  obtain ⟨s₆, hs₆, rg₆, f₆⟩ := restore_ok (s₀ := s₀) (b := B) (by decide)
    (by rw [u₅.wr, h₄.wr]; exact hs.scr) hs.fitB (by rw [u₅.gpr, h₄.r8]) (by rw [u₅.mem]; exact h₄.saved)
  refine WP.of_runBlock ⟨s₆, hs₆, rg₆, ?_⟩
  show Spec.Aes.bytesAt s₆.mem (State.addr (s₀.gpr .r2)) (16 * (Spec.Aes.rounds ((s₀.gpr .r1).toNat / 4) + 1)) =
    Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
  rw [hS, hP, hK']
  have lhs : ∀ n, Spec.Aes.bytesAt s₆.mem (State.addr S) n =
      (List.range n).map fun k => s₆.mem (State.addr S + BitVec.ofNat 64 k) := fun _ => rfl
  rw [lhs, Spec.Aes.expandKey, hlen, Spec.Aes.rounds,
    show 16 * (K / 4 + 6 + 1) = 4 * (4 * (K / 4 + 6 + 1)) by omega]
  refine flatten_expandWords ws.len (by omega) _ _ fun k hk => ?_
  refine (f₆.bytes (R := ⟨State.addr S, 240⟩) (fun r hr => ?_) (by simp) (show k < 240 by omega)).trans ?_
  · simp only [List.mem_singleton] at hr; subst hr
    exact dSB.sub_right (Region.sub_prefix (by decide))
  · rw [u₅.mem]; exact h₄.sched k (by omega)

theorem expandKey_correct (s : State) (hs : Proof.Aes.expandKeyArm.pre s) :
    ∃ t s', Exec isa Impl.Aes.Arm.expandKey s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.expandKeyArm.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := ek_correct hs
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega)
  · exact h₁ 1 (by omega)
  · exact h₁ 2 (by omega)
  · exact h₁ 3 (by omega)
  · exact h₁ 4 (by omega)
  · exact h₁ 5 (by omega)
  · exact h₁ 6 (by omega)
  · exact h₁ 7 (by omega)
  · exact h₁ 8 (by omega)

/-! ## Constant time -/

/-- The initial taint: the pointers and `key_len` are public; `r2` and `r3`
point at the schedule and the scratch buffer. -/
def ekτ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [240, 512],
    bases := [(.r2, 0), (.r3, 1)] }

theorem ek_wf₀ {s : State} (h : Proof.Aes.expandKeyArm.pre s) : VG.Arm.Taint.Wf ekτ₀ s := by
  obtain ⟨_, hwr, _, _, dSB, _, fS, fB, _⟩ := h
  refine ⟨fun _ => ⟨by simp [hwr, ekτ₀], ?_, ?_⟩, ?_, fun h => absurd h (by decide),
    fun _ h => by simp [ekτ₀] at h⟩
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact dSB
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [VG.Proof.MdStream.Arm.addr_toNat] <;> omega
  · intro p hp'
    simp only [ekτ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp [VG.Arm.Taint.region, hwr]

theorem expandKey_ct : ConstantTime isa Proof.Aes.expandKeyArm.pre Proof.Aes.expandKeyArm.pub
    Impl.Aes.Arm.expandKey := by
  refine VG.Taint.constantTime (A := VG.Arm.taint) ekτ₀ (fun s₁ s₂ h₁ h₂ hp => ?_) (by taint_decide)
  obtain ⟨p0, p1, p2, p3⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ek_wf₀ h₁, ek_wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (by decide), fun k hk => absurd hk (by simp [ekτ₀])⟩
  · simp only [ekτ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p2, p3]

/-- A state satisfying the precondition. -/
def ekSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 16 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 240⟩, ⟨0x3000, 512⟩]

theorem expandKey_verified :
    Verified Arm.target Impl.Aes.Arm.expandKey (Spec.Aes.expandKeyContract Arm.abi) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Spec.Aes.expandKeyContract, Spec.Aes.expandKeySig, Proof.Aes.expandKeyArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [Proof.Aes.Arm.ekSat]
      using Proof.Aes.Arm.ekSat)

end VG.Proof.Aes.Arm
