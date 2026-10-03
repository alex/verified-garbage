import VerifiedGarbage.Proof.Argon2.X86.Derive.FillCount

/-!
# Argon2 on x86 (32-bit): the reference block's column and the block pointers

`relative_ok`: the position in the window that J₁ selects (RFC 9106
§3.4.2); `wrap_ok`: its column, from the window's start, modulo the lane
length; `refPointer_ok` and `curPointer_ok`: the reference and current
blocks' addresses, to the locals.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_sub wp_addm wp_cmpi wp_ldm wp_stm wp_andi
  wp_sbb_self wp_and wp_xor wp_xorm)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff)

/-- The position in the window that `j1` selects. -/
def relV (cnt j1 : Nat) : Nat := cnt - 1 - cnt * (j1 * j1 / 2 ^ 32) / 2 ^ 32

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `relative`: `eax :=` the position in the window. -/
theorem relative_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) {cnt : Nat} (hc : 1 ≤ cnt) (hc' : cnt < 2 ^ 32)
    (hcnt : lw s₀ s countOff = BitVec.ofNat 32 cnt) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .eax = BitVec.ofNat 32 (relV cnt J1.toNat) → Divide.Keep s t → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.relative ++ is)) s Q := by
  have jb := J1.isLt
  have x32 := Proof.Argon2.reference_scaled_bound J1.toNat jb
  have lt := Proof.Argon2.reference_scale_lt_count cnt J1.toNat (by omega) jb
  unfold Impl.Argon2.X86.Derive.relative
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc hp h.fs.inv (d := j1Off) (by decide) fun s₁ u₁ => wp_mul fun s₂ _ d₂ k₂ _ => wp_mov fun s₃ u₃ => ?_
  have K₃ := ((Divide.Keep.of_upd u₁ (by simp)).trans k₂).trans (Divide.Keep.of_upd u₃ (by simp))
  refine wp_ldloc hp (h.of_keep K₃).fs.inv (d := countOff) (by decide) fun s₄ u₄ => wp_mul fun s₅ _ d₅ k₅ o₅ =>
    wp_mov fun s₆ u₆ => wp_subi fun s₇ u₇ _ _ => wp_sub fun t u _ => k t ?_ ?_
  · have x₃ : (s₃.gpr .eax).toNat = J1.toNat * J1.toNat / 2 ^ 32 := by
      rw [u₃.gpr, d₂, u₁.gpr, h.j1, Wp.toNat_ofNat_lt x32]
    have c₄ : (s₄.gpr .ecx).toNat = cnt := by
      rw [u₄.gpr, lw_mem K₃.mem, hcnt, Wp.toNat_ofNat_lt hc']
    rw [u.gpr, u₇.gpr, u₇.other .edx (by decide), u₆.gpr, u₆.other .edx (by decide), o₅ .ecx (by decide) (by decide),
      d₅, u₄.other .eax (by decide), x₃, c₄, u₄.gpr, lw_mem K₃.mem, hcnt, Wp.ofNat_pred hc,
      Wp.sub_ofNat (by rw [Nat.mul_comm]; omega), relV, Nat.mul_comm (J1.toNat * J1.toNat / 2 ^ 32) cnt]
  · exact (((((K₃.trans (Divide.Keep.of_upd u₄ (by simp))).trans k₅).trans (Divide.Keep.of_upd u₆ (by simp))).trans
      (Divide.Keep.of_upd u₇ (by simp))).trans (Divide.Keep.of_upd u (by simp)))


/-- `wrap`: `eax := (start + eax) mod laneLen`. -/
theorem wrap_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) {rel stt : Nat} (hr : rel < (prm s₀).laneLen)
    (hs : stt < (prm s₀).laneLen) (ha : s.gpr .eax = BitVec.ofNat 32 rel)
    (hst : lw s₀ s startOff = BitVec.ofNat 32 stt) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .eax = BitVec.ofNat 32 ((stt + rel) % (prm s₀).laneLen) → Divide.Keep s t →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.wrap ++ is)) s Q := by
  have L22 : (prm s₀).laneLen < 2 ^ 22 := by
    have := Nat.le_mul_of_pos_left (prm s₀).laneLen (show 0 < lanesN s₀ from hp.lanes_pos)
    have e := hp.blocks_eq
    have := hp.blocks_lt
    omega
  unfold Impl.Argon2.X86.Derive.wrap
  simp only [List.cons_append, List.nil_append]
  refine wp_addm h.fs.inv.ebp (loc_in' hp h.fs.inv (d := startOff) (by decide)) fun s₁ u₁ => ?_
  have K₁ := Divide.Keep.of_upd u₁ (by simp)
  refine Divide.wp_subm (h.of_keep K₁).fs.inv.ebp (loc_in' hp (h.of_keep K₁).fs.inv (d := laneLenOff) (by decide))
    fun s₂ u₂ c₂ => wp_sbb_self c₂ fun s₃ u₃ => ?_
  have K₃ := (K₁.trans (Divide.Keep.of_upd u₂ (by simp))).trans (Divide.Keep.of_upd u₃ (by simp))
  refine Divide.wp_andm (h.of_keep K₃).fs.inv.ebp (loc_in' hp (h.of_keep K₃).fs.inv (d := laneLenOff) (by decide))
    fun s₄ u₄ => wp_add fun t u _ => k t ?_ ?_
  · have x₁ : s₁.gpr .eax = BitVec.ofNat 32 (stt + rel) := by
      rw [u₁.gpr, ha, show s.mem.readW (addr (E s₀) startOff) 32 = lw s₀ s startOff from rfl, hst,
        BitVec.ofNat_add_ofNat, Nat.add_comm]
    have L₁ : s₁.mem.readW (addr (E s₀) laneLenOff) 32 = BitVec.ofNat 32 (prm s₀).laneLen := by
      show lw s₀ s₁ laneLenOff = _
      rw [lw_mem K₁.mem]; exact h.fs.pr.laneLen
    have L₃ : s₃.mem.readW (addr (E s₀) laneLenOff) 32 = BitVec.ofNat 32 (prm s₀).laneLen := by
      show lw s₀ s₃ laneLenOff = _
      rw [lw_mem K₃.mem]; exact h.fs.pr.laneLen
    rw [u.gpr, u₄.other _ (by decide), u₄.gpr, L₃, u₃.gpr, u₃.other _ (by decide), u₂.gpr, x₁, L₁,
      Wp.toNat_ofNat_lt (by omega), Wp.toNat_ofNat_lt (by omega),
      Proof.Argon2.reference_wrap (stt + rel) (prm s₀).laneLen (by omega)]
    by_cases c : stt + rel < (prm s₀).laneLen
    · simp only [c, decide_true, ite_true, BitVec.allOnes_and, BitVec.sub_add_cancel]
    · simp only [c, decide_false, ite_false, Bool.false_eq_true]
      rw [Wp.sub_ofNat (by omega)]
      simp
  · exact (K₃.trans (Divide.Keep.of_upd u₄ (by simp))).trans (Divide.Keep.of_upd u (by simp))

/-- `refPointer`: the address of block `eax` of the reference lane, to the locals. -/
theorem refPointer_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) {col rl : Nat} (hc : col < (prm s₀).laneLen)
    (hrl : rl < lanesN s₀) (ha : s.gpr .eax = BitVec.ofNat 32 col)
    (hr : lw s₀ s refLaneOff = BitVec.ofNat 32 rl) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, RS s₀ pass slice lane index ctr st J1 J2 t →
      lw s₀ t tmpOff = memP s₀ + BitVec.ofNat 32 ((rl * (prm s₀).laneLen + col) * 1024) →
      (∀ e, e + 4 ≤ 236 → (tmpOff + 4 ≤ e ∨ e + 4 ≤ tmpOff) → lw s₀ t e = lw s₀ s e) →
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.refPointer ++ is)) s Q := by
  unfold Impl.Argon2.X86.Derive.refPointer
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_mov fun s₁ u₁ => ?_
  have K₁ := Divide.Keep.of_upd u₁ (by simp)
  refine wp_ldloc hp (h.of_keep K₁).fs.inv (d := refLaneOff) (by decide) fun s₂ u₂ => ?_
  have K₂ := K₁.trans (Divide.Keep.of_upd u₂ (by simp))
  refine blockAddr_ok hp (h.of_keep K₂).fs.inv (h.of_keep K₂).fs.pr hrl hc
    (by rw [u₂.gpr, lw_mem K₁.mem, hr]) (by rw [u₂.other _ (by decide), u₁.gpr, ha]) fun s₃ a₃ _ k₃ => ?_
  have K₃ := K₂.trans k₃
  refine wp_stloc hp (h.of_keep K₃).fs.inv (d := tmpOff) (by decide) fun t it vt ot gt mt =>
    k t ?_ (by rw [vt, a₃]) (fun e he hd => by rw [ot e he hd, lw_mem K₃.mem]) (fun r a b c => by
      rw [gt, K₃.other r a b c])
  exact (h.of_keep K₃).store hp it (d := tmpOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt

/-- `curPointer`: the address of the current block, to the locals. -/
theorem curPointer_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, RS s₀ pass slice lane index ctr st J1 J2 t →
      lw s₀ t curOff = memP s₀ + BitVec.ofNat 32
        ((lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index)) * 1024) →
      (∀ e, e + 4 ≤ 236 → (curOff + 4 ≤ e ∨ e + 4 ≤ curOff) → lw s₀ t e = lw s₀ s e) →
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.curPointer ++ is)) s Q := by
  have hc := Proof.Argon2.column_lt (prm s₀) hp.lanes_pos hs hi
  unfold Impl.Argon2.X86.Derive.curPointer
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine column_ok hp h.fs.inv h.fs.pr h.fs.pos hs hi fun s₁ _ c₁ k₁ => ?_
  refine wp_ldloc hp (h.of_keep k₁).fs.inv (d := laneOff) (by decide) fun s₂ u₂ => ?_
  have K₂ := k₁.trans (Divide.Keep.of_upd u₂ (by simp))
  refine blockAddr_ok hp (h.of_keep K₂).fs.inv (h.of_keep K₂).fs.pr hl hc
    (by rw [u₂.gpr, lw_mem k₁.mem]; exact h.fs.pos.lane) (by rw [u₂.other _ (by decide), c₁])
    fun s₃ a₃ _ k₃ => ?_
  have K₃ := K₂.trans k₃
  refine wp_stloc hp (h.of_keep K₃).fs.inv (d := curOff) (by decide) fun t it vt ot gt mt =>
    k t ?_ (by rw [vt, a₃]) (fun e he hd => by rw [ot e he hd, lw_mem K₃.mem]) (fun r a b c => by
      rw [gt, K₃.other r a b c])
  exact (h.of_keep K₃).store hp it (d := curOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt
end


theorem j2_eq (J1 J2 : BitVec 32) : ((J2 ++ J1 : BitVec 64) >>> 32).toNat = J2.toNat := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← Proof.Sha512.Word64.hi_toNat,
    Proof.Sha512.Word64.hi_append]

theorem j1_eq (J1 J2 : BitVec 32) : ((J2 ++ J1 : BitVec 64) &&& 0xffffffff).toNat = J1.toNat := by
  rw [BitVec.toNat_and, show (0xffffffff : BitVec 64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    ← Proof.Sha512.Word64.lo_toNat, Proof.Sha512.Word64.lo_append]

theorem count_eq (p : Spec.Argon2.Params) (pass slice index : Nat) (same : Bool) :
    Spec.Argon2.referenceCount p pass slice index same =
      countV (baseV p.segmentLen p.laneLen pass slice) index same := by
  unfold Spec.Argon2.referenceCount countV baseV
  by_cases h : pass = 0
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

theorem ref_eq (p : Spec.Argon2.Params) (pass lane slice index : Nat) (J1 J2 : BitVec 32) :
    Spec.Argon2.reference p pass lane slice index (J2 ++ J1) =
      (refLaneV p.lanes pass slice lane J2.toNat,
        (startV p.segmentLen p.laneLen pass slice +
          relV (countV (baseV p.segmentLen p.laneLen pass slice) index
            (refLaneV p.lanes pass slice lane J2.toNat == lane)) J1.toNat) % p.laneLen) := by
  unfold Spec.Argon2.reference
  simp only [j1_eq, j2_eq, count_eq]
  rfl

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `reference`: the reference and current blocks' addresses, to the locals. -/
theorem reference_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    WP isa Impl.Argon2.X86.Derive.reference s fun t => RS s₀ pass slice lane index ctr st J1 J2 t ∧
      lw s₀ t tmpOff = memP s₀ + BitVec.ofNat 32
        (((Spec.Argon2.reference (prm s₀) pass lane slice index (J2 ++ J1)).1 * (prm s₀).laneLen +
          (Spec.Argon2.reference (prm s₀) pass lane slice index (J2 ++ J1)).2) * 1024) ∧
      lw s₀ t curOff = memP s₀ + BitVec.ofNat 32
        ((lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index)) * 1024) := by
  have L22 : (prm s₀).laneLen < 2 ^ 22 := by
    have := Nat.le_mul_of_pos_left (prm s₀).laneLen (show 0 < lanesN s₀ from hp.lanes_pos)
    have e := hp.blocks_eq
    have := hp.blocks_lt
    omega
  have ll := hp.laneLen_eq
  have s2 := hp.segLen_two
  have hl1 := hp.lanes_pos
  rw [ref_eq]
  generalize hRL : refLaneV (prm s₀).lanes pass slice lane J2.toNat = RL
  have hRL' : refLaneV (lanesN s₀) pass slice lane J2.toNat = RL := hRL
  have rl_lt : RL < lanesN s₀ := by
    rw [← hRL', refLaneV]; split
    · exact hl
    · exact Nat.mod_lt _ (by omega)
  have first : pass = 0 → slice = 0 → RL = lane := fun a b => by rw [← hRL', refLaneV, ite_eq_left ⟨a, b⟩]
  generalize hB : baseV (prm s₀).segmentLen (prm s₀).laneLen pass slice = B
  have b_le : B ≤ (prm s₀).laneLen := by
    rw [← hB, baseV]; split
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (show slice ≤ 3 by omega)) (by omega))
    · omega
  generalize hST : startV (prm s₀).segmentLen (prm s₀).laneLen pass slice = ST
  have st_lt : ST < (prm s₀).laneLen := by
    rw [← hST, startV]; split
    · omega
    · exact Nat.mod_lt _ (by omega)
  have cpos := Proof.Argon2.reference_count_positive (prm s₀) hp.lanes_pos hp.memory_ge pass slice index
    (RL == lane) active fun a b => by simp [first a b]
  have clt := Proof.Argon2.reference_count_lt_lane (prm s₀) hp.lanes_pos hp.memory_ge pass slice index
    (RL == lane) hs hi
  rw [count_eq, hB] at cpos clt
  unfold Impl.Argon2.X86.Derive.reference
  refine WP.seq ((refLane_ok hp h hpass hs).mono fun t₁ ⟨h₁, r₁⟩ => ?_)
  rw [hRL'] at r₁
  refine WP.seq ((refStart_ok hp h₁ hpass hs).mono fun t₂ ⟨h₂, r₂, st₂⟩ => ?_)
  rw [hST] at st₂
  refine WP.seq ((countBase_ok hp h₂ hpass hs).mono fun t₃ ⟨k₃, a₃⟩ => ?_)
  rw [hB] at a₃
  have h₃ := h₂.of_keep k₃
  rw [← List.append_nil Impl.Argon2.X86.Derive.curPointer]
  refine countSelect_ok hp h₃ (base := B) (rl := RL) (by omega) hi hl rl_lt a₃
    (by rw [lw_mem k₃.mem, r₂, r₁]) (fun e => ?_) (fun e e0 => ?_) fun t₄ h₄ a₄ c₄ o₄ g₄ => ?_
  · rw [← hB, baseV]; split
    · rename_i hp0
      by_cases hs0 : slice = 0
      · omega
      · have := Nat.mul_le_mul_right (prm s₀).segmentLen (show 1 ≤ slice by omega); omega
    · omega
  · have : ¬(pass = 0 ∧ slice = 0) := fun ⟨a, b⟩ => e (first a b)
    rw [← hB, baseV]; split
    · rename_i hp0
      have := Nat.mul_le_mul_right (prm s₀).segmentLen (show 1 ≤ slice by omega); omega
    · omega
  refine relative_ok hp h₄ (cnt := countV B index (RL == lane)) cpos (by omega) c₄ fun t₅ a₅ k₅ => ?_
  have h₅ := h₄.of_keep k₅
  have rel_lt : relV (countV B index (RL == lane)) J1.toNat < (prm s₀).laneLen := by
    unfold relV; omega
  refine wrap_ok hp h₅ rel_lt st_lt a₅ (by
      rw [lw_mem k₅.mem, o₄ _ (by decide) (by decide), lw_mem k₃.mem, st₂]) fun t₆ a₆ k₆ => ?_
  have h₆ := h₅.of_keep k₆
  refine refPointer_ok hp h₆ (Nat.mod_lt _ (by omega)) rl_lt a₆ (by
      rw [lw_mem k₆.mem, lw_mem k₅.mem, o₄ _ (by decide) (by decide), lw_mem k₃.mem, r₂, r₁])
    fun t₇ h₇ p₇ o₇ _ => ?_
  refine curPointer_ok hp h₇ hl hs hi fun t h' c' o' _ => WP.block_nil ⟨h', ?_, c'⟩
  rw [o' _ (by decide) (by decide), p₇]

end
end VG.Proof.Argon2.X86.Derive
