import VerifiedGarbage.Proof.Rc4.AArch64.Lookup

/-!
# A write at a secret index

`writeJ_run`: with the index `J` (and `J ^ 64`, `J ^ 128`, `J ^ 192`)
broadcast in `v0`–`v3` and the value `V` broadcast in `v4`, the sixteen
`cmeq`/`bit` pairs replace byte `J` of the table registers by `V`, and leave
the others.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64

/-- The index's four quarters, broadcast in `v0`–`v3`. -/
def Quarters (s : State) (J : BitVec 8) : Prop :=
  ∀ q < 4, s.v (dq q) = bc (J ^^^ BitVec.ofNat 8 (64 * q))

theorem xor_low : ∀ a < 64, ∀ q < 4, a ^^^ 64 * q = 64 * q + a := by decide +kernel

/-- Lane `e` of quarter `r % 4`'s lane numbers equals `J ^ 64 (r / 4)` just
when `16 r + e` is `J`. -/
theorem lane_eq (J : BitVec 8) {r e : Nat} (hr : r < 16) (he : e < 16) :
    BitVec.ofNat 8 (16 * (r % 4) + e) = J ^^^ BitVec.ofNat 8 (64 * (r / 4)) ↔ 16 * r + e = J.toNat := by
  have hJ := J.isLt
  have hq : (BitVec.ofNat 8 (64 * (r / 4))).toNat = 64 * (r / 4) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ha : (BitVec.ofNat 8 (16 * (r % 4) + e)).toNat = 16 * (r % 4) + e := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have low := xor_low (16 * (r % 4) + e) (by omega) (r / 4) (by omega)
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    rw [ha, BitVec.toNat_xor, hq] at h'
    have : J.toNat = (16 * (r % 4) + e) ^^^ 64 * (r / 4) := by
      rw [h', Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [low] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [ha, BitVec.toNat_xor, hq, ← h, show 16 * r + e = 64 * (r / 4) + (16 * (r % 4) + e) by omega,
      ← low, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

def writeN (n : Nat) : List Instr :=
  (List.range n).flatMap fun k =>
    [.vop (.cmeq .b16 .v7 (lanes (k % 4)) (dq (k / 4))), .vop (.bsel .bit (treg k) si .v7)]

theorem writeN_succ (n : Nat) : writeN (n + 1) = writeN n ++
    ([.vop (.cmeq .b16 .v7 (lanes (n % 4)) (dq (n / 4))), .vop (.bsel .bit (treg n) si .v7)] :
      List Instr) := by
  simp only [writeN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- The registers the write changes. -/
def writeRegs : List VReg :=
  [.v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31]

theorem treg_mem : ∀ r < 16, treg r ∈ writeRegs := by decide

theorem notTable_v7 : NotTable .v7 := by decide

theorem lanes_notW : ∀ q < 4, lanes q ∉ writeRegs := by decide
theorem dq_notW : ∀ q < 4, dq q ∉ writeRegs := by decide

theorem writeN_run {s : State} (hk : Consts s) {J V : BitVec 8} (hq : Quarters s J)
    (hv : s.v si = bc V) {n : Nat} (hn : n ≤ 16) :
    ∃ s', runBlock isa (writeN n) s = some s' ∧
      (∀ k < 256, tbyte s'.v k = if k / 16 < n ∧ k = J.toNat then V else tbyte s.v k) ∧
      Only writeRegs s s' := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun k _ => by simp, Only.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, t₁, o₁⟩ := ih (by omega)
    have notW : ∀ r, r ∉ writeRegs → s₁.v r = s.v r := o₁.2
    let m := VArr.b16.map2 (fun w a b => if a = b then BitVec.allOnes w else 0)
      (s₁.v (lanes (n % 4))) (s₁.v (dq (n / 4)))
    let s₂ := s₁.setV .v7 m
    let s₃ := s₂.setV (treg n) (VSelOp.bit.eval (s₂.v (treg n)) (s₂.v si) (s₂.v .v7))
    have e₂ : exec (.vop (.cmeq .b16 .v7 (lanes (n % 4)) (dq (n / 4)))) s₁ = some s₂ := rfl
    have e₃ : exec (.vop (.bsel .bit (treg n) si .v7)) s₂ = some s₃ := rfl
    have l₁ : s₁.v (lanes (n % 4)) = laneNums (n % 4) := by
      rw [notW _ (lanes_notW _ (by omega))]; exact hk.lns _ (by omega)
    have d₁ : s₁.v (dq (n / 4)) = bc (J ^^^ BitVec.ofNat 8 (64 * (n / 4))) := by
      rw [notW _ (dq_notW _ (by omega))]
      exact hq _ (by omega)
    have v₂ : s₂.v si = bc V := by
      rw [v_setV_of_ne _ _ (by decide), notW _ (by decide)]; exact hv
    have m_byte : ∀ e < 16, vbyte (s₂.v .v7) e =
        if 16 * n + e = J.toNat then BitVec.allOnes 8 else 0 := by
      intro e he
      rw [v_setV_self, vbyte_cmeq _ _ he, l₁, d₁, laneNums, vbyte_ofVBytes _ he, vbyte_bc _ he]
      simp only [lane_eq J (by omega : n < 16) he]
    refine ⟨s₃, by rw [writeN_succ]; exact runBlock_cat_some run₁ (by
      rw [runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some, runBlock_nil]), ?_, ?_⟩
    · intro k hk
      by_cases hkn : k / 16 = n
      · have b₃ : tbyte s₃.v k = vbyte (VSelOp.bit.eval (s₂.v (treg n)) (s₂.v si) (s₂.v .v7)) (k % 16) := by
          simp only [tbyte, hkn, s₃, v_setV_self]
        rw [b₃, vbyte_bit _ _ _ (16 * n + k % 16 = J.toNat) (m_byte _ (by omega)), v₂,
          vbyte_bc _ (by omega)]
        have old : vbyte (s₂.v (treg n)) (k % 16) = tbyte s.v k := by
          rw [v_setV_of_ne _ _ (notTable_v7.ne n)]
          have := t₁ k hk
          simp only [show ¬ k / 16 < n by omega, false_and, ite_false] at this
          rw [← this]; simp only [tbyte, hkn]
        rw [old]
        exact ite_iff ⟨fun h => ⟨by omega, by omega⟩, fun h => by omega⟩ _ _
      · have ne : treg (k / 16) ≠ treg n := fun h => hkn (treg_inj _ (by omega) _ (by omega) h)
        have keep : s₃.v (treg (k / 16)) = s₁.v (treg (k / 16)) := by
          rw [v_setV_of_ne _ _ ne, v_setV_of_ne _ _ (notTable_v7.ne _)]
        have : tbyte s₃.v k = tbyte s₁.v k := by simp only [tbyte, keep]
        rw [this, t₁ k hk]
        have e : (k / 16 < n + 1) ↔ (k / 16 < n) := by omega
        simp only [e]
    · exact (o₁.trans (Only.setV _ (by decide) _)).trans (Only.setV _ (treg_mem n (by omega)) _)

end VG.Proof.Rc4.AArch64
