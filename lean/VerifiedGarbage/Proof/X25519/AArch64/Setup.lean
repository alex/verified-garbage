import VerifiedGarbage.Proof.X25519.AArch64.Final
import VerifiedGarbage.Proof.X25519.Bytes

/-!
# X25519 on AArch64: the setup

Untrusted: everything here is checked by Lean. `setup` saves our caller's
registers, decodes the u-coordinate into `x1` and `x3` (`decode`), stores
the bits of the scalar, clamped, at `BITS` (`bits`), and sets `x2 = 1`,
`z2 = 0`, `z3 = 1` (`initSlots`).
-/

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519

/-! ## Saving registers -/

/-- The region of the saved registers. -/
abbrev saveR (b : Addr) : Region := ⟨b, 48⟩

theorem saves_ok {b : Addr} : ∀ n ≤ 6, ∀ s : State, Sc b s →
    WP isa (.block ((List.range n).map fun k => st (saved.getD k .x19) (SAVE + 8 * k))) s fun s' =>
      (∀ k < n, wd s'.mem b (SAVE + 8 * k) = v s (saved.getD k .x19)) ∧ Frame [saveR b] s.mem s'.mem ∧
        Kp [] s s'
  | 0, _, s, _ => WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), Frame.refl _ _, Kp.refl _ _⟩
  | n + 1, hn, s, hs => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append (WP.mono (saves_ok n (by omega) s hs) fun s₁ ⟨e₁, f₁, k₁⟩ => ?_)
    have hs₁ := hs.of_kp k₁ (by decide)
    have hoff : ∀ k < 6, Off (SAVE + 8 * k) := fun k hk =>
      ⟨by simp only [SAVE]; omega, by simp only [SAVE]; omega⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_st hs₁ _ (hoff n (by omega)), WP.block_nil ⟨fun k hk => ?_, ?_, ?_⟩⟩
    · simp only
      rw [wd_writeW _ _ _ (hoff n (by omega)) (hoff k (by omega))]
      by_cases hkn : k = n
      · subst hkn; rw [ite_eq_left rfl, k₁.gpr _ (List.not_mem_nil)]
      · rw [ite_eq_right (by omega)]
        exact e₁ k (by omega)
    · exact f₁.writeW (List.mem_singleton_self _) _
        (Offset.contains_base b (by simp only [SAVE]; omega) (by simp only [SAVE]; omega))
    · exact ⟨fun r _ => k₁.gpr r List.not_mem_nil, k₁.rd, k₁.wr⟩

theorem save_ok {b : Addr} {s : State} (hs : Sc b s) :
    WP isa (.block save) s fun s' =>
      (∀ k < 6, wd s'.mem b (SAVE + 8 * k) = v s (saved.getD k .x19)) ∧ Frame [saveR b] s.mem s'.mem ∧
        Kp [] s s' := saves_ok 6 (by decide) s hs

/-! ## Decoding the u-coordinate -/

/-- The words of the u-coordinate in their registers. -/
def uws (s : State) (q : Nat) : Nat := v s (ureg q)

theorem limbOf_ok {s : State} {i : Nat} (hi : i < 15) (hm : s.gpr .x22 = 0x1ffff) :
    WP isa (.block (limbOf i)) s fun s' => v s' .x17 = ulimb (uws s) i ∧ Kp [.x17, .x19] s s' ∧
      s'.mem = s.mem := by
  have hq : ∀ q < 4, ureg q ≠ .x17 ∧ ureg q ≠ .x19 ∧ ureg q ≠ .x22 := by decide
  have hqi := hq (17 * i / 64) (by omega)
  simp only [limbOf]
  split
  · rename_i h
    apply WP.of_runBlock
    simp only [runBlock_cons, exec_lsr (show 17 * i % 64 < 64 by omega), runStep_some, exec_and_x,
      runBlock_nil, Option.some.injEq, exists_eq_left', gpr_wx_self, gpr_wx_ne _ _ (show Reg.x22 ≠ .x17 by decide)]
    refine ⟨?_, ((kp_wx s _ _).trans (kp_wx _ _ _)).sub (by sub_regs), rfl⟩
    rw [v, gpr_wx_self, and_mask17 _ _ hm, lsr_toNat, ulimb, ite_eq_left h]; rfl
  · rename_i h
    have hq1 := hq (17 * i / 64 + 1) (by omega)
    apply WP.of_runBlock
    simp only [runBlock_cons, exec_lsr (show 17 * i % 64 < 64 by omega), runStep_some,
      exec_lsl (show 64 - 17 * i % 64 < 64 by omega), exec_add_x, exec_and_x,
      runBlock_nil, Option.some.injEq, exists_eq_left', gpr_wx_self, gpr_wx_ne _ _ (show Reg.x22 ≠ .x17 by decide),
      gpr_wx_ne _ _ (show Reg.x22 ≠ .x19 by decide), gpr_wx_ne _ _ (show Reg.x17 ≠ .x19 by decide),
      gpr_wx_ne _ _ hq1.1]
    refine ⟨?_, ((((kp_wx s _ _).trans (kp_wx _ _ _)).trans (kp_wx _ _ _)).trans (kp_wx _ _ _)).sub
      (by sub_regs), rfl⟩
    rw [v, gpr_wx_self, and_mask17 _ _ hm, BitVec.toNat_add, lsr_toNat, lsl_toNat, ulimb, ite_eq_right h]; rfl

theorem ureg_ne : ∀ q < 4, ureg q ∉ [Reg.x17, .x19] := by decide

theorem ureg_ne22 : ∀ q < 4, ureg q ∉ [Reg.x22] := by decide

theorem ulimb_congr {w w' : Nat → Nat} (h : ∀ q < 4, w q = w' q) {i : Nat} (hi : i < 15) :
    ulimb w i = ulimb w' i := by
  simp only [ulimb]
  split
  · rw [h _ (by omega)]
  · rw [h _ (by omega), h (17 * i / 64 + 1) (by omega)]

theorem decodeN_ok {b : Addr} :
    ∀ n ≤ 15, ∀ s : State, Sc b s → s.gpr .x22 = 0x1ffff →
    WP isa (.block ((List.range n).flatMap fun i => limbOf i ++ [st .x17 (X1 + 8 * i), st .x17 (X3 + 8 * i)]))
      s fun s' =>
      (∀ k < n, wd s'.mem b (X1 + 8 * k) = ulimb (uws s) k ∧ wd s'.mem b (X3 + 8 * k) = ulimb (uws s) k) ∧
      Frame [slotR b X1, slotR b X3] s.mem s'.mem ∧ Kp [.x17, .x19] s s'
  | 0, _, s, _, _ => WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), Frame.refl _ _, Kp.refl _ _⟩
  | n + 1, hn, s, hs, hm => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (decodeN_ok n (by omega) s hs hm) fun s₁ ⟨e₁, f₁, k₁⟩ => ?_)
    have hs₁ := hs.of_kp k₁ (by decide)
    have hm₁ : s₁.gpr .x22 = 0x1ffff := by rw [k₁.gpr _ (by decide), hm]
    have hw : ∀ q < 4, uws s₁ q = uws s q := fun q hq => by
      simp only [uws]; rw [v, k₁.gpr _ (ureg_ne q hq)]
    refine WP.block_append (WP.mono (limbOf_ok (i := n) (by omega) hm₁) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
    have hs₂ := hs₁.of_kp k₂ (by decide)
    have hX1 : X1 = 64 := rfl
    have hX3 : X3 = 448 := rfl
    have o1 : ∀ k < 15, Off (X1 + 8 * k) := fun k hk => (slot_ok (n := 0) (by decide)).off hk
    have o3 : ∀ k < 15, Off (X3 + 8 * k) := fun k hk => (slot_ok (n := 3) (by decide)).off hk
    apply WP.of_runBlock
    rw [runBlock_cons, exec_st hs₂ _ (o1 n (by omega)), runStep_some, runBlock_cons,
      exec_st (hs₂.mem _) _ (o3 n (by omega)), runStep_some, runBlock_nil]
    refine ⟨_, rfl, fun k hk => ?_, ?_, ⟨fun r hr => ?_, (k₁.trans k₂).rd, (k₁.trans k₂).wr⟩⟩
    · simp only
      rw [wd_writeW _ _ _ (o3 n (by omega)) (o1 k (by omega)), wd_writeW _ _ _ (o1 n (by omega)) (o1 k (by omega)),
        wd_writeW _ _ _ (o3 n (by omega)) (o3 k (by omega)), wd_writeW _ _ _ (o1 n (by omega)) (o3 k (by omega)),
        m₂]
      by_cases hkn : k = n
      · subst hkn
        rw [ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left rfl, ← v, e₂,
          ulimb_congr hw (by omega)]
        exact ⟨rfl, rfl⟩
      · rw [ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_right (by omega)]
        exact e₁ k (by omega)
    · rw [← m₂] at f₁
      exact (f₁.writeW List.mem_cons_self _ (slot_contains b (slot_ok (n := 0) (by decide)) (by omega))).writeW
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (slot_contains b (slot_ok (n := 3) (by decide))
          (by omega))
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      have hr' : r ∉ [Reg.x17, .x19] ++ [Reg.x17, .x19] := by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr, hr⟩
      exact (k₁.trans k₂).gpr r hr'

/-! ## The bits of the scalar -/

theorem write1_apply (m : Mem) (a x : Addr) (w : BitVec 8) : m.write a 1 w x = if x = a then w else m x := by
  by_cases h : x = a
  · subst h
    rw [ite_eq_left rfl]
    show (if (x - x).toNat < 1 then w.extractLsb' (8 * (x - x).toNat) 8 else m x) = w
    rw [BitVec.sub_self, BitVec.toNat_zero, ite_eq_left (by decide)]
    exact BitVec.extractLsb'_eq_self
  · have h1 : ¬ (x - a).toNat < 1 := by
      intro h1
      apply h
      have h0 : (x - a).toNat = 0 := by omega
      have : x - a = 0 := BitVec.eq_of_toNat_eq (h0.trans rfl)
      rw [← BitVec.sub_add_cancel x a, this]; exact BitVec.zero_add a
    rw [ite_eq_right h, Mem.write_apply h1]

/-- Bit `j` of a byte, as a byte. -/
def bitB (kb : Byte) (j : Nat) : Byte := BitVec.ofNat 8 ((kb.toNat >>> j) &&& 1)

/-- The region of the bits of byte `i`. -/
abbrev bitsR (b : Addr) (i : Nat) : Region := ⟨b + BitVec.ofNat 64 (BITS + 8 * i), 8⟩

theorem bitStep_ok {b : Addr} {s : State} (hs : Sc b s) {i j : Nat} (hi : i < 32) (hj : j < 8)
    (h20 : s.gpr .x20 = 1) :
    WP isa (.block [.lsr .x .x19 .x17 j, .logic .and .x .x19 .x19 .x20, .strb .x19 .x3 (BITS + 8 * i + j)]) s
      fun s' => s'.mem = s.mem.write (b + BitVec.ofNat 64 (BITS + 8 * i + j)) 1
          (BitVec.ofNat 8 ((s.gpr .x17).toNat / 2 ^ j % 2)) ∧ Kp [.x19] s s' := by
  have hoff : BITS + 8 * i + j < 4096 := by simp only [BITS, slot, NSLOT]; omega
  have hin : InRegions s.wr (b + BitVec.ofNat 64 (BITS + 8 * i + j)) 1 :=
    ⟨scR b, hs.wr, Offset.contains_base b (by simp only [BITS, slot, NSLOT]; omega) (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_lsr (show j < 64 by omega), runStep_some, exec_and_x, gpr_wx_self,
    gpr_wx_ne _ _ (show Reg.x20 ≠ .x19 by decide), h20]
  rw [exec_strb hoff (by rw [gpr_wx_ne _ _ (by decide), gpr_wx_ne _ _ (by decide), hs.x3]; exact hin)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', mem_wx,
    gpr_wx_ne _ _ (show Reg.x3 ≠ .x19 by decide), hs.x3, State.read, gpr_wx_self]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and, lsr_toNat, BitVec.toNat_ofNat,
      show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, Size.bits]
    omega
  · show (State.write _ _ _ _).gpr r = _
    rw [gpr_wx_ne _ _ (by simpa using hr), gpr_wx_ne _ _ (by simpa using hr)]

/-- `x` is not in `[b + d, b + d + n)` if its offset from `b` is outside. -/
theorem not_contains {b : Addr} {d n e : Nat} (h : e < d ∨ d + n ≤ e) (hd : d + n ≤ 2 ^ 64) (he : e < 2 ^ 64) :
    ¬ (⟨b + BitVec.ofNat 64 d, n⟩ : Region).Contains (b + BitVec.ofNat 64 e) 1 := by
  simp only [Region.Contains]
  intro hc
  have := (Offset.lt_iff (b + BitVec.ofNat 64 e) b hd).mp (by omega)
  rw [Mem.sub_ofNat_toNat b he] at this
  omega

theorem bitsN_ok {b : Addr} {i : Nat} (hi : i < 32) : ∀ n ≤ 8, ∀ s : State, Sc b s → s.gpr .x20 = 1 →
    WP isa (.block ((List.range n).flatMap fun j =>
      [.lsr .x .x19 .x17 j, .logic .and .x .x19 .x19 .x20, .strb .x19 .x3 (BITS + 8 * i + j)])) s fun s' =>
      (∀ j < n, s'.mem (b + BitVec.ofNat 64 (BITS + 8 * i + j)) =
        BitVec.ofNat 8 ((s.gpr .x17).toNat / 2 ^ j % 2)) ∧
      Frame [bitsR b i] s.mem s'.mem ∧ Kp [.x19] s s'
  | 0, _, s, _, _ => WP.block_nil ⟨fun j hj => absurd hj (Nat.not_lt_zero _), Frame.refl _ _, Kp.refl _ _⟩
  | n + 1, hn, s, hs, h20 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (bitsN_ok hi n (by omega) s hs h20) fun s₁ ⟨e₁, f₁, k₁⟩ => ?_)
    have h20₁ : s₁.gpr .x20 = 1 := by rw [k₁.gpr _ (by decide), h20]
    have h17₁ : s₁.gpr .x17 = s.gpr .x17 := k₁.gpr _ (by decide)
    refine WP.mono (bitStep_ok (hs.of_kp k₁ (by decide)) hi (j := n) (by omega) h20₁) fun s₂ ⟨m₂, k₂⟩ =>
      ⟨fun j hj => ?_, ?_, (k₁.trans k₂).sub (by sub_regs)⟩
    · rw [m₂, write1_apply]
      by_cases hjn : j = n
      · subst hjn; rw [ite_eq_left rfl, h17₁]
      · rw [ite_eq_right (Offset.add_ofNat_ne b (by simp only [BITS, slot, NSLOT]; omega)
          (by simp only [BITS, slot, NSLOT]; omega) (by omega))]
        exact e₁ j (by omega)
    · rw [m₂]
      exact f₁.write (List.mem_singleton_self _) _ (Offset.contains b (by omega) (by omega)
        (by simp only [BITS, slot, NSLOT]; omega))

theorem bitB_eq (kb : Byte) (j : Nat) : BitVec.ofNat 8 (kb.toNat / 2 ^ j % 2) = bitB kb j := by
  simp only [bitB, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

theorem bitsOf_ok {b : Addr} {s : State} (hs : Sc b s) {i : Nat} (hi : i < 32) (h20 : s.gpr .x20 = 1)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 i) 1) :
    WP isa (.block (bitsOf i)) s fun s' =>
      (∀ j < 8, s'.mem (b + BitVec.ofNat 64 (BITS + 8 * i + j)) =
        bitB (s.mem (s.gpr .x1 + BitVec.ofNat 64 i)) j) ∧
      Frame [bitsR b i] s.mem s'.mem ∧ Kp [.x17, .x19] s s' := by
  rw [bitsOf]
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrb (by omega) hin, ?_⟩
  have hs₁ := sc_ww s ((s.mem.read (s.gpr .x1 + BitVec.ofNat 64 i) 1).setWidth 32) hs (show Reg.x17 ≠ .x3 by decide)
  refine WP.mono (bitsN_ok hi 8 (by decide) _ hs₁ (by rw [gpr_ww_ne _ _ (by decide), h20]))
    fun s' ⟨e, f, k⟩ => ⟨fun j hj => ?_, f, ((kp_ww _ _ _).trans k).sub (by sub_regs)⟩
  rw [e j hj, gpr_ww_self, read1_toNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans (s.mem _).isLt (by decide)), bitB_eq]

/-- The region of the bits. -/
abbrev bitsArea (b : Addr) : Region := ⟨b + BitVec.ofNat 64 BITS, 256⟩

theorem bitsR_sub (b : Addr) {i : Nat} (hi : i < 32) : Region.Sub (bitsR b i) (bitsArea b) :=
  Offset.sub b (by omega) (by omega)

theorem bitsAll_ok {b sc : Addr} (hdisj : ∀ i < 32, ∀ r ∈ [bitsArea b], ¬ r.Contains (sc + BitVec.ofNat 64 i) 1) :
    ∀ n ≤ 32, ∀ s : State, Sc b s → s.gpr .x20 = 1 → s.gpr .x1 = sc →
    (∀ i < 32, InRegions (s.rd ++ s.wr) (sc + BitVec.ofNat 64 i) 1) →
    WP isa (.block ((List.range n).flatMap bitsOf)) s fun s' =>
      (∀ t < 8 * n, s'.mem (b + BitVec.ofNat 64 (BITS + t)) =
        bitB (s.mem (sc + BitVec.ofNat 64 (t / 8))) (t % 8)) ∧
      Frame [bitsArea b] s.mem s'.mem ∧ Kp [.x17, .x19] s s'
  | 0, _, s, _, _, _, _ => WP.block_nil ⟨fun t ht => absurd ht (by omega), Frame.refl _ _, Kp.refl _ _⟩
  | n + 1, hn, s, hs, h20, h1, hin => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (bitsAll_ok hdisj n (by omega) s hs h20 h1 hin) fun s₁ ⟨e₁, f₁, k₁⟩ => ?_)
    have h20₁ : s₁.gpr .x20 = 1 := by rw [k₁.gpr _ (by decide), h20]
    have h1₁ : s₁.gpr .x1 = sc := by rw [k₁.gpr _ (by decide), h1]
    refine WP.mono (bitsOf_ok (hs.of_kp k₁ (by decide)) (i := n) (by omega) h20₁
      (by rw [h1₁, k₁.rd, k₁.wr]; exact hin n (by omega))) fun s₂ ⟨e₂, f₂, k₂⟩ =>
      ⟨fun t ht => ?_, f₁.trans (f₂.sub fun r hr => ⟨bitsArea b, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact bitsR_sub b (by omega)⟩),
        (k₁.trans k₂).sub (by sub_regs)⟩
    have hsc : s₁.mem (sc + BitVec.ofNat 64 n) = s.mem (sc + BitVec.ofNat 64 n) := f₁ _ (hdisj n (by omega))
    by_cases htn : t < 8 * n
    · rw [f₂ _ (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact not_contains (by omega) (by simp only [BITS, slot, NSLOT]; omega)
          (by simp only [BITS, slot, NSLOT]; omega))]
      exact e₁ t htn
    · have e := e₂ (t - 8 * n) (by omega)
      rw [show BITS + 8 * n + (t - 8 * n) = BITS + t by omega, h1₁, hsc] at e
      rw [e, show t / 8 = n by omega, show t % 8 = t - 8 * n by omega]

/-! ## The initial values -/

theorem zeroStep_ok {b : Addr} {s : State} (hs : Sc b s) {o i : Nat} (ho : Off (o + 8 * i))
    (h17 : s.gpr .x17 = 0) :
    WP isa (.block [st .x17 (o + 8 * i)]) s fun s' => ∃ x : BitVec 64, x.toNat = 0 ∧
      s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 8 * i)) x ∧ Kp [] s s' := by
  refine WP.block_cons_iff.mpr ⟨_, exec_st hs _ ho, WP.block_nil ⟨s.gpr .x17, by rw [h17]; rfl, rfl,
    ⟨fun _ _ => rfl, rfl, rfl⟩⟩⟩

/-- The limbs of `0`, and of `1`. -/
def zeroL (_ : Nat) : Nat := 0
def oneL (i : Nat) : Nat := if i = 0 then 1 else 0

theorem zero_ok {b : Addr} {s : State} (hs : Sc b s) {o : Nat} (ho : o < 15) (h17 : s.gpr .x17 = 0) :
    WP isa (.block (zero (slot o))) s fun s' =>
      limbs s'.mem b (slot o) = (fun k => if k < 15 then 0 else 0) ∧
      Frame [slotR b (slot o)] s.mem s'.mem ∧ Kp [] s s' :=
  limbwise_all (slot_ok ho) (fun i => [st .x17 (slot o + 8 * i)]) [] (by decide) (fun _ _ => 0)
    (fun _ => []) (fun s => s.gpr .x17 = 0) (fun s s' h k => by rw [k.gpr _ (by simp), h])
    (fun i hi s hs h17 => zeroStep_ok hs ((slot_ok ho).off hi) h17) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ h => absurd h List.not_mem_nil) hs h17

theorem zero_inv {b : Addr} {s₀ s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (h : Inv b s₀ s vals bnds) {o : Nat} (ho : o < 15) (h17 : s.gpr .x17 = 0) :
    WP isa (.block (zero (slot o))) s fun s' =>
      Inv b s₀ s' (Function.update vals o 0) (Function.update bnds o (some 18)) ∧ Kp [] s s' :=
  WP.mono (zero_ok h.sc ho h17) fun s' ⟨e, f, k⟩ =>
    ⟨⟨h.sc.of_kp k (by decide), h.sl.update _ _ (by
      rw [e]
      exact ⟨fun i hi => by simp only [hi, ite_true]; decide, rfl⟩)
      fun n hn hno => limbs_other ho hn hno f,
    h.kp_sub k (List.nil_subset _), frame_slot h.fr ho f⟩, k⟩

/-- `[o] = 1`: zero, then limb 0 set to 1. -/
theorem one_inv {b : Addr} {s₀ s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (h : Inv b s₀ s vals bnds) {o : Nat} (ho : o < 15) (h17 : s.gpr .x17 = 0) :
    WP isa (.block (zero (slot o) ++ ([.movz .x .x19 1 0, st .x19 (slot o)] : List Instr))) s fun s' =>
      Inv b s₀ s' (Function.update vals o 1) (Function.update bnds o (some 18)) := by
  have o0 : Off (slot o) := by have := (slot_ok ho).off (i := 0) (by decide); simpa using this
  refine WP.block_append (WP.mono (zero_ok h.sc ho h17) fun s₁ ⟨e₁, f₁, k₁⟩ => ?_)
  have hs₁ := h.sc.of_kp k₁ (by decide)
  refine WP.block_cons_iff.mpr ⟨_, exec_movz, ?_⟩
  have hs₂ := sc_wx s₁ ((1 : BitVec 16).setWidth 64) hs₁ (show Reg.x19 ≠ .x3 by decide)
  refine WP.block_cons_iff.mpr ⟨_, exec_st hs₂ _ o0, WP.block_nil ?_⟩
  have hf : Frame [slotR b (slot o)] s.mem (s₁.mem.writeW (b + BitVec.ofNat 64 (slot o))
      ((s₁.write .x .x19 ((1 : BitVec 16).setWidth 64)).gpr .x19)) :=
    f₁.writeW (List.mem_singleton_self _) _ (by
      have := slot_contains b (slot_ok ho) (k := 0) (by decide); simpa using this)
  refine ⟨⟨hs₂.x3, hs₂.wr⟩, h.sl.update _ _ ?_ fun n hn hno => limbs_other ho hn hno hf,
    h.kp_sub (k₁.trans (W' := [.x19]) ⟨fun r hr => gpr_wx_ne _ _ (by simpa using hr), rfl, rfl⟩)
      (by decide), frame_slot h.fr ho hf⟩
  have e : limbs (s₁.mem.writeW (b + BitVec.ofNat 64 (slot o)) ((s₁.write .x .x19 ((1 : BitVec 16).setWidth 64)).gpr .x19))
      b (slot o) = fun i => if i < 15 then oneL i else 0 := funext fun i => by
    simp only [limbs]
    split
    · rename_i hi
      rw [wd_writeW _ _ _ o0 ((slot_ok ho).off hi), gpr_wx_self]
      by_cases h0 : i = 0
      · subst h0; rw [ite_eq_left (by simp)]; rfl
      · rw [ite_eq_right (by omega), show wd s₁.mem b (slot o + 8 * i) = limbs s₁.mem b (slot o) i by
          simp only [limbs, hi, ite_true], e₁]
        simp only [oneL, h0, ite_false, hi, ite_true]
    · rfl
  dsimp only
  rw [mem_wx, e]
  refine ⟨fun i hi => by simp only [hi, ite_true, oneL]; split <;> decide, ?_⟩
  rfl

/-! ## Decoding, with the loads -/

/-- Word `q` of the 32 bytes at `p`. -/
def uw (m : Mem) (p : Addr) (q : Nat) : Nat := (m.readW (p + BitVec.ofNat 64 (8 * q)) 64).toNat

theorem ldrx_ok {s : State} {t n : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8) :
    WP isa (.block [.ldr .x t n off]) s fun s' =>
      s'.gpr t = s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64 ∧ Kp [t] s s' ∧ s'.mem = s.mem :=
  WP.block_cons_iff.mpr ⟨_, exec_ldr_x ho hin, WP.block_nil ⟨gpr_wx_self _ _ _, kp_wx _ _ _, rfl⟩⟩

theorem loadU_ok {s : State} {pt : Addr} (h2 : s.gpr .x2 = pt)
    (hin : ∀ q < 4, InRegions (s.rd ++ s.wr) (pt + BitVec.ofNat 64 (8 * q)) 8) :
    WP isa (.block loadU) s fun s' => (∀ q < 4, v s' (ureg q) = uw s.mem pt q) ∧
      Kp [.x4, .x5, .x6, .x7] s s' ∧ s'.mem = s.mem := by
  rw [loadU, show ∀ (a c d e : Instr), [a, c, d, e] = [a] ++ ([c] ++ ([d] ++ [e])) from fun _ _ _ _ => rfl]
  refine WP.block_append (WP.mono (ldrx_ok (s := s) (t := .x4) (off := 0) (by decide)
    (by rw [h2]; exact hin 0 (by decide))) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  have g₁ : s₁.gpr .x2 = pt := by rw [k₁.gpr _ (by decide), h2]
  refine WP.block_append (WP.mono (ldrx_ok (s := s₁) (t := .x5) (off := 8) (by decide)
    (by rw [g₁, k₁.rd, k₁.wr]; exact hin 1 (by decide))) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
  have g₂ : s₂.gpr .x2 = pt := by rw [k₂.gpr _ (by decide), g₁]
  refine WP.block_append (WP.mono (ldrx_ok (s := s₂) (t := .x6) (off := 16) (by decide)
    (by rw [g₂, k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hin 2 (by decide))) fun s₃ ⟨e₃, k₃, m₃⟩ => ?_)
  have g₃ : s₃.gpr .x2 = pt := by rw [k₃.gpr _ (by decide), g₂]
  refine WP.mono (ldrx_ok (s := s₃) (t := .x7) (off := 24) (by decide)
    (by rw [g₃, k₃.rd, k₃.wr, k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hin 3 (by decide))) fun s₄ ⟨e₄, k₄, m₄⟩ =>
    ⟨fun q hq => ?_, (((k₁.trans k₂).trans k₃).trans k₄).sub (by sub_regs), by rw [m₄, m₃, m₂, m₁]⟩
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl
  · show v s₄ .x4 = _
    rw [v, k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), e₁, h2]; rfl
  · show v s₄ .x5 = _
    rw [v, k₄.gpr _ (by decide), k₃.gpr _ (by decide), e₂, g₁, m₁]; rfl
  · show v s₄ .x6 = _
    rw [v, k₄.gpr _ (by decide), e₃, g₂, m₂, m₁]; rfl
  · show v s₄ .x7 = _
    rw [v, e₄, g₃, m₃, m₂, m₁]; rfl

/-- The limbs of the u-coordinate (zero beyond the fifteenth). -/
def ulimbF (w : Nat → Nat) (i : Nat) : Nat := if i < 15 then ulimb w i else 0

theorem decode_ok {b pt : Addr} {s : State} (hs : Sc b s) (h2 : s.gpr .x2 = pt)
    (hin : ∀ q < 4, InRegions (s.rd ++ s.wr) (pt + BitVec.ofNat 64 (8 * q)) 8) :
    WP isa (.block decode) s fun s' =>
      limbs s'.mem b X1 = ulimbF (uw s.mem pt) ∧ limbs s'.mem b X3 = ulimbF (uw s.mem pt) ∧
      Frame [slotR b X1, slotR b X3] s.mem s'.mem ∧ Kp [.x4, .x5, .x6, .x7, .x22, .x17, .x19] s s' := by
  rw [decode, List.append_assoc]
  refine WP.block_append (WP.mono (loadU_ok h2 hin) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  refine WP.block_append (WP.mono (mask17_ok s₁) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
  have hs₂ := (hs.of_kp k₁ (by decide)).of_kp k₂ (by decide)
  refine WP.mono (decodeN_ok 15 (by decide) s₂ hs₂ e₂) fun s₃ ⟨e₃, f₃, k₃⟩ => ?_
  have hu : ∀ i < 15, ulimb (uws s₂) i = ulimb (uw s.mem pt) i := fun i hi =>
    ulimb_congr (fun q hq => by
      simp only [uws]; rw [v, k₂.gpr _ (ureg_ne22 q hq), ← v, e₁ q hq]) hi
  refine ⟨funext fun i => ?_, funext fun i => ?_, by rw [← m₁, ← m₂]; exact f₃,
    ((k₁.trans k₂).trans k₃).sub (by sub_regs)⟩
  · simp only [limbs, ulimbF]; split
    · rename_i hi; rw [(e₃ i hi).1, hu i hi]
    · rfl
  · simp only [limbs, ulimbF]; split
    · rename_i hi; rw [(e₃ i hi).2, hu i hi]
    · rfl

theorem ulimbF_rep {w : Nat → Nat} (h0 : w 0 < 2 ^ 64) (h1 : w 1 < 2 ^ 64) (h2 : w 2 < 2 ^ 64) :
    Bnd (ulimbF w) 17 ∧ valN (ulimbF w) 15 = uN (w 0) (w 1) (w 2) (w 3) % 2 ^ 255 := by
  refine ⟨fun i hi => ?_, ?_⟩
  · simp only [ulimbF, hi, ite_true, ulimb]; split <;> exact Nat.mod_lt _ (by decide)
  · rw [valN_congr (g := fun i => uN (w 0) (w 1) (w 2) (w 3) / 2 ^ (17 * i) % 2 ^ 17) fun i hi => by
      simp only [ulimbF, hi, ite_true]; exact ulimb_eq h0 h1 h2 i hi, valN_digits]

/-! ## The clamped bits -/

/-- The byte at `BITS + t`: bit `t` of the clamped scalar with the bytes `kb`. -/
def clampB (kb : Nat → Byte) (t : Nat) : Byte :=
  if t < 3 then 0 else if t = 254 then 1 else bitB (kb (t / 8)) (t % 8)

theorem bits_ok {b sc : Addr} {s : State} (hs : Sc b s) (h1 : s.gpr .x1 = sc)
    (hin : ∀ i < 32, InRegions (s.rd ++ s.wr) (sc + BitVec.ofNat 64 i) 1)
    (hdisj : ∀ i < 32, ∀ r ∈ [bitsArea b], ¬ r.Contains (sc + BitVec.ofNat 64 i) 1) :
    WP isa (.block Impl.X25519.AArch64.bits) s fun s' =>
      (∀ t < 256, s'.mem (b + BitVec.ofNat 64 (BITS + t)) = clampB (fun i => s.mem (sc + BitVec.ofNat 64 i)) t) ∧
      Frame [bitsArea b] s.mem s'.mem ∧ Kp [.x17, .x19, .x20] s s' := by
  simp only [Impl.X25519.AArch64.bits, List.cons_append, List.nil_append]
  refine WP.block_cons_iff.mpr ⟨_, exec_movz, ?_⟩
  have hs₁ := sc_wx s ((1 : BitVec 16).setWidth 64) hs (show Reg.x20 ≠ .x3 by decide)
  refine WP.block_append (WP.mono (bitsAll_ok hdisj 32 (by decide) _ hs₁ (gpr_wx_self _ _ _)
    (by rw [gpr_wx_ne _ _ (by decide), h1]) hin) fun s₂ ⟨e₂, f₂, k₂⟩ => ?_)
  have hs₂ := hs₁.of_kp k₂ (by decide)
  have h20 : s₂.gpr .x20 = 1 := by rw [k₂.gpr _ (by decide), gpr_wx_self]; rfl
  have c : ∀ t < 256, InRegions s₂.wr (s₂.gpr .x3 + BitVec.ofNat 64 (BITS + t)) 1 := fun t ht => by
    have h1 : BITS + t + 1 ≤ 4096 := by simp only [BITS, slot, NSLOT]; omega
    have h2 : BITS + t < 2 ^ 64 := by simp only [BITS, slot, NSLOT]; omega
    rw [hs₂.x3]
    exact ⟨scR b, hs₂.wr, Offset.contains_base b h1 h2⟩
  have ne : ∀ t < 256, ∀ u < 256, t ≠ u → b + BitVec.ofNat 64 (BITS + t) ≠ b + BitVec.ofNat 64 (BITS + u) :=
    fun t ht u hu h => Offset.add_ofNat_ne b (by simp only [BITS, slot, NSLOT]; omega)
      (by simp only [BITS, slot, NSLOT]; omega) (by omega)
  have cb : ∀ t < 256, (bitsArea b).Contains (b + BitVec.ofNat 64 (BITS + t)) 1 := fun t ht =>
    Offset.contains b (by omega) (by omega) (by simp only [BITS, slot, NSLOT]; omega)
  have hclamp : WP isa (.block [.movz .x .x19 0 0, .strb .x19 .x3 BITS, .strb .x19 .x3 (BITS + 1),
      .strb .x19 .x3 (BITS + 2), .strb .x20 .x3 (BITS + 254)]) s₂ fun s' =>
      s'.mem = (((s₂.mem.write (b + BitVec.ofNat 64 (BITS + 0)) 1 0).write (b + BitVec.ofNat 64 (BITS + 1)) 1 0).write
        (b + BitVec.ofNat 64 (BITS + 2)) 1 0).write (b + BitVec.ofNat 64 (BITS + 254)) 1 1 ∧ Kp [.x19] s₂ s' := by
    refine WP.block_cons_iff.mpr ⟨_, exec_movz, ?_⟩
    have hs₃ := sc_wx s₂ ((0 : BitVec 16).setWidth 64) hs₂ (show Reg.x19 ≠ .x3 by decide)
    have g19 : (s₂.write .x .x19 ((0 : BitVec 16).setWidth 64)).gpr .x19 = 0 := gpr_wx_self _ _ _
    have g20 : (s₂.write .x .x19 ((0 : BitVec 16).setWidth 64)).gpr .x20 = 1 := by
      rw [gpr_wx_ne _ _ (by decide), h20]
    have k3 : Kp [.x19] s₂ (s₂.write .x .x19 ((0 : BitVec 16).setWidth 64)) := kp_wx _ _ _
    have m3 : (s₂.write .x .x19 ((0 : BitVec 16).setWidth 64)).mem = s₂.mem := rfl
    generalize s₂.write .x .x19 ((0 : BitVec 16).setWidth 64) = s₃ at hs₃ g19 g20 k3 m3
    have hst : ∀ (r : Reg) (t : Nat) (s₄ : State), t < 256 → Sc b s₄ → ∀ (l : List Instr) (Q : State → Prop),
        WP isa (.block l) { s₄ with mem := s₄.mem.write (b + BitVec.ofNat 64 (BITS + t)) 1 ((s₄.read .w r).setWidth 8) }
          Q → WP isa (.block (.strb r .x3 (BITS + t) :: l)) s₄ Q := fun r t s₄ ht hs₄ l Q h => by
      have h1 : BITS + t + 1 ≤ 4096 := by simp only [BITS, slot, NSLOT]; omega
      have h2 : BITS + t < 2 ^ 64 := by simp only [BITS, slot, NSLOT]; omega
      have hin : InRegions s₄.wr (s₄.gpr .x3 + BitVec.ofNat 64 (BITS + t)) 1 := by
        rw [hs₄.x3]; exact ⟨scR b, hs₄.wr, Offset.contains_base b h1 h2⟩
      refine WP.block_cons_iff.mpr ⟨_, exec_strb (by omega) hin, ?_⟩
      rw [hs₄.x3]
      exact h
    refine hst .x19 0 s₃ (by decide) hs₃ _ _ ?_
    refine hst .x19 1 _ (by decide) (hs₃.mem _) _ _ ?_
    refine hst .x19 2 _ (by decide) ((hs₃.mem _).mem _) _ _ ?_
    refine hst .x20 254 _ (by decide) (((hs₃.mem _).mem _).mem _) _ _ (WP.block_nil ⟨?_, ⟨k3.gpr, k3.rd, k3.wr⟩⟩)
    simp only [State.read, g19, g20, m3]
    rfl
  refine WP.mono hclamp fun s' ⟨m', k'⟩ => ⟨fun t ht => ?_, ?_, ((kp_wx s _ _).trans (k₂.trans k')).sub
    (by sub_regs)⟩
  · have e := e₂ t (by omega)
    simp only [mem_wx] at e
    rw [m', write1_apply, write1_apply, write1_apply, write1_apply]
    simp only [clampB]
    by_cases h254 : t = 254
    · subst h254; rw [ite_eq_left rfl, ite_eq_right (by decide), ite_eq_left rfl]
    rw [ite_eq_right (ne t ht 254 (by decide) h254), ite_eq_right h254]
    by_cases h2 : t = 2
    · subst h2; rw [ite_eq_left rfl, ite_eq_left (by decide)]
    rw [ite_eq_right (ne t ht 2 (by decide) h2)]
    by_cases h1 : t = 1
    · subst h1; rw [ite_eq_left rfl, ite_eq_left (by decide)]
    rw [ite_eq_right (ne t ht 1 (by decide) h1)]
    by_cases h0 : t = 0
    · subst h0; rw [ite_eq_left rfl, ite_eq_left (by decide)]
    rw [ite_eq_right (ne t ht 0 (by decide) h0), ite_eq_right (by omega), e]
  · simp only [mem_wx] at f₂
    rw [m']
    exact (((f₂.write (List.mem_singleton_self _) _ (cb 0 (by decide))).write
      (List.mem_singleton_self _) _ (cb 1 (by decide))).write (List.mem_singleton_self _) _ (cb 2 (by decide))).write
      (List.mem_singleton_self _) _ (cb 254 (by decide))

end VG.Proof.X25519.AArch64
