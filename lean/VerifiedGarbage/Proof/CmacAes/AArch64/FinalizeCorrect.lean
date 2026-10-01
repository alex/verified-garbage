import VerifiedGarbage.Proof.CmacAes.AArch64.Finalize

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_finalize` is correct

Untrusted: everything here is checked by Lean. Before the call, the
counter block (at `S + 2048`) holds `Mₙ ⊕ C`, for the last block `Mₙ` of
§6.2 step 4 and the chaining value `C` at `state`, the state is zeroed, and
`x19` and `x30` are saved in the scratch buffer; the call leaves
`CIPH_K(C ⊕ Mₙ)` there, the MAC (`macFull_split`).
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- The precondition, by name: the key (schedule and subkeys) `W`, the state
`St`, the last bytes `P` (`L` of them), the scratch buffer `S` and the
rounds `R`. -/
structure FPre (s₀ : State) (W St P S : Addr) (L R : Nat) : Prop where
  x0 : s₀.gpr .x0 = W
  x2 : s₀.gpr .x2 = St
  x3 : s₀.gpr .x3 = P
  x4 : (s₀.gpr .x4).toNat = L
  x5 : s₀.gpr .x5 = S
  x1 : (s₀.gpr .x1).toNat = R
  rd : s₀.rd = [⟨W, 272⟩, ⟨P, L⟩]
  wr : s₀.wr = [⟨St, 16⟩, ⟨S, 2176⟩]
  key_st : (⟨W, 272⟩ : Region).Disjoint ⟨St, 16⟩
  key_scr : (⟨W, 272⟩ : Region).Disjoint ⟨S, 2176⟩
  last_st : (⟨P, L⟩ : Region).Disjoint ⟨St, 16⟩
  last_scr : (⟨P, L⟩ : Region).Disjoint ⟨S, 2176⟩
  st_scr : (⟨St, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  key_wrap : W.toNat + 272 ≤ 2 ^ 64
  st_wrap : St.toNat + 16 ≤ 2 ^ 64
  last_wrap : P.toNat + L ≤ 2 ^ 64
  scr_wrap : S.toNat + 2176 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16

theorem FPre.of {s₀ : State} (h : finalizeAArch64.pre s₀) :
    FPre s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat (s₀.gpr .x1).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes in `m`. -/
abbrev mn (m : Mem) (W P : Addr) (L : Nat) : List Byte :=
  Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 240) 16)
    (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 256) 16) (Spec.Aes.bytesAt m P L)

/-- What the branch on the length leaves: `Mₙ` in the counter block. -/
structure BPost (s₀ : State) (W St P S : Addr) (L : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = W
  x2 : s.gpr .x2 = St
  x5 : s.gpr .x5 = S
  x1 : s.gpr .x1 = s₀.gpr .x1
  saved : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨S + BitVec.ofNat 64 2048, 16⟩] s₀.mem s.mem
  blk : Spec.Aes.bytesAt s.mem (S + BitVec.ofNat 64 2048) 16 = mn s₀.mem W P L

section
variable {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R)
include hp

theorem FPre.inScr {d n : Nat} (h : d + n ≤ 2176) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := ⟨S, 2176⟩) (by simp) (Offset.contains_base _ h (by have := hp.scr_wrap; omega))

theorem FPre.inKey {d n : Nat} (h : d + n ≤ 272) : InRegions (s₀.rd ++ s₀.wr) (W + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := ⟨W, 272⟩) (by simp) (Offset.contains_base _ h (by have := hp.key_wrap; omega))

theorem FPre.inLast {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (P + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := ⟨P, L⟩) (by simp) (Offset.contains_base _ h (by have := hp.len; omega))

end

theorem FPre.scrD {S : Addr} {d n : Nat} (h : d + n ≤ 2176) : Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 2176⟩ :=
  Offset.sub_base _ h

theorem wr_in {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem not_x9 {r : Reg} (hr : r ∈ preserved) : r ≠ .x9 := by rintro rfl; simp [preserved] at hr
theorem not_x10 {r : Reg} (hr : r ∈ preserved) : r ≠ .x10 := by rintro rfl; simp [preserved] at hr
theorem not_x6 {r : Reg} (hr : r ∈ preserved) : r ≠ .x6 := by rintro rfl; simp [preserved] at hr
theorem not_x7 {r : Reg} (hr : r ∈ preserved) : r ≠ .x7 := by rintro rfl; simp [preserved] at hr
theorem not_x8 {r : Reg} (hr : r ∈ preserved) : r ≠ .x8 := by rintro rfl; simp [preserved] at hr

theorem full_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) (hL : L = 16)
    {s : State} (hg : ∀ r, r ≠ .x9 → s.gpr r = s₀.gpr r) (hm : s.mem = s₀.mem) (hsp : s.sp = s₀.sp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block full) s (BPost s₀ W St P S L) := by
  subst hL
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  obtain ⟨s', run, mem, g, sp, rd, wr⟩ := xor2_ok s .x3 .x0 .x5 0 240 2048
    (P := P) (Q := W + BitVec.ofNat 64 240) (C := S + BitVec.ofNat 64 2048)
    (by decide) (by decide) (by decide)
    (by rw [hg _ (by decide), hp.x3, k0]) (by rw [hg _ (by decide), hp.x3])
    (by rw [hg _ (by decide), hp.x0]) (by rw [hg _ (by decide), hp.x0, Offset.add_add])
    (by rw [hg _ (by decide), hp.x5]) (by rw [hg _ (by decide), hp.x5, Offset.add_add])
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by rw [hrd, hwr]; simpa using hp.inLast (d := 0) (n := 8) (by decide))
    (by rw [hrd, hwr]; exact hp.inLast (d := 8) (n := 8) (by decide))
    (by rw [hrd, hwr]; exact hp.inKey (d := 240) (n := 8) (by decide))
    (by rw [hrd, hwr, Offset.add_add]; exact hp.inKey (d := 248) (n := 8) (by decide))
    (by rw [hwr]; exact hp.inScr (d := 2048) (n := 8) (by decide))
    (by rw [hwr, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide))
  rw [full_eq]
  refine WP.of_runBlock ⟨s', run, ?_⟩
  have gg (r : Reg) (h₁ : r ≠ .x9) (h₂ : r ≠ .x10) : s'.gpr r = s₀.gpr r := by rw [g r h₁ h₂, hg r h₁]
  refine ⟨by rw [gg _ (by decide) (by decide), hp.x0], by rw [gg _ (by decide) (by decide), hp.x2],
    by rw [gg _ (by decide) (by decide), hp.x5], gg _ (by decide) (by decide),
    fun r hr => gg r (not_x9 hr) (not_x10 hr), by rw [sp, hsp], by rw [rd, hrd],
    by rw [wr, hwr], by rw [mem, hm]; exact Proof.Cmac.xor2Mem_frame _ _ _ _, ?_⟩
  rw [mem, hm, Proof.Cmac.xor2Mem_bytes]
  · simp only [mn, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, ite_true]
    exact Proof.Cmac.xor_comm _ _
  · exact (hp.last_scr.symm.sub_left (FPre.scrD (d := 2048) (n := 8) (by decide))).sub_right
      (Offset.sub_base P (d := 8) (n := 8) (k := 16) (by decide))
  · rw [Offset.add_add]
    exact (hp.key_scr.symm.sub_left (FPre.scrD (d := 2048) (n := 8) (by decide))).sub_right
      (Offset.sub_base W (d := 248) (n := 8) (k := 272) (by decide))

open VG.WriteBytes in
theorem partial_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) (hL : L < 16)
    {s : State} (hg : ∀ r, r ≠ .x9 → s.gpr r = s₀.gpr r) (hm : s.mem = s₀.mem) (hsp : s.sp = s₀.sp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa partialBlock s (BPost s₀ W St P S L) := by
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  have hb : L < 2 ^ 64 := by omega
  have h4 : s₀.gpr .x4 = BitVec.ofNat 64 L := by rw [← hp.x4]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨C, hC⟩ : ∃ C, S + BitVec.ofNat 64 2048 = C := ⟨_, rfl⟩
  have hc : s.gpr .x5 + BitVec.ofNat 64 2048 = C := by rw [hg _ (by decide), hp.x5, hC]
  have hc8 : s.gpr .x5 + BitVec.ofNat 64 2056 = C + BitVec.ofNat 64 8 := by
    rw [hg _ (by decide), hp.x5, ← hC, Offset.add_add]
  have dPC : (⟨P, L⟩ : Region).Disjoint ⟨C, 16⟩ := by rw [← hC]; exact hp.last_scr.sub_right (FPre.scrD (by decide))
  have dKC (d n : Nat) (h : d + n ≤ 272) : (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨C, 16⟩ := by
    rw [← hC]; exact (hp.key_scr.sub_left (Offset.sub_base _ h)).sub_right (FPre.scrD (by decide))
  -- Zero the block.
  obtain ⟨s₁, run₁, mem₁, x6₁, x7₁, x8₁, g₁, sp₁, rd₁, wr₁⟩ := zero_ok s hc hc8
    (by rw [hwr, ← hC]; exact hp.inScr (d := 2048) (n := 8) (by decide))
    (by rw [hwr, ← hC, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have zf : s₁.mem = Proof.Cmac.zero2 s₀.mem C := by rw [mem₁, hm]
  have fz : Frame [⟨C, 16⟩] s₀.mem (Proof.Cmac.zero2 s₀.mem C) := Proof.Cmac.frame_store2 _ _ _
  have lastZ : Spec.Aes.bytesAt (Proof.Cmac.zero2 s₀.mem C) P L = Spec.Aes.bytesAt s₀.mem P L :=
    Proof.Cmac.bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dPC) (by omega)
  have g₁' (r : Reg) (h₁ : r ≠ .x6) (h₂ : r ≠ .x7) (h₃ : r ≠ .x8) (h₄ : r ≠ .x9) : s₁.gpr r = s₀.gpr r := by
    rw [g₁ r h₁ h₂ h₃ h₄, hg r h₄]
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (s₂ : State) =>
      s₂.mem = writeBytes (Proof.Cmac.zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L) ∧
      s₂.gpr .x6 = C + BitVec.ofNat 64 L ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s₂.gpr r = s₀.gpr r) ∧
      s₂.sp = s₀.sp ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr) ?_ fun s₂ h₂ => ?_)
  · have ev : isa.eval (.zero .x .x4) s₁ = some (decide (L = 0)) := by
      show some (s₁.read .x .x4 == 0) = _
      rw [State.read, g₁' _ (by decide) (by decide) (by decide) (by decide), h4, BitVec.setWidth_eq]
      have := ofNat_ne_zero hb
      rw [bne] at this
      cases hx : (BitVec.ofNat 64 L == 0) <;> rw [hx] at this <;> cases hd : decide (L = 0) <;> simp_all
    by_cases hL0 : L = 0
    · subst hL0
      refine WP.ite true (by rw [ev]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [zf]; simp [Spec.Aes.bytesAt, writeBytes_nil], by rw [x6₁]; simp,
        fun r h₁ h₂ h₃ h₄ => g₁' r h₁ h₂ h₃ h₄, by rw [sp₁, hsp], by rw [rd₁, hrd], by rw [wr₁, hwr]⟩
    · refine WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (copy_ok s₁ (P := P) (C := C) (by omega) hL
        (by rw [x7₁, hg _ (by decide), hp.x3]) x6₁
        (by rw [x8₁, hg _ (by decide), h4])
        (fun i hi => by rw [rd₁, wr₁, hrd, hwr]; exact hp.inLast (d := i) (n := 1) (by omega))
        (fun i hi => by
          rw [wr₁, hwr, ← hC, Offset.add_add]; exact hp.inScr (d := 2048 + i) (n := 1) (by omega)) dPC) ?_
      rintro s₂ ⟨m₂, x6₂, g₂, sp₂, rd₂, wr₂⟩
      refine ⟨by rw [m₂, zf, lastZ], x6₂, fun r h₁ h₂ h₃ h₄ => by rw [g₂ r h₁ h₂ h₃ h₄, g₁' r h₁ h₂ h₃ h₄],
        by rw [sp₂, sp₁, hsp], by rw [rd₂, rd₁, hrd], by rw [wr₂, wr₁, hwr]⟩
  · obtain ⟨m₂, x6₂, g₂, sp₂, rd₂, wr₂⟩ := h₂
    rw [padK2_eq, WP.block_append_iff]
    obtain ⟨s₃, run₃, m₃, g₃, sp₃, rd₃, wr₃⟩ := pad_ok s₂ (B := C + BitVec.ofNat 64 L)
      (by rw [x6₂, BitVec.add_zero])
      (by rw [wr₂, ← hC, Offset.add_add]; exact hp.inScr (d := 2048 + L) (n := 1) (by omega))
    refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
    have x5₃ : s₃.gpr .x5 = S := by
      rw [g₃ _ (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide), hp.x5]
    have x0₃ : s₃.gpr .x0 = W := by
      rw [g₃ _ (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide), hp.x0]
    obtain ⟨s₄, run₄, m₄, g₄, sp₄, rd₄, wr₄⟩ := xor2_ok s₃ .x5 .x0 .x5 2048 256 2048
      (P := C) (Q := W + BitVec.ofNat 64 256) (C := C) (by decide) (by decide) (by decide)
      (by rw [x5₃, hC]) (by rw [x5₃, ← hC, Offset.add_add]) (by rw [x0₃]) (by rw [x0₃, Offset.add_add])
      (by rw [x5₃, hC]) (by rw [x5₃, ← hC, Offset.add_add])
      ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
      (by rw [rd₃, wr₃, rd₂, wr₂, ← hC]; exact wr_in (hp.inScr (d := 2048) (n := 8) (by decide)))
      (by rw [rd₃, wr₃, rd₂, wr₂, ← hC, Offset.add_add]; exact wr_in (hp.inScr (d := 2056) (n := 8) (by decide)))
      (by rw [rd₃, wr₃, rd₂, wr₂]; exact hp.inKey (d := 256) (n := 8) (by decide))
      (by rw [rd₃, wr₃, rd₂, wr₂, Offset.add_add]; exact hp.inKey (d := 264) (n := 8) (by decide))
      (by rw [wr₃, wr₂, ← hC]; exact hp.inScr (d := 2048) (n := 8) (by decide))
      (by rw [wr₃, wr₂, ← hC, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide))
    refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
    have gg (r : Reg) (h₁ : r ≠ .x6) (h₂ : r ≠ .x7) (h₃ : r ≠ .x8) (h₄ : r ≠ .x9) (h₅ : r ≠ .x10) :
        s₄.gpr r = s₀.gpr r := by rw [g₄ r h₄ h₅, g₃ r h₄, g₂ r h₁ h₂ h₃ h₄]
    have hlen : (Spec.Aes.bytesAt s₀.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
    have fW : Frame [⟨C, 16⟩] (writeBytes (Proof.Cmac.zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L)) s₃.mem := by
      rw [m₃, m₂]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    have fB : Frame [⟨C, 16⟩] (Proof.Cmac.zero2 s₀.mem C)
        (writeBytes (Proof.Cmac.zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L)) :=
      writeBytes_frame _ _ _ (by
        rw [hlen]; simpa using Offset.contains_base C (d := 0) (n := L) (k := 16) (by omega) (by decide))
    have f₃ : Frame [⟨C, 16⟩] s₀.mem s₃.mem := (fz.trans fB).trans fW
    have k2 : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 256) 16 =
        Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 256) 16 :=
      Proof.Cmac.bytesAt_frame16 f₃ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dKC 256 16 (by decide)
    have pad : Spec.Aes.bytesAt s₃.mem C 16 =
        Spec.Aes.bytesAt s₀.mem P L ++ [0x80] ++ Spec.Cmac.zeros (16 - L - 1) := by
      have := Proof.Cmac.padded_bytes (Proof.Cmac.zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L)
        (by rw [hlen]; exact hL) (Proof.Cmac.zero2_bytes _ _)
      rw [hlen] at this
      rw [m₃, m₂]; exact this
    refine ⟨by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), hp.x0],
      by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), hp.x2],
      by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), hp.x5],
      gg _ (by decide) (by decide) (by decide) (by decide) (by decide),
      fun r hr => gg r (not_x6 hr) (not_x7 hr) (not_x8 hr) (not_x9 hr) (not_x10 hr),
      by rw [sp₄, sp₃, sp₂], by rw [rd₄, rd₃, rd₂], by rw [wr₄, wr₃, wr₂], ?_, ?_⟩
    · rw [m₄, hC]; exact f₃.trans (Proof.Cmac.xor2Mem_frame _ _ _ _)
    · rw [m₄, hC, Proof.Cmac.xor2Mem_bytes, pad, k2]
      · simp only [mn, Spec.Cmac.lastBlock, hlen, show L ≠ 16 by omega, ite_false]
        exact Proof.Cmac.xor_comm _ _
      · simpa using Offset.disjoint C (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)
      · rw [Offset.add_add]
        exact (dKC 264 8 (by decide)).symm.sub_left (Region.sub_prefix (by decide))

/-! ## Up to the call -/

/-- What the code before the call leaves. -/
structure FMid (s₀ : State) (W St P S : Addr) (L R : Nat) (s : State) : Prop where
  pre : CallPre s W (S + BitVec.ofNat 64 2048) St S R
  blk : Spec.Aes.bytesAt s.mem (S + BitVec.ofNat 64 2048) 16 =
    Spec.Cmac.xor (mn s₀.mem W P L) (Spec.Aes.bytesAt s₀.mem St 16)
  frame : Frame [⟨S + BitVec.ofNat 64 2048, 16⟩, ⟨St, 16⟩, ⟨S + BitVec.ofNat 64 2064, 16⟩] s₀.mem s.mem
  slot19 : s.mem.readW (S + BitVec.ofNat 64 2064) 64 = s₀.gpr .x19
  slot30 : s.mem.readW (S + BitVec.ofNat 64 2072) 64 = s₀.gpr .x30
  x19 : s.gpr .x19 = S
  saved : ∀ r ∈ preserved, r ≠ .x19 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finArgs_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) {s : State}
    (h : BPost s₀ W St P S L s) : WP isa (.block finArgs) s (FMid s₀ W St P S L R) := by
  have sw := hp.scr_wrap
  have tw := hp.st_wrap
  rw [finArgs_eq, WP.block_append_iff]
  have hRegs : s.rd ++ s.wr = [⟨W, 272⟩, ⟨P, L⟩, ⟨St, 16⟩, ⟨S, 2176⟩] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have inC (d : Nat) (hd : d + 8 ≤ 2176) : InRegions s.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [h.wr]; exact hp.inScr (by omega)
  have inSt (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (St + BitVec.ofNat 64 d) 8 := by
    rw [h.wr, hp.wr]; exact in_rw (r := ⟨St, 16⟩) (by simp) (Offset.contains_base _ hd (by omega))
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := xor2_ok s .x5 .x2 .x5 2048 0 2048
    (P := S + BitVec.ofNat 64 2048) (Q := St) (C := S + BitVec.ofNat 64 2048) (by decide) (by decide) (by decide)
    (by rw [h.x5]) (by rw [h.x5, Offset.add_add]) (by rw [h.x2, k0]) (by rw [h.x2])
    (by rw [h.x5]) (by rw [h.x5, Offset.add_add]) ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (wr_in (inC 2048 (by decide))) (by rw [Offset.add_add]; exact wr_in (inC 2056 (by decide)))
    (by simpa using wr_in (inSt 0 (by decide))) (wr_in (inSt 8 (by decide)))
    (inC 2048 (by decide)) (by rw [Offset.add_add]; exact inC 2056 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, m₂, x3₂, x2₂, x4₂, x19₂, g₂, sp₂, rd₂, wr₂⟩ := args_ok s₁ (D := St) (S := S)
    (by rw [g₁ _ (by decide) (by decide), h.x2]) (by rw [g₁ _ (by decide) (by decide), h.x5])
    (by rw [wr₁]; exact inSt 0 (by decide)) (by rw [wr₁]; exact inSt 8 (by decide))
    (by rw [wr₁]; exact inC 2064 (by decide)) (by rw [wr₁]; exact inC 2072 (by decide))
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g (r : Reg) (h₁ : r ≠ .x2) (h₂ : r ≠ .x3) (h₃ : r ≠ .x4) (h₄ : r ≠ .x9) (h₅ : r ≠ .x19) (h₆ : r ≠ .x10) :
      s₂.gpr r = s.gpr r := by
    rw [g₂ r h₁ h₂ h₃ h₄ h₅, g₁ r h₄ h₆]
  have dCSt : (⟨S + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint ⟨St, 16⟩ :=
    hp.st_scr.symm.sub_left (FPre.scrD (by decide))
  have dSlSt : (⟨S + BitVec.ofNat 64 2064, 16⟩ : Region).Disjoint ⟨St, 16⟩ :=
    hp.st_scr.symm.sub_left (FPre.scrD (by decide))
  have dSlC : (⟨S + BitVec.ofNat 64 2064, 16⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 2048, 16⟩ :=
    Offset.disjoint S (by decide) (by omega) (by omega)
  -- The memory: the state zeroed, then the two slots.
  obtain ⟨Z, hZ⟩ : ∃ Z, (s₁.mem.writeW (St + BitVec.ofNat 64 0) (0 : BitVec 64)).writeW (St + BitVec.ofNat 64 8)
      (0 : BitVec 64) = Z := ⟨_, rfl⟩
  have e72 : S + BitVec.ofNat 64 2072 = S + BitVec.ofNat 64 2064 + BitVec.ofNat 64 8 :=
    (Offset.add_add_eq S (a := 2064) (b := 8) (c := 2072) rfl).symm
  have fSl : Frame [⟨S + BitVec.ofNat 64 2064, 16⟩] Z s₂.mem := by
    rw [m₂, hZ, e72]; exact Proof.Cmac.frame_store2 _ _ _
  have fZ : Frame [⟨St, 16⟩] s₁.mem Z := by rw [← hZ]; exact frame_store2' _ _ _
  have stS : Spec.Aes.bytesAt s.mem St 16 = Spec.Aes.bytesAt s₀.mem St 16 :=
    Proof.Cmac.bytesAt_frame16 h.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dCSt.symm
  have hR := hp.rounds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [rd₂, rd₁, h.rd], by rw [wr₂, wr₁, h.wr]⟩
  · exact
    { x0 := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x0]
      x1 := by
        rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x1]
        apply BitVec.eq_of_toNat_eq; simp [hp.x1]; omega
      x2 := x2₂
      x3 := x3₂
      x4 := x4₂
      x5 := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x5]
      rounds := hR
      wc := (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (FPre.scrD (by decide))
      wd := hp.key_st.sub_left (Region.sub_prefix (by decide))
      ws := (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      cd := dCSt
      cs := Offset.disjoint_base _ (by decide) (by omega)
      ds := hp.st_scr.sub_right (Region.sub_prefix (by decide))
      wrap := hp.st_wrap
      reads := by
        rw [rd₂, wr₂, rd₁, wr₁, hRegs]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨⟨W, 272⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 2176⟩, by simp, 2048, rfl, by simp⟩
        · exact ⟨⟨St, 16⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₂, wr₁, h.wr, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨S, 2176⟩, by simp, 2048, rfl, by simp⟩
        · exact ⟨⟨St, 16⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
      zero := by
        rw [Proof.Cmac.bytesAt_frame16 fSl (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact dSlSt.symm), ← hZ, k0,
          Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero, Proof.Cmac.zeros_8_8] }
  · rw [Proof.Cmac.bytesAt_frame16 fSl (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dSlC.symm),
      Proof.Cmac.bytesAt_frame16 fZ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dCSt),
      m₁, Proof.Cmac.xor2Mem_bytes, h.blk, stS]
    · simpa using Offset.disjoint (S + BitVec.ofNat 64 2048) (d := 0) (n := 8) (e := 8) (k := 8) (by decide)
        (by decide) (by decide)
    · exact (dCSt.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  · refine (((h.frame.trans (m₁ ▸ Proof.Cmac.xor2Mem_frame _ _ _ _)).mono (by simp)).trans
      (fZ.mono (by simp))).trans (fSl.mono (by simp))
  · rw [m₂, readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64,
      g₁ _ (by decide) (by decide), h.saved _ (by simp [preserved])]
  · rw [m₂, Mem.readW_writeW_self64, g₁ _ (by decide) (by decide), h.saved _ (by simp [preserved])]
  · exact x19₂
  · intro r hr h19
    have n2 : r ≠ .x2 := by rintro rfl; simp [preserved] at hr
    have n3 : r ≠ .x3 := by rintro rfl; simp [preserved] at hr
    have n4 : r ≠ .x4 := by rintro rfl; simp [preserved] at hr
    rw [g r n2 n3 n4 (not_x9 hr) h19 (not_x10 hr), h.saved r hr]
  · rw [sp₂, sp₁, h.sp]

theorem finPre_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) :
    WP isa finPre s₀ (FMid s₀ W St P S L R) := by
  have h4 : s₀.gpr .x4 = BitVec.ofNat 64 L := by rw [← hp.x4]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨s₁, run₁, ev₁, g₁, sp₁, m₁, rd₁, wr₁⟩ := sub16_ok s₀ h4 hp.len
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := BPost s₀ W St P S L) ?_ fun _ h => finArgs_wp hp h)
  by_cases hL : L = 16
  · exact WP.ite true (by rw [ev₁]; simp [hL]) (fun _ => full_wp hp hL g₁ m₁ sp₁ rd₁ wr₁)
      (fun h => by cases h)
  · exact WP.ite false (by rw [ev₁]; simp [hL]) (fun h => by cases h)
      (fun _ => partial_wp hp (by have := hp.len; omega) g₁ m₁ sp₁ rd₁ wr₁)

theorem restoreF_ok (s : State) {B : Addr} (hb : s.gpr .x19 = B)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2072) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2064) 8) :
    ∃ s', runBlock isa [.ldr .x .x30 .x19 2072, .ldr .x .x19 .x19 2064] s = some s' ∧
      s'.gpr .x30 = s.mem.readW (B + BitVec.ofNat 64 2072) 64 ∧
      s'.gpr .x19 = s.mem.readW (B + BitVec.ofNat 64 2064) 64 ∧
      (∀ r, r ≠ .x19 → r ≠ .x30 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, addr,
      State.load, Size.bytes, Size.bits, gpr_write, mem_write, rd_write, wr_write, ite_true, ite_false,
      Option.bind_some, Option.map_some, hb, r₁, r₂]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, Mem.readW], by simp [gpr_write, Mem.readW],
    fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl⟩

theorem finalize_wp (v : Ctr32Impl) {s₀ : State} (h0 : finalizeAArch64.pre s₀) :
    WP isa (finalize v.callee) s₀ fun s' => GprAbi s₀ s' ∧ finalizeAArch64.post s₀ s' := by
  have hp := FPre.of h0
  generalize s₀.gpr .x0 = W at hp
  generalize s₀.gpr .x2 = St at hp
  generalize s₀.gpr .x3 = P at hp
  generalize s₀.gpr .x5 = S at hp
  generalize (s₀.gpr .x4).toNat = L at hp
  generalize (s₀.gpr .x1).toNat = R at hp
  have hR := hp.rounds
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have sw := hp.scr_wrap
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ctr_call v h₁.pre) fun s₂ h₂ => ?_)
  have x19₂ : s₂.gpr .x19 = S := by rw [h₂.saved .x19 (by simp [preserved]) (by decide), h₁.x19]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]
  obtain ⟨s₃, run₃, x30₃, x19₃, g₃, sp₃, mem₃⟩ := restoreF_ok s₂ x19₂
    (by rw [rdwr₂]; exact wr_in (hp.inScr (d := 2072) (n := 8) (by decide)))
    (by rw [rdwr₂]; exact wr_in (hp.inScr (d := 2064) (n := 8) (by decide)))
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  -- The slots, which the call does not write.
  have slots (d : Nat) (h₁' : 2064 ≤ d) (h₂' : d + 8 ≤ 2080) :
      s₂.mem.readW (S + BitVec.ofNat 64 d) 64 = s₁.mem.readW (S + BitVec.ofNat 64 d) 64 := by
    refine h₂.frame.readW (r := ⟨S + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint S (by omega) (by omega) (by omega)
    · exact (hp.st_scr.symm.sub_left (FPre.scrD (by omega)))
    · exact Offset.disjoint_base _ (by omega) (by omega)
  have big : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s₀.mem s₂.mem := by
    refine (h₁.frame.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨S, 2176⟩, by simp, FPre.scrD (by decide)⟩
      · exact ⟨⟨St, 16⟩, by simp, fun _ h => h⟩
      · exact ⟨⟨S, 2176⟩, by simp, FPre.scrD (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨S, 2176⟩, by simp, FPre.scrD (by decide)⟩
      · exact ⟨⟨St, 16⟩, by simp, fun _ h => h⟩
      · exact ⟨⟨S, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
  have sch : Spec.Aes.bytesAt s₁.mem W (16 * (R + 1)) = Spec.Aes.bytesAt s₀.mem W (16 * (R + 1)) :=
    Proof.Cmac.bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega))).sub_right (FPre.scrD (by decide))
      · exact hp.key_st.sub_left (Region.sub_prefix (by omega))
      · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega))).sub_right (FPre.scrD (by decide))) (by omega)
  refine ⟨⟨fun r hr => ?_, by rw [sp₃, h₂.sp, h₁.sp]⟩, ?_⟩
  · by_cases h19 : r = .x19
    · subst h19; rw [x19₃, slots 2064 (by decide) (by decide), h₁.slot19]
    by_cases h30 : r = .x30
    · subst h30; rw [x30₃, slots 2072 (by decide) (by decide), h₁.slot30]
    rw [g₃ r h19 h30, h₂.saved r hr h30, h₁.saved r hr h19]
  · intro hk msg hm hne hst
    rw [hp.x0, hp.x1] at hk hst ⊢
    rw [hp.x2] at hst ⊢
    rw [hp.x4] at hne
    rw [hp.x3, hp.x4]
    obtain ⟨e1, e2⟩ := Proof.Cmac.k1k2 (Proof.Cmac.subkeys_aes_length _ _) hk
    rw [mem₃, h₂.out, sch, h₁.blk, mn, e1, e2, hst,
      Proof.Cmac.macFull_split _ hm (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
        (by rw [Proof.Cmac.bytesAt_length]; exact hne), Proof.Cmac.xor_comm]

end VG.Proof.CmacAes.AArch64
