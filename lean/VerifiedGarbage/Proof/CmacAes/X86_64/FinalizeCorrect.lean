import VerifiedGarbage.Proof.CmacAes.X86_64.Finalize

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_finalize` is correct

Untrusted: everything here is checked by Lean. Before the call, the
counter block (at `S + 2048`) holds `Mₙ ⊕ C`, for the last block `Mₙ` of
§6.2 step 4 and the chaining value `C` at `state`, and the state is
zeroed; the call leaves `CIPH_K(C ⊕ Mₙ)` there, the MAC (`macFull_split`).
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The precondition, by name: the key (schedule and subkeys) `W`, the state
`St`, the last bytes `P` (`L` of them), the scratch buffer `S` and the
rounds `R`. -/
structure FPre (s₀ : State) (W St P S : Addr) (L R : Nat) : Prop where
  rdi : s₀.gpr .rdi = W
  rdx : s₀.gpr .rdx = St
  rcx : s₀.gpr .rcx = P
  r8 : (s₀.gpr .r8).toNat = L
  r9 : s₀.gpr .r9 = S
  rsi : (s₀.gpr .rsi).toNat = R
  rd : s₀.rd = [⟨W, 272⟩, ⟨P, L⟩]
  wr : s₀.wr = [⟨St, 16⟩, ⟨S, 2176⟩]
  key_st : (⟨W, 272⟩ : Region).Disjoint ⟨St, 16⟩
  key_scr : (⟨W, 272⟩ : Region).Disjoint ⟨S, 2176⟩
  last_st : (⟨P, L⟩ : Region).Disjoint ⟨St, 16⟩
  last_scr : (⟨P, L⟩ : Region).Disjoint ⟨S, 2176⟩
  st_scr : (⟨St, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 16⟩
  ret_scr : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 2176⟩
  stk_key : (below (s₀.gpr .rsp) 8).Disjoint ⟨W, 272⟩
  stk_last : (below (s₀.gpr .rsp) 8).Disjoint ⟨P, L⟩
  stk_st : (below (s₀.gpr .rsp) 8).Disjoint ⟨St, 16⟩
  stk_scr : (below (s₀.gpr .rsp) 8).Disjoint ⟨S, 2176⟩
  key_wrap : W.toNat + 272 ≤ 2 ^ 64
  st_wrap : St.toNat + 16 ≤ 2 ^ 64
  last_wrap : P.toNat + L ≤ 2 ^ 64
  scr_wrap : S.toNat + 2176 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16

theorem FPre.of {s₀ : State} (h : finalizeX86_64.pre s₀) :
    FPre s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (s₀.gpr .rsi).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes in `m`. -/
abbrev mn (m : Mem) (W P : Addr) (L : Nat) : List Byte :=
  Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 240) 16)
    (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 256) 16) (Spec.Aes.bytesAt m P L)

/-- What the branch on the length leaves: `Mₙ` in the counter block. -/
structure BPost (s₀ : State) (W St P S : Addr) (L : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = W
  rdx : s.gpr .rdx = St
  r9 : s.gpr .r9 = S
  rsi : s.gpr .rsi = s₀.gpr .rsi
  saved : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
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

theorem full_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) (hL : L = 16)
    {s : State} (hg : s.gpr = s₀.gpr) (hm : s.mem = s₀.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block full) s (BPost s₀ W St P S L) := by
  subst hL
  have e : full = [.mov .rax (.mem (at_ .rcx 0)), .alu .xor .rax (.mem (at_ .rdi 240)), .store (at_ .r9 2048) .rax,
      .mov .rax (.mem (at_ .rcx (0 + 8))), .alu .xor .rax (.mem (at_ .rdi (240 + 8))),
      .store (at_ .r9 (2048 + 8)) .rax] := rfl
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  obtain ⟨s', run, mem, g, rd, wr⟩ := xor2_ok s .rcx .rdi .r9 0 240 2048
    (P := P) (Q := W + BitVec.ofNat 64 240) (C := S + BitVec.ofNat 64 2048)
    (by rw [hg, hp.rcx, k0]) (by rw [hg, hp.rcx])
    (by rw [hg, hp.rdi]) (by rw [hg, hp.rdi, Offset.add_add])
    (by rw [hg, hp.r9]) (by rw [hg, hp.r9, Offset.add_add])
    ⟨by decide, by decide, by decide⟩
    (by rw [hrd, hwr]; simpa using hp.inLast (d := 0) (n := 8) (by decide))
    (by rw [hrd, hwr]; exact hp.inLast (d := 8) (n := 8) (by decide))
    (by rw [hrd, hwr]; exact hp.inKey (d := 240) (n := 8) (by decide))
    (by rw [hrd, hwr, Offset.add_add]; exact hp.inKey (d := 248) (n := 8) (by decide))
    (by rw [hwr]; exact hp.inScr (d := 2048) (n := 8) (by decide))
    (by rw [hwr, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide))
  rw [e]
  refine WP.of_runBlock ⟨s', run, ?_⟩
  have gg (r : Reg) (hr : r ≠ .rax) : s'.gpr r = s₀.gpr r := by rw [g r hr, hg]
  refine ⟨by rw [gg _ (by decide), hp.rdi], by rw [gg _ (by decide), hp.rdx], by rw [gg _ (by decide), hp.r9],
    gg _ (by decide), fun r hr => gg r (by rintro rfl; simp [calleeSaved] at hr), by rw [rd, hrd],
    by rw [wr, hwr], by rw [mem, hm]; exact xor2Mem_frame _ _ _ _, ?_⟩
  rw [mem, hm, xor2Mem_bytes]
  · simp only [mn, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, ite_true]
    exact xor_comm _ _
  · exact (hp.last_scr.symm.sub_left (FPre.scrD (d := 2048) (n := 8) (by decide))).sub_right
      (Offset.sub_base P (d := 8) (n := 8) (k := 16) (by decide))
  · rw [Offset.add_add]
    exact (hp.key_scr.symm.sub_left (FPre.scrD (d := 2048) (n := 8) (by decide))).sub_right
      (Offset.sub_base W (d := 248) (n := 8) (k := 272) (by decide))

open VG.WriteBytes in
theorem partial_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) (hL : L < 16)
    {s : State} (hg : s.gpr = s₀.gpr) (hm : s.mem = s₀.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa partialBlock s (BPost s₀ W St P S L) := by
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  have h8 : s.gpr .r8 = BitVec.ofNat 64 L := by
    rw [hg, ← hp.r8]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨C, hC⟩ : ∃ C, S + BitVec.ofNat 64 2048 = C := ⟨_, rfl⟩
  have hc : s.gpr .r9 + BitVec.ofNat 64 2048 = C := by rw [hg, hp.r9, hC]
  have hc8 : s.gpr .r9 + BitVec.ofNat 64 2056 = C + BitVec.ofNat 64 8 := by rw [hg, hp.r9, ← hC, Offset.add_add]
  have dPC : (⟨P, L⟩ : Region).Disjoint ⟨C, 16⟩ := by rw [← hC]; exact hp.last_scr.sub_right (FPre.scrD (by decide))
  have dKC (d n : Nat) (h : d + n ≤ 272) : (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨C, 16⟩ := by
    rw [← hC]; exact (hp.key_scr.sub_left (Offset.sub_base _ h)).sub_right (FPre.scrD (by decide))
  -- Zero the block.
  obtain ⟨s₁, run₁, zf₁, mem₁, g₁, rd₁, wr₁⟩ := zero_ok s hc hc8 h8 (by omega)
    (by rw [hwr, ← hC]; exact hp.inScr (d := 2048) (n := 8) (by decide))
    (by rw [hwr, ← hC, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have zf : s₁.mem = zero2 s₀.mem C := by rw [mem₁, hm]
  have fz : Frame [⟨C, 16⟩] s₀.mem (zero2 s₀.mem C) := frame_store2 _ _ _
  have lastZ : Spec.Aes.bytesAt (zero2 s₀.mem C) P L = Spec.Aes.bytesAt s₀.mem P L :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dPC) (by omega)
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.mem = writeBytes (zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s₂.gpr r = s₀.gpr r) ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr) ?_ fun s₂ h₂ => ?_)
  · by_cases hL0 : L = 0
    · subst hL0
      refine WP.ite true (by show s₁.zf = _; rw [zf₁]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [zf]; simp [Spec.Aes.bytesAt, writeBytes_nil], fun r h₁ _ => by rw [g₁ r h₁, hg],
        by rw [rd₁, hrd], by rw [wr₁, hwr]⟩
    · refine WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (copy_ok s₁ (by omega) hL (by rw [g₁ _ (by decide), hg, hp.rcx])
        (by rw [g₁ _ (by decide)]; exact hc) (by rw [g₁ _ (by decide)]; exact h8)
        (fun i hi => by rw [rd₁, wr₁, hrd, hwr]; exact hp.inLast (d := i) (n := 1) (by omega))
        (fun i hi => by
          rw [wr₁, hwr, ← hC, Offset.add_add]; exact hp.inScr (d := 2048 + i) (n := 1) (by omega)) dPC) ?_
      rintro s₂ ⟨m₂, g₂, rd₂, wr₂⟩
      refine ⟨by rw [m₂, zf, lastZ], fun r h₁ h₂ => by rw [g₂ r h₁ h₂, g₁ r h₁, hg], by rw [rd₂, rd₁, hrd],
        by rw [wr₂, wr₁, hwr]⟩
  · obtain ⟨m₂, g₂, rd₂, wr₂⟩ := h₂
    have e : padK2 = [.mov32 .rax (.imm 0x80), .store8 { base := .r9, index := some .r8, disp := cOff } .rax] ++
        [.mov .rax (.mem (at_ .r9 2048)), .alu .xor .rax (.mem (at_ .rdi 256)), .store (at_ .r9 2048) .rax,
          .mov .rax (.mem (at_ .r9 (2048 + 8))), .alu .xor .rax (.mem (at_ .rdi (256 + 8))),
          .store (at_ .r9 (2048 + 8)) .rax] := rfl
    rw [e, WP.block_append_iff]
    have r9₂ : s₂.gpr .r9 = S := by rw [g₂ _ (by decide) (by decide), hp.r9]
    have r8₂ : s₂.gpr .r8 = BitVec.ofNat 64 L := by rw [g₂ _ (by decide) (by decide), ← hg]; exact h8
    obtain ⟨s₃, run₃, m₃, g₃, rd₃, wr₃⟩ := pad_ok s₂ (C := C) (L := L)
      (by rw [r9₂, r8₂, BitVec.mul_one, offset_nat, ← hC, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 L),
        ← BitVec.add_assoc]; rfl)
      (by rw [wr₂, ← hC, Offset.add_add]; exact hp.inScr (d := 2048 + L) (n := 1) (by omega))
    refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
    have r9₃ : s₃.gpr .r9 = S := by rw [g₃ _ (by decide), r9₂]
    have rdi₃ : s₃.gpr .rdi = W := by rw [g₃ _ (by decide), g₂ _ (by decide) (by decide), hp.rdi]
    obtain ⟨s₄, run₄, m₄, g₄, rd₄, wr₄⟩ := xor2_ok s₃ .r9 .rdi .r9 2048 256 2048
      (P := C) (Q := W + BitVec.ofNat 64 256) (C := C)
      (by rw [r9₃, hC]) (by rw [r9₃, ← hC, Offset.add_add]) (by rw [rdi₃]) (by rw [rdi₃, Offset.add_add])
      (by rw [r9₃, hC]) (by rw [r9₃, ← hC, Offset.add_add]) ⟨by decide, by decide, by decide⟩
      (by rw [rd₃, wr₃, rd₂, wr₂, ← hC]; exact wr_in (hp.inScr (d := 2048) (n := 8) (by decide)))
      (by rw [rd₃, wr₃, rd₂, wr₂, ← hC, Offset.add_add]; exact wr_in (hp.inScr (d := 2056) (n := 8) (by decide)))
      (by rw [rd₃, wr₃, rd₂, wr₂]; exact hp.inKey (d := 256) (n := 8) (by decide))
      (by rw [rd₃, wr₃, rd₂, wr₂, Offset.add_add]; exact hp.inKey (d := 264) (n := 8) (by decide))
      (by rw [wr₃, wr₂, ← hC]; exact hp.inScr (d := 2048) (n := 8) (by decide))
      (by rw [wr₃, wr₂, ← hC, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide))
    refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
    have gg (r : Reg) (h₁ : r ≠ .rax) (h₂ : r ≠ .r10) : s₄.gpr r = s₀.gpr r := by rw [g₄ r h₁, g₃ r h₁, g₂ r h₁ h₂]
    have hlen : (Spec.Aes.bytesAt s₀.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
    have fW : Frame [⟨C, 16⟩] (writeBytes (zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L)) s₃.mem := by
      rw [m₃, m₂]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    have fB : Frame [⟨C, 16⟩] (zero2 s₀.mem C) (writeBytes (zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L)) :=
      writeBytes_frame _ _ _ (by
        rw [hlen]; simpa using Offset.contains_base C (d := 0) (n := L) (k := 16) (by omega) (by decide))
    have f₃ : Frame [⟨C, 16⟩] s₀.mem s₃.mem := (fz.trans fB).trans fW
    have k2 : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 256) 16 = Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 256) 16 :=
      bytesAt_frame' f₃ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKC 256 16 (by decide)
    have pad : Spec.Aes.bytesAt s₃.mem C 16 =
        Spec.Aes.bytesAt s₀.mem P L ++ [0x80] ++ Spec.Cmac.zeros (16 - L - 1) := by
      have := padded_bytes (zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L) (by rw [hlen]; exact hL) (zero2_bytes _ _)
      rw [hlen] at this
      rw [m₃, m₂]; exact this
    refine ⟨by rw [gg _ (by decide) (by decide), hp.rdi], by rw [gg _ (by decide) (by decide), hp.rdx],
      by rw [gg _ (by decide) (by decide), hp.r9], gg _ (by decide) (by decide),
      fun r hr => gg r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr),
      by rw [rd₄, rd₃, rd₂], by rw [wr₄, wr₃, wr₂], ?_, ?_⟩
    · rw [m₄, hC]; exact f₃.trans (xor2Mem_frame _ _ _ _)
    · rw [m₄, hC, xor2Mem_bytes, pad, k2]
      · simp only [mn, Spec.Cmac.lastBlock, hlen, show L ≠ 16 by omega, ite_false]
        exact xor_comm _ _
      · simpa using Offset.disjoint C (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)
      · rw [Offset.add_add]
        exact (dKC 264 8 (by decide)).symm.sub_left (Region.sub_prefix (by decide))

/-! ## Up to the call -/

/-- What the code before the call leaves. -/
structure FMid (s₀ : State) (W St P S : Addr) (L R : Nat) (s : State) : Prop where
  pre : CallPre s W (S + BitVec.ofNat 64 2048) St S R
  blk : Spec.Aes.bytesAt s.mem (S + BitVec.ofNat 64 2048) 16 =
    Spec.Cmac.xor (mn s₀.mem W P L) (Spec.Aes.bytesAt s₀.mem St 16)
  frame : Frame [⟨S + BitVec.ofNat 64 2048, 16⟩, ⟨St, 16⟩] s₀.mem s.mem
  saved : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r

theorem finArgs_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) {s : State}
    (h : BPost s₀ W St P S L s) : WP isa (.block finArgs) s (FMid s₀ W St P S L R) := by
  have sw := hp.scr_wrap
  have tw := hp.st_wrap
  have e : finArgs = [.mov .rax (.mem (at_ .r9 2048)), .alu .xor .rax (.mem (at_ .rdx 0)), .store (at_ .r9 2048) .rax,
        .mov .rax (.mem (at_ .r9 (2048 + 8))), .alu .xor .rax (.mem (at_ .rdx (0 + 8))),
        .store (at_ .r9 (2048 + 8)) .rax] ++
      [.mov32 .rax (.imm 0), .store (at_ .rdx 0) .rax, .store (at_ .rdx 8) .rax,
        .mov .rcx (.reg .rdx), .mov .rdx (.reg .r9), .alu .add .rdx (.imm (BitVec.ofNat 32 cOff)),
        .mov32 .r8 (.imm 1)] := rfl
  rw [e, WP.block_append_iff]
  have hRegs : s.rd ++ s.wr = [⟨W, 272⟩, ⟨P, L⟩, ⟨St, 16⟩, ⟨S, 2176⟩] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have inC (d : Nat) (hd : d + 8 ≤ 2176) : InRegions s.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [h.wr]; exact hp.inScr (by omega)
  have inSt (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (St + BitVec.ofNat 64 d) 8 := by
    rw [h.wr, hp.wr]; exact in_rw (r := ⟨St, 16⟩) (by simp) (Offset.contains_base _ hd (by omega))
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := xor2_ok s .r9 .rdx .r9 2048 0 2048
    (P := S + BitVec.ofNat 64 2048) (Q := St) (C := S + BitVec.ofNat 64 2048)
    (by rw [h.r9]) (by rw [h.r9, Offset.add_add]) (by rw [h.rdx, k0]) (by rw [h.rdx])
    (by rw [h.r9]) (by rw [h.r9, Offset.add_add]) ⟨by decide, by decide, by decide⟩
    (wr_in (inC 2048 (by decide))) (by rw [Offset.add_add]; exact wr_in (inC 2056 (by decide)))
    (by simpa using wr_in (inSt 0 (by decide))) (wr_in (inSt 8 (by decide)))
    (inC 2048 (by decide)) (by rw [Offset.add_add]; exact inC 2056 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, m₂, rcx₂, rdx₂, r8₂, g₂, rd₂, wr₂⟩ := args_ok s₁ (D := St)
    (by rw [g₁ _ (by decide), h.rdx]) (by rw [wr₁]; exact inSt 0 (by decide)) (by rw [wr₁]; exact inSt 8 (by decide))
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g (r : Reg) (h₁ : r ≠ .rax) (h₂ : r ≠ .rcx) (h₃ : r ≠ .rdx) (h₄ : r ≠ .r8) : s₂.gpr r = s.gpr r := by
    rw [g₂ r h₁ h₂ h₃ h₄, g₁ r h₁]
  have rsp₂ : s₂.gpr .rsp = s₀.gpr .rsp := by
    rw [g _ (by decide) (by decide) (by decide) (by decide), h.saved _ (by simp [calleeSaved])]
  have dCSt : (⟨S + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint ⟨St, 16⟩ :=
    hp.st_scr.symm.sub_left (FPre.scrD (by decide))
  have fA : Frame [⟨St, 16⟩] s₁.mem s₂.mem := by
    rw [m₂, k0]; exact frame_store2 _ _ _
  have stS : Spec.Aes.bytesAt s.mem St 16 = Spec.Aes.bytesAt s₀.mem St 16 :=
    bytesAt_frame' h.frame fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dCSt.symm
  have hR := hp.rounds
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
    { rdi := by rw [g _ (by decide) (by decide) (by decide) (by decide), h.rdi]
      rsi := by
        rw [g _ (by decide) (by decide) (by decide) (by decide), h.rsi]
        apply BitVec.eq_of_toNat_eq; simp [hp.rsi]; omega
      rdx := by rw [rdx₂, g₁ _ (by decide), h.r9]
      rcx := rcx₂
      r8 := r8₂
      r9 := by rw [g _ (by decide) (by decide) (by decide) (by decide), h.r9]
      rounds := hR
      wc := (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (FPre.scrD (by decide))
      wd := hp.key_st.sub_left (Region.sub_prefix (by decide))
      ws := (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      cd := dCSt
      cs := Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)
      ds := hp.st_scr.sub_right (Region.sub_prefix (by decide))
      stkW := by rw [rsp₂]; exact hp.stk_key.sub_right (Region.sub_prefix (by decide))
      stkC := by rw [rsp₂]; exact hp.stk_scr.sub_right (FPre.scrD (by decide))
      stkD := by rw [rsp₂]; exact hp.stk_st
      stkS := by rw [rsp₂]; exact hp.stk_scr.sub_right (Region.sub_prefix (by decide))
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
      zero := by rw [m₂, k0, Proof.Cmac.bytesAt_store2, zero_le8, zeros_8_8] }
  · rw [bytesAt_frame' fA (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dCSt), m₁,
      xor2Mem_bytes, h.blk, stS]
    · simpa using Offset.disjoint (S + BitVec.ofNat 64 2048) (d := 0) (n := 8) (e := 8) (k := 8) (by decide)
        (by decide) (by decide)
    · exact (dCSt.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  · refine (h.frame.trans (m₁ ▸ xor2Mem_frame _ _ _ _)).mono (by simp) |>.trans (fA.mono (by simp))
  · intro r hr
    rw [g r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr), h.saved r hr]

theorem finPre_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) :
    WP isa finPre s₀ (FMid s₀ W St P S L R) := by
  have h8 : s₀.gpr .r8 = BitVec.ofNat 64 L := by rw [← hp.r8]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨s₁, run₁, zf₁, g₁, m₁, rd₁, wr₁⟩ := cmp16_ok s₀ h8 hp.len
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := BPost s₀ W St P S L) ?_ fun _ h => finArgs_wp hp h)
  by_cases hL : L = 16
  · exact WP.ite true (by show s₁.zf = _; rw [zf₁]; simp [hL]) (fun _ => full_wp hp hL g₁ m₁ rd₁ wr₁)
      (fun h => by cases h)
  · exact WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [hL]) (fun h => by cases h)
      (fun _ => partial_wp hp (by have := hp.len; omega) g₁ m₁ rd₁ wr₁)

theorem k1k2 {m : Mem} {W : Addr} {k1 k2 : List Byte} (h1 : k1.length = 16)
    (h : Spec.Aes.bytesAt m (W + BitVec.ofNat 64 240) 32 = k1 ++ k2) :
    Spec.Aes.bytesAt m (W + BitVec.ofNat 64 240) 16 = k1 ∧ Spec.Aes.bytesAt m (W + BitVec.ofNat 64 256) 16 = k2 := by
  rw [bytesAt_32, Offset.add_add] at h
  exact List.append_inj h (by rw [Proof.Cmac.bytesAt_length, h1])

theorem finalize_wp (v : Ctr32Impl) {s₀ : State} (h0 : finalizeX86_64.pre s₀) :
    WP isa (finalize v.callee) s₀ fun s' => gprPreserved s₀ s' ∧ finalizeX86_64.post s₀ s' := by
  have hp := FPre.of h0
  generalize s₀.gpr .rdi = W at hp
  generalize s₀.gpr .rdx = St at hp
  generalize s₀.gpr .rcx = P at hp
  generalize s₀.gpr .r9 = S at hp
  generalize (s₀.gpr .r8).toNat = L at hp
  generalize (s₀.gpr .rsi).toNat = R at hp
  have hR := hp.rounds
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.mono (ctr_call v h₁.pre) fun s₂ h₂ => ?_
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := h₁.saved _ (by simp [calleeSaved])
  -- The key and the frame.
  have big : Frame [⟨St, 16⟩, ⟨S, 2176⟩, below (s₀.gpr .rsp) 8] s₀.mem s₂.mem := by
    refine (h₁.frame.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨S, 2176⟩, by simp, FPre.scrD (by decide)⟩
      · exact ⟨⟨St, 16⟩, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨S, 2176⟩, by simp, FPre.scrD (by decide)⟩
      · exact ⟨⟨St, 16⟩, by simp, fun _ h => h⟩
      · exact ⟨⟨S, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨below (s₀.gpr .rsp) 8, by simp, by rw [rsp₁]; exact fun _ h => h⟩
  have sch : Spec.Aes.bytesAt s₁.mem W (16 * (R + 1)) = Spec.Aes.bytesAt s₀.mem W (16 * (R + 1)) :=
    bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega))).sub_right (FPre.scrD (by decide))
      · exact hp.key_st.sub_left (Region.sub_prefix (by omega))) (by omega)
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, h₁.saved r hr], ?_⟩, ?_⟩
  · refine big.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_scr
    · exact Offset.base_disjoint_below _ (by decide)
  · intro hk msg hm hne hst
    rw [hp.rdi, hp.rsi] at hk hst ⊢
    rw [hp.rdx] at hst ⊢
    rw [hp.r8] at hne
    rw [hp.rcx, hp.r8]
    obtain ⟨e1, e2⟩ := k1k2 (Proof.Cmac.subkeys_aes_length _ _) hk
    rw [h₂.out, sch, h₁.blk, mn, e1, e2, hst,
      Proof.Cmac.macFull_split _ hm (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
        (by rw [Proof.Cmac.bytesAt_length]; exact hne), xor_comm]

end VG.Proof.CmacAes.X86_64
