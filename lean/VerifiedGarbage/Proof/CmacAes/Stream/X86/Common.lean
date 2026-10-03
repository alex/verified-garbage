import VerifiedGarbage.Proof.CmacAes.Stream.X86.Call
import VerifiedGarbage.Proof.CmacAes.X86.Finalize
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86.ArgTaint
import VerifiedGarbage.Proof.Framework.X86.Spill

/-!
# Streaming AES-CMAC on x86: arithmetic, copies and saved registers

The number of bytes held back, as the code computes it from `count`'s two
words (`held_ok`); the copy of `ecx` bytes from `esi` to `edi` (`copy_wp`);
and the registers saved in the scratch buffer (`slot_read`, `restore_wp`).
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

open VG.WriteBytes

variable (v : Proof.Aes.X86.Ctr32Impl)
open VG.Impl.CmacAes.X86 (at_ argOp)
open VG.Proof.MdStream.X86 (Upd Mupd Fupd WP.cons wp_mov wp_movi wp_movm wp_store wp_addi wp_add wp_subi wp_sub
  wp_andi wp_cmp wp_test wp_movzx8 wp_store8 eval_e eval_ne eval_b ofNat_beq_zero sub_ofNat)
open VG.Proof.CmacAes.X86 (wp_arg ea_at' byte_rt32 addr_at add0')
open VG.Proof.Cmac.Stream (held held_le held_pos held_zero)

/-! ## Arithmetic -/

theorem toNat_count (hi lo : BitVec 32) : (hi ++ lo).toNat = hi.toNat * 2 ^ 32 + lo.toNat := by
  rw [BitVec.toNat_append, Nat.shiftLeft_eq, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt lo.isLt]

theorem zero_iff (x : BitVec 32) : x = 0#32 ↔ x.toNat = 0 :=
  ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩

/-- `or` of the two words of `count` is 0 exactly when `count` is. -/
theorem count_zero (hi lo : BitVec 32) : (hi ||| lo == 0) = decide ((hi ++ lo).toNat = 0) := by
  rw [toNat_count]
  have e : hi ||| lo = 0#32 ↔ hi.toNat * 2 ^ 32 + lo.toNat = 0 := by
    rw [BitVec.or_eq_zero_iff, zero_iff hi, zero_iff lo]; omega
  by_cases h : hi.toNat * 2 ^ 32 + lo.toNat = 0
  · simp only [h, decide_true, beq_iff_eq]; exact e.mpr h
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]; exact fun h' => h (e.mp h')

theorem and15 (x : BitVec 32) : (x &&& 15).toNat = x.toNat % 16 := by
  rw [BitVec.toNat_and, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The number of bytes held back for a nonzero `count`, from its low word,
as `sub 1; and 15; add 1` computes it. -/
theorem held_lo {hi lo : BitVec 32} (h : (hi ++ lo).toNat ≠ 0) :
    ((lo - 1) &&& 15) + 1 = BitVec.ofNat 32 (held (hi ++ lo).toNat) := by
  rw [held_pos (by omega)]
  rw [toNat_count] at h ⊢
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, and15, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
  have := lo.isLt
  omega

/-- For `count` 0, its low word is 0. -/
theorem held_lo0 {hi lo : BitVec 32} (h : (hi ++ lo).toNat = 0) : lo = BitVec.ofNat 32 (held (hi ++ lo).toNat) := by
  rw [h, held_zero]
  rw [toNat_count] at h
  exact (zero_iff lo).mpr (by omega)

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## One instruction at a time -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `or d, r`, with ZF. -/
theorem wp_orz {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d ||| s.gpr r) → s'.zf = some (s.gpr d ||| s.gpr r == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (MdStream.X86.Upd.flags _ _ _ _ _ _) rfl)

/-- `shr d, n`, as a division by `2 ^ n`. -/
theorem wp_shr' {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', Upd s s' d (s.gpr d >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q :=
  MdStream.X86.wp_shr hn k

end

/-! ## The bytes held back -/

/-- `count0 r` then `held r` leave the bytes held back for `count` in `r`,
changing only `r`, `ecx` and the flags. -/
theorem held_ok {r : Reg} (hr : r ≠ .ecx) (hr' : r ≠ .esp) {s₀ s : State} {Q : State → Prop}
    (hesp : s.gpr .esp = s₀.gpr .esp)
    (h2 : InRegions (s.rd ++ s.wr) (argAddr s₀ 2) 4) (h3 : InRegions (s.rd ++ s.wr) (argAddr s₀ 3) 4)
    (v2 : s.mem.readW (argAddr s₀ 2) 32 = arg s₀ 2) (v3 : s.mem.readW (argAddr s₀ 3) 32 = arg s₀ 3)
    (k : ∀ s', s'.gpr r = BitVec.ofNat 32 (held (countX86 s₀).toNat) →
      (∀ q, q ≠ r → q ≠ .ecx → s'.gpr q = s.gpr q) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (countHeld r) s Q := by
  refine WP.seq (wp_arg (s₀ := s₀) hesp h2 v2 fun s₁ u₁ => ?_)
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (Ne.symm hr'), hesp]) (by rw [u₁.rd, u₁.wr]; exact h3)
    (by rw [u₁.mem]; exact v3) fun s₂ u₂ => wp_orz fun s₃ u₃ z₃ => WP.block_nil ?_
  have e₃ : s₃.gpr r = arg s₀ 2 := by rw [u₃.other _ hr, u₂.other _ hr, u₁.gpr]
  have z : s₃.zf = some (decide ((countX86 s₀).toNat = 0)) := by
    rw [z₃, u₂.gpr, u₂.other _ hr, u₁.gpr, countX86, count_zero]
  have g₃ : ∀ q, q ≠ r → q ≠ .ecx → s₃.gpr q = s.gpr q := fun q a b => by
    rw [u₃.other _ b, u₂.other _ b, u₁.other _ a]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have ev : isa.eval .e s₃ = some (decide ((countX86 s₀).toNat = 0)) := by
    show VG.X86.eval .e s₃ = _; rw [eval_e, z]
  by_cases h0 : (countX86 s₀).toNat = 0
  · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact k s₃ (by rw [e₃]; exact held_lo0 h0) g₃ m₃ rd₃ wr₃
  · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
    refine wp_subi fun s₄ u₄ _ => wp_andi fun s₅ u₅ => wp_addi fun s₆ u₆ => WP.block_nil ?_
    refine k s₆ ?_ (fun q a b => by rw [u₆.other _ a, u₅.other _ a, u₄.other _ a, g₃ q a b])
      (by rw [u₆.mem, u₅.mem, u₄.mem, m₃]) (by rw [u₆.rd, u₅.rd, u₄.rd, rd₃]) (by rw [u₆.wr, u₅.wr, u₄.wr, wr₃])
    rw [u₆.gpr, u₅.gpr, u₄.gpr, e₃]
    exact held_lo h0

/-! ## Copying bytes -/

/-- The copy loop, for `L` bytes (not 0). -/
theorem copyLoop_wp {s : State} {p c : BitVec 32} {L : Nat} (hL₀ : 0 < L) (hL : L < 2 ^ 32)
    (hsi : s.gpr .esi = p) (hdi : s.gpr .edi = c) (hcx : s.gpr .ecx = BitVec.ofNat 32 L)
    (fp : p.toNat + L ≤ 2 ^ 32) (fc : c.toNat + L ≤ 2 ^ 32)
    (hr : Covers [⟨p.setWidth 64, L⟩] (s.rd ++ s.wr)) (hw : Covers [⟨c.setWidth 64, L⟩] s.wr)
    (hd : (⟨p.setWidth 64, L⟩ : Region).Disjoint ⟨c.setWidth 64, L⟩) :
    WP isa Impl.CmacAes.X86.copy s fun s' =>
      s'.mem = writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) L) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block [.movzx8 .eax (at_ .esi 0), .store8 (at_ .edi 0) .al,
      .alu .add .esi (.imm 1), .alu .add .edi (.imm 1), .alu .sub .ecx (.imm 1)]) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .esi = p + BitVec.ofNat 32 i ∧
      t.gpr .edi = c + BitVec.ofNat 32 i ∧ t.gpr .ecx = BitVec.ofNat 32 (L - i) ∧
      t.mem = writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) i) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [hsi, add0'], by rw [hdi, add0'], by rw [hcx, Nat.sub_zero],
      by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, xsi, xdi, xcx, mem, g, rd, wr⟩
  refine wp_movzx8 (a := p.setWidth 64 + BitVec.ofNat 64 i) (by rw [ea_at', xsi]; exact addr_at (by omega))
    (by rw [rd, wr]; exact hr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₁ u₁ => ?_
  refine wp_store8 (a := c.setWidth 64 + BitVec.ofNat 64 i)
    (by rw [ea_at', u₁.other _ (by decide), xdi]; exact addr_at (by omega))
    (by rw [u₁.wr, wr]; exact hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₂ v₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_addi fun t₄ u₄ => wp_subi fun t₅ u₅ z₅ => WP.block_nil ?_
  have hlen : (Spec.Aes.bytesAt s.mem (p.setWidth 64) i).length = i := Proof.Cmac.bytesAt_length _ _ _
  have hx : writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) i)
      (p.setWidth 64 + BitVec.ofNat 64 i) = s.mem (p.setWidth 64 + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem (c.setWidth 64) _ (R := ⟨c.setWidth 64, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base _ (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have al : t₁.gpr Reg8.al.reg = (t.mem (p.setWidth 64 + BitVec.ofNat 64 i)).setWidth 32 := u₁.gpr
  have hmem : t₅.mem = writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, v₂.mem, al, u₁.mem, mem, byte_rt32, hx, Proof.Cmac.bytesAt_succ,
      writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega), hlen]
  have cx₄ : t₄.gpr .ecx = BitVec.ofNat 32 (L - i) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), xcx]
  have xcx' : t₅.gpr .ecx = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, cx₄, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub]
  have ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    show VG.X86.eval .ne t₅ = _
    rw [eval_ne, z₅, cx₄, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub,
      ofNat_beq_zero (by omega)]
    rfl
  have gg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → t₅.gpr r = s.gpr r := fun r ha hc hs hd' => by
    rw [u₅.other _ hc, u₄.other _ hd', u₃.other _ hs, v₂.gpr, u₁.other _ ha, g r ha hc hs hd']
  have xdi' : t₅.gpr .edi = c + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), xdi,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have xsi' : t₅.gpr .esi = p + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, v₂.gpr, u₁.other _ (by decide), xsi,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  have wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], gg, rd', wr'⟩
  · right
    exact ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega, xsi', xdi', xcx', hmem, gg,
      rd', wr'⟩

/-- `copy`: the `L` bytes at `p` (`esi`) copied to `c` (`edi`), none if `L`
(`ecx`) is 0. -/
theorem copy_wp {s : State} {p c : BitVec 32} {L : Nat} (hL : L < 2 ^ 32)
    (hsi : s.gpr .esi = p) (hdi : s.gpr .edi = c) (hcx : s.gpr .ecx = BitVec.ofNat 32 L)
    (fp : 0 < L → p.toNat + L ≤ 2 ^ 32) (fc : 0 < L → c.toNat + L ≤ 2 ^ 32)
    (hr : 0 < L → Covers [⟨p.setWidth 64, L⟩] (s.rd ++ s.wr)) (hw : 0 < L → Covers [⟨c.setWidth 64, L⟩] s.wr)
    (hd : 0 < L → (⟨p.setWidth 64, L⟩ : Region).Disjoint ⟨c.setWidth 64, L⟩) :
    WP isa copy s fun s' =>
      s'.mem = writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) L) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_test fun s₁ f₁ z₁ => WP.block_nil ?_)
  have ev : isa.eval .e s₁ = some (decide (L = 0)) := by
    show VG.X86.eval .e s₁ = _; rw [eval_e, z₁, hcx, BitVec.and_self, ofNat_beq_zero hL]
  by_cases h0 : L = 0
  · subst h0
    refine WP.ite true (by rw [ev]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by rw [f₁.mem]; simp [Spec.Aes.bytesAt, writeBytes_nil], fun r _ _ _ _ => by rw [f₁.gpr], f₁.rd, f₁.wr⟩
  · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
    have h0' : 0 < L := by omega
    refine WP.mono (copyLoop_wp h0' hL (by rw [f₁.gpr]; exact hsi) (by rw [f₁.gpr]; exact hdi)
      (by rw [f₁.gpr]; exact hcx) (fp h0') (fc h0') (by rw [f₁.rd, f₁.wr]; exact hr h0')
      (by rw [f₁.wr]; exact hw h0') (hd h0'))
      fun s' ⟨m, g, rd, wr⟩ => ⟨by rw [m, f₁.mem], fun r a b c d => by rw [g r a b c d, f₁.gpr], by rw [rd, f₁.rd],
        by rw [wr, f₁.wr]⟩

/-! ## Bytes written -/

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} (h : xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i h1 _
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) =
      Spec.Aes.bytesAt m p r ++ xs := by
  rw [Proof.Cmac.Stream.bytesAt_append, bytesAt_writeBytes_self _ _ (by omega)]
  congr 1
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact writeBytes_before m p xs (List.mem_range.mp hi) (by omega)

/-! ## The saved registers -/

theorem saved_fits : Spill.Fits 2192 saved := by decide

theorem saved_bound : ∀ p ∈ saved, 2176 ≤ p.2 ∧ p.2 + 4 ≤ 2192 := by decide

theorem saved_ne_eax : ∀ p ∈ saved, p.1 ≠ .eax := by decide

theorem save_eq : save = Spill.saveCode .eax saved := rfl

theorem restore_eq (i : Nat) : restore i = .mov .eax (argOp i) :: (Spill.restoreCode .eax saved ++ []) := rfl

/-- Each slot of `saved` holds the register saved there. -/
theorem saveMem_slot (m : Mem) (B : Addr) (g : Reg → BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (Spill.saveMem m (B + BitVec.ofNat 64 ·) g saved).readW (B + BitVec.ofNat 64 d) 32 = g r :=
  Spill.saveMem_saved_ofNat m B g saved_fits (by decide) (r, d) h

/-- The memory after saving the registers in the scratch buffer at `Sc`. -/
def savedMem (s₀ : State) (Sc : BitVec 32) : Mem :=
  Spill.saveMem s₀.mem (Sc.setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr saved

theorem savedMem_frame (s₀ : State) (Sc : BitVec 32) :
    Frame [⟨Sc.setWidth 64 + BitVec.ofNat 64 2176, 16⟩] s₀.mem (savedMem s₀ Sc) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp => by
    have h := saved_bound p hp
    rw [show Sc.setWidth 64 + BitVec.ofNat 64 p.2 =
        Sc.setWidth 64 + BitVec.ofNat 64 2176 + BitVec.ofNat 64 (p.2 - 2176) by
      rw [Offset.add_add, Nat.add_sub_cancel' h.1]]
    exact Offset.contains_base _ (by omega) (by omega)

/-- Saving the registers, with the scratch buffer `Sc` in `eax`. -/
theorem save_wp {is : List Instr} {s : State} {Q : State → Prop} {Sc : BitVec 32} (heax : s.gpr .eax = Sc)
    (hfit : Sc.toNat + 2304 ≤ 2 ^ 32) (hw : Covers [⟨Sc.setWidth 64, 2304⟩] s.wr)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = Spill.saveMem s.mem (Sc.setWidth 64 + BitVec.ofNat 64 ·) s.gpr saved → WP isa (.block is) s' Q) :
    WP isa (.block (save ++ is)) s Q := by
  rw [save_eq]
  refine Spill.save_ofNat_ok saved saved_fits (by rw [heax]; omega) (fun p hp => ?_) fun s' u =>
    k s' u.gpr u.rd u.wr (by rw [u.mem, heax])
  have hb := saved_bound p hp
  rw [heax]
  exact hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩

/-- Restoring the registers, from the scratch buffer `Sc` (the stack argument
`i`), whose slots hold the registers of `s₀`. -/
theorem restore_wp {s₀ s : State} {i : Nat} {Sc : BitVec 32} (hesp : s.gpr .esp = s₀.gpr .esp)
    (hin : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4) (hv : s.mem.readW (argAddr s₀ i) 32 = Sc)
    (hfit : Sc.toNat + 2304 ≤ 2 ^ 32) (hr : Covers [⟨Sc.setWidth 64, 2304⟩] (s.rd ++ s.wr))
    (hs : ∀ r d, (r, d) ∈ saved → s.mem.readW (Sc.setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r) :
    WP isa (.block (restore i)) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem := by
  rw [restore_eq]
  refine VG.Proof.MdStream.X86.wp_movm (a := argAddr s₀ i) (by rw [ea_at', hesp]; rfl) hin fun s₁ u₁ => ?_
  rw [hv] at u₁
  refine Spill.restore_ofNat_ok saved saved_fits (by rw [u₁.gpr]; omega) saved_ne_eax (fun p hp' => ?_)
    (fun p hp' => by rw [u₁.gpr, u₁.mem]; exact hs p.1 p.2 hp') fun s₂ r₂ =>
      WP.block_nil ⟨r₂.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), hesp]), by rw [r₂.mem, u₁.mem]⟩
  have hb := saved_bound p hp'
  rw [u₁.gpr, u₁.rd, u₁.wr]
  exact hr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩

/-! ## The stack arguments and the stack -/

theorem argAddr_eq {s₀ : State} {n i : Nat} (hfit : (s₀.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) (hi : i < n) :
    argAddr s₀ i = (s₀.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) := addr_eq (by omega)

/-- Argument `i` among the `n`. -/
theorem arg_sub {s₀ : State} {n i : Nat} (hfit : (s₀.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) (hi : i < n) :
    Region.Sub ⟨argAddr s₀ i, 4⟩ ⟨argAddr s₀ 0, 4 * n⟩ := by
  rw [argAddr_eq hfit hi, argAddr_eq hfit (by omega : 0 < n),
    show 4 + 4 * i = (4 + 4 * 0) + 4 * i by omega, ← Offset.add_add]
  exact Offset.sub_base _ (by omega)

/-- The arguments are above the stack below `esp`. -/
theorem args_below {s₀ : State} {n k : Nat} (hfit : (s₀.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) (hn : 0 < n)
    (hk : k ≤ (s₀.gpr .esp).toNat) : (below (s₀.gpr .esp) k).Disjoint ⟨argAddr s₀ 0, 4 * n⟩ := by
  rw [argAddr_eq hfit hn]
  show Region.Disjoint ⟨(s₀.gpr .esp - BitVec.ofNat 32 k).setWidth 64, k⟩ _
  rw [Taint.sub_setWidth hk]
  exact Offset.disjoint_below_above _ (by omega)

/-- So is the return address. -/
theorem ret_below {E : BitVec 32} {k : Nat} (hk : k ≤ E.toNat) :
    (⟨E.setWidth 64, 4⟩ : Region).Disjoint (below E k) := by
  show Region.Disjoint _ ⟨(E - BitVec.ofNat 32 k).setWidth 64, k⟩
  rw [Taint.sub_setWidth hk]
  exact Offset.base_disjoint_below _ (by omega)

theorem below_eq {E : BitVec 32} {k : Nat} (hk : k ≤ E.toNat) :
    below E k = ⟨E.setWidth 64 - BitVec.ofNat 64 k, k⟩ := by
  simp only [below]; rw [Taint.sub_setWidth hk]

/-- An argument is unchanged where only regions disjoint from it change. -/
theorem arg_keep {s₀ : State} {rs : List Region} {m : Mem} (hf : Frame rs s₀.mem m) {i : Nat}
    (hd : ∀ r ∈ rs, (⟨argAddr s₀ i, 4⟩ : Region).Disjoint r) : m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  hf.readW (Region.contains_self _ _) hd (by decide)

theorem arg_ofNat (s₀ : State) (i : Nat) : arg s₀ i = BitVec.ofNat 32 (arg s₀ i).toNat := by simp

/-- `x + d`, as an address, for `x + d` within the 32-bit space. -/
theorem add_setWidth {x : BitVec 32} {d : Nat} (h : x.toNat + d < 2 ^ 32) :
    (x + BitVec.ofNat 32 d).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 d := addr_eq h

theorem add_toNat {x : BitVec 32} {d : Nat} (h : x.toNat + d < 2 ^ 32) :
    (x + BitVec.ofNat 32 d).toNat = x.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega)]; exact Nat.mod_eq_of_lt h

theorem arg_contains {s₀ : State} {n i : Nat} (hfit : (s₀.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) (hi : i < n) :
    (⟨argAddr s₀ 0, 4 * n⟩ : Region).Contains (argAddr s₀ i) 4 := by
  have e : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
    rw [argAddr_eq hfit hi, argAddr_eq hfit (by omega : 0 < n), Offset.add_add]
  rewrite [e]
  exact Offset.contains_base _ (by omega) (by omega)

/-! ## Two runs between the calls -/

/-- What two runs agree on between the calls: `esp`, the writable regions
and the `n` stack arguments are those on entry. -/
structure Pt (n : Nat) (s₀ s : State) : Prop where
  esp : s.gpr .esp = s₀.gpr .esp
  wr : s.wr = s₀.wr
  args : ∀ i < n, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i

theorem Pt.refl (n : Nat) (s₀ : State) : Pt n s₀ s₀ := ⟨rfl, rfl, fun _ _ => rfl⟩

/-- Two runs at points with `Pt`, from entry states that agree on `esp` and
the arguments, agree on `esp`, the arguments and the registers `rs`. -/
theorem Pt.agree {n : Nat} {rs : List Reg} {s₀ s₀' s₁ s₂ : State} (hsp : s₀.gpr .esp = s₀'.gpr .esp)
    (hq : ∀ i < n, arg s₀ i = arg s₀' i) (o : ArgsOut n s₀) (o' : ArgsOut n s₀') (h₁ : Pt n s₀ s₁)
    (h₂ : Pt n s₀' s₂) (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.X86.Taint.Agree (argTaint rs (4 + 4 * n)) s₁ s₂ := by
  have out : ∀ {t s : State}, ArgsOut n t → Pt n t s → ArgsOut n s := fun ⟨a, b⟩ h => by
    rw [ArgsOut, h.esp, h.wr]; exact ⟨a, b⟩
  have cur : ∀ {t s : State}, Pt n t s → ∀ i < n, arg s i = arg t i := fun {t s} h i hi => by
    show s.mem.readW (argAddr s i) 32 = _
    rw [show argAddr s i = argAddr t i by simp only [argAddr, h.esp]]; exact h.args i hi
  exact agree_argTaint hr (by rw [h₁.esp, h₂.esp, hsp]) (out o h₁) (out o' h₂)
    fun i hi => by rw [cur h₁ i hi, cur h₂ i hi, hq i hi]

end VG.Proof.CmacAes.Stream.X86
