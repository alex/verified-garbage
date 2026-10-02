import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Compress

namespace VG.Proof.Sha256.X86.ShaNi
open VG VG.X86 VG.Impl.Sha256.X86.ShaNi
open VG.Proof.Sha256.X86 (workRegion)
open VG.Proof.Sha256.X86 (Pre st bp nb scr esp₀ stR blR scrR H₀ blkAddr blk Saved
  contains_sub work_sub saved_frame blk_word compressBlocks_succ)
open VG.Spec.Sha256 (HashValue Block stateAt compressBlocks)

theorem Pre.scr_vec {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d + 16 ≤ 112) :
    InRegions s₀.wr (addr (scr s₀) d) 16 :=
  ⟨scrR s₀, by simp [hp.wr],
    contains_sub hd (by omega) (hp.scr_eq (by omega))⟩

theorem Pre.blk_fit {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) :
    (blkAddr s₀ i).toNat + 64 ≤ 2 ^ 32 := by
  have hb := hp.blk_fits
  simp only [blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 64 * i < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show (bp s₀).toNat + 64 * i < 2 ^ 32 by omega)]
  omega

theorem Pre.blk_vec {s₀ : State} (hp : Pre s₀) {i n : Nat}
    (hi : i < nb s₀) (hn : n < 4) :
    InRegions (s₀.rd ++ s₀.wr) ((blkAddr s₀ i).setWidth 64 + BitVec.ofNat 64 (16 * n)) 16 := by
  have he : (blkAddr s₀ i).setWidth 64 =
      (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) := by
    simpa only [blkAddr, addr] using addr_eq (x := bp s₀) (k := 64 * i)
      (by have := hp.blk_fits; omega)
  refine ⟨blR s₀, by simp only [hp.rd, List.mem_append, List.mem_cons, true_or], ?_⟩
  rw [he, Offset.add_add]
  exact Offset.contains_base _ (by omega) (by have := hp.blk_fits; omega)

theorem work_write128 (p : BitVec 32) (hfit : p.toNat + 112 ≤ 2 ^ 32)
    (m : Mem) (v : BitVec 128) {d : Nat} (hd : d + 16 ≤ 96) :
    Frame [workRegion p] m (m.writeW (addr p d) v) := by
  refine (Frame.refl _ _).writeW (List.mem_singleton_self _) v ?_
  rw [addr_eq (by omega)]
  exact Offset.contains_base _ hd (by omega)

theorem saveHash_frame (s : State) (hfit : (s.gpr .esi).toNat + 112 ≤ 2 ^ 32) :
    Frame [workRegion (s.gpr .esi)] s.mem
      ((s.mem.writeW (addr (s.gpr .esi) 32) (s.xmm .xmm1)).writeW
        (addr (s.gpr .esi) 48) (s.xmm .xmm2)) :=
  (work_write128 _ hfit _ _ (d := 32) (by decide)).trans
    (work_write128 _ hfit _ _ (d := 48) (by decide))

structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  x1 : s.xmm .xmm1 = abef (compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i)
  x2 : s.xmm .xmm2 = cdgh (compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i)
  esi : s.gpr .esi = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  ebx : s.gpr .ebx = st s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  mask : s.mem.readW (addr (scr s₀) 16) 128 = bswapMask

structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  edi : s.gpr .edi = blkAddr s₀ i
  ebp : s.gpr .ebp = BitVec.ofNat 32 (nb s₀ - i)

theorem saveHash_reads (p : BitVec 32) (hfit : p.toNat + 112 ≤ 2 ^ 32)
    (m : Mem) (x y : BitVec 128) :
    let m' := (m.writeW (addr p 32) x).writeW (addr p 48) y
    m'.readW (addr p 32) 128 = x ∧ m'.readW (addr p 48) 128 = y ∧
      m'.readW (addr p 16) 128 = m.readW (addr p 16) 128 := by
  have sep : ∀ d e : Nat, d + 16 ≤ 112 → e + 16 ≤ 112 →
      d + 16 ≤ e ∨ e + 16 ≤ d → Mem.Sep (addr p d) 16 (addr p e) 16 := by
    intro d e hd he hde
    rw [addr_eq (by omega), addr_eq (by omega)]
    exact Offset.sep _ hde (by omega) (by omega)
  dsimp only
  rw [Mem.readW_writeW_sep (sep 32 48 (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self m _ 16 x (by decide), Mem.readW_writeW_self _ _ 16 y (by decide),
    Mem.readW_writeW_sep (sep 16 48 (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep 16 32 (by decide) (by decide) (by decide)) (by decide)]
  exact ⟨rfl, rfl, rfl⟩

theorem in_read_of_write {rd wr : List Region} {p : Addr} {n : Nat}
    (h : InRegions wr p n) : InRegions (rd ++ wr) p n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append.mpr (.inr hr), hc⟩

theorem body_step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      Common s₀ (i + 1) s' ∧ s'.gpr .edi = blkAddr s₀ (i + 1) ∧
      s'.gpr .ebp = BitVec.ofNat 32 (nb s₀ - (i + 1)) ∧
      s'.zf = some (BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0) := by
  have vecwr : ∀ d : Nat, d + 16 ≤ 112 → InRegions s.wr (addr (s.gpr .esi) d) 16 := by
    intro d hd; rw [hL.wr, hL.esi]; exact Pre.scr_vec hp hd
  refine WP.seq (WP.mono (saveHash_ok s (vecwr 32 (by decide)) (vecwr 48 (by decide)))
    fun s₁ ⟨hm₁, hx₁, hg₁, hrd₁, hwr₁⟩ => ?_)
  have hf₁ : Frame [workRegion (scr s₀)] s.mem s₁.mem := by
    rw [hm₁]
    have hf := saveHash_frame s (by rw [hL.esi]; exact hp.scr_fits)
    simpa only [hL.esi] using hf
  have hf₁full : Frame [stR s₀, scrR s₀] s.mem s₁.mem := hf₁.sub
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨scrR s₀, by simp, work_sub _⟩)
  have hf : Frame [stR s₀, scrR s₀] s₀.mem s₁.mem := hL.frame.trans hf₁full
  have hdi₁ : s₁.gpr .edi = blkAddr s₀ i := (congrFun hg₁ _).trans hL.edi
  have hsi₁ : s₁.gpr .esi = scr s₀ := (congrFun hg₁ _).trans hL.esi
  have savedValues := saveHash_reads (scr s₀) hp.scr_fits s.mem (s.xmm .xmm1) (s.xmm .xmm2)
  have vals : s₁.mem.readW (addr (scr s₀) 32) 128 = s.xmm .xmm1 ∧
      s₁.mem.readW (addr (scr s₀) 48) 128 = s.xmm .xmm2 ∧
      s₁.mem.readW (addr (scr s₀) 16) 128 = bswapMask := by
    rw [hm₁, hL.esi]
    exact ⟨savedValues.1, savedValues.2.1, savedValues.2.2.trans hL.mask⟩
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) (blkAddr s₀ i) (scr s₀) s₁ hdi₁ hsi₁
    (Pre.blk_fit hp hi) (by have := hp.scr_fits; omega)
    (fun n hn => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact Pre.blk_vec hp hi hn)
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr, ← hp.scr_eq (by decide)];
        exact in_read_of_write (Pre.scr_vec hp (d := 16) (by decide)))
    (by rw [← hp.scr_eq (by decide)]; exact vals.2.2)
    (fun t ht => by
      have ea : addr (blkAddr s₀ i) (4 * t) =
          (blkAddr s₀ i).setWidth 64 + BitVec.ofNat 64 (4 * t) :=
        addr_eq (by have := Pre.blk_fit hp hi; omega)
      rw [← ea, hf.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
      exact blk_word hp hi ht)
    (by rw [hx₁]; exact hL.x1) (by rw [hx₁]; exact hL.x2) 16 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hsi₂ : s₂.gpr .esi = scr s₀ := (hR.gpr _ (by decide)).trans hsi₁
  have hg₂ : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r hr =>
    (hR.gpr r hr).trans (congrFun hg₁ r)
  refine WP.mono (finishBlock_ok s₂ _ _ hR.x1 hR.x2
    (by rw [hR.rd, hR.wr, hrd₁, hwr₁, hL.rd, hL.wr, hsi₂];
        exact in_read_of_write (Pre.scr_vec hp (d := 32) (by decide)))
    (by rw [hR.rd, hR.wr, hrd₁, hwr₁, hL.rd, hL.wr, hsi₂];
        exact in_read_of_write (Pre.scr_vec hp (d := 48) (by decide)))
    (by rw [hsi₂, hR.mem, vals.1]; exact hL.x1)
    (by rw [hsi₂, hR.mem, vals.2.1]; exact hL.x2))
    fun s₃ ⟨f1, f2, fdi, fbp, fg, fzf, fm, frd, fwr⟩ => ?_
  have mem : s₃.mem = s₁.mem := fm.trans hR.mem
  have ebp : s₂.gpr .ebp - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [hg₂ _ (by decide), hL.ebp,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fbp.trans ebp, ?_⟩
  · rw [f1, compressBlocks_succ]
  · rw [f2, compressBlocks_succ]
  · rw [fg _ (by decide) (by decide), hg₂ _ (by decide)]; exact hL.esi
  · rw [fg _ (by decide) (by decide), hg₂ _ (by decide)]; exact hL.esp
  · rw [fg _ (by decide) (by decide), hg₂ _ (by decide)]; exact hL.ebx
  · exact frd.trans (hR.rd.trans (hrd₁.trans hL.rd))
  · exact fwr.trans (hR.wr.trans (hwr₁.trans hL.wr))
  · rw [mem]; exact hf
  · rw [mem]; exact saved_frame hp hL.saved (.inl hf₁)
  · rw [mem]; exact vals.2.2
  · rw [fdi, hg₂ _ (by decide), hL.edi, blkAddr, blkAddr, BitVec.add_assoc]
    rw [show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, ← BitVec.ofNat_add]
    exact congrArg (fun n => bp s₀ + BitVec.ofNat 32 n) (by omega)
  · rw [fzf, ebp]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.mono (body_step hp hi hL) fun s' ⟨hc, hdi, hbp, hz⟩ => ?_
  have hev : eval .ne s' = some (!(BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0)) := by
    simp only [eval, hz, Option.map_some]
  by_cases hlast : i + 1 = nb s₀
  · exact .inl ⟨by rw [hev, hlast]; simp, hlast ▸ hc⟩
  · have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 32 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      have hn : nb s₀ < 2 ^ 32 := (arg s₀ 2).isLt
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hn)] at h'
      exact hne h'
    exact .inr ⟨by rw [hev]; simpa using h0, by omega, { hc with edi := hdi, ebp := hbp }⟩

theorem loop_ok {s₀ : State} (hp : Pre s₀) (hpos : 0 < nb s₀) {s : State}
    (hL : LInv s₀ 0 s) :
    WP isa (.loop body .ne) s (Common s₀ (nb s₀)) := by
  let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
  have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
    rintro m s ⟨i, rfl, hi, hL⟩
    refine WP.mono (body_ok hp hi hL) fun s' h => ?_
    rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
    · exact .inl ⟨he, hc⟩
    · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
  exact WP.loop (M := isa) Inv hstep (nb s₀) s ⟨0, rfl, hpos, hL⟩

end VG.Proof.Sha256.X86.ShaNi
