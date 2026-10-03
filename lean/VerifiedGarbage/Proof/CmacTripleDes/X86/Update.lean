import VerifiedGarbage.Proof.CmacTripleDes.X86.Save
import VerifiedGarbage.Proof.CmacTripleDes.Cmac
import VerifiedGarbage.Proof.Cmac.Frame

/-!
# TDEA-CMAC on x86: `vg_cmac_triple_des_update`

Untrusted: everything here is checked by Lean. The invariant after `k`
blocks (`LInv`): words 32 and 33 of the scratch buffer hold the next block
and the blocks left, only the state, the block's words and those two have
changed since the registers were saved, and the state is the chaining value
after the first `k` blocks.
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86 VG.Proof.CmacTripleDes VG.Proof.Cmac
open VG.Proof.MdStream.X86 (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_store wp_addi wp_subi wp_cmpi wp_bswap)

theorem bswap_eq (x : BitVec 32) : bswap x = byteRev32 x := rfl

/-- The key schedule is unchanged outside a frame. -/
theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 384⟩ : Region).Disjoint r) :
    Spec.TripleDes.scheduleAt m' p = Spec.TripleDes.scheduleAt m p := by
  apply Vector.ext
  intro n hn
  rw [← vgetD _ hn 0, ← vgetD _ hn 0, scheduleAt_getD _ _ hn, scheduleAt_getD _ _ hn]
  exact hf.readW (r := ⟨p + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega))) (by decide)

theorem in_rw {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (hc : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, hc⟩

theorem addr_zero (x : BitVec 32) : addr x 0 = x.setWidth 64 := by
  simp only [addr]; rw [show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero]

theorem addr_off2 {x : BitVec 32} {a b : Nat} (h : x.toNat + a + b < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 a) b = x.setWidth 64 + BitVec.ofNat 64 a + BitVec.ofNat 64 b := by
  rw [Straight.addr_add_ofNat, addr_eq (by omega), Offset.add_add]

theorem add0 (a : Addr) : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a

section
variable (s₀ : State)

abbrev W : BitVec 32 := arg s₀ 0
abbrev St : BitVec 32 := arg s₀ 1
abbrev Dp : BitVec 32 := arg s₀ 2
abbrev N : Nat := (arg s₀ 3).toNat
abbrev S : BitVec 32 := arg s₀ 4

abbrev schR : Region := ⟨(W s₀).setWidth 64, 384⟩
abbrev stR : Region := ⟨(St s₀).setWidth 64, 8⟩
abbrev dataR : Region := ⟨(Dp s₀).setWidth 64, 8 * N s₀⟩
abbrev scrR : Region := ⟨(S s₀).setWidth 64, 640⟩
abbrev argsR : Region := ⟨argAddr s₀ 0, 20⟩
abbrev retR : Region := ⟨(s₀.gpr .esp).setWidth 64, 4⟩

/-- The cipher. -/
abbrev ciph : Spec.Cmac.Cipher := ciphAt s₀.mem ((W s₀).setWidth 64)

/-- The message blocks. -/
abbrev blks : List (List Byte) := Spec.Cmac.blocksAt s₀.mem ((Dp s₀).setWidth 64) 8 (N s₀)

/-- What changes after the registers are saved. -/
abbrev chg : List Region :=
  [stR s₀, ⟨(S s₀).setWidth 64, 84⟩, ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 128, 8⟩]

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀, dataR s₀, argsR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  sch_st : (schR s₀).Disjoint (stR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  data_st : (dataR s₀).Disjoint (stR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  st_scr : (stR s₀).Disjoint (scrR s₀)
  args_st : (argsR s₀).Disjoint (stR s₀)
  args_scr : (argsR s₀).Disjoint (scrR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  sch_fit : (W s₀).toNat + 384 ≤ 2 ^ 32
  st_fit : (St s₀).toNat + 8 ≤ 2 ^ 32
  data_fit : (Dp s₀).toNat + 8 * N s₀ ≤ 2 ^ 32
  scr_fit : (S s₀).toNat + 640 ≤ 2 ^ 32
  esp_fit : (s₀.gpr .esp).toNat + 24 ≤ 2 ^ 32

theorem UPre.of {s₀ : State} (h : updateX86.pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (s₀ : State) (k : Nat) (s : State) : Prop where
  esi : s.gpr .esi = W s₀
  ebp : s.gpr .ebp = S s₀
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  dp : s.mem.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 128) 32 = Dp s₀ + BitVec.ofNat 32 (8 * k)
  left : s.mem.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 132) 32 = BitVec.ofNat 32 (N s₀ - k)
  frame : Frame (chg s₀) (savedMem s₀ (S s₀)) s.mem
  state : Spec.Aes.bytesAt s.mem ((St s₀).setWidth 64) 8 =
    Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem ((St s₀).setWidth 64) 8) ((blks s₀).take k)

/-! ## Regions -/

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.inScr {d n : Nat} (h : d + n ≤ 640) (hn : 0 < n) :
    InRegions s₀.wr ((S s₀).setWidth 64 + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ h (by omega))

theorem UPre.scrEa {s : State} (h : s.gpr .ebp = S s₀) {d : Nat} (hd : d < 640) :
    s.ea (at_ .ebp d) = (S s₀).setWidth 64 + BitVec.ofNat 64 d := by
  rw [ea_at', h]; exact addr_eq (by have := hp.scr_fit; omega)

/-- Argument `i`'s address, in the arguments' region. -/
theorem UPre.argAddr_eq {i : Nat} (hi : i < 5) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have := hp.esp_fit
  show addr (s₀.gpr .esp) (4 + 4 * i) = addr (s₀.gpr .esp) (4 + 4 * 0) + _
  rw [addr_eq (by omega), addr_eq (by omega), Offset.add_add, show 4 + 4 * 0 + 4 * i = 4 + 4 * i by omega]

/-- The arguments are unchanged while only `chg` changes after the registers are saved. -/
theorem UPre.arg_eq {m : Mem} (hf : Frame (chg s₀) (savedMem s₀ (S s₀)) m) {i : Nat} (hi : i < 5) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have hsub : Region.Sub ⟨argAddr s₀ i, 4⟩ (argsR s₀) := by
    rw [hp.argAddr_eq hi]; exact Offset.sub_base _ (by omega)
  rw [hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
  · exact (savedMem_frame s₀ (S s₀)).readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.args_scr.sub_left hsub).sub_right (Offset.sub_base _ (by decide))) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.args_st.sub_left hsub
    · exact (hp.args_scr.sub_left hsub).sub_right (Region.sub_prefix (by decide))
    · exact (hp.args_scr.sub_left hsub).sub_right (Offset.sub_base _ (by decide))

theorem UPre.argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr, hp.rd, hp.argAddr_eq hi]
  exact in_rw (r := argsR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))

theorem UPre.sched {m : Mem} (hf : Frame (chg s₀) (savedMem s₀ (S s₀)) m) :
    Spec.TripleDes.scheduleAt m ((W s₀).setWidth 64) = Spec.TripleDes.scheduleAt s₀.mem ((W s₀).setWidth 64) := by
  rw [scheduleAt_frame hf fun r hr => ?_]
  · exact scheduleAt_frame (savedMem_frame s₀ (S s₀)) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.sch_scr.sub_right (Offset.sub_base _ (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.sch_st
    · exact hp.sch_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.sch_scr.sub_right (Offset.sub_base _ (by decide))

theorem UPre.data {m : Mem} (hf : Frame (chg s₀) (savedMem s₀ (S s₀)) m) {k : Nat} (hk : k < N s₀) :
    Spec.Aes.bytesAt m ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k)) 8 =
      Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k)) 8 := by
  have hsub : Region.Sub ⟨(Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k), 8⟩ (dataR s₀) :=
    Offset.sub_base _ (by omega)
  rw [bytesAt_frame hf (fun r hr => ?_) (by decide)]
  · exact bytesAt_frame (savedMem_frame s₀ (S s₀)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left hsub).sub_right (Offset.sub_base _ (by decide))) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.data_st.sub_left hsub
    · exact (hp.data_scr.sub_left hsub).sub_right (Region.sub_prefix (by decide))
    · exact (hp.data_scr.sub_left hsub).sub_right (Offset.sub_base _ (by decide))

/-- The block's precondition, with the registers and regions of the function. -/
theorem UPre.block {s : State} (h9 : s.gpr .esi = W s₀) (h10 : s.gpr .ebp = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) : BlockPre s where
  sched := ⟨384, by rw [hrd, hwr, hp.rd, h9]; simp, Nat.le_refl _, by rw [h9]; exact hp.sch_fit⟩
  scr := ⟨640, by rw [hwr, hp.wr, h10]; simp, by decide, by rw [h10]; exact hp.scr_fit⟩
  disj := by
    rw [h9, h10]
    exact hp.sch_scr.symm.sub_left (Region.sub_prefix (by decide))

end

/-! ## One block -/

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (blks s₀).take (k + 1) =
      (blks s₀).take k ++ [Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k)) 8] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega)]
  simp [Spec.Cmac.blocksAt]

/-- The two words at `a` XORed, as a big-endian integer. -/
theorem bswap_xor_append (a₀ a₁ b₀ b₁ : BitVec 32) :
    bswap (a₀ ^^^ b₀) ++ bswap (a₁ ^^^ b₁) = byteRev64 ((a₁ ++ a₀) ^^^ (b₁ ++ b₀)) := by
  rw [bswap_eq, bswap_eq, byteRev32_append, BitVec.xor_append]

theorem readW_writeW_far (m : Mem) (B : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)

theorem readW_lo_of_hi (m : Mem) (a : Addr) (v w : BitVec 32) :
    ((m.writeW a v).writeW (a + BitVec.ofNat 64 4) w).readW a 32 = v := by
  have := readW_writeW_far (m.writeW a v) a w (d := 0) (e := 4) (by decide) (by decide) (by decide)
  rw [add0] at this
  rw [this, Mem.readW_writeW_self32]

theorem body_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa updBody s fun s' => LInv s₀ (k + 1) s' ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0)) := by
  have hN : N s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  have hsf := hp.scr_fit
  have hdf := hp.data_fit
  have htf := hp.st_fit
  have rdwr : s.rd ++ s.wr = [schR s₀, dataR s₀, argsR s₀, stR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have scrIn : ∀ d, d + 4 ≤ 640 → InRegions (s.rd ++ s.wr) ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  have stIn : ∀ d, d + 4 ≤ 8 → InRegions (s.rd ++ s.wr) ((St s₀).setWidth 64 + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact in_rw (r := stR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  have dIn : ∀ d, d + 4 ≤ 8 →
      InRegions (s.rd ++ s.wr) ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by
      rw [rdwr, Offset.add_add]
      exact in_rw (r := dataR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  -- `chainIn`.
  refine WP.seq (?_ : WP isa (.block chainIn) s _)
  simp only [chainIn, stk]
  refine wp_arg (s₀ := s₀) 1 rfl h.esp (hp.argIn h.rd h.wr (by decide)) (hp.arg_eq h.frame (by decide))
    fun s₁ u₁ => ?_
  refine wp_movm (hp.scrEa (by rw [u₁.other _ (by decide), h.ebp]) (by decide))
    (by rw [u₁.rd, u₁.wr]; exact scrIn 128 (by decide)) fun s₂ u₂ => ?_
  have r1₂ : s₂.gpr .ecx = St s₀ := by rw [u₂.other _ (by decide), u₁.gpr]
  have r7₂ : s₂.gpr .edi = Dp s₀ + BitVec.ofNat 32 (8 * k) := by rw [u₂.gpr, u₁.mem, h.dp]
  refine wp_movm (a := (St s₀).setWidth 64) (by rw [ea_at', r1₂, addr_zero])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; simpa [add0] using stIn 0 (by decide)) fun s₃ u₃ => ?_
  refine wp_movm (a := (St s₀).setWidth 64 + BitVec.ofNat 64 4)
    (by rw [ea_at', u₃.other _ (by decide), r1₂]; exact addr_eq (by omega))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact stIn 4 (by decide)) fun s₄ u₄ => ?_
  refine wp_xorma (a := (Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k))
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), r7₂, addr_off2 (by omega), add0])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; simpa [add0] using dIn 0 (by decide))
    fun s₅ u₅ => ?_
  refine wp_xorma (a := (Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 4)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), r7₂, addr_off2 (by omega)])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact dIn 4 (by decide))
    fun s₆ u₆ => wp_bswap fun s₇ u₇ => wp_bswap fun s₈ u₈ => WP.block_nil ?_
  -- What `chainIn` leaves.
  have g₈ : ∀ r, r ∉ [Reg.eax, .ecx, .edx, .edi] → s₈.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₈.other _ hr.2.2.1, u₇.other _ hr.1, u₆.other _ hr.2.2.1, u₅.other _ hr.1, u₄.other _ hr.2.2.1,
      u₃.other _ hr.1, u₂.other _ hr.2.2.2, u₁.other _ hr.2.1]
  have m₈ : s₈.mem = s.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₈ : s₈.rd = s.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have ax₈ : s₈.gpr .eax ++ s₈.gpr .edx = byteRev64 (s.mem.readW ((St s₀).setWidth 64) 64 ^^^
      s.mem.readW ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k)) 64) := by
    rw [u₈.gpr, u₈.other .eax (by decide), u₇.gpr, u₇.other .edx (by decide), u₆.gpr, u₆.other .eax (by decide),
      u₅.gpr, u₅.other .edx (by decide), u₄.gpr, u₄.other .eax (by decide), u₃.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem,
      u₁.mem, readW64_split, readW64_split s.mem ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (8 * k)), bswap_xor_append]
  refine WP.seq (WP.mono (block_ok (UPre.block hp (by rw [g₈ _ (by decide), h.esi])
    (by rw [g₈ _ (by decide), h.ebp]) (by rw [rd₈, h.rd]) (by rw [wr₈, h.wr]))) fun s₉ ⟨same, esi₉, ax₉⟩ => ?_)
  have ebp₉ : s₉.gpr .ebp = S s₀ := by rw [same.ebp, g₈ _ (by decide), h.ebp]
  have esp₉ : s₉.gpr .esp = s₀.gpr .esp := by rw [same.esp, g₈ _ (by decide), h.esp]
  have xR₈ : xR s₈ = ⟨(S s₀).setWidth 64, 84⟩ := by rw [xR, g₈ _ (by decide), h.ebp]
  have f₉ : Frame [⟨(S s₀).setWidth 64, 84⟩] s.mem s₉.mem := by rw [← m₈, ← xR₈]; exact same.frame
  have slot : ∀ d, 84 ≤ d → d + 4 ≤ 640 →
      s₉.mem.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s.mem.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 :=
    fun d h₁ h₂ => f₉.readW (r := ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)
  have frame₉ : Frame (chg s₀) (savedMem s₀ (S s₀)) s₉.mem := h.frame.trans (f₉.mono (by simp))
  have rd₉ : s₉.rd = s₀.rd := by rw [same.rd, rd₈, h.rd]
  have wr₉ : s₉.wr = s₀.wr := by rw [same.wr, wr₈, h.wr]
  have rdwr₉ : s₉.rd ++ s₉.wr = [schR s₀, dataR s₀, argsR s₀, stR s₀, scrR s₀] := by
    rw [rd₉, wr₉, hp.rd, hp.wr]; rfl
  simp only [chainOut, stk]
  refine wp_arg (s₀ := s₀) 1 rfl esp₉ (hp.argIn rd₉ wr₉ (by decide)) (hp.arg_eq frame₉ (by decide)) fun t₁ v₁ => ?_
  refine wp_movm (hp.scrEa (by rw [v₁.other _ (by decide), ebp₉]) (by decide))
    (by rw [v₁.rd, v₁.wr, rdwr₉]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by decide) (by omega)))
    fun t₂ v₂ => ?_
  refine wp_movm (hp.scrEa (by rw [v₂.other _ (by decide), v₁.other _ (by decide), ebp₉]) (by decide))
    (by rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, rdwr₉]
        exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by decide) (by omega)))
    fun t₃ v₃ => ?_
  have r1₃ : t₃.gpr .ecx = St s₀ := by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr]
  have r7₃ : t₃.gpr .edi = Dp s₀ + BitVec.ofNat 32 (8 * k) := by
    rw [v₃.other _ (by decide), v₂.gpr, v₁.mem, slot 128 (by decide) (by decide), h.dp]
  have r3₃ : t₃.gpr .ebx = BitVec.ofNat 32 (N s₀ - k) := by
    rw [v₃.gpr, v₂.mem, v₁.mem, slot 132 (by decide) (by decide), h.left]
  refine wp_bswap fun t₄ v₄ => wp_bswap fun t₅ v₅ => ?_
  have stW : ∀ d, d + 4 ≤ 8 → InRegions t₅.wr ((St s₀).setWidth 64 + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr₉, hp.wr]
    exact in_rw (r := stR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  refine wp_store (a := (St s₀).setWidth 64) (by rw [ea_at', v₅.other _ (by decide), v₄.other _ (by decide), r1₃,
    addr_zero]) (by simpa [add0] using stW 0 (by decide)) fun t₆ w₆ => ?_
  refine wp_store (a := (St s₀).setWidth 64 + BitVec.ofNat 64 4)
    (by rw [ea_at', w₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), r1₃]; exact addr_eq (by omega))
    (by rw [w₆.wr]; exact stW 4 (by decide)) fun t₇ w₇ => ?_
  refine wp_addi fun t₈ v₈ => wp_subi fun t₉ v₉ _ => ?_
  have g₉ : ∀ r, r ∉ [Reg.eax, .ebx, .ecx, .edx, .edi] → t₉.gpr r = s₉.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [v₉.other _ hr.2.1, v₈.other _ hr.2.2.2.2, w₇.gpr, w₆.gpr, v₅.other _ hr.2.2.2.1, v₄.other _ hr.1,
      v₃.other _ hr.2.1, v₂.other _ hr.2.2.2.2, v₁.other _ hr.2.2.1]
  have ebp₉' : t₉.gpr .ebp = S s₀ := by rw [g₉ _ (by decide), ebp₉]
  have wr₉' : t₉.wr = [stR s₀, scrR s₀] := by
    rw [v₉.wr, v₈.wr, w₇.wr, w₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr₉, hp.wr]
  have scrW : ∀ d, d + 4 ≤ 640 → InRegions t₉.wr ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [wr₉']; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  refine wp_store (hp.scrEa ebp₉' (by decide)) (scrW 128 (by decide)) fun t₁₀ w₁₀ => ?_
  refine wp_store (hp.scrEa (by rw [w₁₀.gpr, ebp₉']) (by decide)) (by rw [w₁₀.wr]; exact scrW 132 (by decide))
    fun t₁₁ w₁₁ => wp_cmpi fun t₁₂ f₁₂ _ z₁₂ => WP.block_nil ?_
  -- The registers stored.
  have r7₉ : t₉.gpr .edi = Dp s₀ + BitVec.ofNat 32 (8 * (k + 1)) := by
    rw [v₉.other _ (by decide), v₈.gpr, w₇.gpr, w₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), r7₃,
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, Offset.add_add, show 8 * k + 8 = 8 * (k + 1) by omega]
  have r3₉ : t₉.gpr .ebx = BitVec.ofNat 32 (N s₀ - (k + 1)) := by
    rw [v₉.gpr, v₈.other _ (by decide), w₇.gpr, w₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), r3₃,
      ofNat_sub_one (by omega) (by omega), Nat.sub_sub]
  -- The memory.
  have m₉ : t₉.mem = (s₉.mem.writeW ((St s₀).setWidth 64) (bswap (s₉.gpr .eax))).writeW
      ((St s₀).setWidth 64 + BitVec.ofNat 64 4) (bswap (s₉.gpr .edx)) := by
    rw [v₉.mem, v₈.mem, w₇.mem, w₆.mem, w₆.gpr, v₅.gpr, v₅.other .eax (by decide), v₄.gpr, v₅.mem, v₄.mem,
      v₄.other .edx (by decide), v₃.other .eax (by decide), v₃.other .edx (by decide), v₂.other .eax (by decide),
      v₂.other .edx (by decide), v₁.other .eax (by decide), v₁.other .edx (by decide), v₃.mem, v₂.mem, v₁.mem]
  have m₁₁ : t₁₁.mem = (t₉.mem.writeW ((S s₀).setWidth 64 + BitVec.ofNat 64 128)
      (Dp s₀ + BitVec.ofNat 32 (8 * (k + 1)))).writeW ((S s₀).setWidth 64 + BitVec.ofNat 64 132)
      (BitVec.ofNat 32 (N s₀ - (k + 1))) := by
    rw [w₁₁.mem, w₁₀.mem, w₁₀.gpr, r7₉, r3₉]
  have g₁₂ : t₁₂.gpr = t₉.gpr := by rw [f₁₂.gpr, w₁₁.gpr, w₁₀.gpr]
  -- The state.
  have hS : sch s₈ = Spec.TripleDes.scheduleAt s₀.mem ((W s₀).setWidth 64) := by
    show Spec.TripleDes.scheduleAt s₈.mem ((s₈.gpr .esi).setWidth 64) = _
    rw [g₈ _ (by decide), h.esi, m₈]; exact UPre.sched hp h.frame
  have hD := UPre.data hp h.frame hk
  have stFrame : Spec.Aes.bytesAt t₁₁.mem ((St s₀).setWidth 64) 8 =
      Spec.Aes.bytesAt t₉.mem ((St s₀).setWidth 64) 8 := by
    rw [m₁₁]
    refine bytesAt_frame (rs := [⟨(S s₀).setWidth 64 + BitVec.ofNat 64 128, 8⟩]) ?_ (fun r hr => ?_) (by decide)
    · have c : ∀ d, 128 ≤ d → d + 4 ≤ 136 →
          (⟨(S s₀).setWidth 64 + BitVec.ofNat 64 128, 8⟩ : Region).Contains
            ((S s₀).setWidth 64 + BitVec.ofNat 64 d) (32 / 8) := fun d h₁ h₂ => by
        rw [show (S s₀).setWidth 64 + BitVec.ofNat 64 d =
          (S s₀).setWidth 64 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (d - 128) from (Offset.add_add_eq _ (by omega)).symm]
        exact Offset.contains_base _ (by omega) (by omega)
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 128 (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (c 132 (by decide) (by decide))
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (Offset.sub_base _ (by decide))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [g₁₂, g₉ _ (by decide), esi₉, g₈ _ (by decide), h.esi]
  · rw [g₁₂, ebp₉']
  · rw [g₁₂, g₉ _ (by decide), esp₉]
  · rw [f₁₂.rd, w₁₁.rd, w₁₀.rd, v₉.rd, v₈.rd, w₇.rd, w₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, rd₉]
  · rw [f₁₂.wr, w₁₁.wr, w₁₀.wr, wr₉', ← hp.wr]
  · rw [f₁₂.mem, m₁₁, readW_writeW_far _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [f₁₂.mem, m₁₁, Mem.readW_writeW_self32]
  · rw [f₁₂.mem, m₁₁, m₉]
    have c4 : (stR s₀).Contains ((St s₀).setWidth 64 + BitVec.ofNat 64 4) (32 / 8) :=
      Offset.contains_base _ (by decide) (by omega)
    have c0 : (stR s₀).Contains ((St s₀).setWidth 64) (32 / 8) := by
      simpa [add0] using Offset.contains_base ((St s₀).setWidth 64) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
    have cs : ∀ d, 128 ≤ d → d + 4 ≤ 136 →
        (⟨(S s₀).setWidth 64 + BitVec.ofNat 64 128, 8⟩ : Region).Contains ((S s₀).setWidth 64 + BitVec.ofNat 64 d)
          (32 / 8) := fun d h₁ h₂ => by
      rw [show (S s₀).setWidth 64 + BitVec.ofNat 64 d = (S s₀).setWidth 64 + BitVec.ofNat 64 128 +
        BitVec.ofNat 64 (d - 128) from (Offset.add_add_eq _ (by omega)).symm]
      exact Offset.contains_base _ (by omega) (by omega)
    exact (((frame₉.writeW (r := stR s₀) (by simp) _ c0).writeW (r := stR s₀) (by simp) _ c4).writeW (by simp) _
      (cs 128 (by decide) (by decide))).writeW (by simp) _ (cs 132 (by decide) (by decide))
  · rw [f₁₂.mem, stFrame, m₉, ← le8_readW, readW64_split, Mem.readW_writeW_self32, readW_lo_of_hi, bswap_eq, bswap_eq,
      byteRev32_append, ax₉, ax₈, hS, ← tdesWith_le8, le8_xor, le8_readW, le8_readW, h.state, hD,
      take_succ_blks s₀ hk, chain_append, chain_single]
  · rw [z₁₂, show t₁₁.gpr .ebx = t₉.gpr .ebx by rw [w₁₁.gpr, w₁₀.gpr], r3₉,
      show ∀ x : BitVec 32, x - 0 = x from fun x => by simp, Wp.ofNat_beq_zero (by omega)]

theorem eval_ne' (s : State) : isa.eval .ne s = s.zf.map (!·) := rfl
theorem eval_e' (s : State) : isa.eval .e s = s.zf := rfl

theorem loop_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : LInv s₀ k s) : WP isa (.loop updBody .ne) s (LInv s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := updBody) (c := .ne) (Q := LInv s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok hp hk h) fun s' ⟨h', z'⟩ => ?_
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [eval_ne', z']; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    refine ⟨by rw [eval_ne', z']; simp [hz], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

/-! ## The whole function -/

/-- The arguments of the entry state, unchanged by saving the registers. -/
theorem UPre.arg_saved {s₀ : State} (hp : UPre s₀) {i : Nat} (hi : i < 5) :
    (savedMem s₀ (S s₀)).readW (argAddr s₀ i) 32 = arg s₀ i :=
  hp.arg_eq (Frame.refl _ _) hi

theorem prologue_wp {s₀ : State} (hp : UPre s₀) :
    WP isa (.block updPre) s₀ fun s => LInv s₀ 0 s ∧ s.zf = some (decide (N s₀ = 0)) := by
  have hsc := hp.scr_fit
  have hN : N s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  rw [show updPre = .mov .eax (stk 20) :: (Spill.saveCode .eax saved ++
    ([.mov .ebp (.reg .eax), .mov .esi (stk 4), .mov .eax (stk 12), .store (at_ .ebp 128) .eax,
      .mov .eax (stk 16), .store (at_ .ebp 132) .eax, .alu .cmp .eax (.imm 0)] : List Instr)) from rfl]
  simp only [stk]
  refine wp_arg (s₀ := s₀) 4 rfl rfl (hp.argIn rfl rfl (by decide)) rfl fun s₁ u₁ => ?_
  refine Spill.save_ofNat_ok saved saved_fits (by rw [u₁.gpr]; exact fits_of hp.scr_fit (by decide))
    (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := saved_bound p hp'
    have hsc' : (arg s₀ 4).toNat + 640 ≤ 2 ^ 32 := hp.scr_fit
    rw [u₁.gpr, u₁.wr]
    exact hp.inScr (by omega) (by decide)
  have hm₂ : s₂.mem = savedMem s₀ (S s₀) := by
    rw [u₂.mem, u₁.mem, u₁.gpr, savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  have fr : ∀ m, m = savedMem s₀ (S s₀) → Frame (chg s₀) (savedMem s₀ (S s₀)) m := fun m h => h ▸ Frame.refl _ _
  refine wp_mov fun s₃ u₃ => ?_
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have esp₃ : s₃.gpr .esp = s₀.gpr .esp := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  refine wp_arg (s₀ := s₀) 0 rfl esp₃ (hp.argIn rd₃ wr₃ (by decide))
    (by rw [u₃.mem, hm₂]; exact hp.arg_saved (by decide)) fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) 2 rfl (by rw [u₄.other _ (by decide), esp₃])
    (hp.argIn (by rw [u₄.rd, rd₃]) (by rw [u₄.wr, wr₃]) (by decide))
    (by rw [u₄.mem, u₃.mem, hm₂]; exact hp.arg_saved (by decide)) fun s₅ u₅ => ?_
  have ebp₅ : s₅.gpr .ebp = S s₀ := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr]
  refine wp_store (hp.scrEa ebp₅ (by decide)) (by rw [u₅.wr, u₄.wr, wr₃]; exact hp.inScr (by decide) (by decide))
    fun s₆ w₆ => ?_
  have m₆ : s₆.mem = (savedMem s₀ (S s₀)).writeW ((S s₀).setWidth 64 + BitVec.ofNat 64 128) (Dp s₀) := by
    rw [w₆.mem, u₅.gpr, u₅.mem, u₄.mem, u₃.mem, hm₂]
  have c : ∀ d, 128 ≤ d → d + 4 ≤ 136 →
      (⟨(S s₀).setWidth 64 + BitVec.ofNat 64 128, 8⟩ : Region).Contains ((S s₀).setWidth 64 + BitVec.ofNat 64 d)
        (32 / 8) := fun d h₁ h₂ => by
    rw [show (S s₀).setWidth 64 + BitVec.ofNat 64 d = (S s₀).setWidth 64 + BitVec.ofNat 64 128 +
      BitVec.ofNat 64 (d - 128) from (Offset.add_add_eq _ (by omega)).symm]
    exact Offset.contains_base _ (by omega) (by omega)
  have f₆ : Frame (chg s₀) (savedMem s₀ (S s₀)) s₆.mem := by
    rw [m₆]; exact (Frame.refl _ _).writeW (by simp) _ (c 128 (by decide) (by decide))
  refine wp_arg (s₀ := s₀) 3 rfl (by rw [w₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), esp₃])
    (hp.argIn (by rw [w₆.rd, u₅.rd, u₄.rd, rd₃]) (by rw [w₆.wr, u₅.wr, u₄.wr, wr₃]) (by decide))
    (hp.arg_eq f₆ (by decide)) fun s₇ u₇ => ?_
  refine wp_store (hp.scrEa (by rw [u₇.other _ (by decide), w₆.gpr, ebp₅]) (by decide))
    (by rw [u₇.wr, w₆.wr, u₅.wr, u₄.wr, wr₃]; exact hp.inScr (by decide) (by decide)) fun s₈ w₈ =>
    wp_cmpi fun s₉ f₉ _ z₉ => WP.block_nil ?_
  have m₉ : s₉.mem = s₆.mem.writeW ((S s₀).setWidth 64 + BitVec.ofNat 64 132) (arg s₀ 3) := by
    rw [f₉.mem, w₈.mem, u₇.gpr, u₇.mem]
  have g₉ : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ebp → s₉.gpr r = s₀.gpr r := fun r ha hs hb => by
    rw [f₉.gpr, w₈.gpr, u₇.other _ ha, w₆.gpr, u₅.other _ ha, u₄.other _ hs, u₃.other _ hb, u₂.gpr, u₁.other _ ha]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [f₉.gpr, w₈.gpr, u₇.other _ (by decide), w₆.gpr, u₅.other _ (by decide), u₄.gpr]
  · rw [f₉.gpr, w₈.gpr, u₇.other _ (by decide), w₆.gpr, ebp₅]
  · rw [g₉ _ (by decide) (by decide) (by decide)]
  · rw [f₉.rd, w₈.rd, u₇.rd, w₆.rd, u₅.rd, u₄.rd, rd₃]
  · rw [f₉.wr, w₈.wr, u₇.wr, w₆.wr, u₅.wr, u₄.wr, wr₃]
  · rw [m₉, readW_writeW_far _ _ _ (by decide) (by decide) (by decide), m₆, Mem.readW_writeW_self32]
    show Dp s₀ = Dp s₀ + BitVec.ofNat 32 0; rw [show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero]
  · rw [m₉, Mem.readW_writeW_self32, Nat.sub_zero]; simp [N]
  · rw [m₉]; exact f₆.writeW (by simp) _ (c 132 (by decide) (by decide))
  · rw [List.take_zero, show Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem ((St s₀).setWidth 64) 8) [] =
      Spec.Aes.bytesAt s₀.mem ((St s₀).setWidth 64) 8 from rfl]
    rw [m₉, m₆, bytesAt_frame (rs := [⟨(S s₀).setWidth 64 + BitVec.ofNat 64 128, 8⟩])
      (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 128 (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (c 132 (by decide) (by decide)))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)]
    exact bytesAt_frame (savedMem_frame s₀ (S s₀)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)
  · rw [z₉, show s₈.gpr .eax = arg s₀ 3 by rw [w₈.gpr, u₇.gpr],
      show ∀ x : BitVec 32, x - 0 = x from fun x => by simp,
      show arg s₀ 3 = BitVec.ofNat 32 (N s₀) by simp [N], Wp.ofNat_beq_zero hN]

theorem mid_wp {s₀ : State} (hp : UPre s₀) {s₁ : State} (h : LInv s₀ 0 s₁) (hz : s₁.zf = some (decide (N s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop updBody .ne)) s₁ (LInv s₀ (N s₀)) := by
  have ev : isa.eval .e s₁ = some (decide (N s₀ = 0)) := by rw [eval_e', hz]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hp (by omega) h

/-- What changes is apart from the return address and the saved registers. -/
theorem UPre.ret_kept {s₀ : State} (hp : UPre s₀) {m : Mem} (hf : Frame (chg s₀) (savedMem s₀ (S s₀)) m) :
    m.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 := by
  rw [hf.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
  · exact (savedMem_frame s₀ (S s₀)).readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.ret_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.ret_scr.sub_right (Offset.sub_base _ (by decide))

theorem epilogue_wp {s₀ : State} (hp : UPre s₀) {s₂ : State} (h₂ : LInv s₀ (N s₀) s₂) :
    WP isa (.block restore) s₂ fun s' => abiPreserved s₀ s' ∧ updateX86.post s₀ s' := by
  have hsc := hp.scr_fit
  refine WP.mono (restore_ok h₂.ebp (by omega) (fun d h₁ h₂' => ?_) (saved_of fun d h₁ h₂' => ?_))
    fun s' r' => ⟨restored r' h₂.esp (by rw [r'.mem]; exact hp.ret_kept h₂.frame), ?_⟩
  · rw [h₂.rd, h₂.wr, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  · refine h₂.frame.readW (r := ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.st_scr.sub_right (Offset.sub_base _ (by omega))).symm
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (d := d) (e := 128) (by omega) (by omega) (by omega)
  · show Spec.Aes.bytesAt s'.mem ((St s₀).setWidth 64) 8 = Spec.Cmac.chain (ciph s₀) _ (blks s₀)
    rw [r'.mem, h₂.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

theorem update_wp {s₀ : State} (h0 : updateX86.pre s₀) :
    WP isa update s₀ fun s' => abiPreserved s₀ s' ∧ updateX86.post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, z₁⟩ =>
    WP.seq (WP.mono (mid_wp hp h₁ z₁) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.CmacTripleDes.X86
