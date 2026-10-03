import VerifiedGarbage.Proof.Argon2.X86.Derive.FillInput

/-!
# Argon2 on x86 (32-bit): the address block and the random word

`stage_ok`: G of two blocks of `scratch` to a third. `addressCalls_ok`: the
address block for the counter, G(0, G(0, input)), at `scratch + 6144`.
`addressCache_ok`: J₁, J₂ from the cached address block, regenerated when
the index enters a new group of 128. `randomSource_ok`: J₁, J₂ are the
random word of `FillStep.random`.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_addm wp_cmpi wp_ldm wp_stm wp_andi wp_shr)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState compress addressBlock)
open VG.Proof.Argon2.X86 (blk)
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem scr_blockAt (m : Mem) {o : Nat} (ho : o + 1024 ≤ 16384) :
    blockAt m ((scrP s₀ + BitVec.ofNat 32 o).setWidth 64) = blk m (scrP s₀) o := by
  have := hp.scr_fits
  rw [Proof.Argon2.X86.blockAt_eq (by rw [add_nat (by omega)]; omega), blk_shift]

/-- `stage x y out`: G of the blocks at `scratch + x` and `scratch + y` to `scratch + out`. -/
theorem stage_ok {s : State} (h : Inv s₀ s) {x y o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384)
    (hx : 4096 ≤ x) (hx' : x + 1024 ≤ 16384) (hxo : x + 1024 ≤ o ∨ o + 1024 ≤ x)
    (hy : 4096 ≤ y) (hy' : y + 1024 ≤ 16384) (hyo : y + 1024 ≤ o ∨ o + 1024 ≤ y) :
    WP isa (Impl.Argon2.X86.Derive.stage x y o) s fun t => Inv s₀ t ∧
      (∀ q ∈ [Reg.ebx, .edi, .ebp, .esp], t.gpr q = s.gpr q) ∧
      Frame [⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrB s₀, 4096⟩, callR s₀] s.mem t.mem ∧
      blk t.mem (scrP s₀) o = compress (blk s.mem (scrP s₀) x) (blk s.mem (scrP s₀) y) := by
  unfold Impl.Argon2.X86.Derive.stage Impl.Argon2.X86.Derive.compressCall
  refine WP.seq (wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_addi fun s₃ u₃ =>
    wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_addi fun s₇ u₇ => WP.block_nil ?_)
  have i₇ := ((((((h.upd u₁ (by decide) (by decide)).upd u₂ (by decide) (by decide)).upd u₃ (by decide)
    (by decide)).upd u₄ (by decide) (by decide)).upd u₅ (by decide) (by decide)).upd u₆ (by decide)
    (by decide)).upd u₇ (by decide) (by decide)
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have dx : s₇.gpr .edx = scrP s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have ax : s₇.gpr .eax = scrP s₀ + BitVec.ofNat 32 x := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.gpr, u₁.gpr]
  have sx : s₇.gpr .esi = scrP s₀ + BitVec.ofNat 32 y := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  have cx : s₇.gpr .ecx = scrP s₀ + BitVec.ofNat 32 o := by
    rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  refine ccall_ok hp i₇ dx ho ho' cx (by rw [ax]; exact .inr ⟨x, hx, hx', hxo, rfl⟩)
    (by rw [sx]; exact .inr ⟨y, hy, hy', hyo, rfl⟩) fun t it cs f post => ⟨it, fun q hq => ?_, by rw [← m₇]; exact f,
      by rw [post, ax, sx, scr_blockAt hp _ hx', scr_blockAt hp _ hy', m₇]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> rw [cs _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]


/-- A block of `scratch` at `d`, outside the regions G's call at `o` writes. -/
theorem stage_keep {m m' : Mem} {o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384)
    (f : Frame [⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrB s₀, 4096⟩, callR s₀] m m') {d : Nat} (hd : 4096 ≤ d)
    (hd' : d + 1024 ≤ 16384) (hdo : d + 1024 ≤ o ∨ o + 1024 ≤ d) :
    blk m' (scrP s₀) d = blk m (scrP s₀) d := by
  rw [scr_blk hp m' hd', scr_blk hp m hd']
  refine blockAt_keep f fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ hdo (by omega) (by omega)
  · exact Offset.disjoint_base _ hd (by omega)
  · exact (call_disj hp (R := scrR s₀) (by simp)).symm.sub_left (Offset.sub_base _ hd')

omit hp in
theorem stage_frame {m m' : Mem} {o : Nat} (ho' : o + 1024 ≤ 16384)
    (f : Frame [⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrB s₀, 4096⟩, callR s₀] m m') :
    Frame [scrR s₀, callR s₀] m m' :=
  f.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scrR s₀, by simp, Offset.sub_base _ ho'⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨callR s₀, by simp, fun _ h => h⟩

/-- `addressCalls`: the address block for the counter `c` at `scratch + 6144`. -/
theorem addressCalls_ok {s : State} (h : Inv s₀ s) {pass slice lane index c : Nat}
    (ps : Pos s₀ s pass slice lane index) (hc : lw s₀ s counterOff = BitVec.ofNat 32 c)
    (h₁ : pass < 2 ^ 32) (h₂ : lane < 2 ^ 32) (h₃ : slice < 2 ^ 32) (h₄ : c < 2 ^ 32) :
    WP isa Impl.Argon2.X86.Derive.addressCalls s fun t => Inv s₀ t ∧
      (∀ q ∈ [Reg.ebx, .edi, .ebp, .esp], t.gpr q = s.gpr q) ∧ Frame [scrR s₀, callR s₀] s.mem t.mem ∧
      blk t.mem (scrP s₀) 6144 = addressBlock (prm s₀) pass lane slice c := by
  unfold Impl.Argon2.X86.Derive.addressCalls
  refine WP.seq ((input_ok hp h ps hc h₁ h₂ h₃ h₄).mono fun t₁ ⟨i₁, g₁, f₁, b₁, z₁⟩ => ?_)
  refine WP.seq ((stage_ok hp i₁ (x := 7168) (y := 5120) (o := 4096) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).mono fun t₂ ⟨i₂, g₂, f₂, b₂⟩ => ?_)
  refine (stage_ok hp i₂ (x := 7168) (y := 4096) (o := 6144) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).mono fun t ⟨it, gt, ft, bt⟩ =>
      ⟨it, fun q hq => ?_, ?_, ?_⟩
  · rw [gt q hq, g₂ q hq]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)
  · refine Frame.trans (f₁.sub fun r hr => ?_) ((stage_frame (by decide) f₂).trans (stage_frame (by decide) ft))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  · rw [bt, stage_keep hp (by decide) (by decide) f₂ (d := 7168) (by decide) (by decide) (by decide), b₂, z₁, b₁]
    rfl
end


theorem and127 {n : Nat} (h : n < 2 ^ 32) : BitVec.ofNat 32 n &&& 127 = BitVec.ofNat 32 (n % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, Wp.toNat_ofNat_lt h, Wp.toNat_ofNat_lt (by omega),
    show (127 : BitVec 32).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem shr7 {n : Nat} (h : n < 2 ^ 32) : BitVec.ofNat 32 n >>> 7 = BitVec.ofNat 32 (n / 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Wp.toNat_ofNat_lt h, Wp.toNat_ofNat_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem dbl32 (n : Nat) : BitVec.ofNat 32 n + BitVec.ofNat 32 n = BitVec.ofNat 32 (2 * n) := by
  rw [BitVec.ofNat_add_ofNat, Nat.two_mul]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `cacheWord`: J₁ and J₂ are word `index mod 128` of the cached address block. -/
theorem cacheWord_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hi : index < 2 ^ 30) :
    WP isa (.block Impl.Argon2.X86.Derive.cacheWord) s fun t => FS s₀ pass slice lane index ctr st t ∧
      lw s₀ t j2Off ++ lw s₀ t j1Off = (blk s.mem (scrP s₀) 6144)[index % 128]'(Nat.mod_lt _ (by decide)) := by
  have hs := hp.scr_fits
  have e8 : 8 * (index % 128) < 1024 := by omega
  unfold Impl.Argon2.X86.Derive.cacheWord
  refine wp_ldloc hp h.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_andi fun s₂ u₂ => wp_add fun s₃ u₃ _ =>
    wp_add fun s₄ u₄ _ => wp_add fun s₅ u₅ _ => ?_
  have h₅ := (((((h.of_keep (Divide.Keep.of_upd u₁ (by simp))).of_keep (Divide.Keep.of_upd u₂ (by simp))).of_keep
    (Divide.Keep.of_upd u₃ (by simp))).of_keep (Divide.Keep.of_upd u₄ (by simp))).of_keep
    (Divide.Keep.of_upd u₅ (by simp)))
  have a₅ : s₅.gpr .eax = BitVec.ofNat 32 (8 * (index % 128)) := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, h.pos.index, and127 (by omega), dbl32, dbl32, dbl32]
    congr 1; omega
  refine wp_addm h₅.inv.ebp (h₅.inv.arg_in hp (i := 15) (by decide)) fun s₆ u₆ => ?_
  have h₆ := h₅.of_keep (Divide.Keep.of_upd u₆ (by simp))
  have a₆ : s₆.gpr .eax = scrP s₀ + BitVec.ofNat 32 (8 * (index % 128)) := by
    rw [u₆.gpr, h₅.inv.arg hp (by decide), a₅, BitVec.add_comm]; rfl
  have inS : ∀ o, o + 4 ≤ 1024 → InRegions (s₆.rd ++ s₆.wr) (addr (s₆.gpr .eax) (6144 + o)) 4 := fun o ho => by
    rw [a₆, addr_shift, scr_addr' hp (by omega), h₆.inv.wr]
    exact ⟨scrR s₀, List.mem_append_right _ (scr_mem hp), Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_ldm rfl (inS 0 (by decide)) fun s₇ u₇ => ?_
  have h₇ := h₆.of_keep (Divide.Keep.of_upd u₇ (by simp))
  refine wp_stloc hp h₇.inv (d := j1Off) (by decide) fun s₈ i₈ v₈ o₈ g₈ m₈ => ?_
  have h₈ := h₇.store hp i₈ (d := j1Off) (by decide) (by decide) (by decide) m₈
  have e₈ : s₈.gpr .eax = s₆.gpr .eax := by rw [g₈, u₇.other _ (by decide)]
  have in₈ : InRegions (s₈.rd ++ s₈.wr) (addr (s₆.gpr .eax) (6144 + 4)) 4 := by
    rw [i₈.rd, i₈.wr, ← h₆.inv.rd, ← h₆.inv.wr]
    exact inS 4 (by decide)
  refine wp_ldm e₈ in₈ fun s₉ u₉ => ?_
  have h₉ := h₈.of_keep (Divide.Keep.of_upd u₉ (by simp))
  refine wp_stloc hp h₉.inv (d := j2Off) (by decide) fun t it vt ot gt mt => WP.block_nil ⟨?_, ?_⟩
  · exact h₉.store hp it (d := j2Off) (by decide) (by decide) (by decide) mt
  · have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    rw [vt, ot j1Off (by decide) (by decide), lw_mem u₉.mem, v₈, u₉.gpr, m₈, a₆, addr_shift,
      scr_loc hp (by decide) (by omega), u₇.gpr, a₆, addr_shift, u₇.mem, u₆.mem, m₅,
      blk_get _ _ _ _ (Nat.mod_lt _ (by decide))]
    rw [show 8 * (index % 128) + 6148 = 6144 + 8 * (index % 128) + 4 by omega,
      show 8 * (index % 128) + 6144 = 6144 + 8 * (index % 128) by omega]

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

omit hp in
/-- The cached address block is that of `c`. -/
theorem cached {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) {c : Nat} (hc : 1 ≤ c) (hc' : c < 2 ^ 32)
    (he : lw s₀ s counterOff = BitVec.ofNat 32 c) :
    blk s.mem (scrP s₀) 6144 = addressBlock (prm s₀) pass lane slice c := by
  obtain ⟨c0, c1, c2 | ⟨_, c4⟩⟩ := h.cache
  · rw [he, c2] at c1
    have := congrArg BitVec.toNat c1
    rw [Wp.toNat_ofNat_lt hc'] at this
    exact absurd this (by simp; omega)
  · rw [c4]
    rw [he] at c1
    have := congrArg BitVec.toNat c1
    rw [Wp.toNat_ofNat_lt hc', Wp.toNat_ofNat_lt c0] at this
    rw [this]

/-- `cacheCheck`: `eax :=` the counter of the index's group; ZF if it is cached. -/
theorem cacheCheck_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hi : index < (prm s₀).segmentLen) :
    WP isa (.block Impl.Argon2.X86.Derive.cacheCheck) s fun t => FS s₀ pass slice lane index ctr st t ∧
      t.gpr .eax = BitVec.ofNat 32 (index / 128 + 1) ∧
      t.zf = some (BitVec.ofNat 32 (index / 128 + 1) - lw s₀ t counterOff == 0) := by
  have sl := segLen_lt hp
  unfold Impl.Argon2.X86.Derive.cacheCheck
  refine wp_ldloc hp h.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_shr (n := 7) (by decide)
    fun s₂ u₂ _ => wp_addi fun s₃ u₃ => ?_
  have h₃ := ((h.of_keep (Divide.Keep.of_upd u₁ (by simp))).of_keep (Divide.Keep.of_upd u₂ (by simp))).of_keep
    (Divide.Keep.of_upd u₃ (by simp))
  have a₃ : s₃.gpr .eax = BitVec.ofNat 32 (index / 128 + 1) := by
    rw [u₃.gpr, u₂.gpr, u₁.gpr, h.pos.index, shr7 (by omega), show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_add_ofNat]
  refine wp_cmpm h₃.inv.ebp (loc_in' hp h₃.inv (d := counterOff) (by decide)) fun s₄ f₄ _ z₄ => WP.block_nil ?_
  exact ⟨h₃.of_keep (Divide.Keep.of_fupd f₄), by rw [f₄.gpr, a₃], by rw [z₄, a₃, lw_mem f₄.mem]⟩

/-- The address block of the index's group, regenerated unless it is cached. -/
theorem cacheFill_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h₄ : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) (a₃ : s.gpr .eax = BitVec.ofNat 32 (index / 128 + 1))
    (z₄ : s.zf = some (BitVec.ofNat 32 (index / 128 + 1) - lw s₀ s counterOff == 0)) :
    WP isa (.ite .e (.block []) (.seq (.block [Impl.Argon2.X86.Derive.st counterOff .eax])
      Impl.Argon2.X86.Derive.addressCalls)) s fun t => FS s₀ pass slice lane index (index / 128 + 1) st t ∧
      blk t.mem (scrP s₀) 6144 = addressBlock (prm s₀) pass lane slice (index / 128 + 1) := by
  have sl := segLen_lt hp
  have hlt := hp.lanes_lt
  refine WP.ite (BitVec.ofNat 32 (index / 128 + 1) - lw s₀ s counterOff == 0) z₄
    (fun hb => ?_) fun hb => ?_
  · have ce : lw s₀ s counterOff = BitVec.ofNat 32 (index / 128 + 1) := by
      have e := beq_iff_eq.mp hb
      exact ((BitVec.sub_eq_iff_eq_add.mp e).trans (by simp)).symm
    have cb := cached h₄ (c := index / 128 + 1) (by omega) (by omega) ce
    exact WP.block_nil ⟨⟨h₄.inv, h₄.pr, h₄.pos, ⟨by omega, ce, .inr ⟨by omega, cb⟩⟩, h₄.mem⟩, cb⟩
  · refine WP.seq (wp_stloc hp h₄.inv (d := counterOff) (by decide) fun s₅ i₅ v₅ o₅ g₅ m₅ => WP.block_nil ?_)
    have L₅ : ∀ d ∈ fsOffs, d ≠ counterOff → lw s₀ s₅ d = lw s₀ s d := fun d hd hd' => by
      simp only [fsOffs, List.mem_cons, List.not_mem_nil, or_false] at hd
      refine o₅ d ?_ ?_ <;>
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | exact absurd rfl hd'
    refine (addressCalls_ok hp i₅ (index := index) (c := index / 128 + 1)
      (h₄.pos.of_lw fun d hd => L₅ d (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl <;> decide))
      (by rw [v₅, a₃]) hpass (by omega) (by omega) (by omega)).mono
      fun t ⟨it, _, ft, bt⟩ => ⟨?_, bt⟩
    have fsub : ∀ r ∈ [scrR s₀, callR s₀], ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' :=
      fun r hr => ⟨r, by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp,
        fun _ h => h⟩
    have Lt : ∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s₅ d := fun d hd => lw_keep hp ft fsub hd
    refine ⟨it, Prm.of_lw h₄.pr fun d hd => ?_, h₄.pos.of_lw fun d hd => ?_, ⟨by omega,
      by rw [Lt _ (by decide), v₅, a₃], .inr ⟨by omega, bt⟩⟩, Represents.keep h₄.mem fun k hk => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rw [Lt d (by rcases hd with rfl | rfl | rfl | rfl <;> decide)]
      exact L₅ d (by simp only [fsOffs]; rcases hd with rfl | rfl | rfl | rfl <;> simp)
        (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rw [Lt d (by rcases hd with rfl | rfl | rfl | rfl <;> decide)]
      exact L₅ d (by simp only [fsOffs]; rcases hd with rfl | rfl | rfl | rfl <;> simp)
        (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
    · have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
      rw [blockAt_keep ft fun r hr => ?_, m₅, blockAt_keep (rs := [⟨addr (E s₀) counterOff, 4⟩])
        ((Frame.refl _ _).writeW (w := 32) (List.mem_singleton_self _) _ (Region.contains_self _ _)) fun r hr => ?_]
      · simp only [List.mem_singleton] at hr; subst hr
        exact (loc_disj hp (d := counterOff) (by decide) (memR s₀) (by simp)).symm.sub_left (cell_in_mem hk')
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.mem_scr.sub_left (cell_in_mem hk')
        · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left (cell_in_mem hk')

/-- `addressCache`: J₁ and J₂ from the address block of the index's group of 128. -/
theorem addressCache_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.X86.Derive.addressCache s fun t => FS s₀ pass slice lane index (index / 128 + 1) st t ∧
      lw s₀ t j2Off ++ lw s₀ t j1Off =
        (addressBlock (prm s₀) pass lane slice (index / 128 + 1))[index % 128]'(Nat.mod_lt _ (by decide)) := by
  have sl := segLen_lt hp
  unfold Impl.Argon2.X86.Derive.addressCache
  refine WP.seq ((cacheCheck_ok hp h hi).mono fun s₄ ⟨h₄, a₄, z₄⟩ => ?_)
  have M := cacheFill_ok hp h₄ hpass hl hs hi a₄ z₄
  refine WP.seq (M.mono fun t ⟨ht, bt⟩ => (cacheWord_ok hp ht (by omega)).mono fun u ⟨hu, wu⟩ => ⟨hu, ?_⟩)
  rw [wu, bt]

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `randomSource`: J₁ and J₂ are the step's random word. -/
theorem randomSource_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.X86.Derive.randomSource s fun t =>
      FS s₀ pass slice lane index (ctrNext (prm s₀) pass slice index ctr) st t ∧
      lw s₀ t j2Off ++ lw s₀ t j1Off = Proof.Argon2.FillStep.random (prm s₀) pass lane slice index st.memory := by
  unfold Impl.Argon2.X86.Derive.randomSource
  refine WP.seq ((addressMode_ok hp h.inv h.pos hpass hs).mono fun s₁ ⟨z₁, k₁⟩ => ?_)
  have h₁ := h.of_keep k₁
  refine WP.ite (!Spec.Argon2.independent (prm s₀) pass slice) z₁ (fun hb => ?_) fun hb => ?_
  · have hind : Spec.Argon2.independent (prm s₀) pass slice = false := by simpa using hb
    refine (dependentWord_ok hp h₁ hl hs hi).mono fun t ⟨ht, wt⟩ => ⟨by rw [ctrNext, hind]; exact ht, ?_⟩
    have cl := Proof.Argon2.previous_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge
      (column := slice * (prm s₀).segmentLen + index) hl
    rw [wt, k₁.mem, h.mem.block _ cl]
    unfold Proof.Argon2.FillStep.random
    rw [hind]
    rfl
  · have hind : Spec.Argon2.independent (prm s₀) pass slice = true := by simpa using hb
    refine (addressCache_ok hp h₁ hpass hl hs hi).mono fun t ⟨ht, wt⟩ => ⟨by rw [ctrNext, hind]; exact ht, ?_⟩
    rw [wt]
    unfold Proof.Argon2.FillStep.random
    rw [hind]
    rfl

end
end VG.Proof.Argon2.X86.Derive
