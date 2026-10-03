import VerifiedGarbage.Proof.Rc4.X86.Replace
import VerifiedGarbage.Proof.Rc4.Identity
import VerifiedGarbage.Proof.Rc4.Schedule
import VerifiedGarbage.Proof.Rc4.Stream

/-! # RC4 on x86 (32-bit): key scheduling -/

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Impl.Rc4.X86 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

theorem writeW_byte8 (m : Mem) (a : Addr) (v : Byte) : m.writeW a v = m.write a 1 v := by
  change m.write a 1 (v.setWidth 8) = _
  rw [BitVec.setWidth_eq]

theorem low_byte32 (b : Byte) : (b.setWidth 32).setWidth 8 = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem ofNat_low32 (r : Nat) : (BitVec.ofNat 32 r).setWidth 8 = BitVec.ofNat 8 r := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem mask255_32 (x : BitVec 32) : x &&& BitVec.ofNat 32 255 = (x.setWidth 8).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (255 % 2 ^ 32 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem byte_add32 (a b : Byte) :
    a.setWidth 32 + b.setWidth 32 &&& BitVec.ofNat 32 255 = (a + b).setWidth 32 := by
  rw [mask255_32]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega

theorem byte_add3_32 (j a k : Byte) :
    j.setWidth 32 + a.setWidth 32 + k.setWidth 32 &&& BitVec.ofNat 32 255 =
      (j + a + k).setWidth 32 := by
  rw [mask255_32]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega

theorem and_mask32 (x : BitVec 32) (p : Bool) :
    x &&& (0#32 - (BitVec.ofBool p).setWidth 32) = if p then x else 0 := by
  rw [borrow_mask32]
  cases p
  · exact BitVec.and_zero
  · exact BitVec.and_allOnes

/-- A word outside the table is unchanged by writes within the table. -/
theorem table_frame_readW {p a : Addr} {m m' : Mem} (h : TableFrame p m m')
    (hs : Mem.Sep a 4 p 256) : m'.readW a 32 = m.readW a 32 :=
  Mem.readW_congr fun i hi => h _ (hs _ (by rw [Mem.sub_ofNat_toNat a (by omega)]; exact hi))

/-! ## The identity permutation -/

def IdentityInv (s₀ : State) (r : Nat) (s : State) : Prop :=
  s.mem = identityMem s₀.mem ((s₀.gpr .edi).setWidth 64) r ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
    s.gpr .edi = s₀.gpr .edi ∧ s.gpr .esp = s₀.gpr .esp ∧ s.gpr .esi = BitVec.ofNat 32 r

theorem identity_step (s₀ s : State) {r : Nat} (hr : r < 256)
    (hfit : (s₀.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hp : InRegions s₀.wr ((s₀.gpr .edi).setWidth 64) 256) (h : IdentityInv s₀ r s) :
    WP isa (.block identityStep) s fun t => IdentityInv s₀ (r + 1) t ∧
      t.zf = some (BitVec.ofNat 32 (r + 1) - BitVec.ofNat 32 256 == 0#32) := by
  obtain ⟨hm, hrd, hwr, hdi, hsp, hsi⟩ := h
  have he : addr (s₀.gpr .edi + BitVec.ofNat 32 r) 0 =
      (s₀.gpr .edi).setWidth 64 + BitVec.ofNat 64 r := by
    have := idx_addr hfit (BitVec.ofNat 8 r)
    rwa [byte32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr] at this
  have hw : InRegions s₀.wr ((s₀.gpr .edi).setWidth 64 + BitVec.ofNat 64 r) 1 :=
    region_offset _ _ _ _ _ (by omega) (by omega) hp
  have hadd : BitVec.ofNat 32 r + BitVec.ofNat 32 1 = BitVec.ofNat 32 (r + 1) := by
    rw [← BitVec.ofNat_add]
  unfold identityStep
  rrun [hw, hm, hrd, hwr, hdi, hsp, hsi, hadd, writeW_byte8, ofNat_low32, IdentityInv, he]
  exact ⟨identityMem_store _ _ _ hr, rfl⟩

theorem identity_loop (s₀ s : State) {r : Nat} (hr : r < 256)
    (hfit : (s₀.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hp : InRegions s₀.wr ((s₀.gpr .edi).setWidth 64) 256) (h : IdentityInv s₀ r s) :
    WP isa (.loop (.block identityStep) .ne) s (IdentityInv s₀ 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ IdentityInv s₀ j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (identity_step s₀ t hj hfit hp ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    simp only [eval, hz, hend, Option.map_some]
    rfl
  · right
    have hnz : BitVec.ofNat 32 (j + 1) - BitVec.ofNat 32 256 ≠ 0#32 := by bv_omega
    refine ⟨?_, 256 - (j + 1), by omega, j + 1, by omega, rfl, hu⟩
    simp only [eval, hz, Option.map_some, beq_eq_false_iff_ne.mpr hnz, Bool.not_false]

/-! ## One round -/

theorem schedule_before (s : State) (i j : Byte) (K : BitVec 32)
    (hsi : s.gpr .esi = i.setWidth 32) (hbp : s.gpr .ebp = j.setWidth 32)
    (hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hp : InRegions (s.rd ++ s.wr) ((s.gpr .edi).setWidth 64) 256)
    (hka : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4)
    (hkv : s.mem.readW (addr (s.gpr .esp) 4) 32 = K)
    (hk : InRegions (s.rd ++ s.wr) (addr (K + s.gpr .ebx) 0) 1) :
    WP isa (.block (loadI ++ ([.alu .add .ebp (.reg .edx), .mov .edx (.mem (at_ .esp 4)),
      .alu .add .edx (.reg .ebx), .movzx8 .edx (at_ .edx 0), .alu .add .ebp (.reg .edx),
      .alu .and .ebp (imm 255)] : List Instr))) s
      fun t => t.gpr .ebp = (j + s.mem ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 i.toNat) +
          s.mem (addr (K + s.gpr .ebx) 0)).setWidth 32 ∧ Keep [.ebp, .edx] s t ∧ t.mem = s.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (loadI_ok s i hsi hfit hp) fun t ⟨tdx, tk, tm⟩ => ?_
  have tbp : t.gpr .ebp = j.setWidth 32 := (tk.gpr (by decide)).trans hbp
  have tbx : t.gpr .ebx = s.gpr .ebx := tk.gpr (by decide)
  have tsp : t.gpr .esp = s.gpr .esp := tk.gpr (by decide)
  refine WP.mono (WP.keep (Q := fun u => u.gpr .ebp = (j + s.mem ((s.gpr .edi).setWidth 64 +
      BitVec.ofNat 64 i.toNat) + s.mem (addr (K + s.gpr .ebx) 0)).setWidth 32 ∧ u.mem = s.mem)
      [.ebp, .edx] ?_ (by decide +kernel)) fun u ⟨h, hk'⟩ => ⟨h.1, ?_, h.2⟩
  · rrun [tbp, tdx, tsp, tbx, tm, tk.2.1, tk.2.2, hka, hkv, hk]
    rw [byte_add3_32]
  · exact (tk.trans hk').mono (by decide)

theorem schedule_after (s : State) (i b : Byte) (Lk : BitVec 32)
    (hsi : s.gpr .esi = i.setWidth 32) (hax : s.gpr .eax = b.setWidth 32)
    (hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions s.wr ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 i.toNat) 1)
    (hla : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4)
    (hlv : s.mem.readW (addr (s.gpr .esp) 8) 32 = Lk) :
    WP isa (.block [.alu .add .ebx (imm 1), .mov .edx (.mem (at_ .esp 8)),
      .alu .cmp .ebx (.reg .edx), .mov .edx (imm 0), .alu .sbb .edx (.reg .edx),
      .alu .and .ebx (.reg .edx), .mov .edx (.reg .edi), .alu .add .edx (.reg .esi),
      .store8 (at_ .edx 0) .al, .alu .add .esi (imm 1), .alu .cmp .esi (imm 256)]) s fun t =>
      t.mem = s.mem.write ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .ebx = (if (s.gpr .ebx + 1#32).toNat < Lk.toNat then s.gpr .ebx + 1#32 else 0#32) ∧
      t.gpr .esi = i.setWidth 32 + 1#32 ∧
      t.zf = some (i.setWidth 32 + 1#32 - BitVec.ofNat 32 256 == 0#32) ∧
      Keep [.ebx, .esi, .edx] s t := by
  have he := idx_addr hfit i
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .ebx = (if (s.gpr .ebx + 1#32).toNat < Lk.toNat then s.gpr .ebx + 1#32 else 0#32) ∧
      t.gpr .esi = i.setWidth 32 + 1#32 ∧
      t.zf = some (i.setWidth 32 + 1#32 - BitVec.ofNat 32 256 == 0#32)) [.ebx, .esi, .edx] ?_
    (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hk⟩
  rrun [hsi, hax, he, hw, hla, hlv, writeW_byte8, low_byte32, and_mask32]
  refine ⟨?_, rfl⟩
  simp only [decide_eq_true_eq]
  rfl

/-- One concrete key-scheduling round, with both swap operands read before either write. -/
theorem schedule_step (s : State) (i j : Byte) (K Lk : BitVec 32)
    (hsi : s.gpr .esi = i.setWidth 32) (hbp : s.gpr .ebp = j.setWidth 32)
    (hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hp : InRegions s.wr ((s.gpr .edi).setWidth 64) 256)
    (hka : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4)
    (hkv : s.mem.readW (addr (s.gpr .esp) 4) 32 = K)
    (hla : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4)
    (hlv : s.mem.readW (addr (s.gpr .esp) 8) 32 = Lk)
    (hk : InRegions (s.rd ++ s.wr) (addr (K + s.gpr .ebx) 0) 1)
    (hsl : Mem.Sep (addr (s.gpr .esp) 8) 4 ((s.gpr .edi).setWidth 64) 256) :
    let p := (s.gpr .edi).setWidth 64
    let a := s.mem (p + BitVec.ofNat 64 i.toNat)
    let jj := j + a + s.mem (addr (K + s.gpr .ebx) 0)
    let b := s.mem (p + BitVec.ofNat 64 jj.toNat)
    WP isa (.block scheduleStep) s fun t =>
      t.mem = (s.mem.write (p + BitVec.ofNat 64 jj.toNat) 1 a).write
        (p + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .ebx = (if (s.gpr .ebx + 1#32).toNat < Lk.toNat then s.gpr .ebx + 1#32 else 0#32) ∧
      t.gpr .ebp = jj.setWidth 32 ∧ t.gpr .esi = i.setWidth 32 + 1#32 ∧
      t.zf = some (i.setWidth 32 + 1#32 - BitVec.ofNat 32 256 == 0#32) ∧
      Keep ([.ebp, .edx] ++ [.eax, .ecx, .edx] ++ [.ebx, .esi, .edx]) s t := by
  intro p a jj b
  have hr : InRegions (s.rd ++ s.wr) p 256 := by
    obtain ⟨r, hr, hc⟩ := hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  unfold scheduleStep
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (schedule_before s i j K hsi hbp hfit hr hka hkv hk) fun t ⟨tbp, tk, tm⟩ => ?_
  have tsi : t.gpr .esi = i.setWidth 32 := (tk.gpr (by decide)).trans hsi
  have tdi : t.gpr .edi = s.gpr .edi := tk.gpr (by decide)
  have tbx : t.gpr .ebx = s.gpr .ebx := tk.gpr (by decide)
  have tsp : t.gpr .esp = s.gpr .esp := tk.gpr (by decide)
  have htp : InRegions t.wr ((t.gpr .edi).setWidth 64) 256 := by rw [tk.2.2, tdi]; exact hp
  refine WP.mono (WP.keep [.eax, .ecx, .edx]
    (replace_core t jj i tbp tsi (by rw [tdi]; exact hfit) htp) (by decide +kernel))
    fun u ⟨⟨uax, um⟩, uk⟩ => ?_
  have usi : u.gpr .esi = i.setWidth 32 := (uk.gpr (by decide)).trans tsi
  have udi : u.gpr .edi = s.gpr .edi := (uk.gpr (by decide)).trans tdi
  have ubx : u.gpr .ebx = s.gpr .ebx := (uk.gpr (by decide)).trans tbx
  have usp : u.gpr .esp = s.gpr .esp := (uk.gpr (by decide)).trans tsp
  have ubp : u.gpr .ebp = jj.setWidth 32 := (uk.gpr (by decide)).trans tbp
  rw [tm, tdi] at uax um
  have hw : InRegions u.wr ((u.gpr .edi).setWidth 64 + BitVec.ofNat 64 i.toNat) 1 := by
    rw [uk.2.2, tk.2.2, udi]
    exact region_offset _ _ _ _ _ (by have := i.isLt; omega) (by have := i.isLt; omega) hp
  have hla' : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) 8) 4 := by
    rw [uk.2.1, uk.2.2, tk.2.1, tk.2.2, usp]; exact hla
  have hlv' : u.mem.readW (addr (u.gpr .esp) 8) 32 = Lk := by
    rw [um, usp, ← hlv]
    simp only [Mem.readW, Nat.reduceDiv]
    rw [Mem.read_write_sep (sep_offset_right hsl (by have := jj.isLt; omega)
      (by have := jj.isLt; omega)) (by decide)]
  refine WP.mono (schedule_after u i b Lk usi uax (by rw [udi]; exact hfit) hw hla' hlv')
    fun v ⟨vm, vbx, vsi, vz, vk⟩ => ?_
  refine ⟨?_, ?_, (vk.gpr (by decide)).trans ubp, vsi, vz, (tk.trans uk).trans vk⟩
  · rw [vm, um, udi]
  · rw [vbx, ubx]

/-- The key bytes, at `K` (32-bit), `Lk` of them. -/
def keyOf (m : Mem) (K Lk : BitVec 32) : List Byte := bytesAt m (K.setWidth 64) Lk.toNat

structure ScheduleInv (s₀ : State) (K Lk : BitVec 32) (r : Nat) (s : State) : Prop where
  frame : TableFrame ((s₀.gpr .edi).setWidth 64) s₀.mem s.mem
  table : (contextAt s.mem ((s₀.gpr .edi).setWidth 64)).table =
    (schedulePrefix (keyOf s₀.mem K Lk) r).1
  j : s.gpr .ebp = (schedulePrefix (keyOf s₀.mem K Lk) r).2.setWidth 32
  i : s.gpr .esi = BitVec.ofNat 32 r
  off : s.gpr .ebx = BitVec.ofNat 32 (r % Lk.toNat)
  p : s.gpr .edi = s₀.gpr .edi
  sp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- What key scheduling needs of the state it starts from. -/
structure SchedulePre (s₀ : State) (K Lk : BitVec 32) : Prop where
  len : 1 ≤ Lk.toNat ∧ Lk.toNat ≤ 256
  fit : (s₀.gpr .edi).toNat + 256 ≤ 2 ^ 32
  table : InRegions s₀.wr ((s₀.gpr .edi).setWidth 64) 256
  key : InRegions (s₀.rd ++ s₀.wr) (K.setWidth 64) Lk.toNat
  keyFit : K.toNat + Lk.toNat ≤ 2 ^ 32
  keySep : Mem.Sep (K.setWidth 64) Lk.toNat ((s₀.gpr .edi).setWidth 64) 256
  ka : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) 4) 4
  kv : s₀.mem.readW (addr (s₀.gpr .esp) 4) 32 = K
  la : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) 8) 4
  lv : s₀.mem.readW (addr (s₀.gpr .esp) 8) 32 = Lk
  ks : Mem.Sep (addr (s₀.gpr .esp) 4) 4 ((s₀.gpr .edi).setWidth 64) 256
  ls : Mem.Sep (addr (s₀.gpr .esp) 8) 4 ((s₀.gpr .edi).setWidth 64) 256

theorem key_addr {K : BitVec 32} {Lk : BitVec 32} (hfit : K.toNat + Lk.toNat ≤ 2 ^ 32) {o : Nat}
    (ho : o < Lk.toNat) : addr (K + BitVec.ofNat 32 o) 0 = K.setWidth 64 + BitVec.ofNat 64 o := by
  unfold addr
  rw [BitVec.add_zero]
  exact VG.Proof.MlKem.X86.ea_off (by omega)

/-- The key offset after `r`, advanced: back to 0 at the key length. -/
theorem key_next32 (r len : Nat) (hl : 0 < len) (hlen : len ≤ 256) :
    (if (BitVec.ofNat 32 (r % len) + 1#32).toNat < len then BitVec.ofNat 32 (r % len) + 1#32
      else 0#32) = BitVec.ofNat 32 ((r + 1) % len) := by
  have hb := Nat.mod_lt r hl
  have ht : (BitVec.ofNat 32 (r % len) + 1#32).toNat = r % len + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show r % len < 2 ^ 32 by omega)]
    change (r % len + 1) % 2 ^ 32 = _
    omega
  rw [ht]
  have ha : (r + 1) % len = (r % len + 1) % len := by
    simp only [Nat.add_mod, Nat.mod_mod]
  by_cases h : r % len + 1 < len
  · rw [ite_eq_left h]
    apply BitVec.eq_of_toNat_eq
    rw [ht, BitVec.toNat_ofNat, ha, Nat.mod_eq_of_lt h,
      Nat.mod_eq_of_lt (show r % len + 1 < 2 ^ 32 by omega)]
  · rw [ite_eq_right h, ha, show r % len + 1 = len by omega, Nat.mod_self]

theorem schedule_inv_step (s₀ s : State) (K Lk : BitVec 32) {r : Nat} (hr : r < 256)
    (hpre : SchedulePre s₀ K Lk) (h : ScheduleInv s₀ K Lk r s) :
    WP isa (.block scheduleStep) s fun t => ScheduleInv s₀ K Lk (r + 1) t ∧
      t.zf = some (BitVec.ofNat 32 (r + 1) - BitVec.ofNat 32 256 == 0#32) := by
  let key := keyOf s₀.mem K Lk
  let st := schedulePrefix key r
  have hlen := hpre.len
  have hrt : (BitVec.ofNat 8 r).toNat = r := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hi : s.gpr .esi = (BitVec.ofNat 8 r).setWidth 32 := by
    rw [h.i, byte32, hrt]
  have hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32 := by rw [h.p]; exact hpre.fit
  have hpoint : InRegions s.wr ((s.gpr .edi).setWidth 64) 256 := by rw [h.wr, h.p]; exact hpre.table
  have hmod := Nat.mod_lt r (show 0 < Lk.toNat by omega)
  have hka : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4 := by
    rw [h.rd, h.wr, h.sp]; exact hpre.ka
  have hla : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4 := by
    rw [h.rd, h.wr, h.sp]; exact hpre.la
  have hkv : s.mem.readW (addr (s.gpr .esp) 4) 32 = K := by
    rw [h.sp, table_frame_readW h.frame hpre.ks]; exact hpre.kv
  have hlv : s.mem.readW (addr (s.gpr .esp) 8) 32 = Lk := by
    rw [h.sp, table_frame_readW h.frame hpre.ls]; exact hpre.lv
  have hkaddr : addr (K + s.gpr .ebx) 0 = K.setWidth 64 + BitVec.ofNat 64 (r % Lk.toNat) := by
    rw [h.off]; exact key_addr hpre.keyFit hmod
  have hkeypoint : InRegions (s.rd ++ s.wr) (addr (K + s.gpr .ebx) 0) 1 := by
    rw [h.rd, h.wr, hkaddr]
    exact region_offset _ _ _ _ _ (by omega) (by omega) hpre.key
  have hkeybyte : s.mem (addr (K + s.gpr .ebx) 0) = key.getD (r % key.length) 0 := by
    rw [hkaddr]
    have hsep := hpre.keySep (K.setWidth 64 + BitVec.ofNat 64 (r % Lk.toNat))
      (by rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hmod)
    rw [h.frame _ hsep]
    dsimp only [key, keyOf]
    rw [bytes_length, bytes_get _ _ _ _ hmod]
  have htablebyte : s.mem ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 r) = st.1.getD r 0 := by
    rw [h.p]
    have hg := table_get s.mem ((s₀.gpr .edi).setWidth 64) (BitVec.ofNat 8 r)
    rw [hrt, h.table] at hg
    exact hg.symm
  have hsl : Mem.Sep (addr (s.gpr .esp) 8) 4 ((s.gpr .edi).setWidth 64) 256 := by
    rw [h.sp, h.p]; exact hpre.ls
  refine WP.mono (schedule_step s _ _ K Lk hi h.j hfit hpoint hka hkv hla hlv hkeypoint hsl)
    fun t ⟨tm, tbx, tbp, tsi, tz, tk⟩ => ?_
  have hnext := schedule_succ key r
  dsimp only [scheduleRound] at hnext
  have hcast : (BitVec.ofNat 8 r).setWidth 32 + 1#32 = BitVec.ofNat 32 (r + 1) := by
    rw [byte32, hrt, ← BitVec.ofNat_add]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, (tk.gpr (by decide)).trans h.p, (tk.gpr (by decide)).trans h.sp,
    tk.2.1.trans h.rd, tk.2.2.trans h.wr⟩, ?_⟩
  · rw [tm, h.p]
    exact h.frame.trans (swap_frame _ _ _ _)
  · rw [tm, h.p, table_swap, h.table, hnext, hrt]
    have hb := htablebyte
    rw [h.p] at hb
    rw [hb, hkeybyte]
  · rw [tbp, hrt, htablebyte, hkeybyte, hnext]
  · rw [tsi, hcast]
  · rw [tbx, h.off]
    exact key_next32 r _ (by omega) hlen.2
  · rw [tz, hcast]

/-- All 256 scheduling rounds realize the complete specified permutation. -/
theorem schedule_loop (s₀ s : State) (K Lk : BitVec 32) {r : Nat} (hr : r < 256)
    (hpre : SchedulePre s₀ K Lk) (h : ScheduleInv s₀ K Lk r s) :
    WP isa (.loop (.block scheduleStep) .ne) s (ScheduleInv s₀ K Lk 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ ScheduleInv s₀ K Lk j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (schedule_inv_step s₀ t K Lk hj hpre ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    simp only [eval, hz, hend, Option.map_some]
    rfl
  · right
    have hnz : BitVec.ofNat 32 (j + 1) - BitVec.ofNat 32 256 ≠ 0#32 := by bv_omega
    refine ⟨?_, 256 - (j + 1), by omega, j + 1, by omega, rfl, hu⟩
    simp only [eval, hz, Option.map_some, beq_eq_false_iff_ne.mpr hnz, Bool.not_false]

end VG.Proof.Rc4.X86
