import VerifiedGarbage.Proof.Rc4.X86_64.Init

/-! # RC4 on x86-64: one PRGA step -/

namespace VG.Proof.Rc4.X86_64
open VG VG.X86_64 VG.Impl.Rc4.X86_64 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly)

theorem byte_inc (i : Byte) :
    i.setWidth 64 + BitVec.ofNat 64 1 &&& BitVec.ofNat 64 255 = (i + 1#8).setWidth 64 := by
  have h := byte_add i 1#8
  rwa [show (1#8).setWidth 64 = BitVec.ofNat 64 1 from rfl] at h

theorem apply_before (s : State) (i j : Byte)
    (hcx : s.gpr .rcx = i.setWidth 64) (h8 : s.gpr .r8 = j.setWidth 64)
    (hp : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 256) :
    WP isa (.block [.alu .add .rcx (imm 1), .alu .and .rcx (imm 255),
      .movzx8 .r10 (atIdx .rdi .rcx), .alu .add .r8 (.reg .r10), .alu .and .r8 (imm 255),
      .mov .r9 (.reg .r8)]) s fun t =>
      t.gpr .rcx = (i + 1#8).setWidth 64 ∧
      t.gpr .r8 = (j + s.mem (s.gpr .rdi + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.gpr .r9 = (j + s.mem (s.gpr .rdi + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      Keep [.rcx, .r8, .r9, .r10] s t ∧ t.mem = s.mem := by
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .rdi + (i + 1#8).setWidth 64) 1 := by
    rw [byte_addr (i + 1#8)]
    exact region_offset _ _ _ _ _ (by have := (i + 1#8).isLt; omega)
      (by have := (i + 1#8).isLt; omega) hp
  refine WP.mono (WP.keep (Q := fun t => t.gpr .rcx = (i + 1#8).setWidth 64 ∧
      t.gpr .r8 = (j + s.mem (s.gpr .rdi + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.gpr .r9 = (j + s.mem (s.gpr .rdi + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.mem = s.mem) [.rcx, .r8, .r9, .r10] ?_ (by decide +kernel))
    fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, hk, h.2.2.2⟩
  rrun [hcx, h8, byte_inc, hi]
  rw [byte_addr (i + 1#8), byte_add]
  exact ⟨rfl, rfl⟩

theorem apply_middle (s : State) (ii b : Byte)
    (hcx : s.gpr .rcx = ii.setWidth 64) (hax : s.gpr .rax = b.setWidth 64)
    (hw : InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 ii.toNat) 1) :
    WP isa (.block [.movzx8 .r10 (atIdx .rdi .rcx), .store8 (atIdx .rdi .rcx) .rax,
      .alu .add .rax (.reg .r10), .alu .and .rax (imm 255), .mov .r9 (.reg .rax)]) s fun t =>
      t.mem = s.mem.write (s.gpr .rdi + BitVec.ofNat 64 ii.toNat) 1 b ∧
      t.gpr .r9 = (b + s.mem (s.gpr .rdi + BitVec.ofNat 64 ii.toNat)).setWidth 64 ∧
      Keep [.rax, .r9, .r10] s t := by
  have hw' : InRegions s.wr (s.gpr .rdi + ii.setWidth 64) 1 := by rw [byte_addr ii]; exact hw
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi + ii.setWidth 64) 1 := by
    obtain ⟨r, hr, hc⟩ := hw'
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .rdi + BitVec.ofNat 64 ii.toNat) 1 b ∧
      t.gpr .r9 = (b + s.mem (s.gpr .rdi + BitVec.ofNat 64 ii.toNat)).setWidth 64)
      [.rax, .r9, .r10] ?_ (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  rrun [hcx, hax, hw', hr, writeW_byte8, low_byte, byte_add]
  rw [byte_addr ii]
  exact ⟨rfl, rfl⟩

theorem low_xor (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 = a ^^^ b := by
  rw [xor_byte, low_byte]

theorem apply_after (s : State) (k : Byte) (hax : s.gpr .rax = k.setWidth 64)
    (hd : InRegions s.wr (s.gpr .rsi) 1) :
    WP isa (.block [.movzx8 .r10 (at_ .rsi 0), .alu .xor .r10 (.reg .rax),
      .store8 (at_ .rsi 0) .r10, .alu .add .rsi (imm 1), .alu .sub .rdx (imm 1)]) s fun t =>
      t.mem = s.mem.write (s.gpr .rsi) 1 (s.mem (s.gpr .rsi) ^^^ k) ∧
      t.gpr .rsi = s.gpr .rsi + 1#64 ∧ t.gpr .rdx = s.gpr .rdx - 1#64 ∧
      t.zf = some (s.gpr .rdx - 1#64 == 0#64) ∧ Keep [.rsi, .rdx, .r10] s t := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1 := by
    obtain ⟨r, hr, hc⟩ := hd
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .rsi) 1 (s.mem (s.gpr .rsi) ^^^ k) ∧
      t.gpr .rsi = s.gpr .rsi + 1#64 ∧ t.gpr .rdx = s.gpr .rdx - 1#64 ∧
      t.zf = some (s.gpr .rdx - 1#64 == 0#64)) [.rsi, .rdx, .r10] ?_ (by decide +kernel))
    fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hk⟩
  rrun [hax, hd, hr, writeW_byte8, low_xor]
  rfl

/-- One iteration, with the writes expressed against the original memory.
Both swap operands are read before either write, including for a self-swap. -/
theorem apply_step (s : State) (i j : Byte)
    (hcx : s.gpr .rcx = i.setWidth 64) (h8 : s.gpr .r8 = j.setWidth 64)
    (hp : InRegions s.wr (s.gpr .rdi) 256) (hd : InRegions s.wr (s.gpr .rsi) 1) :
    let ii := i + 1#8
    let a := s.mem (s.gpr .rdi + BitVec.ofNat 64 ii.toNat)
    let jj := j + a
    let b := s.mem (s.gpr .rdi + BitVec.ofNat 64 jj.toNat)
    let swapped := (s.mem.write (s.gpr .rdi + BitVec.ofNat 64 jj.toNat) 1 a).write
      (s.gpr .rdi + BitVec.ofNat 64 ii.toNat) 1 b
    let k := swapped (s.gpr .rdi + BitVec.ofNat 64 (a + b).toNat)
    WP isa (.block applyStep) s fun t =>
      t.mem = swapped.write (s.gpr .rsi) 1 (swapped (s.gpr .rsi) ^^^ k) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .rdi = s.gpr .rdi ∧
      t.gpr .rsi = s.gpr .rsi + 1#64 ∧ t.gpr .rdx = s.gpr .rdx - 1#64 ∧
      t.zf = some (s.gpr .rdx - 1#64 == 0#64) ∧
      t.gpr .rcx = ii.setWidth 64 ∧ t.gpr .r8 = jj.setWidth 64 := by
  intro ii a jj b swapped k
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 256 := by
    obtain ⟨r, hr, hc⟩ := hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  simp only [applyStep, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (apply_before s i j hcx h8 hr) fun t ⟨tcx, t8, t9, tk, tm⟩ => ?_
  have tdi : t.gpr .rdi = s.gpr .rdi := tk.gpr (by decide)
  have tsi : t.gpr .rsi = s.gpr .rsi := tk.gpr (by decide)
  have tdx : t.gpr .rdx = s.gpr .rdx := tk.gpr (by decide)
  have htp : InRegions t.wr (t.gpr .rdi) 256 := by rw [tk.2.2, tdi]; exact hp
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .r10, .r11] (replace_core t jj ii t9 tcx htp) (by decide +kernel))
    fun u ⟨⟨uax, um⟩, uk⟩ => ?_
  rw [tm, tdi] at uax um
  have ucx : u.gpr .rcx = ii.setWidth 64 := (uk.gpr (by decide)).trans tcx
  have u8 : u.gpr .r8 = jj.setWidth 64 := (uk.gpr (by decide)).trans t8
  have udi : u.gpr .rdi = s.gpr .rdi := (uk.gpr (by decide)).trans tdi
  have usi : u.gpr .rsi = s.gpr .rsi := (uk.gpr (by decide)).trans tsi
  have udx : u.gpr .rdx = s.gpr .rdx := (uk.gpr (by decide)).trans tdx
  have urd : u.rd = s.rd := uk.2.1.trans tk.2.1
  have uwr : u.wr = s.wr := uk.2.2.trans tk.2.2
  have hw : InRegions u.wr (u.gpr .rdi + BitVec.ofNat 64 ii.toNat) 1 := by
    rw [uwr, udi]
    exact region_offset _ _ _ _ _ (by have := ii.isLt; omega) (by have := ii.isLt; omega) hp
  rw [WP.block_append_iff]
  refine WP.mono (apply_middle u ii b ucx uax hw) fun v ⟨vm, v9, vk⟩ => ?_
  have ha : u.mem (u.gpr .rdi + BitVec.ofNat 64 ii.toNat) = a := by
    rw [um, udi, write_byte]
    split <;> rfl
  rw [ha] at v9
  rw [udi, um] at vm
  have hvm : v.mem = swapped := vm
  have v9' : v.gpr .r9 = (a + b).setWidth 64 := by rw [v9, BitVec.add_comm]
  have vdi : v.gpr .rdi = s.gpr .rdi := (vk.gpr (by decide)).trans udi
  have vrd : v.rd = s.rd := vk.2.1.trans urd
  have vwr : v.wr = s.wr := vk.2.2.trans uwr
  have hvp : InRegions (v.rd ++ v.wr) (v.gpr .rdi) 256 := by rw [vrd, vwr, vdi]; exact hr
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .r10, .r11] (lookup_core v (a + b) v9' hvp) (by decide +kernel))
    fun w ⟨⟨wax, wm⟩, wk⟩ => ?_
  rw [hvm, vdi] at wax
  have wsi : w.gpr .rsi = s.gpr .rsi := (wk.gpr (by decide)).trans ((vk.gpr (by decide)).trans usi)
  have wdx : w.gpr .rdx = s.gpr .rdx := (wk.gpr (by decide)).trans ((vk.gpr (by decide)).trans udx)
  have wdi : w.gpr .rdi = s.gpr .rdi := (wk.gpr (by decide)).trans vdi
  have wrd : w.rd = s.rd := wk.2.1.trans vrd
  have wwr : w.wr = s.wr := wk.2.2.trans vwr
  have hwd : InRegions w.wr (w.gpr .rsi) 1 := by rw [wwr, wsi]; exact hd
  refine WP.mono (apply_after w k wax hwd) fun z ⟨zm, zsi, zdx, zz, zk⟩ => ?_
  refine ⟨?_, zk.2.1.trans wrd, zk.2.2.trans wwr, (zk.gpr (by decide)).trans wdi, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [zm, wm, hvm, wsi]
  · rw [zsi, wsi]
  · rw [zdx, wdx]
  · rw [zz, wdx]
  · rw [zk.gpr (by decide), wk.gpr (by decide), vk.gpr (by decide), ucx]
  · rw [zk.gpr (by decide), wk.gpr (by decide), vk.gpr (by decide), u8]

end VG.Proof.Rc4.X86_64
