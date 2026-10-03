import VerifiedGarbage.Proof.Rc4.X86.Init

/-! # RC4 on x86 (32-bit): one PRGA step -/

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Impl.Rc4.X86 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

theorem byte_inc32 (i : Byte) :
    i.setWidth 32 + BitVec.ofNat 32 1 &&& BitVec.ofNat 32 255 = (i + 1#8).setWidth 32 := by
  have h := byte_add32 i 1#8
  rwa [show (1#8).setWidth 32 = BitVec.ofNat 32 1 from rfl] at h

theorem apply_before (s : State) (i j : Byte)
    (hsi : s.gpr .esi = i.setWidth 32) (hbp : s.gpr .ebp = j.setWidth 32)
    (hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hp : InRegions (s.rd ++ s.wr) ((s.gpr .edi).setWidth 64) 256) :
    WP isa (.block (([.alu .add .esi (imm 1), .alu .and .esi (imm 255)] : List Instr) ++ loadI ++
      ([.alu .add .ebp (.reg .edx), .alu .and .ebp (imm 255)] : List Instr))) s fun t =>
      t.gpr .esi = (i + 1#8).setWidth 32 ∧
      t.gpr .ebp = (j + s.mem ((s.gpr .edi).setWidth 64 +
        BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 32 ∧
      Keep (([.esi] : List Reg) ++ ([.edx] : List Reg) ++ ([.ebp] : List Reg)) s t ∧ t.mem = s.mem := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep (Q := fun t => t.gpr .esi = (i + 1#8).setWidth 32 ∧ t.mem = s.mem)
    [.esi] (by rrun [hsi, byte_inc32]) (by decide +kernel)) fun t ⟨⟨tsi, tm⟩, tk⟩ => ?_
  have hft : (t.gpr .edi).toNat + 256 ≤ 2 ^ 32 := by rw [tk.gpr (by decide)]; exact hfit
  have hpt : InRegions (t.rd ++ t.wr) ((t.gpr .edi).setWidth 64) 256 := by
    rw [tk.2.1, tk.2.2, tk.gpr (by decide)]; exact hp
  refine WP.mono (loadI_ok t (i + 1#8) tsi hft hpt) fun u ⟨udx, uk, um⟩ => ?_
  have ubp : u.gpr .ebp = j.setWidth 32 := (uk.gpr (by decide)).trans ((tk.gpr (by decide)).trans hbp)
  rw [tm, tk.gpr (r := .edi) (by decide)] at udx
  refine WP.mono (WP.keep (Q := fun v => v.gpr .ebp = (j + s.mem ((s.gpr .edi).setWidth 64 +
      BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 32 ∧ v.mem = u.mem) [.ebp]
    (by rrun [ubp, udx]; rw [byte_add32]) (by decide +kernel)) fun v ⟨⟨vbp, vm⟩, vk⟩ => ?_
  exact ⟨(vk.gpr (by decide)).trans ((uk.gpr (by decide)).trans tsi), vbp,
    (tk.trans uk).trans vk, vm.trans (um.trans tm)⟩

theorem apply_middle (s : State) (ii a b jj : Byte) (Sc : BitVec 32)
    (hsi : s.gpr .esi = ii.setWidth 32) (hax : s.gpr .eax = b.setWidth 32)
    (hdx : s.gpr .edx = a.setWidth 32) (hbp : s.gpr .ebp = jj.setWidth 32)
    (hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32) (hSfit : Sc.toNat + 64 ≤ 2 ^ 32)
    (hw : InRegions s.wr ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 ii.toNat) 1)
    (hw16 : InRegions s.wr (Sc.setWidth 64 + BitVec.ofNat 64 16) 4)
    (ha16 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4)
    (hv16 : (s.mem.write ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 ii.toNat) 1 b).readW
      (addr (s.gpr .esp) 16) 32 = Sc) :
    WP isa (.block [.mov .ecx (.reg .edi), .alu .add .ecx (.reg .esi), .store8 (at_ .ecx 0) .al,
      .alu .add .eax (.reg .edx), .alu .and .eax (imm 255),
      .mov .edx (.mem (at_ .esp 16)), .store (at_ .edx 16) .ebp, .mov .ebp (.reg .eax)]) s
      fun t => t.mem = (s.mem.write ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 ii.toNat) 1 b).writeW
          (Sc.setWidth 64 + BitVec.ofNat 64 16) (jj.setWidth 32) ∧
        t.gpr .ebp = (b + a).setWidth 32 ∧ Keep [.eax, .ecx, .edx, .ebp] s t := by
  have he := idx_addr hfit ii
  have h16 : addr Sc 16 = Sc.setWidth 64 + BitVec.ofNat 64 16 := save_addr hSfit (by decide)
  have hr16 : InRegions ((s.rd ++ s.wr)) (addr (s.gpr .esp) 16) 4 := ha16
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = (s.mem.write ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 ii.toNat) 1 b).writeW
          (Sc.setWidth 64 + BitVec.ofNat 64 16) (jj.setWidth 32) ∧
        t.gpr .ebp = (b + a).setWidth 32) [.eax, .ecx, .edx, .ebp] ?_ (by decide +kernel))
    fun t ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  rrun [hsi, hax, hdx, hbp, he, hw, writeW_byte8, low_byte32, hr16, hv16, h16, hw16, byte_add32]

theorem low_xor32 (a b : Byte) : (a.setWidth 32 ^^^ b.setWidth 32).setWidth 8 = a ^^^ b := by
  rw [xor_byte32, low_byte32]

theorem apply_after (s : State) (k : Byte) (Sc D L : BitVec 32) (n : Nat)
    (hax : s.gpr .eax = k.setWidth 32) (hbx : s.gpr .ebx = BitVec.ofNat 32 n)
    (hSfit : Sc.toNat + 64 ≤ 2 ^ 32) (hDfit : D.toNat + n < 2 ^ 32)
    (ha16 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4)
    (hv16 : s.mem.readW (addr (s.gpr .esp) 16) 32 = Sc)
    (hr16 : InRegions (s.rd ++ s.wr) (Sc.setWidth 64 + BitVec.ofNat 64 16) 4)
    (ha8 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4)
    (hv8 : s.mem.readW (addr (s.gpr .esp) 8) 32 = D)
    (hd : InRegions s.wr (D.setWidth 64 + BitVec.ofNat 64 n) 1)
    (ha12 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 12) 4)
    (hv12 : ∀ v, (s.mem.write (D.setWidth 64 + BitVec.ofNat 64 n) 1 v).readW
      (addr (s.gpr .esp) 12) 32 = L) :
    WP isa (.block [.mov .edx (.mem (at_ .esp 16)), .mov .ebp (.mem (at_ .edx 16)),
      .mov .edx (.mem (at_ .esp 8)), .alu .add .edx (.reg .ebx), .movzx8 .ecx (at_ .edx 0),
      .alu .xor .ecx (.reg .eax), .store8 (at_ .edx 0) .cl,
      .alu .add .ebx (imm 1), .mov .edx (.mem (at_ .esp 12)), .alu .cmp .ebx (.reg .edx)]) s
      fun t => t.mem = s.mem.write (D.setWidth 64 + BitVec.ofNat 64 n) 1
          (s.mem (D.setWidth 64 + BitVec.ofNat 64 n) ^^^ k) ∧
        t.gpr .ebp = s.mem.readW (Sc.setWidth 64 + BitVec.ofNat 64 16) 32 ∧
        t.gpr .ebx = BitVec.ofNat 32 (n + 1) ∧
        t.zf = some (BitVec.ofNat 32 (n + 1) - L == 0#32) ∧ Keep [.ecx, .edx, .ebx, .ebp] s t := by
  have h16 : addr Sc 16 = Sc.setWidth 64 + BitVec.ofNat 64 16 := save_addr hSfit (by decide)
  have hdn : addr (D + BitVec.ofNat 32 n) 0 = D.setWidth 64 + BitVec.ofNat 64 n := by
    unfold addr
    rw [BitVec.add_zero]
    exact VG.Proof.MlKem.X86.ea_off hDfit
  have hdr : InRegions (s.rd ++ s.wr) (D.setWidth 64 + BitVec.ofNat 64 n) 1 := by
    obtain ⟨r, hr, hc⟩ := hd
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hadd : BitVec.ofNat 32 n + BitVec.ofNat 32 1 = BitVec.ofNat 32 (n + 1) := by
    rw [← BitVec.ofNat_add]
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (D.setWidth 64 + BitVec.ofNat 64 n) 1
          (s.mem (D.setWidth 64 + BitVec.ofNat 64 n) ^^^ k) ∧
        t.gpr .ebp = s.mem.readW (Sc.setWidth 64 + BitVec.ofNat 64 16) 32 ∧
        t.gpr .ebx = BitVec.ofNat 32 (n + 1) ∧
        t.zf = some (BitVec.ofNat 32 (n + 1) - L == 0#32)) [.ecx, .edx, .ebx, .ebp] ?_
    (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hk⟩
  rrun [hax, hbx, ha16, hv16, h16, hr16, ha8, hv8, hdn, hdr, hd, writeW_byte8, low_xor32, hadd,
    ha12, hv12]
  rfl

/-- What a step of the stream function needs of its state: the table at `P`,
the `L` bytes of data at `D`, `scratch` at `Sc`, the arguments readable and
apart from what the step writes. -/
structure StepEnv (s : State) (P D L Sc : BitVec 32) : Prop where
  p : s.gpr .edi = P
  pfit : P.toNat + 258 ≤ 2 ^ 32
  sfit : Sc.toNat + 64 ≤ 2 ^ 32
  dfit : D.toNat + L.toNat ≤ 2 ^ 32
  table : InRegions s.wr (P.setWidth 64) 256
  spill : InRegions s.wr (Sc.setWidth 64 + BitVec.ofNat 64 16) 4
  data : InRegions s.wr (D.setWidth 64) L.toNat
  a8 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4
  a12 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 12) 4
  a16 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4
  v8 : s.mem.readW (addr (s.gpr .esp) 8) 32 = D
  v12 : s.mem.readW (addr (s.gpr .esp) 12) 32 = L
  v16 : s.mem.readW (addr (s.gpr .esp) 16) 32 = Sc
  s8T : Mem.Sep (addr (s.gpr .esp) 8) 4 (P.setWidth 64) 256
  s12T : Mem.Sep (addr (s.gpr .esp) 12) 4 (P.setWidth 64) 256
  s16T : Mem.Sep (addr (s.gpr .esp) 16) 4 (P.setWidth 64) 256
  s8S : Mem.Sep (addr (s.gpr .esp) 8) 4 (Sc.setWidth 64 + BitVec.ofNat 64 16) 4
  s12S : Mem.Sep (addr (s.gpr .esp) 12) 4 (Sc.setWidth 64 + BitVec.ofNat 64 16) 4
  s16S : Mem.Sep (addr (s.gpr .esp) 16) 4 (Sc.setWidth 64 + BitVec.ofNat 64 16) 4
  s8D : Mem.Sep (addr (s.gpr .esp) 8) 4 (D.setWidth 64) L.toNat
  s12D : Mem.Sep (addr (s.gpr .esp) 12) 4 (D.setWidth 64) L.toNat
  s16D : Mem.Sep (addr (s.gpr .esp) 16) 4 (D.setWidth 64) L.toNat
  sTS : Mem.Sep (P.setWidth 64) 256 (Sc.setWidth 64 + BitVec.ofNat 64 16) 4
  sTD : Mem.Sep (P.setWidth 64) 256 (D.setWidth 64) L.toNat
  sSD : Mem.Sep (Sc.setWidth 64 + BitVec.ofNat 64 16) 4 (D.setWidth 64) L.toNat

/-- A word apart from two byte writes. -/
theorem readW_write2 {m : Mem} {a q₁ q₂ : Addr} {v₁ v₂ : Byte} (h₁ : Mem.Sep a 4 q₁ 1)
    (h₂ : Mem.Sep a 4 q₂ 1) : ((m.write q₁ 1 v₁).write q₂ 1 v₂).readW a 32 = m.readW a 32 := by
  simp only [Mem.readW, Nat.reduceDiv]
  rw [Mem.read_write_sep h₂ (by decide), Mem.read_write_sep h₁ (by decide)]

theorem readW_writeW_sep4 {m : Mem} {a q : Addr} {v : BitVec 32} (h : Mem.Sep a 4 q 4) :
    (m.writeW q v).readW a 32 = m.readW a 32 := Mem.readW_writeW_sep h (by decide)

theorem readW_write1 {m : Mem} {a q : Addr} {v : Byte} (h : Mem.Sep a 4 q 1) :
    (m.write q 1 v).readW a 32 = m.readW a 32 := by
  simp only [Mem.readW, Nat.reduceDiv]
  rw [Mem.read_write_sep h (by decide)]

/-- One iteration, with the writes expressed against the original memory.
Both swap operands are read before either write, including for a self-swap. -/
theorem apply_step (s : State) (i j : Byte) (P D L Sc : BitVec 32) (n : Nat)
    (hsi : s.gpr .esi = i.setWidth 32) (hbp : s.gpr .ebp = j.setWidth 32)
    (hbx : s.gpr .ebx = BitVec.ofNat 32 n) (hn : n < L.toNat) (he : StepEnv s P D L Sc) :
    let p := P.setWidth 64
    let ii := i + 1#8
    let a := s.mem (p + BitVec.ofNat 64 ii.toNat)
    let jj := j + a
    let b := s.mem (p + BitVec.ofNat 64 jj.toNat)
    let swapped := (s.mem.write (p + BitVec.ofNat 64 jj.toNat) 1 a).write
      (p + BitVec.ofNat 64 ii.toNat) 1 b
    let m₂ := swapped.writeW (Sc.setWidth 64 + BitVec.ofNat 64 16) (jj.setWidth 32)
    let k := swapped (p + BitVec.ofNat 64 (a + b).toNat)
    WP isa (.block applyStep) s fun t =>
      t.mem = m₂.write (D.setWidth 64 + BitVec.ofNat 64 n) 1
        (m₂ (D.setWidth 64 + BitVec.ofNat 64 n) ^^^ k) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .edi = P ∧ t.gpr .esp = s.gpr .esp ∧
      t.gpr .esi = ii.setWidth 32 ∧ t.gpr .ebp = jj.setWidth 32 ∧
      t.gpr .ebx = BitVec.ofNat 32 (n + 1) ∧
      t.zf = some (BitVec.ofNat 32 (n + 1) - L == 0#32) := by
  intro p ii a jj b swapped m₂ k
  have hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32 := by rw [he.p]; have := he.pfit; omega
  have hp : InRegions s.wr ((s.gpr .edi).setWidth 64) 256 := by rw [he.p]; exact he.table
  have hr : InRegions (s.rd ++ s.wr) ((s.gpr .edi).setWidth 64) 256 := by
    obtain ⟨r, hr, hc⟩ := hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hrP : InRegions (s.rd ++ s.wr) (P.setWidth 64) 256 := by
    obtain ⟨r, hr, hc⟩ := he.table
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have argT {o : Nat} (h : Mem.Sep (addr (s.gpr .esp) o) 4 p 256) (x : Byte) :
      Mem.Sep (addr (s.gpr .esp) o) 4 (p + BitVec.ofNat 64 x.toNat) 1 :=
    sep_offset_right h (by have := x.isLt; omega) (by have := x.isLt; omega)
  simp only [applyStep, List.append_assoc]
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff]
  refine WP.mono (apply_before s i j hsi hbp hfit hr) fun t ⟨tsi, tbp, tk, tm⟩ => ?_
  rw [he.p] at tbp
  have tdi : t.gpr .edi = P := (tk.gpr (by decide)).trans he.p
  have tsp : t.gpr .esp = s.gpr .esp := tk.gpr (by decide)
  have tbx : t.gpr .ebx = BitVec.ofNat 32 n := (tk.gpr (by decide)).trans hbx
  have htp : InRegions t.wr ((t.gpr .edi).setWidth 64) 256 := by rw [tk.2.2, tdi]; exact he.table
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.eax, .ecx, .edx]
    (replace_core t jj ii tbp tsi (by rw [tdi]; have := he.pfit; omega) htp) (by decide +kernel))
    fun u ⟨⟨uax, um⟩, uk⟩ => ?_
  rw [tm, tdi] at uax um
  have usi : u.gpr .esi = ii.setWidth 32 := (uk.gpr (by decide)).trans tsi
  have udi : u.gpr .edi = P := (uk.gpr (by decide)).trans tdi
  have usp : u.gpr .esp = s.gpr .esp := (uk.gpr (by decide)).trans tsp
  have ubp : u.gpr .ebp = jj.setWidth 32 := (uk.gpr (by decide)).trans tbp
  have ubx : u.gpr .ebx = BitVec.ofNat 32 n := (uk.gpr (by decide)).trans tbx
  have urd : u.rd = s.rd := uk.2.1.trans tk.2.1
  have uwr : u.wr = s.wr := uk.2.2.trans tk.2.2
  rw [WP.block_append_iff]
  refine WP.mono (loadI_ok u ii usi (by rw [udi]; have := he.pfit; omega)
    (by rw [urd, uwr, udi]; exact hrP)) fun v ⟨vdx, vk, vm⟩ => ?_
  have ha : u.mem (p + BitVec.ofNat 64 ii.toNat) = a := by
    rw [um, write_byte]
    split <;> rfl
  rw [udi, ha] at vdx
  have vax : v.gpr .eax = b.setWidth 32 := (vk.gpr (by decide)).trans uax
  have vsi : v.gpr .esi = ii.setWidth 32 := (vk.gpr (by decide)).trans usi
  have vbp : v.gpr .ebp = jj.setWidth 32 := (vk.gpr (by decide)).trans ubp
  have vdi : v.gpr .edi = P := (vk.gpr (by decide)).trans udi
  have vsp : v.gpr .esp = s.gpr .esp := (vk.gpr (by decide)).trans usp
  have vrd : v.rd = s.rd := vk.2.1.trans urd
  have vwr : v.wr = s.wr := vk.2.2.trans uwr
  rw [WP.block_append_iff]
  have hw : InRegions v.wr ((v.gpr .edi).setWidth 64 + BitVec.ofNat 64 ii.toNat) 1 := by
    rw [vwr, vdi]
    exact region_offset _ _ _ _ _ (by have := ii.isLt; omega) (by have := ii.isLt; omega) he.table
  refine WP.mono (apply_middle v ii a b jj Sc vsi vax vdx vbp (by rw [vdi]; have := he.pfit; omega)
    he.sfit hw (by rw [vwr]; exact he.spill) (by rw [vrd, vwr, vsp]; exact he.a16)
    (by rw [vm, um, vsp, vdi, readW_write2 (argT he.s16T jj) (argT he.s16T ii)]; exact he.v16))
    fun w ⟨wm, wbp, wk⟩ => ?_
  rw [vm, um, vdi] at wm
  have hwm : w.mem = m₂ := wm
  have wdi : w.gpr .edi = P := (wk.gpr (by decide)).trans vdi
  have wsp : w.gpr .esp = s.gpr .esp := (wk.gpr (by decide)).trans vsp
  have wsi : w.gpr .esi = ii.setWidth 32 := (wk.gpr (by decide)).trans vsi
  have wbx : w.gpr .ebx = BitVec.ofNat 32 n :=
    (wk.gpr (by decide)).trans ((vk.gpr (by decide)).trans ubx)
  have wrd : w.rd = s.rd := wk.2.1.trans vrd
  have wwr : w.wr = s.wr := wk.2.2.trans vwr
  have wbp' : w.gpr .ebp = (a + b).setWidth 32 := by rw [wbp, BitVec.add_comm]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.eax, .ecx, .edx] (lookup_core w (a + b) wbp'
    (by rw [wdi]; have := he.pfit; omega) (by rw [wrd, wwr, wdi]; exact hrP))
    (by decide +kernel)) fun x ⟨⟨xax, xm⟩, xk⟩ => ?_
  have hk : w.mem ((w.gpr .edi).setWidth 64 + BitVec.ofNat 64 (a + b).toNat) = k := by
    rw [hwm, wdi]
    apply Mem.write_apply
    exact he.sTS _ (by rw [Mem.sub_ofNat_toNat _ (by omega)]; exact (a + b).isLt)
  rw [hk] at xax
  have xsp : x.gpr .esp = s.gpr .esp := (xk.gpr (by decide)).trans wsp
  have xrd : x.rd = s.rd := xk.2.1.trans wrd
  have xwr : x.wr = s.wr := xk.2.2.trans wwr
  have hm2 (o : Nat) (hT : Mem.Sep (addr (s.gpr .esp) o) 4 p 256)
      (hS : Mem.Sep (addr (s.gpr .esp) o) 4 (Sc.setWidth 64 + BitVec.ofNat 64 16) 4) :
      m₂.readW (addr (s.gpr .esp) o) 32 = s.mem.readW (addr (s.gpr .esp) o) 32 := by
    rw [readW_writeW_sep4 hS, readW_write2 (argT hT jj) (argT hT ii)]
  have hdn : n < L.toNat := hn
  refine WP.mono (apply_after x k Sc D L n xax ((xk.gpr (by decide)).trans wbx) he.sfit
    (by have := he.dfit; omega)
    (by rw [xrd, xwr, xsp]; exact he.a16) (by rw [xm, hwm, xsp, hm2 16 he.s16T he.s16S]; exact he.v16)
    (by rw [xrd, xwr]; obtain ⟨r, hr', hc⟩ := he.spill; exact ⟨r, List.mem_append_right _ hr', hc⟩)
    (by rw [xrd, xwr, xsp]; exact he.a8) (by rw [xm, hwm, xsp, hm2 8 he.s8T he.s8S]; exact he.v8)
    (by rw [xwr]; exact region_offset _ _ _ _ _ (by omega) (by omega) he.data)
    (by rw [xrd, xwr, xsp]; exact he.a12)
    (fun v => by
      rw [xm, hwm, xsp, readW_write1 (sep_offset_right he.s12D (by omega) (by omega)),
        hm2 12 he.s12T he.s12S]
      exact he.v12)) fun y ⟨ym, ybp, ybx, yz, yk⟩ => ?_
  refine ⟨by rw [ym, xm, hwm], yk.2.1.trans xrd, yk.2.2.trans xwr,
    (yk.gpr (by decide)).trans ((xk.gpr (by decide)).trans wdi), (yk.gpr (by decide)).trans xsp,
    (yk.gpr (by decide)).trans ((xk.gpr (by decide)).trans wsi), ?_, ybx, yz⟩
  rw [ybp, xm, hwm]
  exact Mem.readW_writeW_self32 _ _ _

end VG.Proof.Rc4.X86
