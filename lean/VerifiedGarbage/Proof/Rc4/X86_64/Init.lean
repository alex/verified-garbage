import VerifiedGarbage.Proof.Rc4.X86_64.Schedule
import VerifiedGarbage.Proof.Rc4.Stream

/-! # RC4 on x86-64: checked initialization -/

namespace VG.Proof.Rc4.X86_64
open VG VG.X86_64 VG.Impl.Rc4.X86_64 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly)

/-- Memory changed only within the 258-byte context at `p`. -/
def CtxFrame (p : Addr) (m m' : Mem) : Prop := ∀ x, ¬ (x - p).toNat < 258 → m' x = m x

theorem init_finish (s : State) (hp : InRegions s.wr (s.gpr .rdi) 258) :
    WP isa (.block [.mov .rax (imm 0), .store8 (at_ .rdi 256) .rax,
      .store8 (at_ .rdi 257) .rax]) s fun t => t.gpr .rax = 0#64 ∧
      t.mem = (s.mem.write (s.gpr .rdi + 256#64) 1 0#8).write (s.gpr .rdi + 257#64) 1 0#8 := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  rrun [h256, h257, writeW_byte8]
  rfl

theorem ctx_frame_finish (m m' : Mem) (p : Addr) (h : TableFrame p m m') (a b : Byte) :
    CtxFrame p m ((m'.write (p + 256#64) 1 a).write (p + 257#64) 1 b) := by
  intro x hx
  have h1 : x ≠ p + 256#64 := by
    intro he; apply hx; rw [he, Mem.sub_ofNat_toNat p (by decide)]; decide
  have h2 : x ≠ p + 257#64 := by
    intro he; apply hx; rw [he, Mem.sub_ofNat_toNat p (by decide)]; decide
  rw [write_byte, ite_eq_right h2, write_byte, ite_eq_right h1]
  exact h x (by omega)

theorem init_valid (s : State)
    (hlen : 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 256)
    (hp : InRegions s.wr (s.gpr .rdx) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .rdi) (s.gpr .rsi).toNat)
    (hs : Mem.Sep (s.gpr .rdi) (s.gpr .rsi).toNat (s.gpr .rdx) 256) :
    WP isa initValid s fun t => t.gpr .rax = 0#64 ∧
      contextAt t.mem (s.gpr .rdx) =
        { table := keySchedule (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat), i := 0, j := 0 } ∧
      CtxFrame (s.gpr .rdx) s.mem t.mem := by
  have hstart : WP isa (.block [.mov .rax (.reg .rdi), .mov .rdi (.reg .rdx), .mov .rdx (.reg .rsi),
      .mov .rsi (.reg .rax), .mov .rcx (imm 0)]) s fun a =>
      a.mem = s.mem ∧ a.rd = s.rd ∧ a.wr = s.wr ∧ a.gpr .rdi = s.gpr .rdx ∧
      a.gpr .rdx = s.gpr .rsi ∧ a.gpr .rsi = s.gpr .rdi ∧ a.gpr .rcx = 0#64 := by
    rrun
  unfold initValid
  refine WP.seq (WP.mono hstart fun a ha => ?_)
  obtain ⟨ham, har, haw, hadi, hadx, hasi, hacx⟩ := ha
  have hpa : InRegions a.wr (a.gpr .rdi) 256 := by
    rw [haw, hadi]
    have h' := region_offset _ _ _ 0 256 (by decide) (by decide) hp
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h'
  have hia : IdentityInv a 0 a :=
    ⟨by rw [identityMem_zero], rfl, rfl, rfl, rfl, rfl, by rw [hacx]⟩
  refine WP.seq (WP.mono (identity_loop a a (by decide) hpa hia) fun b hb => ?_)
  obtain ⟨hbm, hbr, hbw, hbdi, hbsi, hbdx, _⟩ := hb
  have hreset : WP isa (.block [.mov .rcx (imm 0), .mov .r8 (imm 0), .mov .r9 (imm 0)]) b
      fun c => c.mem = b.mem ∧ c.rd = b.rd ∧ c.wr = b.wr ∧ c.gpr .rdi = b.gpr .rdi ∧
        c.gpr .rsi = b.gpr .rsi ∧ c.gpr .rdx = b.gpr .rdx ∧ c.gpr .rcx = 0#64 ∧
        c.gpr .r8 = 0#64 ∧ c.gpr .r9 = 0#64 := by
    rrun
  refine WP.seq (WP.mono hreset fun c hc => ?_)
  obtain ⟨hcm, hcr, hcw, hcdi, hcsi, hcdx, hccx, hc8, hc9⟩ := hc
  have hlc : 1 ≤ (c.gpr .rdx).toNat ∧ (c.gpr .rdx).toNat ≤ 256 := by
    rw [hcdx, hbdx, hadx]; exact hlen
  have hpc : InRegions c.wr (c.gpr .rdi) 256 := by rw [hcw, hcdi, hbw, hbdi]; exact hpa
  have hkc : InRegions (c.rd ++ c.wr) (c.gpr .rsi) (c.gpr .rdx).toNat := by
    rw [hcr, hcw, hcsi, hcdx, hbr, hbw, hbsi, hbdx, har, haw, hasi, hadx]; exact hk
  have hsc : Mem.Sep (c.gpr .rsi) (c.gpr .rdx).toNat (c.gpr .rdi) 256 := by
    rw [hcsi, hcdx, hcdi, hbsi, hbdx, hbdi, hasi, hadx, hadi]; exact hs
  have hic : ScheduleInv c 0 c := by
    refine ⟨TableFrame.refl _ _, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · rw [hcm, hbm, hcdi, hbdi, identityMem_table, schedule_zero]
    · rw [hc9]; rfl
    · rw [hccx]
    · rw [hc8, Nat.zero_mod]
  refine WP.seq (WP.mono (schedule_loop c c (by decide) hlc hpc hkc hsc hic) fun d hd => ?_)
  have hpd : InRegions d.wr (d.gpr .rdi) 258 := by
    rw [hd.wr, hd.p, hcw, hcdi, hbw, hbdi, haw, hadi]; exact hp
  refine WP.mono (init_finish d hpd) fun e ⟨heax, hem⟩ => ?_
  have hp0 : d.gpr .rdi = s.gpr .rdx := by rw [hd.p, hcdi, hbdi, hadi]
  have hkey : keyAt c = bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat := by
    unfold keyAt
    rw [hcm, hcsi, hcdx, hbsi, hbdx, hasi, hadx, hbm, ham]
    exact bytes_table_frame _ _ _ _ _ (s.gpr .rsi).isLt
      (identityMem_frame _ _ _ (by decide)) (by rw [hadi]; exact hs)
  refine ⟨heax, ?_, ?_⟩
  · rw [hem, hp0, context_finish, ← hp0, hd.p, hd.table, ← keySchedule_eq, hkey]
    rfl
  · rw [hem, hp0]
    refine ctx_frame_finish _ _ _ ?_ _ _
    have hf := hd.frame
    rw [hcm, hbm, hcdi, hbdi, hadi, ham] at hf
    exact (identityMem_frame _ _ _ (by decide)).trans hf

theorem valid_length (len : BitVec 64) :
    (len - 1#64).toNat < 256 ↔ 1 ≤ len.toNat ∧ len.toNat ≤ 256 := by bv_omega

/-- The full checked initializer, including both key-length boundaries. -/
theorem init_ok (s : State)
    (hp : InRegions s.wr (s.gpr .rdx) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .rdi) (s.gpr .rsi).toNat)
    (hs : Mem.Sep (s.gpr .rdi) (s.gpr .rsi).toNat (s.gpr .rdx) 256) :
    WP isa VG.Impl.Rc4.X86_64.init s fun t =>
      (match VG.Spec.Rc4.init (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) with
      | .ok ctx => t.gpr .rax = 0#64 ∧ contextAt t.mem (s.gpr .rdx) = ctx
      | .error .invalidKeyLength => t.gpr .rax = 1#64) ∧
      CtxFrame (s.gpr .rdx) s.mem t.mem := by
  have hcheck : WP isa (.block [.mov .rax (.reg .rsi), .alu .sub .rax (imm 1),
      .alu .cmp .rax (imm 256)]) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .rdi = s.gpr .rdi ∧
      t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = s.gpr .rdx ∧
      t.cf = some (decide ((s.gpr .rsi - 1#64).toNat < 256)) := by
    rrun
    exact rfl
  unfold VG.Impl.Rc4.X86_64.init
  refine WP.seq (WP.mono hcheck fun t ht => ?_)
  obtain ⟨htm, htr, htw, htdi, htsi, htdx, htcf⟩ := ht
  let good := 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 256
  have hcond : isa.eval .ae t = some (decide (¬ good)) := by
    simp only [eval, htcf, Option.map_some]
    congr 1
    by_cases hg : good
    · rw [decide_eq_true ((valid_length _).mpr hg), decide_eq_false (not_not_intro hg)]
      rfl
    · rw [decide_eq_false (fun h => hg ((valid_length _).mp h)), decide_eq_true hg]
      rfl
  refine WP.ite (decide (¬ good)) hcond (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬ good := of_decide_eq_true hn
    change ¬ (1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 256) at hn'
    simp only [VG.Spec.Rc4.init, bytes_length, hn', ite_false]
    rrun [htm]
    exact fun _ _ => rfl
  · have hg : good := Classical.not_not.mp (of_decide_eq_false hy)
    change 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 256 at hg
    simp only [VG.Spec.Rc4.init, bytes_length, hg, and_self, ite_true]
    have hpt : InRegions t.wr (t.gpr .rdx) 258 := by rw [htw, htdx]; exact hp
    have hkt : InRegions (t.rd ++ t.wr) (t.gpr .rdi) (t.gpr .rsi).toNat := by
      rw [htr, htw, htdi, htsi]; exact hk
    have hst : Mem.Sep (t.gpr .rdi) (t.gpr .rsi).toNat (t.gpr .rdx) 256 := by
      rw [htdi, htsi, htdx]; exact hs
    have hlt : 1 ≤ (t.gpr .rsi).toNat ∧ (t.gpr .rsi).toNat ≤ 256 := htsi ▸ hg
    refine WP.mono (init_valid t hlt hpt hkt hst) fun u ⟨hu0, huc, huf⟩ => ?_
    simp only [htm, htdi, htsi, htdx] at huc huf
    exact ⟨⟨hu0, huc⟩, huf⟩

end VG.Proof.Rc4.X86_64
