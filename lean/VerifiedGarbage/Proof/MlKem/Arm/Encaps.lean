import VerifiedGarbage.Proof.MlKem.Arm.Encrypt

/-!
# ML-KEM-768 on 32-bit ARM: `vg_mlkem768_encaps`, correctness

The buffers of the function (`lay`): `scratch` (the argument on the stack),
the stack below the stack pointer, `ek`, `key` and `ct`; `m`, which may
overlap `ek`, is only read by its copy into `scratch`, with a layout of its
own (`layM`). What every phase keeps (`EnEnv`), and the phases: the setup, `m`
copied, `H(ek)`, `G(m ‖ H(ek))` into `K ‖ r`, `K` copied into `key`, and
K-PKE.Encrypt (`Enc.encrypt_ok`) into `ct`.
-/

namespace VG.Proof.MlKem.Arm.Encaps

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Enc

section
variable (s₀ : State)

def pEk : BitVec 32 := s₀.gpr .r0
def pM : BitVec 32 := s₀.gpr .r1
def pKey : BitVec 32 := s₀.gpr .r2
def pCt : BitVec 32 := s₀.gpr .r3
def pScr : BitVec 32 := stackArg s₀ 0

/-- The buffers: `scratch`, the 8 bytes below the stack pointer, `ek`, `key` and `ct`. -/
def lay : Lay :=
  ⟨fun i => [pScr s₀, s₀.sp - BitVec.ofNat 32 8, pEk s₀, pKey s₀, pCt s₀].getD i 0, [32768, 8, 1184, 32, 1088]⟩

/-- The buffers of the copy of `m`: `scratch`, the stack and `m`. -/
def layM : Lay := ⟨fun i => [pScr s₀, s₀.sp - BitVec.ofNat 32 8, pM s₀].getD i 0, [32768, 8, 32]⟩

end

theorem lay_sizes (s₀ : State) : (lay s₀).sizes = [32768, 8, 1184, 32, 1088] := rfl

theorem layM_sizes (s₀ : State) : (layM s₀).sizes = [32768, 8, 32] := rfl

theorem lay_ptr0 (s₀ : State) : (lay s₀).ptr 0 = pScr s₀ := rfl
theorem layM_ptr0 (s₀ : State) : (layM s₀).ptr 0 = pScr s₀ := rfl

/-- Decides a fact about the offsets in the buffers. -/
macro "edecide" : tactic => `(tactic| first | decide | (simp only [lay_sizes]; decide))

/-- The precondition of the contract. -/
structure Pre (s : State) : Prop where
  sp8 : 8 ≤ s.sp.toNat
  spf : s.sp.toNat + 4 ≤ 2 ^ 32
  rd : s.rd = [⟨State.addr (pEk s), 1184⟩, ⟨State.addr (pM s), 32⟩, ⟨stackArgAddr s 0, 4⟩]
  wr : s.wr = [⟨State.addr (pKey s), 32⟩, ⟨State.addr (pCt s), 1088⟩, ⟨State.addr (pScr s), 32768⟩]
  d_ek_key : (⟨State.addr (pEk s), 1184⟩ : Region).Disjoint ⟨State.addr (pKey s), 32⟩
  d_ek_ct : (⟨State.addr (pEk s), 1184⟩ : Region).Disjoint ⟨State.addr (pCt s), 1088⟩
  d_ek_scr : (⟨State.addr (pEk s), 1184⟩ : Region).Disjoint ⟨State.addr (pScr s), 32768⟩
  d_m_key : (⟨State.addr (pM s), 32⟩ : Region).Disjoint ⟨State.addr (pKey s), 32⟩
  d_m_ct : (⟨State.addr (pM s), 32⟩ : Region).Disjoint ⟨State.addr (pCt s), 1088⟩
  d_m_scr : (⟨State.addr (pM s), 32⟩ : Region).Disjoint ⟨State.addr (pScr s), 32768⟩
  d_key_ct : (⟨State.addr (pKey s), 32⟩ : Region).Disjoint ⟨State.addr (pCt s), 1088⟩
  d_key_scr : (⟨State.addr (pKey s), 32⟩ : Region).Disjoint ⟨State.addr (pScr s), 32768⟩
  d_key_arg : (⟨State.addr (pKey s), 32⟩ : Region).Disjoint ⟨stackArgAddr s 0, 4⟩
  d_ct_scr : (⟨State.addr (pCt s), 1088⟩ : Region).Disjoint ⟨State.addr (pScr s), 32768⟩
  d_ct_arg : (⟨State.addr (pCt s), 1088⟩ : Region).Disjoint ⟨stackArgAddr s 0, 4⟩
  d_scr_arg : (⟨State.addr (pScr s), 32768⟩ : Region).Disjoint ⟨stackArgAddr s 0, 4⟩
  b_ek : (below s 8).Disjoint ⟨State.addr (pEk s), 1184⟩
  b_m : (below s 8).Disjoint ⟨State.addr (pM s), 32⟩
  b_key : (below s 8).Disjoint ⟨State.addr (pKey s), 32⟩
  b_ct : (below s 8).Disjoint ⟨State.addr (pCt s), 1088⟩
  b_scr : (below s 8).Disjoint ⟨State.addr (pScr s), 32768⟩
  b_arg : (below s 8).Disjoint ⟨stackArgAddr s 0, 4⟩
  f_ek : (pEk s).toNat + 1184 ≤ 2 ^ 32
  f_m : (pM s).toNat + 32 ≤ 2 ^ 32
  f_key : (pKey s).toNat + 32 ≤ 2 ^ 32
  f_ct : (pCt s).toNat + 1088 ≤ 2 ^ 32
  f_scr : (pScr s).toNat + 32768 ≤ 2 ^ 32

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem stack_eq : (⟨State.addr (s₀.sp - BitVec.ofNat 32 8), 8⟩ : Region) = below s₀ 8 := by
  rw [addr_sub hp.sp8]

theorem stack_fit : (s₀.sp - BitVec.ofNat 32 8).toNat + 8 ≤ 2 ^ 32 := by
  have := hp.sp8; have := s₀.sp.isLt; bv_omega

theorem lay_ok : (lay s₀).Ok := by
  have es := stack_eq hp
  refine Lay.ok_of (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simp only [lay, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · exact hp.f_scr
    · exact stack_fit hp
    · exact hp.f_ek
    · exact hp.f_key
    · exact hp.f_ct
  · simp only [lay, List.length_cons, List.length_nil] at hi hj
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
    simp only [lay, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · rw [es]; exact hp.b_scr.symm
    · exact hp.d_ek_scr.symm
    · exact hp.d_key_scr.symm
    · exact hp.d_ct_scr.symm
    · rw [es]; exact hp.b_ek
    · rw [es]; exact hp.b_key
    · rw [es]; exact hp.b_ct
    · exact hp.d_ek_key
    · exact hp.d_ek_ct
    · exact hp.d_key_ct

theorem layM_ok : (layM s₀).Ok := by
  have es := stack_eq hp
  refine Lay.ok_of (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simp only [layM, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hp.f_scr
    · exact stack_fit hp
    · exact hp.f_m
  · simp only [layM, List.length_cons, List.length_nil] at hi hj
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
    rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl <;>
    simp only [layM, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · rw [es]; exact hp.b_scr.symm
    · exact hp.d_m_scr.symm
    · rw [es]; exact hp.b_m

end

/-- What every phase keeps: the pointers, our caller's registers in
`scratch`, and `ek`. -/
structure EnEnv (s₀ s : State) : Prop where
  ctx : Ctx (lay s₀) s
  r4 : s.gpr .r4 = pEk s₀
  r6 : s.gpr .r6 = pKey s₀
  r8 : s.gpr .r8 = pCt s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  sav : Saved s.mem ((lay s₀).A 0 840) s₀.gpr
  savlr : s.mem.readW ((lay s₀).A 0 872) 32 = s₀.gpr .lr
  ek : bytesAt s.mem ((lay s₀).A 2 0) 1184 = bytesAt s₀.mem ((lay s₀).A 2 0) 1184

/-- A region the phases may change: apart from the saved registers and `ek`. -/
def okW (w : Nat × Nat × Nat) : Bool := sepB [32768, 8, 1184, 32, 1088] (0, 840, 36) w &&
  sepB [32768, 8, 1184, 32, 1088] (2, 0, 1184) w

theorem EnEnv.keep {s₀ s s' : State} (hp : Pre s₀) (h : EnEnv s₀ s) {xs : List Reg} {W : List (Nat × Nat × Nat)}
    (hk : KeptX xs ((lay s₀).RL W) s s') (hx : ∀ r ∈ [Reg.r4, .r6, .r7, .r8], r ∉ xs) (hW : W.all okW = true) :
    EnEnv s₀ s' := by
  have hL := lay_ok hp
  have h1 : sepAll (lay s₀).sizes (0, 840, 36) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [okW, Bool.and_eq_true] at this; exact this.1
  have h2 : sepAll (lay s₀).sizes (2, 0, 1184) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [okW, Bool.and_eq_true] at this; exact this.2
  have hd := Lay.disjAll hL h1
  have hc : (Lay.R (lay s₀) 0 840 36).Contains ((lay s₀).A 0 872) 4 := by
    simp only [Region.Contains]; bv_omega
  refine ⟨hk.ctx (by simp at hx; exact hx.2.2.1) h.ctx, ?_, ?_, ?_, hk.rd.trans h.rd, hk.wr.trans h.wr,
    hk.sp.trans h.sp, fun i hi => ?_, ?_, ?_⟩
  · rw [hk.cs .r4 (by decide) (by decide) (hx .r4 (by simp)), h.r4]
  · rw [hk.cs .r6 (by decide) (by decide) (hx .r6 (by simp)), h.r6]
  · rw [hk.cs .r8 (by decide) (by decide) (hx .r8 (by simp)), h.r8]
  · rw [hk.frame.readW (r := Lay.R (lay s₀) 0 840 36) (by simp only [Region.Contains]; bv_omega) hd (by decide)]
    exact h.sav i hi
  · rw [hk.frame.readW hc hd (by decide)]; exact h.savlr
  · rw [Lay.bytes_keep hL hk.frame h2 (by decide)]; exact h.ek

theorem buf_wr {s₀ : State} (hp : Pre s₀) :
    (lay s₀).buf 0 ∈ s₀.wr ∧ (lay s₀).buf 3 ∈ s₀.wr ∧ (lay s₀).buf 4 ∈ s₀.wr ∧
      (lay s₀).buf 2 ∈ s₀.rd ++ s₀.wr ∧ (layM s₀).buf 2 ∈ s₀.rd ++ s₀.wr ∧ (layM s₀).buf 0 ∈ s₀.wr := by
  rw [hp.wr, hp.rd]; simp [Lay.buf, lay, layM]

/-! ## The setup -/

theorem ldrSp_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block [.ldrSp .r12 0]) s₀ fun s => s.gpr .r12 = pScr s₀ ∧
      (∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r) ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp := by
  have hin : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 0)) 4 := by
    refine ⟨⟨stackArgAddr s₀ 0, 4⟩, by rw [hp.rd]; simp, ?_⟩
    exact Region.contains_self _ _
  have o0 : (0 : Nat) < 4096 := by decide
  run_block [hin, o0]
  refine ⟨rfl, fun r hr => ?_, trivial⟩
  show (if r = .r12 then _ else s₀.gpr r) = s₀.gpr r
  exact ite_eq_right hr

theorem setup_ok {s₀ s₁ : State} (hp : Pre s₀) (h12 : s₁.gpr .r12 = pScr s₀)
    (hr : ∀ r, r ≠ .r12 → s₁.gpr r = s₀.gpr r) (hm : s₁.mem = s₀.mem) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr)
    (hsp : s₁.sp = s₀.sp) :
    WP isa (.block encapsSetup) s₁ fun s => EnEnv s₀ s ∧ s.gpr .r5 = pM s₀ ∧
      bytesAt s.mem ((layM s₀).A 2 0) 32 = bytesAt s₀.mem ((layM s₀).A 2 0) 32 := by
  have hL := lay_ok hp
  have fc := hp.f_scr
  obtain ⟨w0, -, -, -, -, -⟩ := buf_wr hp
  have wS : ∀ {o n : Nat}, o + n ≤ 32768 → InRegions s₁.wr ((lay s₀).A 0 o) n := fun h => by
    rw [hwr]; exact Lay.covers w0 h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [encapsSetup, WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r12 (off := 840) (by decide) (by rw [h12]; exact fit_le (by decide) fc) fun i hi => by
    rw [h12, add_ofNat_add]; exact wS (by omega)) fun s₂ h₂ => ?_
  have g12 : s₂.gpr .r12 = pScr s₀ := by rw [h₂.gpr, h12]
  have e872 : State.addr (s₂.gpr .r12 + BitVec.ofNat 32 (oSave + 32)) = (lay s₀).A 0 872 := by
    rw [g12]; exact addr_add (by offs)
  have i872 : InRegions s₂.wr (State.addr (s₂.gpr .r12 + BitVec.ofNat 32 (oSave + 32))) 4 := by
    rw [e872, h₂.wr]; exact wS (by decide)
  have o1 : oSave + 32 < 4096 := by decide
  run_block [i872, o1]
  have ne1 : ∀ i < 8, ∀ (m : Mem) (v : BitVec 32), (m.writeW ((lay s₀).A 0 872) v).readW
      ((lay s₀).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 = m.readW ((lay s₀).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 :=
    fun i hi m v => Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by decide)
  have g : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr' => by rw [h₂.gpr, hr r hr']
  have hne : ∀ i < 8, savedRegs.getD i Reg.r4 ≠ Reg.r12 := by decide
  have fr₀ : Frame ((lay s₀).RL [(0, 840, 36)]) s₀.mem s₂.mem := by
    rw [← hm]
    refine h₂.frame.sub fun r hr' => ⟨Lay.R (lay s₀) 0 840 36, by simp, ?_⟩
    rw [List.mem_singleton] at hr'; subst hr'
    show Region.Sub ⟨State.addr (s₁.gpr .r12) + BitVec.ofNat 64 840, 32⟩ _
    rw [h12, ← lay_ptr0]
    exact Lay.R_sub_R hL (by simp [lay]) (by decide) (by decide) (by simp [lay])
  have c872 : ((lay s₀).R 0 840 36).Contains ((lay s₀).A 0 872) 4 := by
    simp only [Region.Contains]; bv_omega
  refine ⟨⟨⟨hL, Nat.le_refl _, rfl, by simp [lay], ?_, by show 8 ≤ s₂.sp.toNat; rw [h₂.sp, hsp]; exact hp.sp8, ?_, ?_⟩,
    ?_, ?_, ?_, h₂.rd.trans hrd, h₂.wr.trans hwr, h₂.sp.trans hsp, fun i hi => ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [h₂.gpr, h12]; rfl
  · show s₀.sp - BitVec.ofNat 32 8 = s₂.sp - BitVec.ofNat 32 8
    rw [h₂.sp, hsp]
  · show (⟨State.addr (pScr s₀), 32768⟩ : Region) ∈ s₂.wr
    rw [h₂.wr, hwr, hp.wr]; simp
  · simp [g .r0 (by decide)]; rfl
  · simp [g .r2 (by decide)]; rfl
  · simp [g .r3 (by decide)]; rfl
  · show (s₂.mem.writeW _ _).readW _ _ = _
    rw [e872, ne1 i hi]
    have := h₂.saved i hi
    rw [h12] at this
    exact this.trans (hr _ (hne i hi))
  · show (s₂.mem.writeW _ _).readW _ _ = _
    rw [e872, Mem.readW_writeW_self32, h₂.gpr, hr .lr (by decide)]
  · show bytesAt (s₂.mem.writeW _ _) _ _ = _
    rw [e872]
    exact Lay.bytes_keep hL (fr₀.writeW (List.mem_singleton_self _) _ c872) (by edecide) (by decide)
  · simp [g .r1 (by decide)]; rfl
  · show bytesAt (s₂.mem.writeW _ _) _ _ = _
    rw [e872]
    have fM : Frame ((layM s₀).RL [(0, 840, 36)]) s₀.mem (s₂.mem.writeW ((lay s₀).A 0 872) (s₂.gpr .lr)) := by
      have := fr₀.writeW (List.mem_singleton_self _) (s₂.gpr .lr) c872
      simpa only [Lay.RL, List.map_cons, List.map_nil, Lay.R, lay_ptr0, layM_ptr0] using this
    exact Lay.bytes_keep (layM_ok hp) fM (by rw [layM_sizes]; decide) (by decide)


/-! ## `m` copied -/

/-- `m`. -/
abbrev M (s₀ : State) : List Byte := bytesAt s₀.mem ((layM s₀).A 2 0) 32

/-- `ek`. -/
abbrev EK (s₀ : State) : List Byte := bytesAt s₀.mem ((lay s₀).A 2 0) 1184

theorem layA0 (s₀ : State) (o : Nat) : (layM s₀).A 0 o = (lay s₀).A 0 o := by
  simp only [Lay.A, lay_ptr0, layM_ptr0]

theorem copyM_ok {s₀ s : State} (hp : Pre s₀) (h : EnEnv s₀ s) (h5 : s.gpr .r5 = pM s₀)
    (hm : bytesAt s.mem ((layM s₀).A 2 0) 32 = M s₀) :
    WP isa (copy .r5 0 .r7 oMsg 32) s fun s' =>
      EnEnv s₀ s' ∧ bytesAt s'.mem ((lay s₀).A 0 oMsg) 32 = M s₀ := by
  obtain ⟨-, -, -, -, wM, wM0⟩ := buf_wr hp
  refine WP.mono (copyL (layM_ok hp) (i := 2) (j := 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h5
    (by rw [h.ctx.r7, lay_ptr0, layM_ptr0]) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [layM_sizes]; decide) (by rw [h.rd, h.wr]; exact wM) (by rw [h.wr]; exact wM0)) fun s' ⟨k, e⟩ => ⟨?_, ?_⟩
  · have k' : Kept ((lay s₀).RL [(0, oMsg, 32)]) s s' := by
      simpa only [Lay.RL, List.map_cons, List.map_nil, Lay.R, lay_ptr0, layM_ptr0] using k
    exact h.keep hp (k'.x []) (by simp) (by decide)
  · rw [← layA0, e, hm]

theorem ptr5_ok {s : State} :
    WP isa (.block [ptrTo .r5 .r7 oMsg]) s fun s' =>
      KeptX [.r5] [] s s' ∧ s'.gpr .r5 = s.gpr .r7 + BitVec.ofNat 32 oMsg ∧ s'.mem = s.mem := by
  have e1 : encodable (BitVec.ofNat 32 oMsg) = true := by decide
  run_block [ptrTo, e1]
  refine ⟨⟨fun r _ _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, trivial⟩
  show (if r = .r5 then _ else s.gpr r) = s.gpr r
  exact ite_eq_right (fun e : r = .r5 => hx (by rw [e]; exact List.mem_singleton_self _))

/-! ## The hashes -/

/-- The buffer of each pointer register. -/
def eidx : Reg → Nat
  | .r4 => 2 | .r6 => 3 | .r8 => 4 | _ => 0

theorem pieceE {s₀ s : State} (hp : Pre s₀) (h : EnEnv s₀ s) {p : Piece} {w : Bool}
    (hb : p.base = .r4 ∨ p.base = .r7) (hw : w = true → p.base = .r7)
    (hoe : encodable (BitVec.ofNat 32 p.off) = true) (hle : encodable (BitVec.ofNat 32 p.len) = true)
    (hpos : 0 < p.len) (hlt : p.off + p.len < 2 ^ 32)
    (hsep : sepAll [32768, 8, 1184, 32, 1088] (eidx p.base, p.off, p.len) kRegs = true) :
    PieceOk (lay s₀) eidx s w p := by
  obtain ⟨w0, -, -, w2, -, -⟩ := buf_wr hp
  rw [← h.wr] at w0
  rw [← h.wr, ← h.rd] at w2
  refine ⟨?_, ?_, hoe, hle, hpos, hlt, hsep, ?_⟩
  · rcases hb with e | e <;> rw [e] <;> decide
  · rcases hb with e | e <;> rw [e]
    · exact h.r4
    · exact h.ctx.r7
  · cases w
    · simp only [Bool.false_eq_true, ite_false]
      rcases hb with e | e <;> rw [e]
      · exact w2
      · exact mem_rd_wr w0
    · simp only [ite_true]
      rw [hw rfl]; exact w0

theorem hashH_ok {s₀ s : State} (hp : Pre s₀) (h : EnEnv s₀ s) :
    WP isa (hash 136 0x06 [⟨.r4, 0, 1184⟩] [⟨.r7, oHek, 32⟩]) s fun s' =>
      EnEnv s₀ s' ∧ Frame ((lay s₀).RL (kRegs ++ [(0, oHek, 32)])) s.mem s'.mem ∧ s'.gpr .r5 = s.gpr .r5 ∧
      bytesAt s'.mem ((lay s₀).A 0 oHek) 32 = H (EK s₀) := by
  have hin : ∀ p ∈ [(⟨.r4, 0, 1184⟩ : Piece)], PieceOk (lay s₀) eidx s false p := by
    intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
    exact pieceE hp h (.inl rfl) (by simp) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hout : ∀ p ∈ [(⟨.r7, oHek, 32⟩ : Piece)], PieceOk (lay s₀) eidx s true p := by
    intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
    exact pieceE hp h (.inr rfl) (fun _ => rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine WP.mono (hash_ok (idx := eidx) VG.Proof.MlKem.rate136 (by decide) (by decide) (by decide) h.ctx
    (List.cons_ne_nil _ _) hin hout (List.pairwise_singleton _ _)) fun s' ⟨k, o⟩ =>
    ⟨h.keep hp (k.x []) (by simp) (by decide), k.frame, k.cs .r5 (by decide) (by decide), ?_⟩
  have e := o.1
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at e
  refine e.trans ?_
  show _ = H (EK s₀)
  have ek : bytesAt s.mem ((lay s₀).A 2 0) 1184 = EK s₀ := h.ek
  rw [VG.Proof.MlKem.H_eq, ← ek]; rfl

theorem hashG_ok {s₀ s : State} (hp : Pre s₀) (h : EnEnv s₀ s)
    (hm : bytesAt s.mem ((lay s₀).A 0 oMsg) 32 = M s₀) (hh : bytesAt s.mem ((lay s₀).A 0 oHek) 32 = H (EK s₀)) :
    WP isa (hash 72 0x06 [⟨.r7, oMsg, 32⟩, ⟨.r7, oHek, 32⟩] [⟨.r7, oG, 64⟩]) s fun s' =>
      EnEnv s₀ s' ∧ Frame ((lay s₀).RL (kRegs ++ [(0, oG, 64)])) s.mem s'.mem ∧ s'.gpr .r5 = s.gpr .r5 ∧
      bytesAt s'.mem ((lay s₀).A 0 oG) 32 = (G (M s₀ ++ H (EK s₀))).1 ∧
      bytesAt s'.mem ((lay s₀).A 0 oSigma) 32 = (G (M s₀ ++ H (EK s₀))).2 := by
  have hin : ∀ p ∈ [(⟨.r7, oMsg, 32⟩ : Piece), ⟨.r7, oHek, 32⟩], PieceOk (lay s₀) eidx s false p := by
    intro p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact pieceE hp h (.inr rfl) (by simp) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact pieceE hp h (.inr rfl) (by simp) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hout : ∀ p ∈ [(⟨.r7, oG, 64⟩ : Piece)], PieceOk (lay s₀) eidx s true p := by
    intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
    exact pieceE hp h (.inr rfl) (fun _ => rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hin' : (List.map ((lay s₀).pb eidx s.mem) [⟨.r7, oMsg, 32⟩, ⟨.r7, oHek, 32⟩]).flatten =
      M s₀ ++ H (EK s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    show bytesAt s.mem ((lay s₀).A 0 oMsg) 32 ++ bytesAt s.mem ((lay s₀).A 0 oHek) 32 = _
    rw [hm, hh]
  refine WP.mono (hash_ok VG.Proof.MlKem.rate72 (by decide) (by decide) (by decide) h.ctx (List.cons_ne_nil _ _)
    hin hout (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ => ⟨?_, k'.frame, k'.cs .r5 (by decide) (by decide), ?_⟩
  · exact h.keep hp (k'.x []) (by simp) (by decide)
  · have e1 := o'.1
    rw [hin'] at e1
    have e2 : bytesAt s'.mem ((lay s₀).A 0 oG) 64 = (G (M s₀ ++ H (EK s₀))).1 ++ (G (M s₀ ++ H (EK s₀))).2 :=
      e1.trans (G_split _)
    rw [show (64 : Nat) = 32 + 32 from rfl, bytesAt_add] at e2
    have l1 : (bytesAt s'.mem ((lay s₀).A 0 oG) 32).length = (G (M s₀ ++ H (EK s₀))).1.length := by
      rw [bytesAt_length, VG.Proof.MlKem.G_fst_length]
    obtain ⟨r1, r2⟩ := List.append_inj e2 l1
    refine ⟨r1, ?_⟩
    show bytesAt s'.mem (State.addr ((lay s₀).ptr 0) + BitVec.ofNat 64 (888 + 32)) 32 = _
    rw [← add_ofNat_add]; exact r2

theorem copyK_ok {s₀ s : State} (hp : Pre s₀) (h : EnEnv s₀ s) :
    WP isa (copy .r7 oG .r6 0 32) s fun s' => EnEnv s₀ s' ∧ Kept ((lay s₀).RL [(3, 0, 32)]) s s' ∧
      bytesAt s'.mem ((lay s₀).A 3 0) 32 = bytesAt s.mem ((lay s₀).A 0 oG) 32 := by
  obtain ⟨w0, w3, -, -, -, -⟩ := buf_wr hp
  exact WP.mono (copyL (lay_ok hp) (i := 0) (j := 3) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h.ctx.r7 h.r6
    (by decide) (by decide) (by decide) (by decide) (by decide) (by edecide)
    (by rw [h.rd, h.wr]; exact mem_rd_wr w0) (by rw [h.wr]; exact w3)) fun s' ⟨k, e⟩ =>
    ⟨h.keep hp (k.x []) (by simp) (by decide), k, e⟩

/-! ## K-PKE.Encrypt -/

/-- The buffers of `encrypt`: `ek`, the copy of `m`, and `ct`. -/
abbrev eb : EB := ⟨2, 0, 0, oMsg, 4, 0⟩

theorem encPre {s₀ s : State} (hp : Pre s₀) (h : EnEnv s₀ s) (h5 : s.gpr .r5 = (lay s₀).ptr 0 + BitVec.ofNat 32 oMsg) :
    EncPre (lay s₀) eb s := by
  obtain ⟨w0, -, w4, w2, -, -⟩ := buf_wr hp
  exact ⟨h.ctx, by rw [h.r4, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero]; rfl, h5,
    by rw [h.r8, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero]; rfl, by edecide, by edecide, by edecide,
    by rw [h.rd, h.wr]; exact w2, by rw [h.rd, h.wr]; exact mem_rd_wr w0, by rw [h.wr]; exact w4⟩

theorem encW_ok : (encW eb).all okW = true ∧ sepAll [32768, 8, 1184, 32, 1088] (3, 0, 32) (encW eb) = true := by
  decide


/-! ## The phases, from the copy of `m` on -/

section
variable (s₀ : State)

/-- `K`, the first output of `G(m ‖ H(ek))`. -/
abbrev KK : List Byte := (G (M s₀ ++ H (EK s₀))).1

/-- `r`, the second output of `G(m ‖ H(ek))`. -/
abbrev RR : List Byte := (G (M s₀ ++ H (EK s₀))).2

/-- After the copy of `m`, with its pointer in `r5`. -/
abbrev F4 (s : State) : Prop := EnEnv s₀ s ∧ s.gpr .r5 = (lay s₀).ptr 0 + BitVec.ofNat 32 oMsg ∧
  bytesAt s.mem ((lay s₀).A 0 oMsg) 32 = M s₀

end

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem s4_ok {s : State} (h : EnEnv s₀ s) (hm : bytesAt s.mem ((lay s₀).A 0 oMsg) 32 = M s₀) :
    WP isa (.block [ptrTo .r5 .r7 oMsg]) s (F4 s₀) :=
  WP.mono ptr5_ok fun _ ⟨k, g5, m⟩ =>
    ⟨h.keep hp (W := []) k (by simp) rfl, by rw [g5, h.ctx.r7], by rw [m]; exact hm⟩

theorem s5_ok {s : State} (h : F4 s₀ s) :
    WP isa (hash 136 0x06 [⟨.r4, 0, 1184⟩] [⟨.r7, oHek, 32⟩]) s fun s' =>
      F4 s₀ s' ∧ bytesAt s'.mem ((lay s₀).A 0 oHek) 32 = H (EK s₀) :=
  WP.mono (hashH_ok hp h.1) fun _ ⟨e, f, g5, hh⟩ =>
    ⟨⟨e, by rw [g5, h.2.1], (Lay.bytes_keep (lay_ok hp) f (by edecide) (by decide)).trans h.2.2⟩, hh⟩

theorem s6_ok {s : State} (h : F4 s₀ s ∧ bytesAt s.mem ((lay s₀).A 0 oHek) 32 = H (EK s₀)) :
    WP isa (hash 72 0x06 [⟨.r7, oMsg, 32⟩, ⟨.r7, oHek, 32⟩] [⟨.r7, oG, 64⟩]) s fun s' =>
      F4 s₀ s' ∧ bytesAt s'.mem ((lay s₀).A 0 oG) 32 = KK s₀ ∧ bytesAt s'.mem ((lay s₀).A 0 oSigma) 32 = RR s₀ :=
  WP.mono (hashG_ok hp h.1.1 h.1.2.2 h.2) fun _ ⟨e, f, g5, k, r⟩ =>
    ⟨⟨e, by rw [g5, h.1.2.1], (Lay.bytes_keep (lay_ok hp) f (by edecide) (by decide)).trans h.1.2.2⟩, k, r⟩

theorem s7_ok {s : State}
    (h : F4 s₀ s ∧ bytesAt s.mem ((lay s₀).A 0 oG) 32 = KK s₀ ∧ bytesAt s.mem ((lay s₀).A 0 oSigma) 32 = RR s₀) :
    WP isa (copy .r7 oG .r6 0 32) s fun s' =>
      F4 s₀ s' ∧ bytesAt s'.mem ((lay s₀).A 3 0) 32 = KK s₀ ∧ bytesAt s'.mem ((lay s₀).A 0 oSigma) 32 = RR s₀ :=
  WP.mono (copyK_ok hp h.1.1) fun _ ⟨e, k, key⟩ =>
    ⟨⟨e, by rw [k.cs .r5 (by decide) (by decide), h.1.2.1],
      (Lay.bytes_keep (lay_ok hp) k.frame (by edecide) (by decide)).trans h.1.2.2⟩, key.trans h.2.1,
      (Lay.bytes_keep (lay_ok hp) k.frame (by edecide) (by decide)).trans h.2.2⟩

theorem s8_ok {s : State}
    (h : F4 s₀ s ∧ bytesAt s.mem ((lay s₀).A 3 0) 32 = KK s₀ ∧ bytesAt s.mem ((lay s₀).A 0 oSigma) 32 = RR s₀) :
    WP isa encrypt s fun s' => EnEnv s₀ s' ∧ bytesAt s'.mem ((lay s₀).A 3 0) 32 = KK s₀ ∧
      s'.gpr .r11 = (if okEnc (ekRho mlKem768 (EK s₀)) 3 then 1 else 0) ∧
      bytesAt s'.mem ((lay s₀).A 4 0) 1088 =
        VG.Proof.MlKem.ct768 (aEnc (ekRho mlKem768 (EK s₀)) (RR s₀)) (EK s₀) (M s₀) (RR s₀) := by
  have eρ : ρE (lay s₀) eb s = ekRho mlKem768 (EK s₀) := by
    show ekRho mlKem768 (bytesAt s.mem ((lay s₀).A 2 0) 1184) = _
    rw [h.1.1.ek]
  have er : rB (lay s₀) s = RR s₀ := h.2.2
  have e1 : ekB (lay s₀) eb s = EK s₀ := h.1.1.ek
  have e2 : mB (lay s₀) eb s = M s₀ := h.1.2.2
  refine WP.mono (encrypt_ok (encPre hp h.1.1 h.1.2.1)) fun s' ⟨K, r11, ct⟩ =>
    ⟨h.1.1.keep hp K (by simp) encW_ok.1, (Lay.bytes_keep (lay_ok hp) K.frame encW_ok.2 (by decide)).trans h.2.1,
      ?_, ?_⟩
  · rw [r11]; show (if okEnc (ρE (lay s₀) eb s) 3 = true then _ else _) = _; rw [eρ]
  · rw [e1, e2] at ct
    show _ = VG.Proof.MlKem.ct768 (aEnc (ekRho mlKem768 (EK s₀)) (RR s₀)) (EK s₀) (M s₀) (RR s₀)
    rw [← eρ, ← er]; exact ct

end

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa encaps s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      s.gpr .r0 = (if okEnc (ekRho mlKem768 (EK s₀)) 3 then 1 else 0) ∧
      bytesAt s.mem (State.addr (pKey s₀)) 32 = KK s₀ ∧
      bytesAt s.mem (State.addr (pCt s₀)) 1088 =
        VG.Proof.MlKem.ct768 (aEnc (ekRho mlKem768 (EK s₀)) (RR s₀)) (EK s₀) (M s₀) (RR s₀) := by
  refine WP.seq (WP.mono (ldrSp_ok hp) fun s₁ ⟨a, b, c, d, e, f⟩ => ?_)
  refine WP.seq (WP.mono (setup_ok hp a b c d e f) fun s₂ ⟨h₂, g5, m₂⟩ => ?_)
  refine WP.seq (WP.mono (copyM_ok hp h₂ g5 m₂) fun s₃ ⟨h₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono (s4_ok hp h₃ m₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (s5_ok hp h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (s6_ok hp h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (s7_ok hp h₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (s8_ok hp h₇) fun s₈ ⟨h₈, key₈, r11₈, ct₈⟩ => ?_)
  refine WP.mono (topEnd_ok h₈.ctx h₈.sav h₈.savlr) fun s ⟨pr, r0, m', sp'⟩ =>
    ⟨pr, sp'.trans h₈.sp, by rw [r0, r11₈], ?_, ?_⟩
  · rw [m', show State.addr (pKey s₀) = (lay s₀).A 3 0 by simp only [Lay.A, add_ofNat_zero]; rfl]
    exact key₈
  · rw [m', show State.addr (pCt s₀) = (lay s₀).A 4 0 by simp only [Lay.A, add_ofNat_zero]; rfl]
    exact ct₈

end VG.Proof.MlKem.Arm.Encaps
