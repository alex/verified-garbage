import VerifiedGarbage.Proof.MlKem1024.Arm.RowSum

/-!
# ML-KEM-1024 on 32-bit ARM: `vg_mlkem1024_keygen`, correctness

The buffers of the function (`lay`): `scratch`, the stack, `seed`, `ek` and
`dk`; what every phase keeps (`KEnv`: the pointers, our caller's registers in
`scratch`, the seed); and the phases: the setup, `G(d ‖ 4)` into `ρ` and `σ`,
the `PRF`s into `ŝ` and `ê`, the rows of `t̂ = Â ∘ ŝ + ê` encoded into `ek`,
`ŝ` encoded into `dk`, the copies of `ρ`, `ek` and `z`, and `H(ek)`.
-/

namespace VG.Proof.MlKem1024.Arm.KeyGen

open VG VG.Arm VG.Impl.MlKem.Arm VG.Impl.MlKem1024.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.Arm VG.Proof.MlKem1024.Arm

section
variable (s₀ : State)

abbrev pSeed : BitVec 32 := s₀.gpr .r0
abbrev pEk : BitVec 32 := s₀.gpr .r1
abbrev pDk : BitVec 32 := s₀.gpr .r2
abbrev pScr : BitVec 32 := s₀.gpr .r3

/-- The buffers: `scratch`, the 8 bytes below the stack pointer, `seed`,
`ek` and `dk`. -/
def lay : Lay :=
  ⟨fun i => [pScr s₀, s₀.sp - BitVec.ofNat 32 8, pSeed s₀, pEk s₀, pDk s₀].getD i 0, [49152, 8, 64, 1568, 3168]⟩

end

theorem lay_sizes (s₀ : State) : (lay s₀).sizes = [49152, 8, 64, 1568, 3168] := rfl

/-- Decides a fact about the offsets in the buffers. -/
macro "ldecide" : tactic => `(tactic| first | decide | (simp only [lay_sizes]; decide))

/-- The precondition of the contract. -/
structure Pre (s₀ : State) : Prop where
  sp8 : 8 ≤ s₀.sp.toNat
  rd : s₀.rd = [⟨State.addr (pSeed s₀), 64⟩]
  wr : s₀.wr = [⟨State.addr (pEk s₀), 1568⟩, ⟨State.addr (pDk s₀), 3168⟩, ⟨State.addr (pScr s₀), 49152⟩]
  d_se : (⟨State.addr (pSeed s₀), 64⟩ : Region).Disjoint ⟨State.addr (pEk s₀), 1568⟩
  d_sd : (⟨State.addr (pSeed s₀), 64⟩ : Region).Disjoint ⟨State.addr (pDk s₀), 3168⟩
  d_ss : (⟨State.addr (pSeed s₀), 64⟩ : Region).Disjoint ⟨State.addr (pScr s₀), 49152⟩
  d_ed : (⟨State.addr (pEk s₀), 1568⟩ : Region).Disjoint ⟨State.addr (pDk s₀), 3168⟩
  d_es : (⟨State.addr (pEk s₀), 1568⟩ : Region).Disjoint ⟨State.addr (pScr s₀), 49152⟩
  d_ds : (⟨State.addr (pDk s₀), 3168⟩ : Region).Disjoint ⟨State.addr (pScr s₀), 49152⟩
  b_s : (below s₀ 8).Disjoint ⟨State.addr (pSeed s₀), 64⟩
  b_e : (below s₀ 8).Disjoint ⟨State.addr (pEk s₀), 1568⟩
  b_d : (below s₀ 8).Disjoint ⟨State.addr (pDk s₀), 3168⟩
  b_c : (below s₀ 8).Disjoint ⟨State.addr (pScr s₀), 49152⟩
  f_s : (pSeed s₀).toNat + 64 ≤ 2 ^ 32
  f_e : (pEk s₀).toNat + 1568 ≤ 2 ^ 32
  f_d : (pDk s₀).toNat + 3168 ≤ 2 ^ 32
  f_c : (pScr s₀).toNat + 49152 ≤ 2 ^ 32

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem stack_eq : (⟨State.addr (s₀.sp - BitVec.ofNat 32 8), 8⟩ : Region) = below s₀ 8 := by
  rw [addr_sub hp.sp8]

theorem lay_ok : (lay s₀).Ok := by
  have es := stack_eq hp
  refine Lay.ok_of (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simp only [lay, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · exact hp.f_c
    · show (s₀.sp - BitVec.ofNat 32 8).toNat + 8 ≤ 2 ^ 32
      have := hp.sp8; have := s₀.sp.isLt; bv_omega
    · exact hp.f_s
    · exact hp.f_e
    · exact hp.f_d
  · simp only [lay, List.length_cons, List.length_nil] at hi hj
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
    simp only [lay, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · rw [es]; exact hp.b_c.symm
    · exact hp.d_ss.symm
    · exact hp.d_es.symm
    · exact hp.d_ds.symm
    · rw [es]; exact hp.b_s
    · rw [es]; exact hp.b_e
    · rw [es]; exact hp.b_d
    · exact hp.d_se
    · exact hp.d_sd
    · exact hp.d_ed

end

/-- What every phase keeps: the pointers, our caller's registers in
`scratch`, and the seed. -/
structure KEnv (s₀ s : State) : Prop where
  ctx : Ctx (lay s₀) s
  r4 : s.gpr .r4 = pSeed s₀
  r5 : s.gpr .r5 = pEk s₀
  r6 : s.gpr .r6 = pDk s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  sav : Saved s.mem ((lay s₀).A 0 840) s₀.gpr
  savlr : s.mem.readW ((lay s₀).A 0 872) 32 = s₀.gpr .lr
  seed : bytesAt s.mem ((lay s₀).A 2 0) 64 = bytesAt s₀.mem ((lay s₀).A 2 0) 64

/-- A region the phases may change: apart from the saved registers and the seed. -/
def okW (w : Nat × Nat × Nat) : Bool := sepB [49152, 8, 64, 1568, 3168] (0, 840, 36) w &&
  sepB [49152, 8, 64, 1568, 3168] (2, 0, 64) w

theorem KEnv.keep {s₀ s s' : State} (hp : Pre s₀) (h : KEnv s₀ s) {xs : List Reg} {W : List (Nat × Nat × Nat)}
    (hk : KeptX xs ((lay s₀).RL W) s s') (hx : ∀ r ∈ [Reg.r4, .r5, .r6, .r7], r ∉ xs) (hW : W.all okW = true) :
    KEnv s₀ s' := by
  have hL := lay_ok hp
  have h1 : sepAll (lay s₀).sizes (0, 840, 36) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [okW, Bool.and_eq_true] at this; exact this.1
  have h2 : sepAll (lay s₀).sizes (2, 0, 64) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [okW, Bool.and_eq_true] at this; exact this.2
  have hd := Lay.disjAll hL h1
  have hc : (Lay.R (lay s₀) 0 840 36).Contains ((lay s₀).A 0 872) 4 := by
    simp only [Region.Contains]; bv_omega
  refine ⟨hk.ctx (by simp at hx; exact hx.2.2.2) h.ctx, ?_, ?_, ?_, hk.rd.trans h.rd, hk.wr.trans h.wr,
    hk.sp.trans h.sp, fun i hi => ?_, ?_, ?_⟩
  · rw [hk.cs .r4 (by decide) (by decide) (hx .r4 (by simp)), h.r4]
  · rw [hk.cs .r5 (by decide) (by decide) (hx .r5 (by simp)), h.r5]
  · rw [hk.cs .r6 (by decide) (by decide) (hx .r6 (by simp)), h.r6]
  · rw [hk.frame.readW (r := Lay.R (lay s₀) 0 840 36) (by simp only [Region.Contains]; bv_omega) hd (by decide)]
    exact h.sav i hi
  · rw [hk.frame.readW hc hd (by decide)]; exact h.savlr
  · rw [Lay.bytes_keep hL hk.frame h2 (by decide)]; exact h.seed

theorem buf_wr {s₀ : State} (hp : Pre s₀) :
    (lay s₀).buf 0 ∈ s₀.wr ∧ (lay s₀).buf 3 ∈ s₀.wr ∧ (lay s₀).buf 4 ∈ s₀.wr ∧ (lay s₀).buf 2 ∈ s₀.rd ++ s₀.wr := by
  rw [hp.wr, hp.rd]; simp [Lay.buf, lay]

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block kgSetup4) s₀ fun s => KEnv s₀ s ∧ s.mem ((lay s₀).A 0 oK) = 4 := by
  have hL := lay_ok hp
  have fc := hp.f_c
  obtain ⟨w0, -, -, -⟩ := buf_wr hp
  have wS : ∀ {o n : Nat}, o + n ≤ 49152 → InRegions s₀.wr ((lay s₀).A 0 o) n := fun h =>
    Lay.covers w0 h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [kgSetup4, WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r3 (off := 840) (by decide) (fit_le (by decide) fc) fun i hi => by
    rw [add_ofNat_add]; exact wS (by omega)) fun s₁ h₁ => ?_
  have g3 : s₁.gpr .r3 = pScr s₀ := by rw [h₁.gpr]
  have e872 : State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (oSave + 32)) = (lay s₀).A 0 872 := by
    rw [g3]; exact addr_add (by offs4)
  have e1152 : State.addr (s₁.gpr .r3 + BitVec.ofNat 32 oK) = (lay s₀).A 0 1152 := by
    rw [g3]; exact addr_add (by offs4)
  have i872 : InRegions s₁.wr (State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (oSave + 32))) 4 := by
    rw [e872, h₁.wr]; exact wS (by decide)
  have i1152 : InRegions s₁.wr (State.addr (s₁.gpr .r3 + BitVec.ofNat 32 oK)) 1 := by
    rw [e1152, h₁.wr]; exact wS (by decide)
  have o1 : oSave + 32 < 4096 := by decide
  have o2 : oK < 4096 := by decide
  have e3 : encodable (4 : BitVec 32) = true := by decide
  run_block [i872, i1152, o1, o2, e3]
  have eS : (lay s₀).A 0 840 = State.addr (s₀.gpr .r3) + BitVec.ofNat 64 840 := rfl
  have ne1 : ∀ i < 8, ∀ (m : Mem) (v : BitVec 32), (m.writeW ((lay s₀).A 0 872) v).readW
      ((lay s₀).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 = m.readW ((lay s₀).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 :=
    fun i hi m v => Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by decide)
  have ne2 : ∀ i < 9, ∀ (m : Mem) (v : Byte), (m.writeW ((lay s₀).A 0 1152) v).readW
      ((lay s₀).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 = m.readW ((lay s₀).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 :=
    fun i hi m v => Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by decide)
  refine ⟨⟨⟨hL, by simp [lay], rfl, by simp [lay], ?_, by show 8 ≤ s₁.sp.toNat; rw [h₁.sp]; exact hp.sp8, ?_, ?_⟩, ?_, ?_, ?_, h₁.rd, h₁.wr, h₁.sp, fun i hi => ?_, ?_, ?_⟩, ?_⟩
  · simp [h₁.gpr]; rfl
  · show s₀.sp - BitVec.ofNat 32 8 = s₁.sp - BitVec.ofNat 32 8
    rw [h₁.sp]
  · show (⟨State.addr (pScr s₀), 49152⟩ : Region) ∈ s₁.wr
    rw [h₁.wr, hp.wr]; simp
  · simp [h₁.gpr]
  · simp [h₁.gpr]
  · simp [h₁.gpr]
  · show ((s₁.mem.writeW _ _).writeW _ _).readW _ _ = _
    rw [e872, e1152, ne2 i (by omega), ne1 i hi]
    exact h₁.saved i hi
  · show ((s₁.mem.writeW _ _).writeW _ _).readW _ _ = _
    rw [e872, e1152, show (lay s₀).A 0 872 = (lay s₀).A 0 840 + BitVec.ofNat 64 (4 * 8) by
      rw [add_ofNat_add], ne2 8 (by decide), add_ofNat_add, Mem.readW_writeW_self32, h₁.gpr]
  · show bytesAt ((s₁.mem.writeW _ _).writeW _ _) _ _ = _
    rw [e872, e1152]
    have fr : Frame ((lay s₀).RL [(0, 840, 36), (0, 1152, 1)]) s₀.mem
        ((s₁.mem.writeW ((lay s₀).A 0 872) (s₁.gpr .lr)).writeW ((lay s₀).A 0 1152) (BitVec.setWidth 8 (4 : BitVec 32))) := by
      refine ((h₁.frame.sub fun r hr => ⟨Lay.R (lay s₀) 0 840 36, by simp, ?_⟩).writeW (r := Lay.R (lay s₀) 0 840 36)
        (by simp) _ ?_).writeW (r := Lay.R (lay s₀) 0 1152 1) (by simp) _ ?_
      · rw [List.mem_singleton] at hr; subst hr
        show Region.Sub (Lay.R (lay s₀) 0 840 32) _
        exact Lay.R_sub_R hL (by simp [lay]) (by decide) (by decide) (by simp [lay])
      · simp only [Region.Contains]; bv_omega
      · simp only [Region.Contains]; bv_omega
    exact Lay.bytes_keep hL fr (by ldecide) (by decide)
  · show ((s₁.mem.writeW _ _).writeW _ _) _ = _
    rw [e1152, writeW8_apply]; simp

/-! ## Pieces of the hashes -/

/-- The buffer of each pointer register. -/
def kidx : Reg → Nat
  | .r4 => 2 | .r5 => 3 | .r6 => 4 | _ => 0

theorem pieceK {s₀ s : State} (hp : Pre s₀) (h : KEnv s₀ s) {p : Piece} {w : Bool}
    (hb : p.base = .r4 ∨ p.base = .r5 ∨ p.base = .r6 ∨ p.base = .r7) (hw : w = true → p.base ≠ .r4)
    (hoe : encodable (BitVec.ofNat 32 p.off) = true) (hle : encodable (BitVec.ofNat 32 p.len) = true)
    (hpos : 0 < p.len) (hlt : p.off + p.len < 2 ^ 32)
    (hsep : sepAll [49152, 8, 64, 1568, 3168] (kidx p.base, p.off, p.len) kRegs = true) :
    PieceOk (lay s₀) kidx s w p := by
  obtain ⟨w0, w3, w4, w2⟩ := buf_wr hp
  rw [← h.wr] at w0 w3 w4
  rw [← h.wr, ← h.rd] at w2
  have hsep' : sepAll (lay s₀).sizes (kidx p.base, p.off, p.len) kRegs = true := hsep
  refine ⟨?_, ?_, hoe, hle, hpos, hlt, hsep', ?_⟩
  · rcases hb with e | e | e | e <;> rw [e] <;> decide
  · rcases hb with e | e | e | e <;> rw [e]
    · exact h.r4
    · exact h.r5
    · exact h.r6
    · exact h.ctx.r7
  · cases w
    · simp only [Bool.false_eq_true, ite_false]
      rcases hb with e | e | e | e <;> rw [e]
      · exact w2
      · exact mem_rd_wr w3
      · exact mem_rd_wr w4
      · exact mem_rd_wr w0
    · simp only [ite_true]
      rcases hb with e | e | e | e
      · exact absurd e (hw rfl)
      all_goals rw [e]
      · exact w3
      · exact w4
      · exact w0

/-! ## `G(d ‖ 4)` -/

/-- `d`, the first half of the seed. -/
abbrev D (s₀ : State) : List Byte := bytesAt s₀.mem (State.addr (pSeed s₀)) 32

/-- `z`, the second half of the seed. -/
abbrev Z (s₀ : State) : List Byte := bytesAt s₀.mem (State.addr (pSeed s₀) + BitVec.ofNat 64 32) 32

theorem rate72 : 72 ∈ Spec.Sha3.rates := by decide

theorem g_ins {s₀ s : State} (hp : Pre s₀) (h : KEnv s₀ s) :
    ∀ p ∈ [(⟨.r4, 0, 32⟩ : Piece), ⟨.r7, oK, 1⟩], PieceOk (lay s₀) kidx s false p := by
  intro p hp'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl
  · exact pieceK hp h (.inl rfl) (by simp) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact pieceK hp h (.inr (.inr (.inr rfl))) (by simp) (by decide) (by decide) (by decide) (by decide)
      (by decide)

theorem g_outs {s₀ s : State} (hp : Pre s₀) (h : KEnv s₀ s) :
    ∀ p ∈ [(⟨.r7, oG, 64⟩ : Piece)], PieceOk (lay s₀) kidx s true p := by
  intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
  exact pieceK hp h (.inr (.inr (.inr rfl))) (by simp) (by decide) (by decide) (by decide) (by decide)
    (by decide)

theorem g_ok {s₀ s : State} (hp : Pre s₀) (h : KEnv s₀ s) (h3 : s.mem ((lay s₀).A 0 oK) = 4) :
    WP isa (hash 72 0x06 [⟨.r4, 0, 32⟩, ⟨.r7, oK, 1⟩] [⟨.r7, oG, 64⟩]) s fun s' =>
      KEnv s₀ s' ∧ bytesAt s'.mem ((lay s₀).A 0 oG) 32 = VG.Proof.MlKem.kgRho1024 (D s₀) ∧
      bytesAt s'.mem ((lay s₀).A 0 oSigma) 32 = VG.Proof.MlKem.kgSigma1024 (D s₀) := by
  have hin := g_ins hp h
  have hout := g_outs hp h
  have hD : bytesAt s.mem ((lay s₀).A 2 0) 32 = D s₀ := by
    have := congrArg (List.take 32) h.seed
    rw [bytesAt_take _ _ (by decide), bytesAt_take _ _ (by decide)] at this
    rw [this]; show bytesAt s₀.mem (State.addr (pSeed s₀) + BitVec.ofNat 64 0) 32 = _; rw [add_ofNat_zero]
  have hin' : (List.map ((lay s₀).pb kidx s.mem) [⟨.r4, 0, 32⟩, ⟨.r7, oK, 1⟩]).flatten =
      D s₀ ++ [BitVec.ofNat 8 4] := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    show bytesAt s.mem ((lay s₀).A 2 0) 32 ++ bytesAt s.mem ((lay s₀).A 0 oK) 1 = _
    rw [hD, bytes_one, h3]; rfl
  refine WP.mono (hash_ok rate72 (by decide) (by decide) (by decide) h.ctx (List.cons_ne_nil _ _) hin hout
    (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ => ⟨?_, ?_⟩
  · exact h.keep hp (k'.x []) (by simp) (by decide)
  · have e1 := o'.1
    rw [hin'] at e1
    have e2 : bytesAt s'.mem ((lay s₀).A 0 oG) 64 = (G (D s₀ ++ [BitVec.ofNat 8 4])).1 ++
        (G (D s₀ ++ [BitVec.ofNat 8 4])).2 := e1.trans (G_split _)
    rw [show (64 : Nat) = 32 + 32 from rfl, bytesAt_add] at e2
    have l1 : (bytesAt s'.mem ((lay s₀).A 0 oG) 32).length = (G (D s₀ ++ [BitVec.ofNat 8 4])).1.length := by
      rw [bytesAt_length, VG.Proof.MlKem.G_fst_length]
    obtain ⟨r1, r2⟩ := List.append_inj e2 l1
    refine ⟨r1, ?_⟩
    show bytesAt s'.mem (State.addr ((lay s₀).ptr 0) + BitVec.ofNat 64 (888 + 32)) 32 = _
    rw [← add_ofNat_add]; exact r2

theorem rho_ok {s₀ s : State} (hp : Pre s₀) (h : KEnv s₀ s)
    (hr : bytesAt s.mem ((lay s₀).A 0 oG) 32 = VG.Proof.MlKem.kgRho1024 (D s₀))
    (hs : bytesAt s.mem ((lay s₀).A 0 oSigma) 32 = VG.Proof.MlKem.kgSigma1024 (D s₀)) :
    WP isa (copy .r7 oG .r7 oSeed 32) s fun s' => KEnv s₀ s' ∧
      bytesAt s'.mem ((lay s₀).A 0 oSeed) 32 = VG.Proof.MlKem.kgRho1024 (D s₀) ∧
      bytesAt s'.mem ((lay s₀).A 0 oSigma) 32 = VG.Proof.MlKem.kgSigma1024 (D s₀) := by
  have hL := lay_ok hp
  obtain ⟨w0, -, -, -⟩ := buf_wr hp
  refine WP.mono (copyL hL (i := 0) (j := 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h.ctx.r7 h.ctx.r7
    (by decide) (by decide) (by decide) (by decide) (by decide) (by ldecide)
    (by rw [h.rd, h.wr]; exact mem_rd_wr w0) (by rw [h.wr]; exact w0)) fun s' ⟨k', b'⟩ =>
    ⟨h.keep hp (k'.x []) (by simp) (by decide), b'.trans hr,
      (Lay.bytes_keep hL k'.frame (by ldecide) (by decide)).trans hs⟩

/-! ## The `PRF`s -/

theorem prf_phase {s₀ s : State} (hp : Pre s₀) (h : KEnv s₀ s)
    (hr : bytesAt s.mem ((lay s₀).A 0 oSeed) 32 = VG.Proof.MlKem.kgRho1024 (D s₀))
    (hs : bytesAt s.mem ((lay s₀).A 0 oSigma) 32 = VG.Proof.MlKem.kgSigma1024 (D s₀)) :
    WP isa (prfLoop4 true 0 8) s fun s' => KEnv s₀ s' ∧
      bytesAt s'.mem ((lay s₀).A 0 oSeed) 32 = VG.Proof.MlKem.kgRho1024 (D s₀) ∧
      ∀ N < 8, PolyIs s'.mem ((lay s₀).A 0 (oPoly (4 + N))) (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.kgSigma1024 (D s₀)) N)) :=
  WP.mono (prfLoop_ok h.ctx true (by decide) (by decide) hs) fun s' ⟨k', p'⟩ =>
    ⟨h.keep hp k' (by simp) (by decide), by rw [← hr]; exact Lay.bytes_keep (lay_ok hp) k'.frame (by ldecide) (by decide),
      fun N hN => p' N (Nat.zero_le _) hN⟩

/-! ## The rows of `t̂` -/

section
variable (s₀ : State)

/-- `ρ`. -/
abbrev ρ₀ : List Byte := VG.Proof.MlKem.kgRho1024 (D s₀)

/-- The entries of `Â` the products use. -/
abbrev aK (i j : Nat) : Poly := effA false (ρ₀ s₀) i j (VG.Proof.MlKem.kgS1024 (D s₀) j)

/-- Whether the `SampleNTT`s of the first `i` rows finished. -/
def okK (i : Nat) : Bool := (List.range i).all fun i' => okRow false (ρ₀ s₀) i' 4

end

theorem okK_succ (s₀ : State) (i : Nat) : okK s₀ (i + 1) = (okK s₀ i && okRow false (ρ₀ s₀) i 4) := by
  simp only [okK, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

/-- After the first `i` rows. -/
structure KRow (s₀ : State) (i : Nat) (s : State) : Prop where
  env : KEnv s₀ s
  r9 : s.gpr .r9 = BitVec.ofNat 32 i
  r11 : s.gpr .r11 = if okK s₀ i then 1 else 0
  rho : bytesAt s.mem ((lay s₀).A 0 oSeed) 32 = ρ₀ s₀
  slots : ∀ N < 8, PolyIs s.mem ((lay s₀).A 0 (oPoly (4 + N)))
    (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.kgSigma1024 (D s₀)) N))
  ek : ∀ i' < i, bytesAt s.mem ((lay s₀).A 3 (384 * i')) 384 = encode12 (VG.Proof.MlKem.kgT1024 (aK s₀) (D s₀) i')

/-- What a row changes. -/
abbrev rowK (i : Nat) : List (Nat × Nat × Nat) :=
  [(0, 1248, 2), (0, oAcc4, 3072), (0, oSample4, 3072), (1, 0, 8), (0, oAcc4, 1024), (3, 384 * i, 384)]

abbrev kSz : List Nat := [49152, 8, 64, 1568, 3168]

theorem rowK_ok : ∀ i < 4, (rowK i).all okW = true ∧ sepAll kSz (0, oSeed, 32) (rowK i) = true ∧
    (∀ N < 8, sepAll kSz (0, oPoly (4 + N), 1024) (rowK i) = true) ∧
    (∀ i' < 4, (i' == i || sepAll kSz (3, 384 * i', 384) (rowK i)) = true) ∧
    sepB kSz (0, oAcc4, 1024) (3, 384 * i, 384) = true ∧
    sepB kSz (0, oAcc4, 1024) (0, oPoly (4 + (4 + i)), 1024) = true := by
  decide

/-- The row's facts at its start `s`, for its `RowSum`. -/
theorem KRow.rowPre {s₀ : State} {i : Nat} (hi : i < 4) {s : State} (h : KRow s₀ i s) :
    RowPre (lay s₀) (ρ₀ s₀) (VG.Proof.MlKem.kgS1024 (D s₀)) i (okK s₀ i) s :=
  ⟨h.env.ctx, hi, h.r9, h.r11, h.rho, fun j hj => h.slots j (by omega)⟩

section
variable (s₀ : State) (i : Nat) (s : State)

/-- After the arguments of `t̂[i] += ê[i]`. -/
structure KR2 (s₂ : State) : Prop where
  K : KeptX [.r9, .r10, .r11] ((lay s₀).RL (rowK i)) s s₂
  r9 : s₂.gpr .r9 = BitVec.ofNat 32 i
  r0 : s₂.gpr .r0 = (lay s₀).ptr 0 + BitVec.ofNat 32 oAcc4
  r1 : s₂.gpr .r1 = (lay s₀).ptr 0 + BitVec.ofNat 32 (oPoly (4 + (4 + i)))
  r11 : s₂.gpr .r11 = if okK s₀ (i + 1) then 1 else 0
  acc : PolyIs s₂.mem ((lay s₀).A 0 oAcc4) (VG.Proof.MlKem.dot4 (aK s₀ i) (VG.Proof.MlKem.kgS1024 (D s₀)))

/-- After `t̂[i]`. -/
structure KR3 (s₃ : State) : Prop where
  K : KeptX [.r9, .r10, .r11] ((lay s₀).RL (rowK i)) s s₃
  r9 : s₃.gpr .r9 = BitVec.ofNat 32 i
  r11 : s₃.gpr .r11 = if okK s₀ (i + 1) then 1 else 0
  acc : PolyIs s₃.mem ((lay s₀).A 0 oAcc4) (VG.Proof.MlKem.kgT1024 (aK s₀) (D s₀) i)

/-- After the arguments of its encoding. -/
structure KR4 (s₄ : State) : Prop where
  r3 : KR3 s₀ i s s₄
  r0 : s₄.gpr .r0 = (lay s₀).ptr 0 + BitVec.ofNat 32 oAcc4
  r1 : s₄.gpr .r1 = (lay s₀).ptr 3 + BitVec.ofNat 32 (384 * i)

/-- After its encoding. -/
structure KR5 (s₅ : State) : Prop where
  K : KeptX [.r9, .r10, .r11] ((lay s₀).RL (rowK i)) s s₅
  r9 : s₅.gpr .r9 = BitVec.ofNat 32 i
  r11 : s₅.gpr .r11 = if okK s₀ (i + 1) then 1 else 0
  enc : bytesAt s₅.mem ((lay s₀).A 3 (384 * i)) 384 = encode12 (VG.Proof.MlKem.kgT1024 (aK s₀) (D s₀) i)

end

theorem KRow.ctxOf {s₀ : State} {i : Nat} {s : State} (h : KRow s₀ i s) {x : State} {xs : List Reg}
    {W : List (Nat × Nat × Nat)} (k : KeptX xs ((lay s₀).RL W) s x) (h7 : Reg.r7 ∉ xs) : Ctx (lay s₀) x :=
  k.ctx h7 h.env.ctx

section
variable {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 4) {s : State} (h : KRow s₀ i s)
include hp hi h

omit hp in
theorem kr2_ok {s₁ : State}
    (r : RowInv (lay s₀) false (ρ₀ s₀) (VG.Proof.MlKem.kgS1024 (D s₀)) i (okK s₀ i) s 4 s₁) :
    WP isa (.block (ptrTo .r0 .r7 oAcc4 :: slotAt .r1 .r9 (oPoly 8))) s₁ (KR2 s₀ i s) := by
  have hc₁ := h.ctxOf r.kx (by decide)
  have g9₁ : s₁.gpr .r9 = BitVec.ofNat 32 i := by rw [r.kx.cs .r9 (by decide) (by decide) (by decide), h.r9]
  refine WP.mono (ptrSlot_ok (i := i) hc₁.r7 g9₁ (by decide) (by decide)) fun s₂ ⟨o₂, a0, a1⟩ => ?_
  rw [slot_eq _ (by offs4), show oPoly 8 + 1024 * i = oPoly (4 + (4 + i)) by offs4] at a1
  exact ⟨((r.kx.weaken (by simp)).monoL (by simp)).trans (o₂.x _ _),
    by rw [o₂.cs .r9 (by decide) (by decide), g9₁], a0, a1,
    by rw [o₂.cs .r11 (by decide) (by decide), r.r11, ← okK_succ],
    by rw [o₂.mem, ← rowAcc_four]; exact r.acc⟩

theorem kr3_ok {s₂ : State} (r : KR2 s₀ i s s₂) : WP isa callAdd s₂ (KR3 s₀ i s) := by
  have hL := lay_ok hp
  have hc₂ := h.ctxOf r.K (by decide)
  obtain ⟨-, -, c_slots, -, -, c_add⟩ := rowK_ok i hi
  have sl₂ : PolyIs s₂.mem ((lay s₀).A 0 (oPoly (4 + (4 + i))))
      (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.kgSigma1024 (D s₀)) (4 + i))) :=
    Lay.polyIs_keep hL r.K.frame (c_slots (4 + i) (by omega)) (h.slots (4 + i) (by omega))
  exact addL hL r.r0 r.r1 c_add hc₂.buf0 (mem_rd_wr hc₂.buf0) r.acc sl₂ fun s₃ k₃ p₃ =>
    ⟨r.K.trans ((k₃.x _).monoL (by simp)), by rw [k₃.cs .r9 (by decide) (by decide), r.r9],
      by rw [k₃.cs .r11 (by decide) (by decide), r.r11], p₃⟩

omit hp in
theorem kr4_ok {s₃ : State} (r : KR3 s₀ i s s₃) :
    WP isa (.block (ptrTo .r0 .r7 oAcc4 :: at384 .r1 .r5 .r9)) s₃ (KR4 s₀ i s) := by
  have hc₃ := h.ctxOf r.K (by decide)
  have g5₃ : s₃.gpr .r5 = pEk s₀ := by rw [r.K.cs .r5 (by decide) (by decide) (by decide), h.env.r5]
  refine WP.mono (ptr384_ok (b := .r5) (.inl rfl) hc₃.r7 g5₃ r.r9 (by decide)) fun s₄ ⟨o₄, b0, b1⟩ => ?_
  rw [at384_eq _ (by omega)] at b1
  exact ⟨⟨r.K.trans (o₄.x _ _), by rw [o₄.cs .r9 (by decide) (by decide), r.r9],
    by rw [o₄.cs .r11 (by decide) (by decide), r.r11], by rw [o₄.mem]; exact r.acc⟩, b0, b1⟩

theorem kr5_ok {s₄ : State} (r : KR4 s₀ i s s₄) : WP isa callEncode12 s₄ (KR5 s₀ i s) := by
  have hL := lay_ok hp
  have hc₄ := h.ctxOf r.r3.K (by decide)
  obtain ⟨-, -, -, -, c_enc, -⟩ := rowK_ok i hi
  obtain ⟨-, w3, -, -⟩ := buf_wr hp
  exact encode12L hL (i := 0) (j := 3) (o' := 384 * i) r.r0 r.r1 c_enc (mem_rd_wr hc₄.buf0)
    (by rw [r.r3.K.wr, h.env.wr]; exact w3) r.r3.acc fun s₅ k₅ e₅ =>
    ⟨r.r3.K.trans ((k₅.x _).monoL (by simp)), by rw [k₅.cs .r9 (by decide) (by decide), r.r3.r9],
      by rw [k₅.cs .r11 (by decide) (by decide), r.r3.r11], e₅⟩

theorem kr6_ok {s₅ : State} (r : KR5 s₀ i s s₅) :
    WP isa (.block (count .r9 4)) s₅ fun s' => KRow s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 4) := by
  have hL := lay_ok hp
  obtain ⟨c_ok, c_rho, c_slots, c_ek, -, -⟩ := rowK_ok i hi
  refine WP.mono (count_ok (by omega) (by decide) (by decide) r.r9) fun s' ⟨k', g', z'⟩ => ⟨⟨?_, g', ?_, ?_, ?_, ?_⟩, z'⟩
  all_goals have K : KeptX [.r9, .r10, .r11] ((lay s₀).RL (rowK i)) s s' :=
    r.K.trans ((k'.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil))
  · exact h.env.keep hp K (by simp) c_ok
  · rw [k'.cs .r11 (by decide) (by decide) (by decide), r.r11]
  · rw [← h.rho]; exact Lay.bytes_keep hL K.frame c_rho (by decide)
  · exact fun N hN => Lay.polyIs_keep hL K.frame (c_slots N hN) (h.slots N hN)
  · intro i' hi'
    by_cases e : i' = i
    · subst e
      exact (bytesAt_frame k'.frame (fun _ h => absurd h List.not_mem_nil) (by decide)).trans r.enc
    · have := c_ek i' (by omega)
      simp only [Bool.or_eq_true, beq_iff_eq, e, false_or] at this
      rw [← h.ek i' (by omega)]; exact Lay.bytes_keep hL K.frame this (by decide)

end

theorem kgRow_step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 4) {s : State} (h : KRow s₀ i s) :
    WP isa kgRowBody4 s fun s' => KRow s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 4) :=
  WP.seq (WP.mono (rowSum_ok (transpose := false) (h.rowPre hi)) fun _ r₁ =>
    WP.seq (WP.mono (kr2_ok hi h r₁) fun _ r₂ => WP.seq (WP.mono (kr3_ok hp hi h r₂) fun _ r₃ =>
    WP.seq (WP.mono (kr4_ok hi h r₃) fun _ r₄ => WP.seq (WP.mono (kr5_ok hp hi h r₄) fun _ r₅ =>
      kr6_ok hp hi h r₅)))))

theorem rows_init {s₀ s : State} (hp : Pre s₀) (h : KEnv s₀ s)
    (hr : bytesAt s.mem ((lay s₀).A 0 oSeed) 32 = ρ₀ s₀)
    (hs : ∀ N < 8, PolyIs s.mem ((lay s₀).A 0 (oPoly (4 + N)))
      (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.kgSigma1024 (D s₀)) N))) :
    WP isa (.block [.mov .r11 (.imm 1), .mov .r9 (.imm 0)]) s (KRow s₀ 0) :=
  WP.mono flagInit_ok fun _ ⟨k₁, g11, g9, m₁⟩ =>
    ⟨h.keep hp (xs := [.r9, .r11]) (W := []) k₁ (by simp) rfl, g9, by rw [g11]; rfl, by rw [m₁]; exact hr,
      by rw [m₁]; exact hs, fun i' hi' => absurd hi' (Nat.not_lt_zero _)⟩

/-! ## `ŝ` into `dk` -/

/-- After encoding the first `j` polynomials of `ŝ`. -/
structure KS (s₀ : State) (j : Nat) (s : State) : Prop where
  env : KEnv s₀ s
  r9 : s.gpr .r9 = BitVec.ofNat 32 j
  r11 : s.gpr .r11 = if okK s₀ 4 then 1 else 0
  rho : bytesAt s.mem ((lay s₀).A 0 oSeed) 32 = ρ₀ s₀
  ek : ∀ i' < 4, bytesAt s.mem ((lay s₀).A 3 (384 * i')) 384 = encode12 (VG.Proof.MlKem.kgT1024 (aK s₀) (D s₀) i')
  slots : ∀ j' < 4, PolyIs s.mem ((lay s₀).A 0 (oPoly (4 + j'))) (VG.Proof.MlKem.kgS1024 (D s₀) j')
  dk : ∀ j' < j, bytesAt s.mem ((lay s₀).A 4 (384 * j')) 384 = encode12 (VG.Proof.MlKem.kgS1024 (D s₀) j')

theorem sK_ok : ∀ j < 4, [((4 : Nat), 384 * j, (384 : Nat))].all okW = true ∧
    sepAll kSz (0, oSeed, 32) [(4, 384 * j, 384)] = true ∧
    (∀ i' < 4, sepAll kSz (3, 384 * i', 384) [(4, 384 * j, 384)] = true) ∧
    (∀ j' < 4, sepAll kSz (0, oPoly (4 + j'), 1024) [(4, 384 * j, 384)] = true) ∧
    (∀ j' < 4, (j' == j || sepAll kSz (4, 384 * j', 384) [(4, 384 * j, 384)]) = true) ∧
    sepB kSz (0, oPoly (4 + j), 1024) (4, 384 * j, 384) = true := by
  decide

theorem s_init {s₀ s : State} (hp : Pre s₀) (h : KRow s₀ 4 s) :
    WP isa (.block [.mov .r9 (.imm 0)]) s (KS s₀ 0) :=
  WP.mono (movc_ok .r9 (N := 0) (by decide)) fun _ ⟨k₆, g9', m₆⟩ =>
    ⟨h.env.keep hp (xs := [.r9]) (W := []) k₆ (by simp) rfl, g9',
      by rw [k₆.cs .r11 (by decide) (by decide) (by decide), h.r11], by rw [m₆]; exact h.rho,
      by rw [m₆]; exact h.ek, fun j' hj' => by rw [m₆]; exact h.slots j' (by omega),
      fun j' hj' => absurd hj' (Nat.not_lt_zero _)⟩

section
variable (s₀ : State) (j : Nat) (s : State)

/-- After the arguments of the encoding of `ŝ[j]`. -/
structure KS1 (s₁ : State) : Prop where
  o : Only s s₁
  r0 : s₁.gpr .r0 = (lay s₀).ptr 0 + BitVec.ofNat 32 (oPoly (4 + j))
  r1 : s₁.gpr .r1 = (lay s₀).ptr 4 + BitVec.ofNat 32 (384 * j)

/-- After the encoding of `ŝ[j]`. -/
structure KS2 (s₂ : State) : Prop where
  K : KeptX [.r9] ((lay s₀).RL [(4, 384 * j, 384)]) s s₂
  r9 : s₂.gpr .r9 = BitVec.ofNat 32 j
  enc : bytesAt s₂.mem ((lay s₀).A 4 (384 * j)) 384 = encode12 (VG.Proof.MlKem.kgS1024 (D s₀) j)

end

section
variable {s₀ : State} (hp : Pre s₀) {j : Nat} (hj : j < 4) {s : State} (h : KS s₀ j s)
include hp hj h

omit hp in
theorem ks1_ok : WP isa (.block (slotAt .r0 .r9 (oPoly 4) ++ at384 .r1 .r6 .r9)) s (KS1 s₀ j s) := by
  refine WP.mono (slot384_ok (b := .r6) (.inr rfl) h.env.ctx.r7 h.env.r6 h.r9 (o' := oPoly 4) (by decide))
    fun s₁ ⟨o₁, a0, a1⟩ => ⟨o₁, ?_, ?_⟩
  · rw [a0, slot_eq _ (by offs4), show oPoly 4 + 1024 * j = oPoly (4 + j) by offs4]
  · rw [a1, at384_eq _ (by omega)]; rfl

theorem ks2_ok {s₁ : State} (r : KS1 s₀ j s s₁) : WP isa callEncode12 s₁ (KS2 s₀ j s) := by
  have hL := lay_ok hp
  have hc₁ := h.env.ctx.only r.o
  obtain ⟨-, -, -, -, -, c_enc⟩ := sK_ok j hj
  obtain ⟨-, -, w4, -⟩ := buf_wr hp
  exact encode12L hL (i := 0) (j := 4) (o' := 384 * j) r.r0 r.r1 c_enc (mem_rd_wr hc₁.buf0)
    (by rw [r.o.wr, h.env.wr]; exact w4) (by rw [r.o.mem]; exact h.slots j hj) fun s₂ k₂ e₂ =>
    ⟨(r.o.x _ _).trans ((k₂.x _).monoL (by simp)),
      by rw [k₂.cs .r9 (by decide) (by decide), r.o.cs .r9 (by decide) (by decide), h.r9], e₂⟩

theorem ks3_ok {s₂ : State} (r : KS2 s₀ j s s₂) :
    WP isa (.block (count .r9 4)) s₂ fun s' => KS s₀ (j + 1) s' ∧ s'.z = decide (j + 1 = 4) := by
  have hL := lay_ok hp
  obtain ⟨c_ok, c_rho, c_ek, c_slots, c_dk, -⟩ := sK_ok j hj
  refine WP.mono (count_ok (by omega) (by decide) (by decide) r.r9) fun s' ⟨k', g', z'⟩ =>
    ⟨⟨?_, g', ?_, ?_, ?_, ?_, ?_⟩, z'⟩
  all_goals have K : KeptX [.r9] ((lay s₀).RL [(4, 384 * j, 384)]) s s' :=
    r.K.trans (k'.mono (fun _ h => absurd h List.not_mem_nil))
  · exact h.env.keep hp K (by simp) c_ok
  · rw [K.cs .r11 (by decide) (by decide) (by decide), h.r11]
  · rw [← h.rho]; exact Lay.bytes_keep hL K.frame c_rho (by decide)
  · exact fun i' hi' => (Lay.bytes_keep hL K.frame (c_ek i' hi') (by decide)).trans (h.ek i' hi')
  · exact fun j' hj' => Lay.polyIs_keep hL K.frame (c_slots j' hj') (h.slots j' hj')
  · intro j' hj'
    by_cases e : j' = j
    · subst e
      exact (bytesAt_frame k'.frame (fun _ h => absurd h List.not_mem_nil) (by decide)).trans r.enc
    · have := c_dk j' (by omega)
      simp only [Bool.or_eq_true, beq_iff_eq, e, false_or] at this
      exact (Lay.bytes_keep hL K.frame this (by decide)).trans (h.dk j' (by omega))

end

theorem kgS_step {s₀ : State} (hp : Pre s₀) {j : Nat} (hj : j < 4) {s : State} (h : KS s₀ j s) :
    WP isa kgSBody4 s fun s' => KS s₀ (j + 1) s' ∧ s'.z = decide (j + 1 = 4) :=
  WP.seq (WP.mono (ks1_ok hj h) fun _ r₁ => WP.seq (WP.mono (ks2_ok hp hj h r₁) fun _ r₂ => ks3_ok hp hj h r₂))

/-! ## The encapsulation key, `H(ek)` and `z` -/

section
variable (s₀ : State)

/-- `ek`. -/
abbrev EK : List Byte := VG.Proof.MlKem.ekPKE1024 (aK s₀) (D s₀)

/-- `dk`. -/
abbrev DK : List Byte := VG.Proof.MlKem.dkPKE1024 (D s₀) ++ EK s₀ ++ H (EK s₀) ++ Z s₀

end

theorem bytes5 (m : Mem) (p : Addr) :
    bytesAt m p 1568 = bytesAt m p 384 ++ bytesAt m (p + BitVec.ofNat 64 384) 384 ++
      bytesAt m (p + BitVec.ofNat 64 768) 384 ++ bytesAt m (p + BitVec.ofNat 64 1152) 384 ++
      bytesAt m (p + BitVec.ofNat 64 1536) 32 := by
  rw [show (1568 : Nat) = 384 + (384 + (384 + (384 + 32))) from rfl, bytesAt_add, bytesAt_add, bytesAt_add,
    bytesAt_add, add_ofNat_add, add_ofNat_add, add_ofNat_add]
  simp only [List.append_assoc]

theorem bytes7 (m : Mem) (p : Addr) :
    bytesAt m p 3168 = bytesAt m p 384 ++ bytesAt m (p + BitVec.ofNat 64 384) 384 ++
      bytesAt m (p + BitVec.ofNat 64 768) 384 ++ bytesAt m (p + BitVec.ofNat 64 1152) 384 ++
      bytesAt m (p + BitVec.ofNat 64 1536) 1568 ++
      bytesAt m (p + BitVec.ofNat 64 3104) 32 ++ bytesAt m (p + BitVec.ofNat 64 3136) 32 := by
  rw [show (3168 : Nat) = 384 + (384 + (384 + (384 + (1568 + (32 + 32))))) from rfl, bytesAt_add, bytesAt_add,
    bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add, add_ofNat_add, add_ofNat_add, add_ofNat_add,
    add_ofNat_add, add_ofNat_add]
  simp only [List.append_assoc]

theorem tail_regs : [(3 : Nat), 4].all (fun i => i < 5) = true := rfl

theorem h_ins {s₀ s : State} (hp : Pre s₀) (h : KEnv s₀ s) :
    ∀ p ∈ [(⟨.r5, 0, 1568⟩ : Piece)], PieceOk (lay s₀) kidx s false p := by
  intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
  exact pieceK hp h (.inr (.inl rfl)) (by simp) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem h_outs {s₀ s : State} (hp : Pre s₀) (h : KEnv s₀ s) :
    ∀ p ∈ [(⟨.r6, 3104, 32⟩ : Piece)], PieceOk (lay s₀) kidx s true p := by
  intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
  exact pieceK hp h (.inr (.inr (.inl rfl))) (by simp) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-! What each step of the end keeps, for the proof of constant time. -/

section
variable {s₀ s : State} (hp : Pre s₀) (h : KEnv s₀ s)
include hp h

theorem cpRho_env : WP isa (copy .r7 oSeed .r5 1536 32) s (KEnv s₀) := by
  obtain ⟨w0, w3, -, -⟩ := buf_wr hp
  exact WP.mono (copyL (lay_ok hp) (i := 0) (j := 3) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h.ctx.r7 h.r5
    (by decide) (by decide) (by decide) (by decide) (by decide) (by ldecide) (by rw [h.rd, h.wr]; exact mem_rd_wr w0)
    (by rw [h.wr]; exact w3)) fun _ ⟨k, _⟩ => h.keep hp (k.x []) (by simp) (by decide)

theorem cpEk_env : WP isa (copy .r5 0 .r6 1536 1568) s (KEnv s₀) := by
  obtain ⟨-, w3, w4, -⟩ := buf_wr hp
  exact WP.mono (copyL (lay_ok hp) (i := 3) (j := 4) (so := 0) (dO := 1536) (len := 1568) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ h.r5 h.r6 (by decide) (by decide) (by decide) (by decide) (by decide) (by ldecide)
    (by rw [h.rd, h.wr]; exact mem_rd_wr w3) (by rw [h.wr]; exact w4)) fun _ ⟨k, _⟩ =>
    h.keep hp (k.x []) (by simp) (by decide)

theorem hashH_env : WP isa (hash 136 0x06 [⟨.r5, 0, 1568⟩] [⟨.r6, 3104, 32⟩]) s (KEnv s₀) :=
  WP.mono (hash_ok (idx := kidx) MlKem.rate136 (by decide) (by decide) (by decide) h.ctx (List.cons_ne_nil _ _)
    (h_ins hp h) (h_outs hp h) (List.pairwise_singleton _ _)) fun _ ⟨k, _⟩ => h.keep hp (k.x []) (by simp) (by decide)

theorem cpZ_env : WP isa (copy .r4 32 .r6 3136 32) s (KEnv s₀) := by
  obtain ⟨-, -, w4, w2⟩ := buf_wr hp
  exact WP.mono (copyL (lay_ok hp) (i := 2) (j := 4) (so := 32) (dO := 3136) (len := 32) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ h.r4 h.r6 (by decide) (by decide) (by decide) (by decide) (by decide) (by ldecide)
    (by rw [h.rd, h.wr]; exact w2) (by rw [h.wr]; exact w4)) fun _ ⟨k, _⟩ => h.keep hp (k.x []) (by simp) (by decide)

end

theorem tail_ok {s₀ s : State} (hp : Pre s₀) (h : KS s₀ 4 s) :
    WP isa (.seq (copy .r7 oSeed .r5 1536 32) <| .seq (copy .r5 0 .r6 1536 1568) <|
      .seq (hash 136 0x06 [⟨.r5, 0, 1568⟩] [⟨.r6, 3104, 32⟩]) <| .seq (copy .r4 32 .r6 3136 32) (.block topEnd)) s
      fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧
        s'.gpr .r0 = (if okK s₀ 4 then 1 else 0) ∧ bytesAt s'.mem (State.addr (pEk s₀)) 1568 = EK s₀ ∧
        bytesAt s'.mem (State.addr (pDk s₀)) 3168 = DK s₀ := by
  have hL := lay_ok hp
  obtain ⟨w0, w3, w4, w2⟩ := buf_wr hp
  have e0 : ∀ (i : Nat) (x : State), State.addr ((lay s₀).ptr i) = (lay s₀).A i 0 := fun i _ => by
    simp only [Lay.A, add_ofNat_zero]
  -- `ρ` into `ek`
  have h₀ := h.env
  refine WP.seq (WP.mono (copyL hL (i := 0) (j := 3) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h₀.ctx.r7 h₀.r5
    (by decide) (by decide) (by decide) (by decide) (by decide) (by ldecide) (by rw [h₀.rd, h₀.wr]; exact mem_rd_wr w0)
    (by rw [h₀.wr]; exact w3)) fun s₁ ⟨k₁, b₁⟩ => ?_)
  have h₁ := h₀.keep hp (k₁.x []) (by simp) (by decide)
  have ek₁ : bytesAt s₁.mem ((lay s₀).A 3 0) 1568 = EK s₀ := by
    rw [bytes5, add_ofNat_add, add_ofNat_add, add_ofNat_add, add_ofNat_add, show 0 + 1536 = 1536 from rfl, b₁,
      h.rho]
    have r0 := (Lay.bytes_keep hL k₁.frame (i := 3) (o := 384 * 0) (l := 384) (by ldecide) (by decide)).trans (h.ek 0 (by decide))
    have r1 := (Lay.bytes_keep hL k₁.frame (i := 3) (o := 384 * 1) (l := 384) (by ldecide) (by decide)).trans (h.ek 1 (by decide))
    have r2 := (Lay.bytes_keep hL k₁.frame (i := 3) (o := 384 * 2) (l := 384) (by ldecide) (by decide)).trans (h.ek 2 (by decide))
    have r3 := (Lay.bytes_keep hL k₁.frame (i := 3) (o := 384 * 3) (l := 384) (by ldecide) (by decide)).trans (h.ek 3 (by decide))
    rw [show 384 * 0 = 0 + 0 from rfl] at r0
    rw [show 384 * 1 = 0 + 384 from rfl] at r1
    rw [show 384 * 2 = 0 + 768 from rfl] at r2
    rw [show 384 * 3 = 0 + 1152 from rfl] at r3
    simp only [Lay.A] at r0 r1 r2 r3 ⊢
    rw [r0, r1, r2, r3]; rfl
  -- `ek` into `dk`
  refine WP.seq (WP.mono (copyL hL (i := 3) (j := 4) (so := 0) (dO := 1536) (len := 1568) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ h₁.r5 h₁.r6 (by decide) (by decide) (by decide) (by decide) (by decide) (by ldecide)
    (by rw [h₁.rd, h₁.wr]; exact mem_rd_wr w3) (by rw [h₁.wr]; exact w4)) fun s₂ ⟨k₂, b₂⟩ => ?_)
  rw [ek₁] at b₂
  have h₂ := h₁.keep hp (k₂.x []) (by simp) (by decide)
  have ek₂ : bytesAt s₂.mem ((lay s₀).A 3 0) 1568 = EK s₀ :=
    (Lay.bytes_keep hL k₂.frame (by ldecide) (by decide)).trans ek₁
  -- `H(ek)`
  have hin := h_ins hp h₂
  have hout := h_outs hp h₂
  refine WP.seq (WP.mono (hash_ok (idx := kidx) MlKem.rate136 (by decide) (by decide) (by decide) h₂.ctx
    (List.cons_ne_nil _ _) hin hout (List.pairwise_singleton _ _)) fun s₃ ⟨k₃, o₃⟩ => ?_)
  have h₃ := h₂.keep hp (k₃.x []) (by simp) (by decide)
  have hek₃ : bytesAt s₃.mem ((lay s₀).A 4 3104) 32 = H (EK s₀) := by
    have e := o₃.1
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at e
    refine e.trans ?_
    show _ = H (EK s₀)
    rw [VG.Proof.MlKem.H_eq, ← ek₂]; rfl
  -- `z`
  refine WP.seq (WP.mono (copyL hL (i := 2) (j := 4) (so := 32) (dO := 3136) (len := 32) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ h₃.r4 h₃.r6 (by decide) (by decide) (by decide) (by decide) (by decide) (by ldecide)
    (by rw [h₃.rd, h₃.wr]; exact w2) (by rw [h₃.wr]; exact w4)) fun s₄ ⟨k₄, b₄⟩ => ?_)
  have h₄ := h₃.keep hp (k₄.x []) (by simp) (by decide)
  have z₄ : bytesAt s₄.mem ((lay s₀).A 4 3136) 32 = Z s₀ := by
    rw [b₄]
    have := congrArg (List.drop 32) h₃.seed
    rw [bytesAt_drop _ _ (by decide), bytesAt_drop _ _ (by decide)] at this
    rw [show (lay s₀).A 2 32 = (lay s₀).A 2 0 + BitVec.ofNat 64 32 by simp only [Lay.A, add_ofNat_add], this]
    simp only [Lay.A, add_ofNat_zero]; rfl
  refine WP.mono (topEnd_ok h₄.ctx h₄.sav h₄.savlr) fun s' ⟨pr, r0, m', sp'⟩ => ⟨pr, sp'.trans h₄.sp, ?_, ?_, ?_⟩
  · rw [r0, k₄.cs .r11 (by decide) (by decide), k₃.cs .r11 (by decide) (by decide), k₂.cs .r11 (by decide) (by decide),
      k₁.cs .r11 (by decide) (by decide), h.r11]
  · rw [m', show State.addr (pEk s₀) = (lay s₀).A 3 0 by simp only [Lay.A, add_ofNat_zero]; rfl,
      Lay.bytes_keep hL k₄.frame (by ldecide) (by decide), Lay.bytes_keep hL k₃.frame (by ldecide) (by decide), ek₂]
  · rw [m', show State.addr (pDk s₀) = State.addr ((lay s₀).ptr 4) from rfl, bytes7]
    have kd : ∀ o, sepAll kSz (4, o, 384) [(3, 1536, 32)] = true → sepAll kSz (4, o, 384) [(4, 1536, 1568)] = true →
        sepAll kSz (4, o, 384) (kRegs ++ [(4, 3104, 32)]) = true → sepAll kSz (4, o, 384) [(4, 3136, 32)] = true →
        bytesAt s₄.mem ((lay s₀).A 4 o) 384 = bytesAt s.mem ((lay s₀).A 4 o) 384 := fun o c1 c2 c3 c4 =>
      (Lay.bytes_keep hL k₄.frame c4 (by decide)).trans ((Lay.bytes_keep hL k₃.frame c3 (by decide)).trans
        ((Lay.bytes_keep hL k₂.frame c2 (by decide)).trans (Lay.bytes_keep hL k₁.frame c1 (by decide))))
    have d0 := (kd (384 * 0) (by decide) (by decide) (by decide) (by decide)).trans (h.dk 0 (by decide))
    have d1 := (kd (384 * 1) (by decide) (by decide) (by decide) (by decide)).trans (h.dk 1 (by decide))
    have d2 := (kd (384 * 2) (by decide) (by decide) (by decide) (by decide)).trans (h.dk 2 (by decide))
    have d3 := (kd (384 * 3) (by decide) (by decide) (by decide) (by decide)).trans (h.dk 3 (by decide))
    have e4 := (Lay.bytes_keep hL k₄.frame (i := 4) (o := 1536) (l := 1568) (by ldecide) (by decide)).trans
      ((Lay.bytes_keep hL k₃.frame (by ldecide) (by decide)).trans b₂)
    have hh := (Lay.bytes_keep hL k₄.frame (i := 4) (o := 3104) (l := 32) (by ldecide) (by decide)).trans hek₃
    simp only [Lay.A] at d0 d1 d2 d3 e4 hh z₄ ⊢
    rw [show 384 * 0 = 0 from rfl, add_ofNat_zero] at d0
    rw [show 384 * 1 = 384 from rfl] at d1
    rw [show 384 * 2 = 768 from rfl] at d2
    rw [show 384 * 3 = 1152 from rfl] at d3
    rw [d0, d1, d2, d3, e4, hh, z₄]; rfl

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa keygen1024 s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      s.gpr .r0 = (if okK s₀ 4 then 1 else 0) ∧ bytesAt s.mem (State.addr (pEk s₀)) 1568 = EK s₀ ∧
      bytesAt s.mem (State.addr (pDk s₀)) 3168 = DK s₀ := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨h₁, b₁⟩ => ?_)
  refine WP.seq (WP.mono (g_ok hp h₁ b₁) fun s₂ ⟨h₂, r₂, σ₂⟩ => ?_)
  refine WP.seq (WP.mono (rho_ok hp h₂ r₂ σ₂) fun s₂' ⟨h₂', r₂', σ₂'⟩ => ?_)
  refine WP.seq (WP.mono (prf_phase hp h₂' r₂' σ₂') fun s₃ ⟨h₃, r₃, p₃⟩ => ?_)
  refine WP.seq (WP.mono (rows_init hp h₃ r₃ p₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (wp_loop_ne (KRow s₀) (N := 4) (by decide) (fun i hi s h => kgRow_step hp hi h)
    (fun _ h => h) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (s_init hp h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (wp_loop_ne (KS s₀) (N := 4) (by decide) (fun j hj s h => kgS_step hp hj h)
    (fun _ h => h) h₆) fun s₇ h₇ => ?_)
  exact WP.mono (tail_ok hp h₇) fun s ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩

end VG.Proof.MlKem1024.Arm.KeyGen
