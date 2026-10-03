import VerifiedGarbage.Proof.MlKem.Arm.Encrypt

/-!
# ML-KEM on 32-bit ARM: key generation, correctness

`K.keygen` for any parameter set `K` (`KemLay.WF`). The buffers of the
function (`lay`): `scratch`, the stack, `seed`, `ek` and `dk`; what every
phase keeps (`KEnv`: the pointers, our caller's registers in `scratch`, the
seed); and the phases: the setup, `G(d ‖ k)` into `ρ` and `σ`, the `PRF`s
into `ŝ` and `ê`, the rows of `t̂ = Â ∘ ŝ + ê` encoded into `ek`, `ŝ` encoded
into `dk`, the copies of `ρ`, `ek` and `z`, and `H(ek)`.
-/

namespace VG.Proof.MlKem.Arm.KeyGen

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Enc (bytes_catK catK_congr)

section
variable (s₀ : State)

abbrev pSeed : BitVec 32 := s₀.gpr .r0
abbrev pEk : BitVec 32 := s₀.gpr .r1
abbrev pDk : BitVec 32 := s₀.gpr .r2
abbrev pScr : BitVec 32 := s₀.gpr .r3

/-- The buffers: `scratch`, the 8 bytes below the stack pointer, `seed`,
`ek` and `dk`. -/
def lay (K : KemLay) : Lay :=
  ⟨fun i => [pScr s₀, s₀.sp - BitVec.ofNat 32 8, pSeed s₀, pEk s₀, pDk s₀].getD i 0,
    [K.scratch, 8, 64, K.ekLen, K.dkLen]⟩

end

/-- The sizes of the buffers. -/
abbrev kSz (K : KemLay) : List Nat := [K.scratch, 8, 64, K.ekLen, K.dkLen]

theorem lay_sizes (K : KemLay) (s₀ : State) : (lay s₀ K).sizes = kSz K := rfl

/-- The precondition of the contract. -/
structure Pre (K : KemLay) (s₀ : State) : Prop where
  wf : K.WF
  calls : K.CallsOk
  sp8 : 8 ≤ s₀.sp.toNat
  rd : s₀.rd = [⟨State.addr (pSeed s₀), 64⟩]
  wr : s₀.wr = [⟨State.addr (pEk s₀), K.ekLen⟩, ⟨State.addr (pDk s₀), K.dkLen⟩, ⟨State.addr (pScr s₀), K.scratch⟩]
  d_se : (⟨State.addr (pSeed s₀), 64⟩ : Region).Disjoint ⟨State.addr (pEk s₀), K.ekLen⟩
  d_sd : (⟨State.addr (pSeed s₀), 64⟩ : Region).Disjoint ⟨State.addr (pDk s₀), K.dkLen⟩
  d_ss : (⟨State.addr (pSeed s₀), 64⟩ : Region).Disjoint ⟨State.addr (pScr s₀), K.scratch⟩
  d_ed : (⟨State.addr (pEk s₀), K.ekLen⟩ : Region).Disjoint ⟨State.addr (pDk s₀), K.dkLen⟩
  d_es : (⟨State.addr (pEk s₀), K.ekLen⟩ : Region).Disjoint ⟨State.addr (pScr s₀), K.scratch⟩
  d_ds : (⟨State.addr (pDk s₀), K.dkLen⟩ : Region).Disjoint ⟨State.addr (pScr s₀), K.scratch⟩
  b_s : (below s₀ 8).Disjoint ⟨State.addr (pSeed s₀), 64⟩
  b_e : (below s₀ 8).Disjoint ⟨State.addr (pEk s₀), K.ekLen⟩
  b_d : (below s₀ 8).Disjoint ⟨State.addr (pDk s₀), K.dkLen⟩
  b_c : (below s₀ 8).Disjoint ⟨State.addr (pScr s₀), K.scratch⟩
  f_s : (pSeed s₀).toNat + 64 ≤ 2 ^ 32
  f_e : (pEk s₀).toNat + K.ekLen ≤ 2 ^ 32
  f_d : (pDk s₀).toNat + K.dkLen ≤ 2 ^ 32
  f_c : (pScr s₀).toNat + K.scratch ≤ 2 ^ 32

section
variable {K : KemLay} {s₀ : State} (hp : Pre K s₀)
include hp

theorem stack_eq : (⟨State.addr (s₀.sp - BitVec.ofNat 32 8), 8⟩ : Region) = below s₀ 8 := by
  rw [addr_sub hp.sp8]

theorem lay_ok : (lay s₀ K).Ok := by
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
structure KEnv (K : KemLay) (s₀ s : State) : Prop where
  ctx : Ctx (lay s₀ K) s
  r4 : s.gpr .r4 = pSeed s₀
  r5 : s.gpr .r5 = pEk s₀
  r6 : s.gpr .r6 = pDk s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  sav : Saved s.mem ((lay s₀ K).A 0 840) s₀.gpr
  savlr : s.mem.readW ((lay s₀ K).A 0 872) 32 = s₀.gpr .lr
  seed : bytesAt s.mem ((lay s₀ K).A 2 0) 64 = bytesAt s₀.mem ((lay s₀ K).A 2 0) 64

/-- A region the phases may change: apart from the saved registers and the seed. -/
def okW (K : KemLay) (w : Nat × Nat × Nat) : Bool := sepB (kSz K) (0, 840, 36) w && sepB (kSz K) (2, 0, 64) w

/-- The buffer of each pointer register. -/
def kidx : Reg → Nat
  | .r4 => 2 | .r5 => 3 | .r6 => 4 | _ => 0

/-- Decides a fact about the offsets in the buffers. -/
macro "ldecide" : tactic => `(tactic| first
  | decide
  | ((try simp only [lay_sizes, kSz, kidx, okW, kRegs, List.all_cons, List.all_nil, List.all_append, List.map_cons,
        List.map_nil, trip, Bool.and_true])
     (try have := (‹KemLay.WF _›).scr)
     kdecide))

theorem KEnv.keep {K : KemLay} {s₀ s s' : State} (hp : Pre K s₀) (h : KEnv K s₀ s) {xs : List Reg}
    {W : List (Nat × Nat × Nat)} (hk : KeptX xs ((lay s₀ K).RL W) s s') (hx : ∀ r ∈ [Reg.r4, .r5, .r6, .r7], r ∉ xs)
    (hW : W.all (okW K) = true) : KEnv K s₀ s' := by
  have hL := lay_ok hp
  have h1 : sepAll (lay s₀ K).sizes (0, 840, 36) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [okW, Bool.and_eq_true] at this; exact this.1
  have h2 : sepAll (lay s₀ K).sizes (2, 0, 64) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [okW, Bool.and_eq_true] at this; exact this.2
  have hd := Lay.disjAll hL h1
  have hc : (Lay.R (lay s₀ K) 0 840 36).Contains ((lay s₀ K).A 0 872) 4 := by
    simp only [Region.Contains]; bv_omega
  refine ⟨hk.ctx (by simp at hx; exact hx.2.2.2) h.ctx, ?_, ?_, ?_, hk.rd.trans h.rd, hk.wr.trans h.wr,
    hk.sp.trans h.sp, fun i hi => ?_, ?_, ?_⟩
  · rw [hk.cs .r4 (by decide) (by decide) (hx .r4 (by simp)), h.r4]
  · rw [hk.cs .r5 (by decide) (by decide) (hx .r5 (by simp)), h.r5]
  · rw [hk.cs .r6 (by decide) (by decide) (hx .r6 (by simp)), h.r6]
  · rw [hk.frame.readW (r := Lay.R (lay s₀ K) 0 840 36) (by simp only [Region.Contains]; bv_omega) hd (by decide)]
    exact h.sav i hi
  · rw [hk.frame.readW hc hd (by decide)]; exact h.savlr
  · rw [Lay.bytes_keep hL hk.frame h2 (by decide)]; exact h.seed

theorem buf_wr {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    (lay s₀ K).buf 0 ∈ s₀.wr ∧ (lay s₀ K).buf 3 ∈ s₀.wr ∧ (lay s₀ K).buf 4 ∈ s₀.wr ∧
      (lay s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr := by
  rw [hp.wr, hp.rd]; simp [Lay.buf, lay]

theorem setup_ok {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    WP isa (.block K.kgSetup) s₀ fun s => KEnv K s₀ s ∧ s.mem ((lay s₀ K).A 0 oK) = BitVec.ofNat 8 K.k := by
  have hL := lay_ok hp
  have hK := hp.wf
  have fc := hp.f_c
  have := hK.scr
  obtain ⟨w0, -, -, -⟩ := buf_wr hp
  have wS : ∀ {o n : Nat}, o + n ≤ 32768 → InRegions s₀.wr ((lay s₀ K).A 0 o) n := fun h =>
    Lay.covers w0 (by simp only [lay, Lay.size, List.getD_cons_zero]; omega) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [KemLay.kgSetup, WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r3 (off := 840) (by decide) (fit_le (by omega) fc) fun i hi => by
    rw [add_ofNat_add]; exact wS (by omega)) fun s₁ h₁ => ?_
  have g3 : s₁.gpr .r3 = pScr s₀ := by rw [h₁.gpr]
  have e872 : State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (oSave + 32)) = (lay s₀ K).A 0 872 := by
    rw [g3]; exact addr_add (by offs)
  have e1152 : State.addr (s₁.gpr .r3 + BitVec.ofNat 32 oK) = (lay s₀ K).A 0 1152 := by
    rw [g3]; exact addr_add (by offs)
  have i872 : InRegions s₁.wr (State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (oSave + 32))) 4 := by
    rw [e872, h₁.wr]; exact wS (by decide)
  have i1152 : InRegions s₁.wr (State.addr (s₁.gpr .r3 + BitVec.ofNat 32 oK)) 1 := by
    rw [e1152, h₁.wr]; exact wS (by decide)
  have o1 : oSave + 32 < 4096 := by decide
  have o2 : oK < 4096 := by decide
  have e3 : encodable (BitVec.ofNat 32 K.k) = true := by kenc
  run_block [i872, i1152, o1, o2, e3]
  have eS : (lay s₀ K).A 0 840 = State.addr (s₀.gpr .r3) + BitVec.ofNat 64 840 := rfl
  have ne1 : ∀ i < 8, ∀ (m : Mem) (v : BitVec 32), (m.writeW ((lay s₀ K).A 0 872) v).readW
      ((lay s₀ K).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 = m.readW ((lay s₀ K).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 :=
    fun i hi m v => Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by decide)
  have ne2 : ∀ i < 9, ∀ (m : Mem) (v : Byte), (m.writeW ((lay s₀ K).A 0 1152) v).readW
      ((lay s₀ K).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 = m.readW ((lay s₀ K).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 :=
    fun i hi m v => Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by decide)
  refine ⟨⟨⟨hL, hK.scr, rfl, by simp [lay], ?_, by show 8 ≤ s₁.sp.toNat; rw [h₁.sp]; exact hp.sp8, ?_, ?_⟩, ?_, ?_, ?_,
    h₁.rd, h₁.wr, h₁.sp, fun i hi => ?_, ?_, ?_⟩, ?_⟩
  · simp [h₁.gpr]; rfl
  · show s₀.sp - BitVec.ofNat 32 8 = s₁.sp - BitVec.ofNat 32 8
    rw [h₁.sp]
  · show (⟨State.addr (pScr s₀), K.scratch⟩ : Region) ∈ s₁.wr
    rw [h₁.wr, hp.wr]; simp
  · simp [h₁.gpr]
  · simp [h₁.gpr]
  · simp [h₁.gpr]
  · show ((s₁.mem.writeW _ _).writeW _ _).readW _ _ = _
    rw [e872, e1152, ne2 i (by omega), ne1 i hi]
    exact h₁.saved i hi
  · show ((s₁.mem.writeW _ _).writeW _ _).readW _ _ = _
    rw [e872, e1152, show (lay s₀ K).A 0 872 = (lay s₀ K).A 0 840 + BitVec.ofNat 64 (4 * 8) by
      rw [add_ofNat_add], ne2 8 (by decide), add_ofNat_add, Mem.readW_writeW_self32, h₁.gpr]
  · show bytesAt ((s₁.mem.writeW _ _).writeW _ _) _ _ = _
    rw [e872, e1152]
    have fr : Frame ((lay s₀ K).RL [(0, 840, 36), (0, 1152, 1)]) s₀.mem
        ((s₁.mem.writeW ((lay s₀ K).A 0 872) (s₁.gpr .lr)).writeW ((lay s₀ K).A 0 1152)
          (BitVec.setWidth 8 (BitVec.ofNat 32 K.k))) := by
      refine ((h₁.frame.sub fun r hr => ⟨Lay.R (lay s₀ K) 0 840 36, by simp, ?_⟩).writeW
        (r := Lay.R (lay s₀ K) 0 840 36) (by simp) _ ?_).writeW (r := Lay.R (lay s₀ K) 0 1152 1) (by simp) _ ?_
      · rw [List.mem_singleton] at hr; subst hr
        show Region.Sub (Lay.R (lay s₀ K) 0 840 32) _
        exact Lay.R_sub_R hL (by simp [lay]) (by decide) (by decide) (by simp [lay]; omega)
      · simp only [Region.Contains]; bv_omega
      · simp only [Region.Contains]; bv_omega
    exact Lay.bytes_keep hL fr (by ldecide) (by decide)
  · show ((s₁.mem.writeW _ _).writeW _ _) _ = _
    rw [e1152, writeW8_apply, ite_eq_left rfl, setWidth8_ofNat (by have := hK.k4; omega)]

/-! ## Pieces of the hashes -/

theorem pieceK {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s) {p : Piece} {w : Bool}
    (hb : p.base = .r4 ∨ p.base = .r5 ∨ p.base = .r6 ∨ p.base = .r7) (hw : w = true → p.base ≠ .r4)
    (hoe : encodable (BitVec.ofNat 32 p.off) = true) (hle : encodable (BitVec.ofNat 32 p.len) = true)
    (hpos : 0 < p.len) (hlt : p.off + p.len < 2 ^ 32)
    (hsep : sepAll (kSz K) (kidx p.base, p.off, p.len) kRegs = true) :
    PieceOk (lay s₀ K) kidx s w p := by
  obtain ⟨w0, w3, w4, w2⟩ := buf_wr hp
  rw [← h.wr] at w0 w3 w4
  rw [← h.wr, ← h.rd] at w2
  have hsep' : sepAll (lay s₀ K).sizes (kidx p.base, p.off, p.len) kRegs = true := hsep
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

/-! ## `G(d ‖ k)` -/

/-- `d`, the first half of the seed. -/
abbrev D (s₀ : State) : List Byte := bytesAt s₀.mem (State.addr (pSeed s₀)) 32

/-- `z`, the second half of the seed. -/
abbrev Z (s₀ : State) : List Byte := bytesAt s₀.mem (State.addr (pSeed s₀) + BitVec.ofNat 64 32) 32

theorem rate72 : 72 ∈ Spec.Sha3.rates := by decide

theorem g_ins {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s) :
    ∀ p ∈ [(⟨.r4, 0, 32⟩ : Piece), ⟨.r7, oK, 1⟩], PieceOk (lay s₀ K) kidx s false p := by
  have hK := hp.wf
  intro p hp'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl
  · exact pieceK hp h (.inl rfl) (by simp) (by decide) (by decide) (by decide) (by decide) (by ldecide)
  · exact pieceK hp h (.inr (.inr (.inr rfl))) (by simp) (by decide) (by decide) (by decide) (by decide)
      (by ldecide)

theorem g_outs {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s) :
    ∀ p ∈ [(⟨.r7, oG, 64⟩ : Piece)], PieceOk (lay s₀ K) kidx s true p := by
  have hK := hp.wf
  intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
  exact pieceK hp h (.inr (.inr (.inr rfl))) (by simp) (by decide) (by decide) (by decide) (by decide)
    (by ldecide)

theorem g_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s)
    (h3 : s.mem ((lay s₀ K).A 0 oK) = BitVec.ofNat 8 K.k) :
    WP isa (hash 72 0x06 [⟨.r4, 0, 32⟩, ⟨.r7, oK, 1⟩] [⟨.r7, oG, 64⟩]) s fun s' =>
      KEnv K s₀ s' ∧ bytesAt s'.mem ((lay s₀ K).A 0 oG) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₀) ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₀) := by
  have hK := hp.wf
  have hin := g_ins hp h
  have hout := g_outs hp h
  have hD : bytesAt s.mem ((lay s₀ K).A 2 0) 32 = D s₀ := by
    have := congrArg (List.take 32) h.seed
    rw [bytesAt_take _ _ (by decide), bytesAt_take _ _ (by decide)] at this
    rw [this]; show bytesAt s₀.mem (State.addr (pSeed s₀) + BitVec.ofNat 64 0) 32 = _; rw [add_ofNat_zero]
  have hin' : (List.map ((lay s₀ K).pb kidx s.mem) [⟨.r4, 0, 32⟩, ⟨.r7, oK, 1⟩]).flatten =
      D s₀ ++ [BitVec.ofNat 8 K.k] := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    show bytesAt s.mem ((lay s₀ K).A 2 0) 32 ++ bytesAt s.mem ((lay s₀ K).A 0 oK) 1 = _
    rw [hD, bytes_one, h3]
  refine WP.mono (hash_ok rate72 (by decide) (by decide) (by decide) h.ctx (List.cons_ne_nil _ _) hin hout
    (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ => ⟨?_, ?_⟩
  · exact h.keep hp (k'.x []) (by simp) (by ldecide)
  · have e1 := o'.1
    rw [hin'] at e1
    have e2 : bytesAt s'.mem ((lay s₀ K).A 0 oG) 64 = (G (D s₀ ++ [BitVec.ofNat 8 K.k])).1 ++
        (G (D s₀ ++ [BitVec.ofNat 8 K.k])).2 := e1.trans (G_split _)
    rw [show (64 : Nat) = 32 + 32 from rfl, bytesAt_add] at e2
    have l1 : (bytesAt s'.mem ((lay s₀ K).A 0 oG) 32).length = (G (D s₀ ++ [BitVec.ofNat 8 K.k])).1.length := by
      rw [bytesAt_length, VG.Proof.MlKem.G_fst_length]
    obtain ⟨r1, r2⟩ := List.append_inj e2 l1
    refine ⟨r1, ?_⟩
    show bytesAt s'.mem (State.addr ((lay s₀ K).ptr 0) + BitVec.ofNat 64 (888 + 32)) 32 = _
    rw [← add_ofNat_add]; exact r2

theorem rho_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s)
    (hr : bytesAt s.mem ((lay s₀ K).A 0 oG) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₀))
    (hs : bytesAt s.mem ((lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₀)) :
    WP isa (copy .r7 oG .r7 oSeed 32) s fun s' => KEnv K s₀ s' ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₀) ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₀) := by
  have hL := lay_ok hp
  have hK := hp.wf
  obtain ⟨w0, -, -, -⟩ := buf_wr hp
  refine WP.mono (copyL hL (i := 0) (j := 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h.ctx.r7 h.ctx.r7
    (by decide) (by decide) (by decide) (by decide) (by decide) (by ldecide)
    (by rw [h.rd, h.wr]; exact mem_rd_wr w0) (by rw [h.wr]; exact w0)) fun s' ⟨k', b'⟩ =>
    ⟨h.keep hp (k'.x []) (by simp) (by ldecide), b'.trans hr,
      (Lay.bytes_keep hL k'.frame (by ldecide) (by decide)).trans hs⟩

/-! ## The `PRF`s -/

theorem prf_phase {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s)
    (hr : bytesAt s.mem ((lay s₀ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₀))
    (hs : bytesAt s.mem ((lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₀)) :
    WP isa (K.prfLoop true 0 (2 * K.k)) s fun s' => KEnv K s₀ s' ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₀) ∧
      ∀ N < 2 * K.k, PolyIs s'.mem ((lay s₀ K).A 0 (oPoly (K.k + N)))
        (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (D s₀)) N)) := by
  have hK := hp.wf
  exact WP.mono (prfLoop_ok hK h.ctx true (by have := hK.k1; omega) (by omega) hs) fun s' ⟨k', p'⟩ =>
    ⟨h.keep hp k' (by simp) (by ldecide), by rw [← hr]; exact Lay.bytes_keep (lay_ok hp) k'.frame (by ldecide) (by decide),
      fun N hN => p' N (Nat.zero_le _) hN⟩

/-! ## The rows of `t̂` -/

section
variable (K : KemLay) (s₀ : State)

/-- `ρ`. -/
abbrev ρ₀ : List Byte := VG.Proof.MlKem.KPke.kgRho K.p (D s₀)

/-- `ŝ`. -/
abbrev sK : Nat → Poly := VG.Proof.MlKem.KPke.kgS K.p (D s₀)

/-- The entries of `Â` the products use. -/
abbrev aK (i j : Nat) : Poly := effA false (ρ₀ K s₀) i j (sK K s₀ j)

/-- Whether the `SampleNTT`s of the first `i` rows finished. -/
def okK (i : Nat) : Bool := (List.range i).all fun i' => okRow false (ρ₀ K s₀) i' K.k

/-- `t̂`. -/
abbrev tK : Nat → Poly := VG.Proof.MlKem.KPke.kgT K.p (aK K s₀) (D s₀)

end

theorem okK_succ (K : KemLay) (s₀ : State) (i : Nat) :
    okK K s₀ (i + 1) = (okK K s₀ i && okRow false (ρ₀ K s₀) i K.k) := by
  simp only [okK, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

/-- After the first `i` rows. -/
structure KRow (K : KemLay) (s₀ : State) (i : Nat) (s : State) : Prop where
  env : KEnv K s₀ s
  r9 : s.gpr .r9 = BitVec.ofNat 32 i
  r11 : s.gpr .r11 = if okK K s₀ i then 1 else 0
  rho : bytesAt s.mem ((lay s₀ K).A 0 oSeed) 32 = ρ₀ K s₀
  slots : ∀ N < 2 * K.k, PolyIs s.mem ((lay s₀ K).A 0 (oPoly (K.k + N)))
    (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (D s₀)) N))
  ek : ∀ i' < i, bytesAt s.mem ((lay s₀ K).A 3 (384 * i')) 384 = encode12 (tK K s₀ i')

/-- What a row changes. -/
abbrev rowK (K : KemLay) (i : Nat) : List (Nat × Nat × Nat) :=
  [(0, 1248, 2), (0, K.oAcc, 3072), (0, K.oSample, 3072), (1, 0, 8), (0, K.oAcc, 1024), (3, 384 * i, 384)]

/-- `rowK_ok` with the sizes `sz` of the buffers. -/
abbrev RowKF (K : KemLay) (sz : List Nat) : Prop := ∀ i < K.k,
    (rowK K i).all (fun w => sepB sz (0, 840, 36) w && sepB sz (2, 0, 64) w) = true ∧
    sepAll sz (0, oSeed, 32) (rowK K i) = true ∧
    (∀ N < 2 * K.k, sepAll sz (0, oPoly (K.k + N), 1024) (rowK K i) = true) ∧
    (∀ i' < K.k, i' ≠ i → sepAll sz (3, 384 * i', 384) (rowK K i) = true) ∧
    sepB sz (0, K.oAcc, 1024) (3, 384 * i, 384) = true ∧
    sepB sz (0, K.oAcc, 1024) (0, oPoly (K.k + (K.k + i)), 1024) = true

theorem rowK_ok {K : KemLay} (hK : K.WF) {i : Nat} (hi : i < K.k) : (rowK K i).all (okW K) = true ∧
    sepAll (kSz K) (0, oSeed, 32) (rowK K i) = true ∧
    (∀ N < 2 * K.k, sepAll (kSz K) (0, oPoly (K.k + N), 1024) (rowK K i) = true) ∧
    (∀ i' < K.k, i' ≠ i → sepAll (kSz K) (3, 384 * i', 384) (rowK K i) = true) ∧
    sepB (kSz K) (0, K.oAcc, 1024) (3, 384 * i, 384) = true ∧
    sepB (kSz K) (0, K.oAcc, 1024) (0, oPoly (K.k + (K.k + i)), 1024) = true := by
  have scr := hK.scr
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ :=
    (by decide : ∀ k < 5, RowKF (kOf k) (kSz (kOf k))) K.k (by have := hK.k4; omega) i hi
  refine ⟨List.all_eq_true.mpr fun w hw => ?_, sepAll_scr c2 scr, fun N hN => sepAll_scr (c3 N hN) scr,
    fun i' hi' hne => sepAll_scr (c4 i' hi' hne) scr, sepB_scr c5 scr, sepB_scr c6 scr⟩
  have := List.all_eq_true.mp c1 w hw
  simp only [okW, Bool.and_eq_true] at this ⊢
  exact ⟨sepB_scr this.1 scr, sepB_scr this.2 scr⟩

/-- The row's facts at its start `s`, for its `RowSum`. -/
theorem KRow.rowPre {K : KemLay} {s₀ : State} (hp : Pre K s₀) {i : Nat} (hi : i < K.k) {s : State}
    (h : KRow K s₀ i s) : RowPre K (lay s₀ K) (ρ₀ K s₀) (sK K s₀) i (okK K s₀ i) s :=
  ⟨hp.wf, h.env.ctx, hi, h.r9, h.r11, h.rho, fun j hj => h.slots j (by omega)⟩

section
variable (K : KemLay) (s₀ : State) (i : Nat) (s : State)

/-- After the arguments of `t̂[i] += ê[i]`. -/
structure KR2 (s₂ : State) : Prop where
  kx : KeptX [.r9, .r10, .r11] ((lay s₀ K).RL (rowK K i)) s s₂
  r9 : s₂.gpr .r9 = BitVec.ofNat 32 i
  r0 : s₂.gpr .r0 = (lay s₀ K).ptr 0 + BitVec.ofNat 32 K.oAcc
  r1 : s₂.gpr .r1 = (lay s₀ K).ptr 0 + BitVec.ofNat 32 (oPoly (K.k + (K.k + i)))
  r11 : s₂.gpr .r11 = if okK K s₀ (i + 1) then 1 else 0
  acc : PolyIs s₂.mem ((lay s₀ K).A 0 K.oAcc) (VG.Proof.MlKem.KPke.dotK (aK K s₀ i) (sK K s₀) K.k)

/-- After `t̂[i]`. -/
structure KR3 (s₃ : State) : Prop where
  kx : KeptX [.r9, .r10, .r11] ((lay s₀ K).RL (rowK K i)) s s₃
  r9 : s₃.gpr .r9 = BitVec.ofNat 32 i
  r11 : s₃.gpr .r11 = if okK K s₀ (i + 1) then 1 else 0
  acc : PolyIs s₃.mem ((lay s₀ K).A 0 K.oAcc) (tK K s₀ i)

/-- After the arguments of its encoding. -/
structure KR4 (s₄ : State) : Prop where
  r3 : KR3 K s₀ i s s₄
  r0 : s₄.gpr .r0 = (lay s₀ K).ptr 0 + BitVec.ofNat 32 K.oAcc
  r1 : s₄.gpr .r1 = (lay s₀ K).ptr 3 + BitVec.ofNat 32 (384 * i)

/-- After its encoding. -/
structure KR5 (s₅ : State) : Prop where
  kx : KeptX [.r9, .r10, .r11] ((lay s₀ K).RL (rowK K i)) s s₅
  r9 : s₅.gpr .r9 = BitVec.ofNat 32 i
  r11 : s₅.gpr .r11 = if okK K s₀ (i + 1) then 1 else 0
  enc : bytesAt s₅.mem ((lay s₀ K).A 3 (384 * i)) 384 = encode12 (tK K s₀ i)

end

theorem KRow.ctxOf {K : KemLay} {s₀ : State} {i : Nat} {s : State} (h : KRow K s₀ i s) {x : State} {xs : List Reg}
    {W : List (Nat × Nat × Nat)} (k : KeptX xs ((lay s₀ K).RL W) s x) (h7 : Reg.r7 ∉ xs) : Ctx (lay s₀ K) x :=
  k.ctx h7 h.env.ctx

section
variable {K : KemLay} {s₀ : State} (hp : Pre K s₀) {i : Nat} (hi : i < K.k) {s : State} (h : KRow K s₀ i s)
include hp hi h

theorem kr2_ok {s₁ : State}
    (r : RowInv K (lay s₀ K) false (ρ₀ K s₀) (sK K s₀) i (okK K s₀ i) s K.k s₁) :
    WP isa (.block (ptrTo .r0 .r7 K.oAcc :: slotAt .r1 .r9 (oPoly (2 * K.k)))) s₁ (KR2 K s₀ i s) := by
  have hK := hp.wf
  have hc₁ := h.ctxOf r.kx (by decide)
  have g9₁ : s₁.gpr .r9 = BitVec.ofNat 32 i := by rw [r.kx.cs .r9 (by decide) (by decide) (by decide), h.r9]
  refine WP.mono (ptrSlot_ok (i := i) hc₁.r7 g9₁ (by kenc) (by kenc)) fun s₂ ⟨o₂, a0, a1⟩ => ?_
  rw [slot_eq _ (by offs), show oPoly (2 * K.k) + 1024 * i = oPoly (K.k + (K.k + i)) by offs] at a1
  exact ⟨((r.kx.weaken (by simp)).monoL (by simp)).trans (o₂.x _ _),
    by rw [o₂.cs .r9 (by decide) (by decide), g9₁], a0, a1,
    by rw [o₂.cs .r11 (by decide) (by decide), r.r11, ← okK_succ],
    by rw [o₂.mem, ← rowAcc_eq]; exact r.acc⟩

theorem kr3_ok {s₂ : State} (r : KR2 K s₀ i s s₂) : WP isa callAdd s₂ (KR3 K s₀ i s) := by
  have hL := lay_ok hp
  have hc₂ := h.ctxOf r.kx (by decide)
  obtain ⟨-, -, c_slots, -, -, c_add⟩ := rowK_ok hp.wf hi
  have sl₂ : PolyIs s₂.mem ((lay s₀ K).A 0 (oPoly (K.k + (K.k + i))))
      (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (D s₀)) (K.k + i))) :=
    Lay.polyIs_keep hL r.kx.frame (c_slots (K.k + i) (by omega)) (h.slots (K.k + i) (by omega))
  exact addL hL r.r0 r.r1 c_add hc₂.buf0 (mem_rd_wr hc₂.buf0) r.acc sl₂ fun s₃ k₃ p₃ =>
    ⟨r.kx.trans ((k₃.x _).monoL (by simp)), by rw [k₃.cs .r9 (by decide) (by decide), r.r9],
      by rw [k₃.cs .r11 (by decide) (by decide), r.r11], p₃⟩

theorem kr4_ok {s₃ : State} (r : KR3 K s₀ i s s₃) :
    WP isa (.block (ptrTo .r0 .r7 K.oAcc :: at384 .r1 .r5 .r9)) s₃ (KR4 K s₀ i s) := by
  have hK := hp.wf
  have hc₃ := h.ctxOf r.kx (by decide)
  have g5₃ : s₃.gpr .r5 = pEk s₀ := by rw [r.kx.cs .r5 (by decide) (by decide) (by decide), h.env.r5]
  refine WP.mono (ptr384_ok (b := .r5) (.inl rfl) hc₃.r7 g5₃ r.r9 (by kenc)) fun s₄ ⟨o₄, b0, b1⟩ => ?_
  rw [at384_eq _ (by offs)] at b1
  exact ⟨⟨r.kx.trans (o₄.x _ _), by rw [o₄.cs .r9 (by decide) (by decide), r.r9],
    by rw [o₄.cs .r11 (by decide) (by decide), r.r11], by rw [o₄.mem]; exact r.acc⟩, b0, b1⟩

theorem kr5_ok {s₄ : State} (r : KR4 K s₀ i s s₄) : WP isa callEncode12 s₄ (KR5 K s₀ i s) := by
  have hL := lay_ok hp
  have hc₄ := h.ctxOf r.r3.kx (by decide)
  obtain ⟨-, -, -, -, c_enc, -⟩ := rowK_ok hp.wf hi
  obtain ⟨-, w3, -, -⟩ := buf_wr hp
  exact encode12L hL (i := 0) (j := 3) (o' := 384 * i) r.r0 r.r1 c_enc (mem_rd_wr hc₄.buf0)
    (by rw [r.r3.kx.wr, h.env.wr]; exact w3) r.r3.acc fun s₅ k₅ e₅ =>
    ⟨r.r3.kx.trans ((k₅.x _).monoL (by simp)), by rw [k₅.cs .r9 (by decide) (by decide), r.r3.r9],
      by rw [k₅.cs .r11 (by decide) (by decide), r.r3.r11], e₅⟩

theorem kr6_ok {s₅ : State} (r : KR5 K s₀ i s s₅) :
    WP isa (.block (count .r9 K.k)) s₅ fun s' => KRow K s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = K.k) := by
  have hL := lay_ok hp
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨c_ok, c_rho, c_slots, c_ek, -, -⟩ := rowK_ok hK hi
  refine WP.mono (count_ok (by omega) (by omega) (by kenc) r.r9) fun s' ⟨k', g', z'⟩ => ⟨⟨?_, g', ?_, ?_, ?_, ?_⟩, z'⟩
  all_goals have K' : KeptX [.r9, .r10, .r11] ((lay s₀ K).RL (rowK K i)) s s' :=
    r.kx.trans ((k'.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil))
  · exact h.env.keep hp K' (by simp) c_ok
  · rw [k'.cs .r11 (by decide) (by decide) (by decide), r.r11]
  · rw [← h.rho]; exact Lay.bytes_keep hL K'.frame c_rho (by decide)
  · exact fun N hN => Lay.polyIs_keep hL K'.frame (c_slots N hN) (h.slots N hN)
  · intro i' hi'
    by_cases e : i' = i
    · subst e
      exact (bytesAt_frame k'.frame (fun _ h => absurd h List.not_mem_nil) (by decide)).trans r.enc
    · rw [← h.ek i' (by omega)]; exact Lay.bytes_keep hL K'.frame (c_ek i' (by omega) e) (by decide)

end

theorem kgRow_step {K : KemLay} {s₀ : State} (hp : Pre K s₀) {i : Nat} (hi : i < K.k) {s : State}
    (h : KRow K s₀ i s) :
    WP isa K.kgRowBody s fun s' => KRow K s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = K.k) :=
  WP.seq (WP.mono (rowSum_ok (transpose := false) (h.rowPre hp hi)) fun _ r₁ =>
    WP.seq (WP.mono (kr2_ok hp hi h r₁) fun _ r₂ => WP.seq (WP.mono (kr3_ok hp hi h r₂) fun _ r₃ =>
    WP.seq (WP.mono (kr4_ok hp hi h r₃) fun _ r₄ => WP.seq (WP.mono (kr5_ok hp hi h r₄) fun _ r₅ =>
      kr6_ok hp hi h r₅)))))

theorem rows_init {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s)
    (hr : bytesAt s.mem ((lay s₀ K).A 0 oSeed) 32 = ρ₀ K s₀)
    (hs : ∀ N < 2 * K.k, PolyIs s.mem ((lay s₀ K).A 0 (oPoly (K.k + N)))
      (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (D s₀)) N))) :
    WP isa (.block [.mov .r11 (.imm 1), .mov .r9 (.imm 0)]) s (KRow K s₀ 0) :=
  WP.mono flagInit_ok fun _ ⟨k₁, g11, g9, m₁⟩ =>
    ⟨h.keep hp (xs := [.r9, .r11]) (W := []) k₁ (by simp) rfl, g9, by rw [g11]; rfl, by rw [m₁]; exact hr,
      by rw [m₁]; exact hs, fun i' hi' => absurd hi' (Nat.not_lt_zero _)⟩

/-! ## `ŝ` into `dk` -/

/-- After encoding the first `j` polynomials of `ŝ`. -/
structure KS (K : KemLay) (s₀ : State) (j : Nat) (s : State) : Prop where
  env : KEnv K s₀ s
  r9 : s.gpr .r9 = BitVec.ofNat 32 j
  r11 : s.gpr .r11 = if okK K s₀ K.k then 1 else 0
  rho : bytesAt s.mem ((lay s₀ K).A 0 oSeed) 32 = ρ₀ K s₀
  ek : ∀ i' < K.k, bytesAt s.mem ((lay s₀ K).A 3 (384 * i')) 384 = encode12 (tK K s₀ i')
  slots : ∀ j' < K.k, PolyIs s.mem ((lay s₀ K).A 0 (oPoly (K.k + j'))) (sK K s₀ j')
  dk : ∀ j' < j, bytesAt s.mem ((lay s₀ K).A 4 (384 * j')) 384 = encode12 (sK K s₀ j')

/-- `sK_ok` with the sizes `sz` of the buffers. -/
abbrev SKF (K : KemLay) (sz : List Nat) : Prop := ∀ j < K.k,
    [((4 : Nat), 384 * j, (384 : Nat))].all (fun w => sepB sz (0, 840, 36) w && sepB sz (2, 0, 64) w) = true ∧
    sepAll sz (0, oSeed, 32) [(4, 384 * j, 384)] = true ∧
    (∀ i' < K.k, sepAll sz (3, 384 * i', 384) [(4, 384 * j, 384)] = true) ∧
    (∀ j' < K.k, sepAll sz (0, oPoly (K.k + j'), 1024) [(4, 384 * j, 384)] = true) ∧
    (∀ j' < K.k, j' ≠ j → sepAll sz (4, 384 * j', 384) [(4, 384 * j, 384)] = true) ∧
    sepB sz (0, oPoly (K.k + j), 1024) (4, 384 * j, 384) = true

theorem sK_ok {K : KemLay} (hK : K.WF) {j : Nat} (hj : j < K.k) : [((4 : Nat), 384 * j, (384 : Nat))].all (okW K) = true ∧
    sepAll (kSz K) (0, oSeed, 32) [(4, 384 * j, 384)] = true ∧
    (∀ i' < K.k, sepAll (kSz K) (3, 384 * i', 384) [(4, 384 * j, 384)] = true) ∧
    (∀ j' < K.k, sepAll (kSz K) (0, oPoly (K.k + j'), 1024) [(4, 384 * j, 384)] = true) ∧
    (∀ j' < K.k, j' ≠ j → sepAll (kSz K) (4, 384 * j', 384) [(4, 384 * j, 384)] = true) ∧
    sepB (kSz K) (0, oPoly (K.k + j), 1024) (4, 384 * j, 384) = true := by
  have scr := hK.scr
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ :=
    (by decide : ∀ k < 5, SKF (kOf k) (kSz (kOf k))) K.k (by have := hK.k4; omega) j hj
  refine ⟨List.all_eq_true.mpr fun w hw => ?_, sepAll_scr c2 scr, fun i' hi' => sepAll_scr (c3 i' hi') scr,
    fun j' hj' => sepAll_scr (c4 j' hj') scr, fun j' hj' hne => sepAll_scr (c5 j' hj' hne) scr, sepB_scr c6 scr⟩
  have := List.all_eq_true.mp c1 w hw
  simp only [okW, Bool.and_eq_true] at this ⊢
  exact ⟨sepB_scr this.1 scr, sepB_scr this.2 scr⟩

theorem s_init {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KRow K s₀ K.k s) :
    WP isa (.block [.mov .r9 (.imm 0)]) s (KS K s₀ 0) :=
  WP.mono (movc_ok .r9 (N := 0) (by decide)) fun _ ⟨k₆, g9', m₆⟩ =>
    ⟨h.env.keep hp (xs := [.r9]) (W := []) k₆ (by simp) rfl, g9',
      by rw [k₆.cs .r11 (by decide) (by decide) (by decide), h.r11], by rw [m₆]; exact h.rho,
      by rw [m₆]; exact h.ek, fun j' hj' => by rw [m₆]; exact h.slots j' (by omega),
      fun j' hj' => absurd hj' (Nat.not_lt_zero _)⟩

section
variable (K : KemLay) (s₀ : State) (j : Nat) (s : State)

/-- After the arguments of the encoding of `ŝ[j]`. -/
structure KS1 (s₁ : State) : Prop where
  o : Only s s₁
  r0 : s₁.gpr .r0 = (lay s₀ K).ptr 0 + BitVec.ofNat 32 (oPoly (K.k + j))
  r1 : s₁.gpr .r1 = (lay s₀ K).ptr 4 + BitVec.ofNat 32 (384 * j)

/-- After the encoding of `ŝ[j]`. -/
structure KS2 (s₂ : State) : Prop where
  kx : KeptX [.r9] ((lay s₀ K).RL [(4, 384 * j, 384)]) s s₂
  r9 : s₂.gpr .r9 = BitVec.ofNat 32 j
  enc : bytesAt s₂.mem ((lay s₀ K).A 4 (384 * j)) 384 = encode12 (sK K s₀ j)

end

section
variable {K : KemLay} {s₀ : State} (hp : Pre K s₀) {j : Nat} (hj : j < K.k) {s : State} (h : KS K s₀ j s)
include hp hj h

theorem ks1_ok : WP isa (.block (slotAt .r0 .r9 (oPoly K.k) ++ at384 .r1 .r6 .r9)) s (KS1 K s₀ j s) := by
  have hK := hp.wf
  refine WP.mono (slot384_ok (b := .r6) (.inr rfl) h.env.ctx.r7 h.env.r6 h.r9 (o' := oPoly K.k) (by kenc))
    fun s₁ ⟨o₁, a0, a1⟩ => ⟨o₁, ?_, ?_⟩
  · rw [a0, slot_eq _ (by offs), show oPoly K.k + 1024 * j = oPoly (K.k + j) by offs]
  · rw [a1, at384_eq _ (by offs)]; rfl

theorem ks2_ok {s₁ : State} (r : KS1 K s₀ j s s₁) : WP isa callEncode12 s₁ (KS2 K s₀ j s) := by
  have hL := lay_ok hp
  have hc₁ := h.env.ctx.only r.o
  obtain ⟨-, -, -, -, -, c_enc⟩ := sK_ok hp.wf hj
  obtain ⟨-, -, w4, -⟩ := buf_wr hp
  exact encode12L hL (i := 0) (j := 4) (o' := 384 * j) r.r0 r.r1 c_enc (mem_rd_wr hc₁.buf0)
    (by rw [r.o.wr, h.env.wr]; exact w4) (by rw [r.o.mem]; exact h.slots j hj) fun s₂ k₂ e₂ =>
    ⟨(r.o.x _ _).trans ((k₂.x _).monoL (by simp)),
      by rw [k₂.cs .r9 (by decide) (by decide), r.o.cs .r9 (by decide) (by decide), h.r9], e₂⟩

theorem ks3_ok {s₂ : State} (r : KS2 K s₀ j s s₂) :
    WP isa (.block (count .r9 K.k)) s₂ fun s' => KS K s₀ (j + 1) s' ∧ s'.z = decide (j + 1 = K.k) := by
  have hL := lay_ok hp
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨c_ok, c_rho, c_ek, c_slots, c_dk, -⟩ := sK_ok hK hj
  refine WP.mono (count_ok (by omega) (by omega) (by kenc) r.r9) fun s' ⟨k', g', z'⟩ =>
    ⟨⟨?_, g', ?_, ?_, ?_, ?_, ?_⟩, z'⟩
  all_goals have K' : KeptX [.r9] ((lay s₀ K).RL [(4, 384 * j, 384)]) s s' :=
    r.kx.trans (k'.mono (fun _ h => absurd h List.not_mem_nil))
  · exact h.env.keep hp K' (by simp) c_ok
  · rw [K'.cs .r11 (by decide) (by decide) (by decide), h.r11]
  · rw [← h.rho]; exact Lay.bytes_keep hL K'.frame c_rho (by decide)
  · exact fun i' hi' => (Lay.bytes_keep hL K'.frame (c_ek i' hi') (by decide)).trans (h.ek i' hi')
  · exact fun j' hj' => Lay.polyIs_keep hL K'.frame (c_slots j' hj') (h.slots j' hj')
  · intro j' hj'
    by_cases e : j' = j
    · subst e
      exact (bytesAt_frame k'.frame (fun _ h => absurd h List.not_mem_nil) (by decide)).trans r.enc
    · exact (Lay.bytes_keep hL K'.frame (c_dk j' (by omega) e) (by decide)).trans (h.dk j' (by omega))

end

theorem kgS_step {K : KemLay} {s₀ : State} (hp : Pre K s₀) {j : Nat} (hj : j < K.k) {s : State} (h : KS K s₀ j s) :
    WP isa K.kgSBody s fun s' => KS K s₀ (j + 1) s' ∧ s'.z = decide (j + 1 = K.k) :=
  WP.seq (WP.mono (ks1_ok hp hj h) fun _ r₁ => WP.seq (WP.mono (ks2_ok hp hj h r₁) fun _ r₂ => ks3_ok hp hj h r₂))

/-! ## The encapsulation key, `H(ek)` and `z` -/

section
variable (K : KemLay) (s₀ : State)

/-- `ek`. -/
abbrev EK : List Byte := VG.Proof.MlKem.KPke.ekPKE K.p (aK K s₀) (D s₀)

/-- `dk`. -/
abbrev DK : List Byte := VG.Proof.MlKem.KPke.dkPKE K.p (D s₀) ++ EK K s₀ ++ H (EK K s₀) ++ Z s₀

end

theorem h_ins {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s) :
    ∀ p ∈ [(⟨.r5, 0, K.ekLen⟩ : Piece)], PieceOk (lay s₀ K) kidx s false p := by
  have hK := hp.wf
  intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
  exact pieceK hp h (.inr (.inl rfl)) (by simp) enc0 hK.encEk (by offs) (by offs) (by ldecide)

theorem h_outs {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s) :
    ∀ p ∈ [(⟨.r6, 768 * K.k + 32, 32⟩ : Piece)], PieceOk (lay s₀ K) kidx s true p := by
  have hK := hp.wf
  intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
  exact pieceK hp h (.inr (.inr (.inl rfl))) (by simp) hK.encH (by dsimp only; decide) (by dsimp only; decide) (by offs) (by ldecide)

/-! What each step of the end keeps, for the proof of constant time. -/

section
variable {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s)
include hp h

theorem cpRho_env : WP isa (copy .r7 oSeed .r5 (384 * K.k) 32) s (KEnv K s₀) := by
  have hK := hp.wf
  obtain ⟨w0, w3, -, -⟩ := buf_wr hp
  exact WP.mono (copyL (lay_ok hp) (i := 0) (j := 3) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h.ctx.r7 h.r5
    (by decide) hK.encT (by decide) (by decide) (by decide) (by ldecide) (by rw [h.rd, h.wr]; exact mem_rd_wr w0)
    (by rw [h.wr]; exact w3)) fun _ ⟨k, _⟩ => h.keep hp (k.x []) (by simp) (by ldecide)

theorem cpEk_env : WP isa (copy .r5 0 .r6 (384 * K.k) K.ekLen) s (KEnv K s₀) := by
  have hK := hp.wf
  obtain ⟨-, w3, w4, -⟩ := buf_wr hp
  exact WP.mono (copyL (lay_ok hp) (i := 3) (j := 4) (so := 0) (dO := 384 * K.k) (len := K.ekLen) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ h.r5 h.r6 (by decide) hK.encT hK.encEk (by offs) (by offs) (by ldecide)
    (by rw [h.rd, h.wr]; exact mem_rd_wr w3) (by rw [h.wr]; exact w4)) fun _ ⟨k, _⟩ =>
    h.keep hp (k.x []) (by simp) (by ldecide)

theorem hashH_env : WP isa (hash 136 0x06 [⟨.r5, 0, K.ekLen⟩] [⟨.r6, 768 * K.k + 32, 32⟩]) s (KEnv K s₀) := by
  have hK := hp.wf
  exact WP.mono (hash_ok (idx := kidx) rate136 (by decide) (by decide) (by decide) h.ctx (List.cons_ne_nil _ _)
    (h_ins hp h) (h_outs hp h) (List.pairwise_singleton _ _)) fun _ ⟨k, _⟩ => h.keep hp (k.x []) (by simp) (by ldecide)

theorem cpZ_env : WP isa (copy .r4 32 .r6 (768 * K.k + 64) 32) s (KEnv K s₀) := by
  have hK := hp.wf
  obtain ⟨-, -, w4, w2⟩ := buf_wr hp
  exact WP.mono (copyL (lay_ok hp) (i := 2) (j := 4) (so := 32) (dO := 768 * K.k + 64) (len := 32)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h.r4 h.r6 (by decide) hK.encZ (by decide) (by decide) (by decide)
    (by ldecide) (by rw [h.rd, h.wr]; exact w2) (by rw [h.wr]; exact w4)) fun _ ⟨k, _⟩ =>
    h.keep hp (k.x []) (by simp) (by ldecide)

end

theorem ek_split (K : KemLay) (m : Mem) (q : Addr) :
    bytesAt m q K.ekLen = bytesAt m q (384 * K.k) ++ bytesAt m (q + BitVec.ofNat 64 (384 * K.k)) 32 :=
  bytesAt_add _ _ (384 * K.k) 32

theorem dk_split (K : KemLay) (m : Mem) (q : Addr) :
    bytesAt m q K.dkLen = bytesAt m q (384 * K.k) ++ bytesAt m (q + BitVec.ofNat 64 (384 * K.k)) K.ekLen ++
      bytesAt m (q + BitVec.ofNat 64 (768 * K.k + 32)) 32 ++ bytesAt m (q + BitVec.ofNat 64 (768 * K.k + 64)) 32 := by
  rw [show K.dkLen = 384 * K.k + (K.ekLen + (32 + 32)) by simp only [KemLay.dkLen, KemLay.ekLen]; omega,
    bytesAt_add _ _ (384 * K.k), bytesAt_add _ _ K.ekLen, bytesAt_add _ _ 32 32, add_ofNat_add, add_ofNat_add,
    show 384 * K.k + K.ekLen = 768 * K.k + 32 by simp only [KemLay.ekLen]; omega,
    show 768 * K.k + 32 + 32 = 768 * K.k + 64 by omega]
  simp only [List.append_assoc]

/-- What a region of `KEnv` must be apart from, with the sizes `sz` of the buffers. -/
abbrev okWz (sz : List Nat) (w : Nat × Nat × Nat) : Bool := sepB sz (0, 840, 36) w && sepB sz (2, 0, 64) w

theorem okWz_scr {r : List Nat} {s : Nat} {W : List (Nat × Nat × Nat)} (h : W.all (okWz (32768 :: r)) = true)
    (hs : 32768 ≤ s) : W.all (okWz (s :: r)) = true :=
  List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp h w hw
    simp only [okWz, Bool.and_eq_true] at this ⊢
    exact ⟨sepB_scr this.1 hs, sepB_scr this.2 hs⟩

/-- The separations of the copies and the hash of `tail_ok`, with the sizes `sz` of the buffers. -/
abbrev TailF (K : KemLay) (sz : List Nat) : Prop :=
  sepB sz (0, oSeed, 32) (3, 384 * K.k, 32) = true ∧ [(3, 384 * K.k, 32)].all (okWz sz) = true ∧
  (∀ i < K.k, sepAll sz (3, 384 * i, 384) [(3, 384 * K.k, 32)] = true) ∧
  sepB sz (3, 0, K.ekLen) (4, 384 * K.k, K.ekLen) = true ∧ [(4, 384 * K.k, K.ekLen)].all (okWz sz) = true ∧
  sepAll sz (3, 0, K.ekLen) [(4, 384 * K.k, K.ekLen)] = true ∧
  (kRegs ++ [(4, 768 * K.k + 32, 32)]).all (okWz sz) = true ∧
  sepB sz (2, 32, 32) (4, 768 * K.k + 64, 32) = true ∧ [(4, 768 * K.k + 64, 32)].all (okWz sz) = true ∧
  sepAll sz (3, 0, K.ekLen) [(4, 768 * K.k + 64, 32)] = true ∧
  sepAll sz (3, 0, K.ekLen) (kRegs ++ [(4, 768 * K.k + 32, 32)]) = true ∧
  (∀ i < K.k, sepAll sz (4, 384 * i, 384) [(4, 768 * K.k + 64, 32)] = true ∧
    sepAll sz (4, 384 * i, 384) (kRegs ++ [(4, 768 * K.k + 32, 32)]) = true ∧
    sepAll sz (4, 384 * i, 384) [(4, 384 * K.k, K.ekLen)] = true ∧
    sepAll sz (4, 384 * i, 384) [(3, 384 * K.k, 32)] = true) ∧
  sepAll sz (4, 384 * K.k, K.ekLen) [(4, 768 * K.k + 64, 32)] = true ∧
  sepAll sz (4, 384 * K.k, K.ekLen) (kRegs ++ [(4, 768 * K.k + 32, 32)]) = true ∧
  sepAll sz (4, 768 * K.k + 32, 32) [(4, 768 * K.k + 64, 32)] = true

theorem tail_facts {K : KemLay} (hK : K.WF) : TailF K (kSz K) := by
  have s := hK.scr
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ :=
    (by decide : ∀ k < 5, TailF (kOf k) (kSz (kOf k))) K.k (by have := hK.k4; omega)
  exact ⟨sepB_scr f1 s, okWz_scr f2 s, fun i hi => sepAll_scr (f3 i hi) s, sepB_scr f4 s, okWz_scr f5 s,
    sepAll_scr f6 s, okWz_scr f7 s, sepB_scr f8 s, okWz_scr f9 s, sepAll_scr f10 s, sepAll_scr f11 s,
    fun i hi => ⟨sepAll_scr (f12 i hi).1 s, sepAll_scr (f12 i hi).2.1 s, sepAll_scr (f12 i hi).2.2.1 s,
      sepAll_scr (f12 i hi).2.2.2 s⟩, sepAll_scr f13 s, sepAll_scr f14 s, sepAll_scr f15 s⟩

theorem tail_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KS K s₀ K.k s) :
    WP isa (.seq (copy .r7 oSeed .r5 (384 * K.k) 32) <| .seq (copy .r5 0 .r6 (384 * K.k) K.ekLen) <|
      .seq (hash 136 0x06 [⟨.r5, 0, K.ekLen⟩] [⟨.r6, 768 * K.k + 32, 32⟩]) <|
      .seq (copy .r4 32 .r6 (768 * K.k + 64) 32) (.block topEnd)) s
      fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧
        s'.gpr .r0 = (if okK K s₀ K.k then 1 else 0) ∧ bytesAt s'.mem (State.addr (pEk s₀)) K.ekLen = EK K s₀ ∧
        bytesAt s'.mem (State.addr (pDk s₀)) K.dkLen = DK K s₀ := by
  have hL := lay_ok hp
  have hK := hp.wf
  have k4 := hK.k4
  have scr := hK.scr
  obtain ⟨w0, w3, w4, w2⟩ := buf_wr hp
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ := tail_facts hK
  -- `ρ` into `ek`
  have h₀ := h.env
  refine WP.seq (WP.mono (copyL hL (i := 0) (j := 3) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h₀.ctx.r7 h₀.r5
    (by decide) hK.encT (by decide) (by decide) (by decide) f1 (by rw [h₀.rd, h₀.wr]; exact mem_rd_wr w0)
    (by rw [h₀.wr]; exact w3)) fun s₁ ⟨k₁, b₁⟩ => ?_)
  have h₁ := h₀.keep hp (k₁.x []) (by simp) f2
  have ek₁ : bytesAt s₁.mem ((lay s₀ K).A 3 0) K.ekLen = EK K s₀ := by
    rw [ek_split, bytes_catK, add_ofNat_add, Nat.zero_add, b₁, h.rho]
    refine congrArg (· ++ _) (catK_congr fun i hi => ?_)
    rw [add_ofNat_add, Nat.zero_add]
    exact (Lay.bytes_keep hL k₁.frame (f3 i hi) (by decide)).trans (h.ek i hi)
  -- `ek` into `dk`
  refine WP.seq (WP.mono (copyL hL (i := 3) (j := 4) (so := 0) (dO := 384 * K.k) (len := K.ekLen) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ h₁.r5 h₁.r6 (by decide) hK.encT hK.encEk (by offs) (by offs) f4
    (by rw [h₁.rd, h₁.wr]; exact mem_rd_wr w3) (by rw [h₁.wr]; exact w4)) fun s₂ ⟨k₂, b₂⟩ => ?_)
  rw [ek₁] at b₂
  have h₂ := h₁.keep hp (k₂.x []) (by simp) f5
  have ek₂ : bytesAt s₂.mem ((lay s₀ K).A 3 0) K.ekLen = EK K s₀ :=
    (Lay.bytes_keep hL k₂.frame f6 (by offs)).trans ek₁
  -- `H(ek)`
  have hin := h_ins hp h₂
  have hout := h_outs hp h₂
  refine WP.seq (WP.mono (hash_ok (idx := kidx) rate136 (by decide) (by decide) (by decide) h₂.ctx
    (List.cons_ne_nil _ _) hin hout (List.pairwise_singleton _ _)) fun s₃ ⟨k₃, o₃⟩ => ?_)
  have h₃ := h₂.keep hp (k₃.x []) (by simp) f7
  have hek₃ : bytesAt s₃.mem ((lay s₀ K).A 4 (768 * K.k + 32)) 32 = H (EK K s₀) := by
    have e := o₃.1
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at e
    refine e.trans ?_
    show _ = H (EK K s₀)
    rw [VG.Proof.MlKem.H_eq, ← ek₂]; rfl
  -- `z`
  refine WP.seq (WP.mono (copyL hL (i := 2) (j := 4) (so := 32) (dO := 768 * K.k + 64) (len := 32)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h₃.r4 h₃.r6 (by decide) hK.encZ (by decide) (by decide) (by decide)
    f8 (by rw [h₃.rd, h₃.wr]; exact w2) (by rw [h₃.wr]; exact w4)) fun s₄ ⟨k₄, b₄⟩ => ?_)
  have h₄ := h₃.keep hp (k₄.x []) (by simp) f9
  have z₄ : bytesAt s₄.mem ((lay s₀ K).A 4 (768 * K.k + 64)) 32 = Z s₀ := by
    rw [b₄]
    have := congrArg (List.drop 32) h₃.seed
    rw [bytesAt_drop _ _ (by decide), bytesAt_drop _ _ (by decide)] at this
    rw [show (lay s₀ K).A 2 32 = (lay s₀ K).A 2 0 + BitVec.ofNat 64 32 by simp only [Lay.A, add_ofNat_add], this]
    simp only [Lay.A, add_ofNat_zero]; rfl
  refine WP.mono (topEnd_ok h₄.ctx h₄.sav h₄.savlr) fun s' ⟨pr, r0, m', sp'⟩ => ⟨pr, sp'.trans h₄.sp, ?_, ?_, ?_⟩
  · rw [r0, k₄.cs .r11 (by decide) (by decide), k₃.cs .r11 (by decide) (by decide), k₂.cs .r11 (by decide) (by decide),
      k₁.cs .r11 (by decide) (by decide), h.r11]
  · rw [m', show State.addr (pEk s₀) = (lay s₀ K).A 3 0 by simp only [Lay.A, add_ofNat_zero]; rfl,
      Lay.bytes_keep hL k₄.frame f10 (by offs), Lay.bytes_keep hL k₃.frame f11 (by offs), ek₂]
  · have kd : ∀ i < K.k, bytesAt s₄.mem ((lay s₀ K).A 4 (384 * i)) 384 = bytesAt s.mem ((lay s₀ K).A 4 (384 * i)) 384 :=
      fun i hi => (Lay.bytes_keep hL k₄.frame (f12 i hi).1 (by decide)).trans
        ((Lay.bytes_keep hL k₃.frame (f12 i hi).2.1 (by decide)).trans
        ((Lay.bytes_keep hL k₂.frame (f12 i hi).2.2.1 (by decide)).trans
          (Lay.bytes_keep hL k₁.frame (f12 i hi).2.2.2 (by decide))))
    have e4 := (Lay.bytes_keep hL k₄.frame (i := 4) (o := 384 * K.k) (l := K.ekLen) f13 (by offs)).trans
      ((Lay.bytes_keep hL k₃.frame f14 (by offs)).trans b₂)
    have hh := (Lay.bytes_keep hL k₄.frame (i := 4) (o := 768 * K.k + 32) (l := 32) f15 (by decide)).trans hek₃
    simp only [Lay.A] at e4 hh z₄ kd
    rw [m', show State.addr (pDk s₀) = State.addr ((lay s₀ K).ptr 4) from rfl, dk_split, bytes_catK, e4, hh, z₄]
    refine congrArg (· ++ _ ++ _ ++ _) (catK_congr fun i hi => ?_)
    exact (kd i hi).trans (h.dk i hi)

/-! ## The whole function -/

theorem correct {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    WP isa K.keygen s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      s.gpr .r0 = (if okK K s₀ K.k then 1 else 0) ∧ bytesAt s.mem (State.addr (pEk s₀)) K.ekLen = EK K s₀ ∧
      bytesAt s.mem (State.addr (pDk s₀)) K.dkLen = DK K s₀ := by
  have hK := hp.wf
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨h₁, b₁⟩ => ?_)
  refine WP.seq (WP.mono (g_ok hp h₁ b₁) fun s₂ ⟨h₂, r₂, σ₂⟩ => ?_)
  refine WP.seq (WP.mono (rho_ok hp h₂ r₂ σ₂) fun s₂' ⟨h₂', r₂', σ₂'⟩ => ?_)
  refine WP.seq (WP.mono (prf_phase hp h₂' r₂' σ₂') fun s₃ ⟨h₃, r₃, p₃⟩ => ?_)
  refine WP.seq (WP.mono (rows_init hp h₃ r₃ p₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (wp_loop_ne (KRow K s₀) (N := K.k) hK.k1 (fun i hi s h => kgRow_step hp hi h)
    (fun _ h => h) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (s_init hp h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (wp_loop_ne (KS K s₀) (N := K.k) hK.k1 (fun j hj s h => kgS_step hp hj h)
    (fun _ h => h) h₆) fun s₇ h₇ => ?_)
  exact WP.mono (tail_ok hp h₇) fun s ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩

end VG.Proof.MlKem.Arm.KeyGen
