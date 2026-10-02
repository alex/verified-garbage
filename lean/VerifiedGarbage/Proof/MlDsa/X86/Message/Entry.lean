import VerifiedGarbage.Proof.MlDsa.X86.Message.Call
import VerifiedGarbage.Proof.MlKem.X86.Leaf

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message`: the check, the entry and the leaf

Untrusted: everything here is checked by Lean. What both functions' proofs
need of their layouts (`Shape`): where the arguments are, and the facts
their preconditions give. After the leaf's push, the body loads `ctx_len`
and compares it with 256 (`chk_piece`); if it is larger it returns 2
(`ret2_piece`), and otherwise points `esi` at the 1 KiB and stores
`0 ‖ ctx_len` there (`enter_piece`), which is where `Ctx` starts; then the
rest of the body, in a leaf (`top_piece`).
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Only Piece P0 E0 frameR retR P0_esp P0_wr P0_arg P0_argIn P0_argAddr LeafEnd LeafPost)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa (Params)

/-- What the proofs need of the layouts of runs from states satisfying
`Pre`: the function's arguments, `scratch` among them (argument `si`), and
the facts the precondition gives. -/
structure Shape (Pre : State → Prop) (Pub : State → State → Prop) (lay : State → Lay) (si : Nat) (p : Params) :
    Prop where
  sp : ∀ s₀, Pre s₀ → (lay s₀).SP = E0 s₀
  rd : ∀ s₀, Pre s₀ → (lay s₀).rd = s₀.rd
  wr : ∀ s₀, Pre s₀ → (lay s₀).wr = s₀.wr
  argv : ∀ s₀, Pre s₀ → ∀ i < (lay s₀).nA, (lay s₀).argv.getD i 0 = arg s₀ i
  ctxLen : ∀ s₀, Pre s₀ → (lay s₀).ctxLen = arg s₀ 4
  scr : ∀ s₀, Pre s₀ → (lay s₀).scr = arg s₀ si
  siLt : ∀ s₀, Pre s₀ → si < (lay s₀).nA
  E : ∀ s₀, Pre s₀ → (lay s₀).E = oE p
  ok : ∀ s₀, Pre s₀ → (arg s₀ 4).toNat < 256 → (lay s₀).Ok
  e16 : ∀ s₀, Pre s₀ → 16 ≤ (E0 s₀).toNat ∧ (E0 s₀).toNat + 4 ≤ 2 ^ 32
  fit : ∀ s₀, Pre s₀ → (E0 s₀).toNat + 4 + 4 * (lay s₀).nA ≤ 2 ^ 32
  fd : ∀ s₀, Pre s₀ → (⟨(E0 s₀).setWidth 64 - 16#64, 16⟩ : Region).Disjoint ⟨argAddr s₀ 0, 4 * (lay s₀).nA⟩
  ain : ∀ s₀, Pre s₀ → (⟨argAddr s₀ 0, 4 * (lay s₀).nA⟩ : Region) ∈ s₀.rd ++ s₀.wr
  n5 : ∀ s₀, Pre s₀ → 5 ≤ (lay s₀).nA
  pubE : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → E0 s₀ = E0 s₀'
  pubA : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → arg s₀ 4 = arg s₀' 4 ∧ arg s₀ si = arg s₀' si
  pubL : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → PubL (lay s₀) (lay s₀')

/-- `mov [b + o], r8` -/
theorem wp_st8 {is : List Instr} {s : State} {Q : State → Prop} {b : Reg} {r : Reg8} {B : BitVec 32} {o : Nat}
    (hb : s.gpr b = B) (hout : InRegions s.wr (addr B o) 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW (addr B o) ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 ⟨b, o⟩ r :: is)) s Q := by
  refine cons (s' := { s with mem := s.mem.writeW (addr B o) ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp [exec, State.store8, ea_mk, hb, hout]

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {lay : State → Lay} {si : Nat} {p : Params}

/-- After the check: `eax` is `ctx_len`, and the carry says whether it is below 256. -/
def Chk (s₀ s : State) : Prop :=
  Only [.eax] (P0 s₀) s ∧ s.cf = some (decide ((arg s₀ 4).toNat < 256))

theorem arg4_in (hS : Shape Pre Pub lay si p) {s₀ : State} (h₀ : Pre s₀) {i : Nat} (hi : i < (lay s₀).nA) :
    InRegions ((P0 s₀).rd ++ (P0 s₀).wr) (addr (E0 s₀ - 16) (20 + 4 * i)) 4 := by
  rw [← P0_esp]
  show InRegions _ (((P0 s₀).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64) 4
  rw [P0_argAddr]
  exact P0_argIn hi (hS.fit s₀ h₀) (hS.ain s₀ h₀)

theorem arg_P0 (hS : Shape Pre Pub lay si p) {s₀ : State} (h₀ : Pre s₀) {i : Nat} (hi : i < (lay s₀).nA) :
    (P0 s₀).mem.readW (addr (E0 s₀ - 16) (20 + 4 * i)) 32 = arg s₀ i := by
  rw [← P0_esp]
  show (P0 s₀).mem.readW (((P0 s₀).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64) 32 = _
  rw [P0_argAddr]
  exact P0_arg (hS.e16 s₀ h₀).1 hi (hS.fit s₀ h₀) (hS.fd s₀ h₀)

theorem chk_piece (hS : Shape Pre Pub lay si p) :
    Piece Pre Pub (fun s₀ s => s = P0 s₀) Chk (.block [.mov .eax (.mem (argAt 4)), .alu .cmp .eax (.imm 256)]) := by
  refine Piece.taint [.esp] (fun s₀ s h₀ e => ?_) (fun s₀ s₀' s s' h₀ h₀' hq e e' r hr => ?_) (by taint_decide)
  · subst e
    have h4 : 4 < (lay s₀).nA := by have := hS.n5 s₀ h₀; omega
    refine wp_ldm (b := .esp) (P0_esp s₀) (arg4_in hS h₀ h4) fun s₁ u₁ => wp_cmpi fun s₂ f₂ c₂ _ => WP.block_nil ?_
    refine ⟨⟨fun r hr => ?_, by rw [f₂.mem, u₁.mem], by rw [f₂.rd, u₁.rd], by rw [f₂.wr, u₁.wr]⟩, ?_⟩
    · rw [f₂.gpr, u₁.other r (by simpa using hr)]
    · rw [c₂, u₁.gpr, arg_P0 hS h₀ h4]; rfl
  · simp only [List.mem_singleton] at hr; subst hr
    rw [e, e', P0_esp, P0_esp, hS.pubE s₀ s₀' h₀ h₀' hq]

/-- `ctx_len ≥ 256`: return 2. -/
theorem ret2_piece {B : State → State → Prop}
    (hB : ∀ s₀ s, Pre s₀ → Only [.eax] (P0 s₀) s → 256 ≤ (arg s₀ 4).toNat → s.gpr .eax = 2 → B s₀ s) :
    Piece Pre Pub (fun s₀ s => Chk s₀ s ∧ (!decide ((arg s₀ 4).toNat < 256)) = true) B
      (.block [.mov .eax (.imm 2)]) := by
  refine Piece.taint [] (fun s₀ s h₀ ⟨⟨o, _⟩, hb⟩ => wp_movi fun s₁ u₁ => WP.block_nil ?_)
    (fun _ _ _ _ _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Nat.not_lt] at hb
  refine hB s₀ s₁ h₀ ⟨fun r hr => ?_, by rw [u₁.mem, o.mem], by rw [u₁.rd, o.rd], by rw [u₁.wr, o.wr]⟩ hb u₁.gpr
  rw [u₁.other r (by simpa using hr), o.gpr r hr]

/-- Bytes `0 ‖ c` at `X + 944`, from their stores. -/
theorem hdr_bytes (m : Mem) (X : Addr) (c : BitVec 32) :
    bytesAt ((m.writeW (X + BitVec.ofNat 64 944) ((0 : BitVec 32).setWidth 8)).writeW (X + BitVec.ofNat 64 945)
      (c.setWidth 8)) (X + BitVec.ofNat 64 944) 2 = [0, BitVec.ofNat 8 c.toNat] := by
  have n45 : X + BitVec.ofNat 64 944 ≠ X + BitVec.ofNat 64 945 :=
    Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)
  simp only [bytesAt, List.range, List.range.loop, List.map_cons, List.map_nil, add_add, Nat.reduceAdd]
  rw [byte_writeW_other _ n45, byte_writeW_self, byte_writeW_self]
  refine List.cons_eq_cons.mpr ⟨rfl, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem E0_E1 (hS : Shape Pre Pub lay si p) {s₀ : State} (h₀ : Pre s₀) : E0 s₀ - 16 = (lay s₀).E1 := by
  rw [Lay.E1, hS.sp s₀ h₀]; rfl

/-- `esi ← scratch + oE p`, and `0 ‖ ctx_len` at `esi + 944`. -/
theorem enter_piece (hS : Shape Pre Pub lay si p) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt si)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true) :
    Piece Pre Pub (fun s₀ s => Chk s₀ s ∧ (!decide ((arg s₀ 4).toNat < 256)) = false) (CtxO lay) (enter si p) := by
  refine Piece.seq (B := fun s₀ s => Only [.eax, .esi] (P0 s₀) s ∧ s.gpr .esi = (lay s₀).X32 ∧ (lay s₀).Ok)
    (Piece.taint [.esp] (fun s₀ s h₀ ⟨⟨o, _⟩, hb⟩ => ?_) (fun s₀ s₀' s s' h₀ h₀' hq ⟨⟨o, _⟩, _⟩ ⟨⟨o', _⟩, _⟩ r hr => ?_) tt)
    (Piece.taint [.esp, .esi] (fun s₀ s h₀ ⟨o, hx, hL⟩ => ?_)
      (fun s₀ s₀' s s' h₀ h₀' hq ⟨o, hx, _⟩ ⟨o', hx', _⟩ r hr => ?_) (by taint_decide))
  · have hc : (arg s₀ 4).toNat < 256 := by simpa using hb
    have hsp : s.gpr .esp = E0 s₀ - 16 := by rw [o.gpr _ (by decide), P0_esp]
    have hin : InRegions (s.rd ++ s.wr) (addr (E0 s₀ - 16) (20 + 4 * si)) 4 := by
      rw [o.rd, o.wr]; exact arg4_in hS h₀ (hS.siLt s₀ h₀)
    refine wp_ldm (b := .esp) hsp hin fun s₁ u₁ => wp_addi fun s₂ u₂ => WP.block_nil
      ⟨⟨fun r hr => ?_, by rw [u₂.mem, u₁.mem, o.mem], by rw [u₂.rd, u₁.rd, o.rd], by rw [u₂.wr, u₁.wr, o.wr]⟩,
        ?_, hS.ok s₀ h₀ hc⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u₂.other r hr.2, u₁.other r hr.2, o.gpr r (by simpa using hr.1)]
    · rw [u₂.gpr, u₁.gpr, o.mem, arg_P0 hS h₀ (hS.siLt s₀ h₀), Lay.X32, hS.scr s₀ h₀, hS.E s₀ h₀]
  · simp only [List.mem_singleton] at hr; subst hr
    rw [o.gpr _ (by decide), o'.gpr _ (by decide), P0_esp, P0_esp, hS.pubE s₀ s₀' h₀ h₀' hq]
  · have hsp : s.gpr .esp = E0 s₀ - 16 := by rw [o.gpr _ (by decide), P0_esp]
    have h4 : 4 < (lay s₀).nA := by have := hS.n5 s₀ h₀; omega
    have e944 : addr (lay s₀).X32 oHdr = (lay s₀).X + BitVec.ofNat 64 944 := hL.xo (by decide)
    have e945 : addr (lay s₀).X32 (oHdr + 1) = (lay s₀).X + BitVec.ofNat 64 945 := hL.xo (by decide)
    have hwr : s.wr = frameR s₀ :: (lay s₀).wr := by rw [o.wr, P0_wr, hS.wr s₀ h₀]
    have hout : ∀ e, e + 1 ≤ 1024 → InRegions s.wr ((lay s₀).X + BitVec.ofNat 64 e) 1 := fun e he => by
      obtain ⟨R, hR, c⟩ := hL.inW (e := e) (k := 1) he
      exact ⟨R, by rw [hwr]; exact List.mem_cons_of_mem _ hR, c⟩
    have cSC : ∀ e, e + 1 ≤ 1024 → (lay s₀).SC.Contains ((lay s₀).X + BitVec.ofNat 64 e) 1 := fun e he =>
      hL.sub_sc (e := e) (k := 1) he _ (Region.contains_self _ _)
    refine wp_movi fun s₁ u₁ => wp_st8 (b := .esi) (B := (lay s₀).X32) (by rw [u₁.other _ (by decide), hx])
      (by rw [e944, u₁.wr]; exact hout 944 (by omega)) fun s₂ m₂ => ?_
    have f₂ : Frame [(lay s₀).SC, (lay s₀).STK] (P0 s₀).mem s₂.mem := by
      rw [m₂.mem, u₁.mem, o.mem, e944]
      exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _ (cSC 944 (by omega))
    have hargs : ∀ {m : Mem}, Frame [(lay s₀).SC, (lay s₀).STK] (P0 s₀).mem m → ∀ i < (lay s₀).nA,
        m.readW (((lay s₀).SP + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64) 32 = arg s₀ i := by
      intro m fr i hi
      rw [fr.readW (hL.argIn hi) (fun r hr => ?_) (by decide), ← Lay.Ok.argAt_eq, ← E0_E1 hS h₀]
      · exact arg_P0 hS h₀ hi
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.aSC
        · exact hL.kArgs.symm
    refine wp_ldm (b := .esp) (by rw [m₂.gpr, u₁.other _ (by decide), hsp])
      (by rw [m₂.rd, m₂.wr, u₁.rd, u₁.wr, o.rd, o.wr]; exact arg4_in hS h₀ h4) fun s₃ u₃ => ?_
    have v₃ : s₃.gpr .eax = arg s₀ 4 := by
      rw [u₃.gpr, E0_E1 hS h₀, Lay.Ok.argAt_eq]; exact hargs f₂ 4 h4
    refine wp_st8 (b := .esi) (B := (lay s₀).X32) (by rw [u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), hx])
      (by rw [e945, u₃.wr, m₂.wr, u₁.wr]; exact hout 945 (by omega)) fun s₄ m₄ => WP.block_nil ⟨hL, ?_⟩
    have mm : s₄.mem = ((P0 s₀).mem.writeW ((lay s₀).X + BitVec.ofNat 64 944) ((0 : BitVec 32).setWidth 8)).writeW
        ((lay s₀).X + BitVec.ofNat 64 945) ((arg s₀ 4).setWidth 8) := by
      have ral : Reg8.al.reg = .eax := rfl
      rw [m₄.mem, u₃.mem, e945, m₂.mem, u₁.mem, o.mem, e944, ral, v₃, u₁.gpr]
    have f₄ : Frame [(lay s₀).SC, (lay s₀).STK] (P0 s₀).mem s₄.mem := by
      rw [m₄.mem, u₃.mem, e945]
      exact f₂.writeW (List.mem_cons_self ..) _ (cSC 945 (by omega))
    refine ⟨by rw [m₄.rd, u₃.rd, m₂.rd, u₁.rd, o.rd, pushed_rd, hS.rd s₀ h₀],
      by rw [m₄.wr, u₃.wr, m₂.wr, u₁.wr, hwr, hS.sp s₀ h₀], by rw [m₄.gpr, u₃.other _ (by decide), m₂.gpr,
        u₁.other _ (by decide), hsp, E0_E1 hS h₀],
      by rw [m₄.gpr, u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), hx],
      by rw [mm, hdr_bytes, hS.ctxLen s₀ h₀], fun i hi => by rw [hargs f₄ i hi, hS.argv s₀ h₀ i hi], f₄⟩
  · have hp := hS.pubL s₀ s₀' h₀ h₀' hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [o.gpr _ (by decide), o'.gpr _ (by decide), P0_esp, P0_esp, hS.pubE s₀ s₀' h₀ h₀' hq]
    · rw [hx, hx', hp.x]

/-- The whole function: the check, and the entry and `rest` if `ctx_len < 256`, in a leaf
that changes memory only within `W`. -/
theorem top_piece (hS : Shape Pre Pub lay si p) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt si)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true)
    {rest : Prog isa} {B : State → State → Prop} (W : State → List Region)
    (hW : ∀ s₀, Pre s₀ → ∀ r ∈ W s₀, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r)
    (hsp : NoSp (.seq (.block [.mov .eax (.mem (argAt 4)), .alu .cmp .eax (.imm 256)])
      (.ite .ae (.block [.mov .eax (.imm 2)]) (.seq (enter si p) rest))))
    (hr : Piece Pre Pub (CtxO lay) (fun s₀ s => LeafEnd s₀ (W s₀) s ∧ B s₀ s) rest) :
    Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (fun s => (256 ≤ (arg s₀ 4).toNat ∧
      s.gpr .eax = 2) ∨ B s₀ s) s₀ s') (top (enter si p) rest) := by
  refine Piece.leaf W hsp hS.e16 hW hS.pubE ?_
  refine Piece.seq (chk_piece hS) (Piece.ite (fun s₀ => !decide ((arg s₀ 4).toNat < 256))
    (fun s₀ s h₀ h => ?_) (fun s₀ s₀' h₀ h₀' hq => ?_) (ret2_piece fun s₀ s h₀ o hc h2 => ?_)
    (Piece.seq (enter_piece hS tt) (hr.mono (fun _ _ _ h => h) fun s₀ s h₀ ⟨he, hb⟩ => ⟨he, .inr hb⟩)))
  · show s.cf.map (!·) = _
    rw [h.2]; rfl
  · rw [(hS.pubA s₀ s₀' h₀ h₀' hq).1]
  · exact ⟨⟨by rw [o.mem]; exact Frame.refl _ _, o.gpr _ (by decide), o.rd, o.wr⟩, .inl ⟨hc, h2⟩⟩

/-- `LeafEnd`, from `Ctx` and a frame of the memory from it. -/
theorem CtxO.leafEnd (hS : Shape Pre Pub lay si p) {s₀ s s' : State} (h₀ : Pre s₀) (hc : CtxO lay s₀ s)
    {W : List Region} (hW : ∀ r ∈ [(lay s₀).SC, (lay s₀).STK], r ∈ W) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hrs : ∀ r ∈ rs, ∃ R ∈ W, Region.Sub r R)
    (hsp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : LeafEnd s₀ W s' := by
  refine ⟨(hc.ctx.frame.sub fun r hr => ⟨r, hW r hr, fun _ h => h⟩).trans (hf.sub hrs),
    by rw [hsp, hc.ctx.esp, ← E0_E1 hS h₀, P0_esp], by rw [hrd, hc.ctx.rd, hS.rd s₀ h₀, pushed_rd],
    by rw [hwr, hc.ctx.wr, P0_wr, hS.wr s₀ h₀, hS.sp s₀ h₀]⟩

end

end VG.Proof.MlDsa.X86.Message
