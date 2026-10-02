import VerifiedGarbage.Proof.MlKem.Arm.RowSum

/-!
# ML-KEM-768 on 32-bit ARM: the hash routine in constant time

Two runs of `hash` from states whose buffers are the same (`HashOk` of the
same layout, and the same stack pointer) leak the same trace (`hash_ct`): the
blocks that set up the arguments access no memory (`relct_noMem`), the Keccak
state is zeroed through `r7` (the taint analysis), and the calls of the sponge
functions are on the same arguments in both runs (`absorb_ct`, …), the
positions being those of the same lengths.
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.Sha3 (rates)
open VG.Proof.MlKem.Arm.Sample (taint_block relct_wp)

/-! ## Blocks that access no memory -/

/-- An instruction that accesses no memory. -/
def noMem : Instr → Bool
  | .ldr .. | .str .. | .ldrb .. | .strb .. | .ldrSp .. | .push _ | .pop .. => false
  | _ => true

theorem addrs_noMem {i : Instr} (h : noMem i = true) (s : State) : addrs i s = [] := by
  cases i <;> first | rfl | simp [noMem] at h

theorem execBlock_noMem : ∀ {is : List Instr}, is.all noMem = true → ∀ {s s' : State} {t : List Leak},
    execBlock isa is s = some (s', t) → t = []
  | [], _, _, _, _, h => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  | i :: is, hm, s, s', t, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hm
    simp only [execBlock] at h
    split at h
    · cases h
    · obtain ⟨⟨s'', t'⟩, h₁, h₂⟩ := Option.map_eq_some_iff.mp h
      cases h₂
      rw [addrs_noMem hm.1 s]
      simpa using execBlock_noMem hm.2 h₁

/-- A block that accesses no memory leaks nothing. -/
theorem relct_noMem {P : State → State → Prop} {is : List Instr} (h : is.all noMem = true) :
    RelCT isa P (.block is) fun _ _ => True := fun _ _ _ _ _ _ _ e₁ e₂ => by
  rw [Exec.block_iff] at e₁ e₂
  rw [execBlock_noMem h e₁, execBlock_noMem h e₂]; exact ⟨rfl, trivial⟩

/-- The empty block. -/
theorem relct_nil {P : State → State → Prop} : RelCT isa P (.block []) P := fun _ _ _ _ _ _ hp e₁ e₂ => by
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
  obtain ⟨rfl, rfl⟩ := e₁
  obtain ⟨rfl, rfl⟩ := e₂
  exact ⟨rfl, hp⟩

theorem kargs_noMem (rate : Nat) (first : Bool) (p : Piece) :
    (keccakArgs rate first ++ pieceArgs p).all noMem = true := by
  cases first <;> rfl

theorem pargs_noMem (rate sfx : Nat) :
    (keccakArgs rate false ++ ([.mov .r3 (.imm (BitVec.ofNat 32 sfx))] : List Instr)).all noMem = true := rfl

/-! ## The absorbs -/

/-- After the arguments of an `absorb` or a `squeeze` of piece `p` from position `X`. -/
structure KA (L : Lay) (idx : Reg → Nat) (rate : Nat) (p : Piece) (X : Nat) (s₀ s : State) : Prop where
  rg : Rg s₀ s
  r0 : s.gpr .r0 = L.ptr 0
  r1 : s.gpr .r1 = BitVec.ofNat 32 rate
  r2 : s.gpr .r2 = BitVec.ofNat 32 X
  r3 : s.gpr .r3 = L.ptr (idx p.base) + BitVec.ofNat 32 p.off
  r12 : s.gpr .r12 = BitVec.ofNat 32 p.len
  lr : s.gpr .lr = L.ptr 0 + BitVec.ofNat 32 200

theorem ka_ok {L : Lay} {idx : Reg → Nat} {rate : Nat} (hre : encodable (BitVec.ofNat 32 rate) = true)
    {s₀ s : State} (hc : Ctx L s₀) {first : Bool} {X : Nat} {p : Piece} {w : Bool} (hp : PieceOk L idx s₀ w p)
    (hg : Rg s₀ s) (hX : Pos first s = X) :
    WP isa (.block (keccakArgs rate first ++ pieceArgs p)) s (KA L idx rate p X s₀) :=
  WP.mono (kargs_ok first hp.base hre hp.oenc hp.lenc) fun s₁ ⟨o₁, g0, g1, g2, g3, g12, glr⟩ =>
    ⟨hg.kept (o₁.kept []), by rw [g0, (hg.ctx hc).r7], g1, by rw [g2, pos_r2, hX],
      by rw [g3, hg.cs _ hp.base.1 hp.base.2, hp.ptr], g12, by rw [glr, (hg.ctx hc).r7]⟩

theorem absorbs_ct {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates)
    (hre : encodable (BitVec.ofNat 32 rate) = true) {s₀₁ s₀₂ : State} (hc₁ : Ctx L s₀₁) (hc₂ : Ctx L s₀₂)
    (hsp : s₀₁.sp = s₀₂.sp) :
    ∀ (ps : List Piece) (first : Bool) (X : Nat),
      (∀ p ∈ ps, PieceOk L idx s₀₁ false p ∧ PieceOk L idx s₀₂ false p) → X < rate →
      RelCT isa (fun a b => Rg s₀₁ a ∧ Rg s₀₂ b ∧ Pos first a = X ∧ Pos first b = X) (absorbs rate first ps)
        (fun a b => Rg s₀₁ a ∧ Rg s₀₂ b ∧ ∃ Y, Y < rate ∧ Pos (first && ps.isEmpty) a = Y ∧
          Pos (first && ps.isEmpty) b = Y)
  | [], first, X, _, hX =>
    RelCT.mono relct_nil (fun _ _ h => h) fun a b ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, h2, X, hX, by simpa using h3, by simpa using h4⟩
  | p :: ps, first, X, hps, hX => by
    obtain ⟨hp₁, hp₂⟩ := hps p (List.mem_cons_self ..)
    have rpos := rate_pos hrate
    refine RelCT.seq (R := fun a b => KA L idx rate p X s₀₁ a ∧ KA L idx rate p X s₀₂ b)
      (relct_wp (relct_noMem (kargs_noMem _ _ _)) fun a b hab =>
        ⟨ka_ok hre hc₁ hp₁ hab.1 hab.2.2.1, ka_ok hre hc₂ hp₂ hab.2.1 hab.2.2.2⟩) ?_
    have hA : ∀ {s₀ s : State}, Ctx L s₀ → PieceOk L idx s₀ false p → KA L idx rate p X s₀ s →
        AbsorbArgs s (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx p.base) + BitVec.ofNat 32 p.off)
          rate X p.len := fun hc hp h =>
      absorbArgs_of hrate (h.rg.ctx hc) h.rg hp hX h.r0 h.r1 h.r2 h.r3 h.r12 h.lr
    refine RelCT.seq (R := fun a b => Rg s₀₁ a ∧ Rg s₀₂ b ∧ Pos false a = (X + p.len) % rate ∧
      Pos false b = (X + p.len) % rate) ?_ ?_
    · refine RelCT.mono (relct_wp (F₁ := fun s' => Rg s₀₁ s' ∧ (s'.gpr .r0).toNat = (X + p.len) % rate)
        (F₂ := fun s' => Rg s₀₂ s' ∧ (s'.gpr .r0).toNat = (X + p.len) % rate) (absorb_ct fun a b hab => ⟨by rw [hab.1.rg.sp, hab.2.rg.sp, hsp], _, _, _, _, _, _,
        hA hc₁ hp₁ hab.1, hA hc₂ hp₂ hab.2⟩) fun a b hab =>
        ⟨absorb_ok (hA hc₁ hp₁ hab.1) fun s' k' _ r' => ⟨hab.1.rg.kept k', r'⟩,
         absorb_ok (hA hc₂ hp₂ hab.2) fun s' k' _ r' => ⟨hab.2.rg.kept k', r'⟩⟩) (fun _ _ h => h)
        fun a b ⟨⟨g₁, r₁⟩, ⟨g₂, r₂⟩⟩ => ⟨g₁, g₂, r₁, r₂⟩
    · refine RelCT.mono (absorbs_ct hrate hre hc₁ hc₂ hsp ps false ((X + p.len) % rate)
        (fun q hq => hps q (List.mem_cons_of_mem _ hq)) (Nat.mod_lt _ rpos)) (fun _ _ h => h)
        fun a b ⟨g₁, g₂, Y, hY, e₁, e₂⟩ => ⟨g₁, g₂, Y, hY, by simpa using e₁, by simpa using e₂⟩

/-! ## The whole hash -/

/-- A state `hash` may run from. -/
structure HashOk (L : Lay) (idx : Reg → Nat) (ins outs : List Piece) (s : State) : Prop where
  ctx : Ctx L s
  ins : ∀ p ∈ ins, PieceOk L idx s false p
  outs : ∀ p ∈ outs, PieceOk L idx s true p

/-- After the arguments of a `pad` from position `Y`. -/
structure PA (L : Lay) (rate sfx Y : Nat) (s₀ s : State) : Prop where
  rg : Rg s₀ s
  r0 : s.gpr .r0 = L.ptr 0
  r1 : s.gpr .r1 = BitVec.ofNat 32 rate
  r2 : s.gpr .r2 = BitVec.ofNat 32 Y
  r3 : s.gpr .r3 = BitVec.ofNat 32 sfx
  lr : s.gpr .lr = L.ptr 0 + BitVec.ofNat 32 200

theorem hash_ct {L : Lay} {idx : Reg → Nat} {rate sfx : Nat} (hrate : rate ∈ rates)
    (hre : encodable (BitVec.ofNat 32 rate) = true) (hse : encodable (BitVec.ofNat 32 sfx) = true)
    {ins : List Piece} {q : Piece} (hne : ins ≠ []) {P : State → State → Prop}
    (hP : ∀ a b, P a b → HashOk L idx ins [q] a ∧ HashOk L idx ins [q] b ∧ a.sp = b.sp) :
    RelCT isa P (hash rate sfx ins [q]) fun _ _ => True := by
  refine RelCT.mono (P := fun a b => ∃ x : State × State, a = x.1 ∧ b = x.2 ∧ HashOk L idx ins [q] x.1 ∧
    HashOk L idx ins [q] x.2 ∧ x.1.sp = x.2.sp) (RelCT.exists_ fun ⟨s₀₁, s₀₂⟩ => ?_)
    (fun a b h => ⟨(a, b), rfl, rfl, hP a b h⟩) (fun _ _ h => h)
  by_cases hH : HashOk L idx ins [q] s₀₁ ∧ HashOk L idx ins [q] s₀₂ ∧ s₀₁.sp = s₀₂.sp
  swap
  · exact RelCT.of_false fun a b h => hH ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  obtain ⟨h₁, h₂, hsp⟩ := hH
  have hc₁ := h₁.ctx
  have hc₂ := h₂.ctx
  have rpos := rate_pos hrate
  have g₀ : ∀ {s₀ : State}, Rg s₀ s₀ := ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩
  refine RelCT.mono (P := fun a b => a = s₀₁ ∧ b = s₀₂) ?_ (fun a b h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  -- the state set to zero
  refine RelCT.seq (R := fun a b => Rg s₀₁ a ∧ Rg s₀₂ b)
    (RelCT.mono (relct_wp (F₁ := Rg s₀₁) (F₂ := Rg s₀₂) (taint_block [.r7] (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1, hab.2, hc₁.r7, hc₂.r7]) (by taint_decide))
      fun a b hab => ⟨by rw [hab.1]; exact WP.mono (zeroState_ok hc₁) fun s' h => (h.1.rg),
        by rw [hab.2]; exact WP.mono (zeroState_ok hc₂) fun s' h => (h.1.rg)⟩) (fun _ _ h => h) fun _ _ h => h) ?_
  -- the absorbs
  refine RelCT.seq (R := fun a b => Rg s₀₁ a ∧ Rg s₀₂ b ∧ ∃ Y, Y < rate ∧ Pos false a = Y ∧ Pos false b = Y)
    (RelCT.mono (absorbs_ct hrate hre hc₁ hc₂ hsp ins true 0 (fun p hp => ⟨h₁.ins p hp, h₂.ins p hp⟩) rpos)
      (fun a b h => ⟨h.1, h.2, rfl, rfl⟩) fun a b ⟨g₁, g₂, Y, hY, e₁, e₂⟩ => ⟨g₁, g₂, Y, hY, ?_, ?_⟩) ?_
  · cases ins with
    | nil => exact absurd rfl hne
    | cons _ _ => exact e₁
  · cases ins with
    | nil => exact absurd rfl hne
    | cons _ _ => exact e₂
  -- the padding
  refine RelCT.mono (P := fun a b => ∃ Y, Y < rate ∧ Rg s₀₁ a ∧ Rg s₀₂ b ∧ Pos false a = Y ∧ Pos false b = Y)
    (RelCT.exists_ fun Y => ?_) (fun a b ⟨g₁, g₂, Y, hY, e₁, e₂⟩ => ⟨Y, hY, g₁, g₂, e₁, e₂⟩) (fun _ _ h => h)
  by_cases hY : Y < rate
  swap
  · exact RelCT.of_false fun a b h => hY h.1
  have pa : ∀ (s₀ s : State), Ctx L s₀ → Rg s₀ s → Pos false s = Y →
      WP isa (.block (keccakArgs rate false ++ ([.mov .r3 (.imm (BitVec.ofNat 32 sfx))] : List Instr))) s
        (PA L rate sfx Y s₀) := fun s₀ s hc hg hX =>
    WP.mono (pargs_ok hre hse) fun s' ⟨o', g0, g1, g2, g3, glr⟩ =>
      ⟨hg.kept (o'.kept []), by rw [g0, (hg.ctx hc).r7], g1,
        by rw [g2, ← hX, show Pos false s = (s.gpr .r0).toNat from rfl, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        g3, by rw [glr, (hg.ctx hc).r7]⟩
  refine RelCT.seq (R := fun a b => PA L rate sfx Y s₀₁ a ∧ PA L rate sfx Y s₀₂ b)
    (relct_wp (relct_noMem (pargs_noMem _ _)) fun a b hab =>
      ⟨pa _ _ hc₁ hab.2.1 hab.2.2.2.1, pa _ _ hc₂ hab.2.2.1 hab.2.2.2.2⟩) ?_
  have hPA : ∀ {s₀ s : State}, Ctx L s₀ → PA L rate sfx Y s₀ s →
      PadArgs s (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) rate Y (BitVec.ofNat 32 sfx) := fun hc h =>
    padArgs_of hrate (h.rg.ctx hc) hY h.r0 h.r1 h.r2 h.r3 h.lr
  refine RelCT.seq (R := fun a b => Rg s₀₁ a ∧ Rg s₀₂ b)
    (RelCT.mono (relct_wp (F₁ := Rg s₀₁) (F₂ := Rg s₀₂) (pad_ct fun a b hab =>
      ⟨by rw [hab.1.rg.sp, hab.2.rg.sp, hsp], _, _, _, _, _, hPA hc₁ hab.1, hPA hc₂ hab.2⟩) fun a b hab =>
      ⟨pad_ok (hPA hc₁ hab.1) fun s' k' _ => hab.1.rg.kept k', pad_ok (hPA hc₂ hab.2) fun s' k' _ => hab.2.rg.kept k'⟩)
      (fun _ _ h => h) fun _ _ h => h) ?_
  -- the squeeze
  have hq₁ := h₁.outs q (List.mem_singleton_self _)
  have hq₂ := h₂.outs q (List.mem_singleton_self _)
  refine RelCT.seq (R := fun a b => KA L idx rate q 0 s₀₁ a ∧ KA L idx rate q 0 s₀₂ b)
    (relct_wp (relct_noMem (kargs_noMem _ _ _)) fun a b hab =>
      ⟨ka_ok hre hc₁ hq₁ hab.1 rfl, ka_ok hre hc₂ hq₂ hab.2 rfl⟩) ?_
  have hS : ∀ {s₀ s : State}, Ctx L s₀ → PieceOk L idx s₀ true q → KA L idx rate q 0 s₀ s →
      SqueezeArgs s (L.ptr 0) (L.ptr 0 + BitVec.ofNat 32 200) (L.ptr (idx q.base) + BitVec.ofNat 32 q.off)
        rate 0 q.len := fun hc hq h =>
    squeezeArgs_of hrate (h.rg.ctx hc) h.rg hq (Nat.zero_le _) h.r0 h.r1 h.r2 h.r3 h.r12 h.lr
  refine RelCT.seq (R := fun _ _ => True) (squeeze_ct fun a b hab =>
    ⟨by rw [hab.1.rg.sp, hab.2.rg.sp, hsp], _, _, _, _, _, _, hS hc₁ hq₁ hab.1, hS hc₂ hq₂ hab.2⟩) relct_nil

end VG.Proof.MlKem.Arm
