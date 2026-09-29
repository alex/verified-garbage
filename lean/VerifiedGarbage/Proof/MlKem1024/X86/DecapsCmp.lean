import VerifiedGarbage.Proof.MlKem1024.X86.DecapsPre
import VerifiedGarbage.Proof.MlKem.X86.CheckEk

/-!
# ML-KEM-1024 on x86 (32-bit): the implicit rejection in `vg_mlkem1024_decaps`

Untrusted: everything here is checked by Lean. `cmpC` compares `ct` with
`c'` (at `eC`) without branching on them: `ebx` is the OR of the XORs of
their bytes (`accB`), then all ones if it is 0 and zero otherwise (`sub`,
`sbb`), which is all ones exactly when `ct = c'` (`eq_iff_foldl_or_xor`):
`cmp_piece`. `selC` writes `K̄ ^ ((K' ^ K̄) & mask)` byte by byte into `key`
(`sel_piece`): `K'` if the mask is all ones, and `K̄` if it is zero.
-/

namespace VG.Proof.MlKem1024.X86.Decaps

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlKem1024.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {A B : State → State → Prop}

/-! ## Single instructions -/

theorem wp_movzx' {d b : Reg} {disp : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ b disp)) 1)
    (k : ∀ s', Only [d] s s' → s'.gpr d = (s.mem (s.ea (at_ b disp))).setWidth 32 → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d (at_ b disp) :: is)) s Q :=
  wp_movzx hin (k _ (Only.setReg s d _) (by simp [State.setReg]))

theorem wp_xorr {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d ^^^ s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.reg r) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d ^^^ s.gpr r) false false).setReg d (s.gpr d ^^^ s.gpr r))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]))

theorem wp_orr {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d ||| s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.reg r) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d ||| s.gpr r) false false).setReg d (s.gpr d ||| s.gpr r))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]))

theorem wp_subi {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d - v → s'.cf = some (decide ((s.gpr d).toNat < v.toNat)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d - v) (decide ((s.gpr d).toNat < v.toNat))
      (subOverflow (s.gpr d) v (s.gpr d - v))).setReg d (s.gpr d - v))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]) (by simp [State.setReg, arithFlags, State.setFlags]))

theorem wp_sbbself {d : Reg} {c : Bool} {is : List Instr} {s : State} {Q : State → Prop} (hc : s.cf = some c)
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d - s.gpr d - (BitVec.ofBool c).setWidth 32 →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sbb d (.reg d) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d - s.gpr d - (BitVec.ofBool c).setWidth 32)
      (decide ((s.gpr d).toNat < (s.gpr d).toNat + c.toNat))
      (subOverflow (s.gpr d) (s.gpr d) (s.gpr d - s.gpr d - (BitVec.ofBool c).setWidth 32))).setReg d
        (s.gpr d - s.gpr d - (BitVec.ofBool c).setWidth 32))
    (by simp only [exec, execAlu, readSrc, Option.bind_some, hc, Option.map_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]))

/-! ## The comparison -/

/-- The OR of the XORs of the first `k` bytes of `c` and `c'`. -/
def accB (c c' : List Byte) : Nat → Byte
  | 0 => 0
  | k + 1 => accB c c' k ||| (c.getD k 0 ^^^ c'.getD k 0)

theorem accB_eq (c c' : List Byte) : ∀ n, n ≤ c.length → n ≤ c'.length →
    accB c c' n = ((c.take n).zipWith (· ^^^ ·) (c'.take n)).foldl (· ||| ·) 0
  | 0, _, _ => by simp [accB]
  | n + 1, h₁, h₂ => by
    rw [accB, accB_eq c c' n (by omega) (by omega), List.take_add_one, List.take_add_one,
      List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega), Option.toList_some,
      Option.toList_some, List.zipWith_append (by simp; omega), List.foldl_append]
    simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_cons, List.foldl_nil,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show n < c.length by omega),
      List.getElem?_eq_getElem (show n < c'.length by omega), Option.getD_some]

/-- `c` and `c'` of 1568 bytes are equal exactly when `accB` of all their bytes is 0. -/
theorem accB_zero {c c' : List Byte} (h₁ : c.length = 1568) (h₂ : c'.length = 1568) :
    c = c' ↔ accB c c' 1568 = 0 := by
  rw [accB_eq c c' 1568 (by omega) (by omega), List.take_of_length_le (by omega),
    List.take_of_length_le (by omega)]
  exact eq_iff_foldl_or_xor (by omega)

/-- `c'`. -/
abbrev bC : Buf := ⟨3, e4C, 1568⟩

/-- The mask: all ones if `p`, and zero otherwise. -/
def mask (p : Prop) [Decidable p] : BitVec 32 := if p then 0xffffffff else 0

/-- The comparison, from the setup. -/
structure CL (s₀ : State) (m : Mem) (k : Nat) (u : State) : Prop where
  ctx : Ctx Y s₀ u
  mem : u.mem = m
  edi : u.gpr .edi = arg s₀ 1 + BitVec.ofNat 32 k
  ebp : u.gpr .ebp = arg s₀ 3 + BitVec.ofNat 32 k
  ecx : u.gpr .ecx = BitVec.ofNat 32 (1568 - k)
  ebx : u.gpr .ebx = (accB (ct s₀) (bytesAt m (Buf.addr s₀ bC) 1568) k).setWidth 32

theorem cmp_step {s₀ : State} (hp : TPre Y s₀) {m : Mem} {k : Nat} (hk : k < 1568) {u : State}
    (h : CL s₀ m k u) :
    WP isa (.block cmp4Body) u fun u' => CL s₀ m (k + 1) u' ∧ isa.eval .ne u' = some (decide (k + 1 < 1568)) := by
  have f1 : (arg s₀ 1).toNat + 1568 ≤ 2 ^ 32 := hp.fit 1 (by decide)
  have f3 : (arg s₀ 3).toNat + 49152 ≤ 2 ^ 32 := hp.fit 3 (by decide)
  have e₁ : u.ea (at_ .edi 0) = Buf.addr s₀ ⟨1, 0, 1568⟩ + BitVec.ofNat 64 k := by
    simp only [State.ea, at_, h.edi]; rw [ea_add (by omega), addr0]; rfl
  have e₂ : u.ea (at_ .ebp e4C) = Buf.addr s₀ bC + BitVec.ofNat 64 k := by
    simp only [State.ea, at_, h.ebp]
    rw [ea_add (by simp only [e4C]; omega), Buf.addr_eq hp (b := bC) (by decide), BitVec.add_assoc,
      ← BitVec.ofNat_add, Nat.add_comm]
  have i₁ := Buf.inRegR (o := k) (n := 1) hp (b := ⟨1, 0, 1568⟩) (by decide) h.ctx.rd h.ctx.wr (show k + 1 ≤ 1568 by omega)
  refine wp_movzx' (by rw [e₁]; exact i₁) fun u₁ o₁ v₁ => ?_
  have c₁ := h.ctx.only o₁ (by decide) (by decide)
  have e₂' : u₁.ea (at_ .ebp e4C) = Buf.addr s₀ bC + BitVec.ofNat 64 k := by
    rw [← e₂]; simp only [State.ea, at_, o₁.gpr .ebp (by decide)]
  have i₂ := Buf.inRegR (o := k) (n := 1) hp (b := bC) (by decide) c₁.rd c₁.wr (show k + 1 ≤ 1568 by omega)
  refine wp_movzx' (by rw [e₂']; exact i₂) fun u₂ o₂ v₂ => ?_
  refine wp_xorr fun u₃ o₃ v₃ => wp_orr fun u₄ o₄ v₄ => wp_addi fun u₅ o₅ v₅ => wp_addi fun u₆ o₆ v₆ =>
    wp_subi_last fun u₇ o₇ v₇ z₇ => ?_
  have c₇ := (((((c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)).only o₄ (by decide)
    (by decide)).only o₅ (by decide) (by decide)).only o₆ (by decide) (by decide)).only o₇ (by decide) (by decide)
  have m₁ : u₁.mem = m := o₁.mem.trans h.mem
  have x₁ : u.mem (Buf.addr s₀ ⟨1, 0, 1568⟩ + BitVec.ofNat 64 k) = (ct s₀).getD k 0 := by
    rw [h.ctx.ro hp (b := ⟨1, 0, 1568⟩) (by decide) rfl hk, ct_eq, bytesAt_getD _ _ hk]
  have x₂ : u₁.mem (Buf.addr s₀ bC + BitVec.ofNat 64 k) = (bytesAt m (Buf.addr s₀ bC) 1568).getD k 0 := by
    rw [m₁, bytesAt_getD _ _ hk]
  have ex : u₆.gpr .ecx = BitVec.ofNat 32 (1568 - k) := by
    rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide),
      o₂.gpr _ (by decide), o₁.gpr _ (by decide), h.ecx]
  refine ⟨⟨c₇, by rw [o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, m₁], ?_, ?_, by rw [v₇, ex]; exact cnt_next hk,
    ?_⟩, ?_⟩
  · rw [o₇.gpr .edi (by decide), o₆.gpr .edi (by decide), v₅, o₄.gpr .edi (by decide), o₃.gpr .edi (by decide),
      o₂.gpr .edi (by decide), o₁.gpr .edi (by decide), h.edi,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]
  · rw [o₇.gpr .ebp (by decide), v₆, o₅.gpr .ebp (by decide), o₄.gpr .ebp (by decide), o₃.gpr .ebp (by decide),
      o₂.gpr .ebp (by decide), o₁.gpr .ebp (by decide), h.ebp,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]
  · rw [o₇.gpr .ebx (by decide), o₆.gpr .ebx (by decide), o₅.gpr .ebx (by decide), v₄, v₃, o₃.gpr .ebx (by decide),
      o₂.gpr .ebx (by decide), o₂.gpr .eax (by decide), v₂, o₁.gpr .ebx (by decide), v₁, h.ebx, e₁, e₂', x₁, x₂,
      accB, BitVec.setWidth_or, BitVec.setWidth_xor]
  · show u₇.zf.map (!·) = _
    rw [z₇, ex]; exact cnt_ne hk (by decide)

/-- `ebx ←` all ones if `ct = c'`, and zero otherwise. -/
theorem cmp_piece (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → s'.mem = s.mem →
      s'.gpr .ebx = mask (ct s₀ = bytesAt s.mem (Buf.addr s₀ bC) 1568) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B cmp4C := by
  refine Piece.seq (setup_piece (fun s₀ s₁ => s₁.gpr .edi = arg s₀ 1 ∧ s₁.gpr .ebp = arg s₀ 3 ∧
      s₁.gpr .ecx = 1568 ∧ s₁.gpr .ebx = 0) (fun s₀ s hp h => ?_) hA (by taint_decide)) ?_
  · have ea : s.ea (at_ .esp 24) = argAddr s₀ 1 := h.argEa (i := 1)
    refine wp_movm' (by rw [ea]; exact h.argIn hp (by decide)) fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine wp_movr' fun s₂ o₂ v₂ => wp_movi fun s₃ o₃ v₃ => wp_movi fun s₄ o₄ v₄ => WP.block_nil_iff.mpr ?_
    have c₄ := ((c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)).only o₄ (by decide) (by decide)
    refine ⟨c₄, by rw [o₄.mem, o₃.mem, o₂.mem, o₁.mem], ?_, ?_, by rw [o₄.gpr _ (by decide), v₃], v₄⟩
    · rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁, ea, h.argw hp (by decide)]
    · rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂, c₁.esi]; rfl
  refine Piece.seq (B := fun s₀ u => ∃ s, A s₀ s ∧ CL s₀ s.mem 1568 u)
    (Piece.taint [.edi, .ebp, .ecx] (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂, e₃, e₄⟩ => ?_)
      (fun s₀ s₀' s s' hp hp' hq ⟨_, _, _, _, e₁, e₂, e₃, _⟩ ⟨_, _, _, _, e₁', e₂', e₃', _⟩ r hr => ?_)
      (by taint_decide)) ?_
  · refine (wp_count (N := 1568) (by decide) (CL s₀ s.mem) ⟨h₁, m₁, by rw [e₁]; simp, by rw [e₂]; simp,
      by rw [e₃]; rfl, by rw [e₄]; rfl⟩ fun k hk u h => cmp_step hp hk h).mono fun u h => ⟨s, ha, h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [e₁, e₁', hq.2.1 1 (by decide)]
    · rw [e₂, e₂', hq.2.1 3 (by decide)]
    · rw [e₃, e₃']
  refine Piece.taint [] (fun s₀ u hp ⟨s, ha, h⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  refine wp_subi fun u₁ o₁ v₁ f₁ => wp_sbbself f₁ fun u₂ o₂ v₂ => WP.block_nil_iff.mpr ?_
  have c₂ := (h.ctx.only o₁ (by decide) (by decide)).only o₂ (by decide) (by decide)
  refine hQ s₀ s u₂ hp ha c₂ (by rw [o₂.mem, o₁.mem, h.mem]) ?_
  rw [v₂, CheckEk.sbb_mask, h.ebx, mask]
  have hl : (bytesAt s.mem (Buf.addr s₀ bC) 1568).length = 1568 := bytesAt_length _ _ _
  have hc : (ct s₀).length = 1568 := by rw [ct_eq]; exact bytesAt_length _ _ _
  have lt := (accB (ct s₀) (bytesAt s.mem (Buf.addr s₀ bC) 1568) 1568).isLt
  by_cases e : ct s₀ = bytesAt s.mem (Buf.addr s₀ bC) 1568
  · have z := (accB_zero hc hl).mp e
    rw [ite_eq_left e, z]; rfl
  · have z : accB (ct s₀) (bytesAt s.mem (Buf.addr s₀ bC) 1568) 1568 ≠ 0 := fun z => e ((accB_zero hc hl).mpr z)
    rw [ite_eq_right e]
    have : ¬ ((accB (ct s₀) (bytesAt s.mem (Buf.addr s₀ bC) 1568) 1568).setWidth 32).toNat < (1 : BitVec 32).toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
      intro h'
      exact z (BitVec.eq_of_toNat_eq (by simp at h'; simp [h']))
    simp only [this, decide_false]
    rfl

/-! ## The selection -/

/-- `b ^ ((a ^ b) & m)`: `a` if `m` is all ones, and `b` if it is zero. -/
def selB (m a b : Byte) : Byte := b ^^^ ((a ^^^ b) &&& m)

/-- `key`, `K'` and `K̄`. -/
abbrev bKey : Buf := ⟨2, 0, 32⟩
abbrev bK : Buf := ⟨3, e4KR, 32⟩
abbrev bKB : Buf := ⟨3, de4KB, 32⟩

/-- The selection, from the setup. -/
structure SL (s₀ : State) (m : Mem) (M : BitVec 32) (k : Nat) (u : State) : Prop where
  ctx : Ctx Y s₀ u
  fr : Frame [Buf.rgn s₀ bKey] m u.mem
  edi : u.gpr .edi = arg s₀ 3 + BitVec.ofNat 32 k
  ebp : u.gpr .ebp = arg s₀ 2 + BitVec.ofNat 32 k
  ecx : u.gpr .ecx = BitVec.ofNat 32 (32 - k)
  ebx : u.gpr .ebx = M
  out : ∀ j < k, u.mem (Buf.addr s₀ bKey + BitVec.ofNat 64 j) =
    selB (M.setWidth 8) (m (Buf.addr s₀ bK + BitVec.ofNat 64 j)) (m (Buf.addr s₀ bKB + BitVec.ofNat 64 j))

theorem sel_step {s₀ : State} (hp : TPre Y s₀) {m : Mem} {M : BitVec 32} {k : Nat} (hk : k < 32) {u : State}
    (h : SL s₀ m M k u) :
    WP isa (.block sel4Body) u fun u' => SL s₀ m M (k + 1) u' ∧ isa.eval .ne u' = some (decide (k + 1 < 32)) := by
  have f2 : (arg s₀ 2).toNat + 32 ≤ 2 ^ 32 := hp.fit 2 (by decide)
  have f3 : (arg s₀ 3).toNat + 49152 ≤ 2 ^ 32 := hp.fit 3 (by decide)
  have ea : ∀ (u' : State) (o : Nat) (b : Buf), u'.gpr .edi = arg s₀ 3 + BitVec.ofNat 32 k → b.arg = 3 → b.off = o →
      Y.ok b = true → o + k < 49152 → u'.ea (at_ .edi o) = Buf.addr s₀ b + BitVec.ofNat 64 k :=
    fun u' o b e h₁ h₂ hok ho => by
      simp only [State.ea, at_, e]
      rw [ea_add (by omega), Buf.addr_eq hp hok, h₁, h₂, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]
  have e₁ := ea u e4KR bK h.edi rfl rfl (by decide) (by simp only [e4KR]; omega)
  have i₁ := Buf.inRegR (o := k) (n := 1) hp (b := bK) (by decide) h.ctx.rd h.ctx.wr (show k + 1 ≤ 32 by omega)
  refine wp_movzx' (by rw [e₁]; exact i₁) fun u₁ o₁ v₁ => ?_
  have c₁ := h.ctx.only o₁ (by decide) (by decide)
  have e₂ := ea u₁ de4KB bKB (by rw [o₁.gpr .edi (by decide), h.edi]) rfl rfl (by decide)
    (by simp only [de4KB]; omega)
  have i₂ := Buf.inRegR (o := k) (n := 1) hp (b := bKB) (by decide) c₁.rd c₁.wr (show k + 1 ≤ 32 by omega)
  refine wp_movzx' (by rw [e₂]; exact i₂) fun u₂ o₂ v₂ => ?_
  have c₂ := c₁.only o₂ (by decide) (by decide)
  refine wp_xorr fun u₃ o₃ v₃ => wp_andr fun u₄ o₄ v₄ => wp_xorr fun u₅ o₅ v₅ => ?_
  have c₅ := ((c₂.only o₃ (by decide) (by decide)).only o₄ (by decide) (by decide)).only o₅ (by decide) (by decide)
  have eb : u₅.gpr .ebp = arg s₀ 2 + BitVec.ofNat 32 k := by
    rw [o₅.gpr .ebp (by decide), o₄.gpr .ebp (by decide), o₃.gpr .ebp (by decide), o₂.gpr .ebp (by decide),
      o₁.gpr .ebp (by decide), h.ebp]
  have e₃ : u₅.ea (at_ .ebp 0) = Buf.addr s₀ bKey + BitVec.ofNat 64 k := by
    simp only [State.ea, at_, eb]; rw [ea_add (by omega), addr0]; rfl
  have i₃ := Buf.inRegW (o := k) (n := 1) hp (b := bKey) (by decide) (by decide) c₅.wr (show k + 1 ≤ 32 by omega)
  refine wp_store8 (by rw [e₃]; exact i₃) (wp_addi fun u₆ o₆ v₆ => wp_addi fun u₇ o₇ v₇ =>
    wp_subi_last fun u₈ o₈ v₈ z₈ => ?_)
  obtain ⟨r, hr, hcr⟩ := Buf.contains hp (b := bKey) (by decide) (by decide) (o := k) (n := 1)
    (show k + 1 ≤ 32 by omega)
  set u₅' : State := { u₅ with mem := u₅.mem.writeW (u₅.ea (at_ .ebp 0)) ((u₅.gpr Reg8.al.reg).setWidth 8) }
  have c₅' : Ctx Y s₀ u₅' := ⟨c₅.esp, c₅.rd, c₅.wr, c₅.esi, by
    show Frame _ _ (u₅.mem.writeW _ _); rw [e₃]; exact c₅.frame.writeW hr _ hcr⟩
  have c₈ := ((c₅'.only o₆ (by decide) (by decide)).only o₇ (by decide) (by decide)).only o₈ (by decide)
    (by decide)
  have m₅ : u₅.mem = u.mem := by rw [o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  have m₈ : u₈.mem = u.mem.writeW (Buf.addr s₀ bKey + BitVec.ofNat 64 k) ((u₅.gpr .eax).setWidth 8) := by
    rw [o₈.mem, o₇.mem, o₆.mem]; show u₅.mem.writeW _ _ = _; rw [e₃, m₅]; rfl
  have keepK : ∀ b : Buf, b.arg = 3 → Y.ok b = true → ∀ i < b.len,
      u.mem (Buf.addr s₀ b + BitVec.ofNat 64 i) = m (Buf.addr s₀ b + BitVec.ofNat 64 i) := fun b hb hok i hi =>
    (h.fr.bytes (R := Buf.rgn s₀ b) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact Buf.disj hp hok (c := bKey) (by decide) (by simp [Lay.sep, hb, Y, Lay.awr])) (by
        show b.len ≤ 2 ^ 64; have := Buf.fit hp hok; omega) hi)
  have x₁ : u.mem (Buf.addr s₀ bK + BitVec.ofNat 64 k) = m (Buf.addr s₀ bK + BitVec.ofNat 64 k) :=
    keepK bK rfl (by decide) k hk
  have x₂ : u₁.mem (Buf.addr s₀ bKB + BitVec.ofNat 64 k) = m (Buf.addr s₀ bKB + BitVec.ofNat 64 k) := by
    rw [o₁.mem]; exact keepK bKB rfl (by decide) k hk
  have ex : u₇.gpr .ecx = BitVec.ofNat 32 (32 - k) := by
    rw [o₇.gpr .ecx (by decide), o₆.gpr .ecx (by decide), show u₅'.gpr .ecx = u₅.gpr .ecx from rfl,
      o₅.gpr .ecx (by decide), o₄.gpr .ecx (by decide), o₃.gpr .ecx (by decide), o₂.gpr .ecx (by decide),
      o₁.gpr .ecx (by decide), h.ecx]
  have ebx₅ : u₅.gpr .ebx = M := by
    rw [o₅.gpr .ebx (by decide), o₄.gpr .ebx (by decide), o₃.gpr .ebx (by decide), o₂.gpr .ebx (by decide),
      o₁.gpr .ebx (by decide), h.ebx]
  have val : (u₅.gpr .eax).setWidth 8 =
      selB (M.setWidth 8) (m (Buf.addr s₀ bK + BitVec.ofNat 64 k)) (m (Buf.addr s₀ bKB + BitVec.ofNat 64 k)) := by
    rw [v₅, v₄, v₃, o₄.gpr .edx (by decide), o₃.gpr .edx (by decide), o₃.gpr .ebx (by decide),
      o₂.gpr .ebx (by decide), o₂.gpr .eax (by decide), v₂, v₁, o₁.gpr .ebx (by decide), h.ebx, e₁, e₂, x₁, x₂,
      selB]
    simp only [BitVec.setWidth_xor, BitVec.setWidth_and, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide),
      BitVec.setWidth_eq]
    rw [BitVec.xor_comm]
  refine ⟨⟨c₈, ?_, ?_, ?_, by rw [v₈, ex]; exact cnt_next hk, ?_, fun j hj => ?_⟩, ?_⟩
  · rw [m₈]
    exact h.fr.writeW (List.mem_singleton_self _) _ (by
      show (⟨Buf.addr s₀ bKey, 32⟩ : Region).Contains _ (8 / 8)
      simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
  · rw [o₈.gpr .edi (by decide), o₇.gpr .edi (by decide), v₆, show u₅'.gpr .edi = u₅.gpr .edi from rfl,
      o₅.gpr .edi (by decide), o₄.gpr .edi (by decide), o₃.gpr .edi (by decide), o₂.gpr .edi (by decide),
      o₁.gpr .edi (by decide), h.edi, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]
  · rw [o₈.gpr .ebp (by decide), v₇, o₆.gpr .ebp (by decide), show u₅'.gpr .ebp = u₅.gpr .ebp from rfl, eb,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]
  · rw [o₈.gpr .ebx (by decide), o₇.gpr .ebx (by decide), o₆.gpr .ebx (by decide),
      show u₅'.gpr .ebx = u₅.gpr .ebx from rfl, ebx₅]
  · rw [m₈, writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have ne : Buf.addr s₀ bKey + BitVec.ofNat 64 j ≠ Buf.addr s₀ bKey + BitVec.ofNat 64 k := fun e => by
        have := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp e)
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        omega
      rw [ite_eq_right ne]
      exact h.out j hj
    · rw [ite_eq_left rfl, val]
  · show u₈.zf.map (!·) = _
    rw [z₈, ex]; exact cnt_ne hk (by decide)

/-- `key ← K̄ ^ ((K' ^ K̄) & ebx)`, byte by byte. -/
theorem sel_piece (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → Frame [Buf.rgn s₀ bKey] s.mem s'.mem →
      (∀ j < 32, s'.mem (Buf.addr s₀ bKey + BitVec.ofNat 64 j) = selB ((s.gpr .ebx).setWidth 8)
        (s.mem (Buf.addr s₀ bK + BitVec.ofNat 64 j)) (s.mem (Buf.addr s₀ bKB + BitVec.ofNat 64 j))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B sel4C := by
  refine Piece.seq (B := fun s₀ s₁ => ∃ s, A s₀ s ∧ SL s₀ s.mem (s.gpr .ebx) 0 s₁)
    (Piece.taint [.esp, .esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) (by taint_decide))
    ?_
  · have h := hA s₀ s hp ha
    have ea : s.ea (at_ .esp 28) = argAddr s₀ 2 := h.argEa (i := 2)
    refine wp_movr' fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine wp_movm' (by rw [o₁.rd, o₁.wr, show s₁.ea (at_ .esp 28) = s.ea (at_ .esp 28) by
      simp only [State.ea, at_, o₁.gpr .esp (by decide)], ea]; exact h.argIn hp (by decide)) fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine wp_movi fun s₃ o₃ v₃ => WP.block_nil_iff.mpr ⟨s, ha, ?_⟩
    have c₃ := c₂.only o₃ (by decide) (by decide)
    refine ⟨c₃, by rw [o₃.mem, o₂.mem, o₁.mem]; exact Frame.refl _ _, ?_, ?_, by rw [v₃]; rfl, ?_,
      fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    · rw [o₃.gpr .edi (by decide), o₂.gpr .edi (by decide), v₁, h.esi]; simp; rfl
    · rw [o₃.gpr .ebp (by decide), v₂, o₁.mem, show s₁.ea (at_ .esp 28) = s.ea (at_ .esp 28) by
        simp only [State.ea, at_, o₁.gpr .esp (by decide)], ea, h.argw hp (by decide)]; simp
    · rw [o₃.gpr .ebx (by decide), o₂.gpr .ebx (by decide), o₁.gpr .ebx (by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [(hA _ _ hp ha).esp, (hA _ _ ‹_› ha').esp, hq.E1]
    · rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]
  refine Piece.taint [.edi, .ebp, .ecx] (fun s₀ s₁ hp ⟨s, ha, h⟩ => ?_)
    (fun s₀ s₀' s s' hp hp' hq ⟨_, _, h⟩ ⟨_, _, h'⟩ r hr => ?_) (by taint_decide)
  · refine (wp_count (N := 32) (by decide) (SL s₀ s.mem (s.gpr .ebx)) h fun k hk u h => sel_step hp hk h).mono
      fun u h => hQ s₀ s u hp ha h.ctx h.fr fun j hj => h.out j hj
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h.edi, h'.edi, hq.2.1 3 (by decide)]
    · rw [h.ebp, h'.ebp, hq.2.1 2 (by decide)]
    · rw [h.ecx, h'.ecx]

end VG.Proof.MlKem1024.X86.Decaps
