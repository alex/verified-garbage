import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Impl.MdStream.Arm
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Streaming Merkle–Damgård hash functions on ARMv7: common lemmas

Untrusted: everything here is checked by Lean. The contracts the generic
proofs are written against, what they need of a hash function's parameters
(`Shape`) and of its compression function (`CalleeOk`), the call of the
compression function (`compressAt`), saving and restoring the caller's
registers, and weakest-precondition rules for the instruction forms used
(which the proofs of other ARMv7 code use too).
-/

namespace VG.Proof.MdStream.Arm

open VG VG.Arm VG.Impl.MdStream.Arm
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes)

/-! ## Addresses and regions -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

theorem add_ofNat (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem frame_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region}
    (hd : ∀ r ∈ rs, R.Disjoint r) (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m' (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) := by
  refine hf _ fun r hr hc => hd r hr _ ?_ hc
  simp only [Region.Contains]
  rw [Offset.add_sub_cancel_left, toNat_ofNat_lt (by omega)]
  omega

/-- Addresses within a region that does not wrap around the 32-bit space. -/
theorem addr_off {a : BitVec 32} {k : Nat} (h : a.toNat + k < 2 ^ 32) :
    State.addr (a + BitVec.ofNat 32 k) = State.addr a + BitVec.ofNat 64 k := addr_add h

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

/-- Byte `k` of the `n` bytes of stack arguments. -/
theorem argByte_eq {s : State} {n : Nat} (hsp : s.sp.toNat + n ≤ 2 ^ 32) {k : Nat} (hk : k < n) :
    VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [VG.Arm.Taint.argByte, stackArgAddr]
  rw [addr_off (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v` (the flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 32) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 32) : Upd s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl, rfl⟩

theorem Upd.subs (s : State) (d : Reg) (x y v : BitVec 32) : Upd s ((subFlags s x y).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, subFlags, h], rfl, rfl, rfl, rfl⟩

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

/-- `s'` is `s` with other flags. -/
structure Fupd (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

theorem op2_imm {s : State} {v : BitVec 32} (h : encodable v = true) : (Op2.imm v).eval s = some v := by
  simp [Op2.eval, h]

theorem op2_reg (s : State) (r : Reg) : (Op2.reg r).eval s = some (s.gpr r) := rfl

theorem op2_lsr {s : State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .lsr n).eval s = some (s.gpr r >>> n) := by
  simp [Op2.eval, h]

theorem op2_lsl {s : State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .lsl n).eval s = some (s.gpr r <<< n) := by
  simp [Op2.eval, h]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s = some v)
    (k : ∀ s', Upd s s' d v → WP isa (.block is) s' Q) : WP isa (.block (.mov d o :: is)) s Q :=
  WP.cons (s' := s.setReg d v) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_add {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .add d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n + y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_sub {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n - y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .sub d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n - y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_and {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n &&& y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .and d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n &&& y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_orr {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n ||| y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .orr d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n ||| y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_subs {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n - y) → s'.z = (s.gpr n - y == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y)) (by simp [exec, ho])
    (k _ (Upd.subs _ _ _ _ _) rfl)

theorem wp_cmp {n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Fupd s s' → s'.z = (s.gpr n - y == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.cmp n o :: is)) s Q :=
  WP.cons (s' := subFlags s (s.gpr n) y) (by simp [exec, ho]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

theorem wp_rev {d m : Reg} (k : ∀ s', Upd s s' d (rev (s.gpr m)) → WP isa (.block is) s' Q) :
    WP isa (.block (.rev d m :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_ldr {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_ldr ho hin) (k _ (Upd.setReg _ _ _))

theorem wp_str {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_str ho hout) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem wp_ldrb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrb t n off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := s.setReg t ((s.mem _).setWidth 32)) (by simp [exec, ho, State.load8, hin])
    (k _ (Upd.setReg _ _ _))

theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := { s with mem := s.mem.writeW _ ((s.gpr t).setWidth 8) })
    (by simp [exec, ho, State.store8, hout]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem wp_ldrSp {t : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.sp + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := s.setReg t (s.mem.readW _ 32)) (by simp [exec, ho, State.load32, hin])
    (k _ (Upd.setReg _ _ _))

end

/-! ## Arithmetic -/

theorem bytesAt_getD {m : Mem} {p : Addr} {n : Nat} {l : List Byte} (h : bytesAt m p n = l) {k : Nat}
    (hk : k < n) : m (p + BitVec.ofNat 64 k) = l.getD k 0 := by
  subst h; simp [bytesAt, List.getD_eq_getElem?_getD, hk]

theorem eval_eq (s : State) : eval .eq s = some s.z := rfl
theorem eval_ne (s : State) : eval .ne s = some !s.z := rfl

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  rw [show BitVec.ofNat 32 a = BitVec.ofNat 32 (a - b) + BitVec.ofNat 32 b by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h], BitVec.add_sub_cancel]

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    change _ = 0 at this
    omega

theorem ofNat_shr {a n : Nat} (h : a < 2 ^ 32) : BitVec.ofNat 32 a >>> n = BitVec.ofNat 32 (a / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)]

theorem shr6 {a : Nat} (h : a < 2 ^ 32) : BitVec.ofNat 32 a >>> 6 = BitVec.ofNat 32 (a / 64) :=
  ofNat_shr h

theorem cmp0 {a : Nat} (h : a < 2 ^ 32) : (BitVec.ofNat 32 a - 0 == 0) = decide (a = 0) := by
  rw [show BitVec.ofNat 32 a - 0 = BitVec.ofNat 32 a by simp]; exact ofNat_beq_zero h

theorem and63 (x : BitVec 32) : x &&& 63 = BitVec.ofNat 32 (x.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (63 : BitVec 32).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-! ## Saving and restoring registers -/

/-- The memory after storing the registers `l` (values `g`) at `B + offset`. -/
def saveMem (m : Mem) (B : Addr) (g : Reg → BitVec 32) : List (Reg × Nat) → Mem
  | [] => m
  | (r, d) :: l => saveMem (m.writeW (B + BitVec.ofNat 64 d) (g r)) B g l

theorem saveList_ok {b : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop),
    (∀ p ∈ l, p.2 < 4096 ∧ (s.gpr b).toNat + p.2 < 2 ^ 32 ∧
      InRegions s.wr (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMem s.mem (State.addr (s.gpr b)) s.gpr l → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.str p.1 b p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ k; exact k s rfl rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hl k
    obtain ⟨h1, h2, h3⟩ := hl p (by simp)
    refine wp_str h1 (addr_add h2) h3 fun s₁ u₁ => ?_
    refine ih s₁ Q (fun q hq => ?_) fun s' g rd wr sp m => k s' (g.trans u₁.gpr) (rd.trans u₁.rd)
      (wr.trans u₁.wr) (sp.trans u₁.sp) ?_
    · rw [u₁.gpr, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rw [m, u₁.mem, u₁.gpr]; rfl

theorem save_sep (B : Addr) {d e : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) : Mem.Sep (B + BitVec.ofNat 64 d) 4 (B + BitVec.ofNat 64 e) 4 := by
  exact Offset.sep _ h (by omega) (by omega)

theorem readW_writeW_save (m : Mem) (B : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (save_sep B hd he h) (by decide)

/-! Saves at `so + d`, with the conditions on the literal offsets `d`, `e`
alone, which `decide` discharges. -/
theorem readW_writeW_save_so {so : Nat} (hso : so ≤ 256) (m : Mem) (B : Addr) (v : BitVec 32)
    {d e : Nat} (hd : d ≤ 64) (he : e ≤ 64) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (B + BitVec.ofNat 64 (so + e)) v).readW (B + BitVec.ofNat 64 (so + d)) 32 =
      m.readW (B + BitVec.ofNat 64 (so + d)) 32 :=
  readW_writeW_save m B v (by omega) (by omega) (by omega)

theorem readW_writeW_save_so_l {so : Nat} (hso : so ≤ 256) (m : Mem) (B : Addr) (v : BitVec 32)
    {e : Nat} (he : e ≤ 64) (h : 4 ≤ e) :
    (m.writeW (B + BitVec.ofNat 64 (so + e)) v).readW (B + BitVec.ofNat 64 so) 32 =
      m.readW (B + BitVec.ofNat 64 so) 32 :=
  readW_writeW_save m B v (by omega) (by omega) (by omega)


theorem saveMem_frame (m : Mem) (B : Addr) (g : Reg → BitVec 32) {L : Nat} (hL : L < 2 ^ 32) :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, p.2 + 4 ≤ L) → Frame [⟨B, L⟩] m (saveMem m B g l) := by
  intro l
  induction l generalizing m with
  | nil => intro _; exact Frame.refl _ _
  | cons p l ih =>
    intro hl
    have h := hl p (by simp)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (n := 32 / 8) h (by omega))).trans
      (ih _ fun q hq => hl q (List.mem_cons_of_mem _ hq))

theorem restoreList_ok {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ≠ .r3 ∧ p.2 < 4096 ∧ (s.gpr .r3).toNat + p.2 < 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r3) + BitVec.ofNat 64 p.2) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW (State.addr (s.gpr .r3) + BitVec.ofNat 64 p.2) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.ldr p.1 .r3 p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h0, h1, h2, h3⟩ := hl p (by simp)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine wp_ldr h1 (addr_add h2) h3 fun s₁ u₁ => ?_
    have e3 : s₁.gpr .r3 = s.gpr .r3 := u₁.other _ (Ne.symm h0)
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm hrd hwr hsp => k s' (fun q hq => ?_)
      (fun r hr => ?_) (hm.trans u₁.mem) (hrd.trans u₁.rd) (hwr.trans u₁.wr) (hsp.trans u₁.sp)
    · rw [e3, u₁.rd, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, e3]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other r hr.1]

/-! ## Sizes -/

/-- The sizes the generic proofs support, checked for each hash function by
`decide`. -/
structure Dims (P : Params) : Prop where
  N : 0 < P.N ∧ P.N ≤ 64
  so : P.so % 4 = 0 ∧ P.so ≤ 256
  enc : encodable (BitVec.ofNat 32 P.N) = true

/-! ## Saving the caller's registers -/

section
variable {P : Params}

theorem saved_bound (hd : Dims P) : ∀ p ∈ saved P, P.so ≤ p.2 ∧ p.2 + 4 ≤ P.so + 36 := by
  have := hd.so
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

theorem saved_nodup (P : Params) : ((saved P).map Prod.fst).Nodup := by
  simp only [saved, List.map_cons, List.map_nil]; decide

theorem saved_ne_r3 {p : Reg × Nat} (hp : p ∈ saved P) : p.1 ≠ .r3 := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide

/-- Saving `r4`–`r11` and `lr` with the scratch pointer in `b`. -/
theorem save_ok (hd : Dims P) {b : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    (hfit : (s.gpr b).toNat + (P.so + 48) ≤ 2 ^ 32)
    (hin : ∀ d, P.so ≤ d → d + 4 ≤ P.so + 36 → InRegions s.wr (State.addr (s.gpr b) + BitVec.ofNat 64 d) 4)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMem s.mem (State.addr (s.gpr b)) s.gpr (saved P) → WP isa (.block rest) s' Q) :
    WP isa (.block (save P b ++ rest)) s Q := by
  have := hd.so
  refine saveList_ok (saved P) s Q (fun p hp => ?_) k
  have := saved_bound hd p hp
  exact ⟨by omega, by omega, hin _ this.1 this.2⟩

set_option simprocs false in
theorem saveMem_saved (hd : Dims P) (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    ∀ p ∈ saved P, (saveMem m B g (saved P)).readW (B + BitVec.ofNat 64 p.2) 32 = g p.1 := by
  have := hd.so
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [saved, saveMem, Mem.readW_writeW_self32,
    readW_writeW_save_so this.2, readW_writeW_save_so_l this.2]

/-- Restoring `r4`–`r11` and `lr` from the save area at `scratch`. -/
theorem restore_ok (hd : Dims P) {s : State} {scr : BitVec 32} (h3 : s.gpr .r3 = scr)
    (hfit : scr.toNat + (P.so + 48) ≤ 2 ^ 32)
    (hin : ∀ d, P.so ≤ d → d + 4 ≤ P.so + 36 → InRegions (s.rd ++ s.wr) (State.addr scr + BitVec.ofNat 64 d) 4)
    (g : Reg → BitVec 32) (hsv : ∀ p ∈ saved P, s.mem.readW (State.addr scr + BitVec.ofNat 64 p.2) 32 = g p.1)
    {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved P, s'.gpr p.1 = g p.1) → (∀ r, r ∉ (saved P).map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block (restore P)) s Q := by
  have := hd.so
  rw [restore, ← List.append_nil ((saved P).map _)]
  refine restoreList_ok (saved P) s Q (saved_nodup P) (fun p hp => ?_)
    fun s' ho hr hm hrd hwr hsp => WP.block_nil (k s' (fun p hp => ?_) hr hm hrd hwr hsp)
  · have := saved_bound hd p hp
    rw [h3]
    exact ⟨saved_ne_r3 hp, by omega, by omega, hin _ this.1 this.2⟩
  · rw [ho p hp, h3, hsv p hp]

/-- The callee-saved registers are the caller's again once `restore` has run. -/
theorem preserved_of {s₀ s' : State} (hsv : ∀ p ∈ saved P, s'.gpr p.1 = s₀.gpr p.1) :
    ∀ r ∈ preserved, s'.gpr r = s₀.gpr r := by
  intro r hr
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsv (.r4, P.so) (by simp [saved])
  · exact hsv (.r5, P.so + 4) (by simp [saved])
  · exact hsv (.r6, P.so + 8) (by simp [saved])
  · exact hsv (.r7, P.so + 12) (by simp [saved])
  · exact hsv (.r8, P.so + 16) (by simp [saved])
  · exact hsv (.r9, P.so + 20) (by simp [saved])
  · exact hsv (.r10, P.so + 24) (by simp [saved])
  · exact hsv (.r11, P.so + 28) (by simp [saved])
  · exact hsv (.lr, P.so + 32) (by simp [saved])

end

/-! ## The contracts

The generic proofs are written against these; each hash function's own
contracts are these for its instance. -/

/-- The 64-bit `count` argument of `update`/`finalize`, in `r2:r3` (AAPCS: the
low word in `r2`). -/
def count (s : State) : BitVec 64 := s.gpr .r3 ++ s.gpr .r2

section
variable {P : Params} (H : Md 64 P.N 8)

/-- The contract of the compression function: updates the hash value at
`r0` with the `r2` blocks at `r1`, with scratch space `r3` (`so` bytes). -/
def compressK : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), P.N⟩
    let blocks : Region := ⟨State.addr (s.gpr .r1), 64 * (s.gpr .r2).toNat⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), P.so⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    (s.gpr .r0).toNat + P.N ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 64 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + P.so ≤ 2 ^ 32
  post s s' :=
    H.stateAt s'.mem (State.addr (s.gpr .r0)) =
      H.compressBlocks (H.stateAt s.mem (State.addr (s.gpr .r0))) s.mem (State.addr (s.gpr .r1))
        (s.gpr .r2).toNat
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

/-- The contract of `update`: if the state at `r0` represents a message of
`count` bytes (modulo 2⁶⁴) from any initial hash value, it then represents
that message followed by the `len` bytes at `data`. -/
def updK : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), P.N + 64⟩
    let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 2), P.so + 48⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + (P.N + 64) ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
    (stackArg s 2).toNat + (P.so + 48) ≤ 2 ^ 32 ∧ s.sp.toNat + 12 ≤ 2 ^ 32
  post s s' := ∀ iv m, H.Repr iv s.mem (State.addr (s.gpr .r0)) m → count s = BitVec.ofNat 64 m.length →
    H.Repr iv s'.mem (State.addr (s.gpr .r0))
      (m ++ bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

/-- The contract of `finalize`: if the state at `r0` represents a message of
`count` bytes, writes its final hash value to `out` (`N` bytes). -/
def finK : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), P.N + 64⟩
    let out : Region := ⟨State.addr (stackArg s 0), P.N⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), P.so + 48⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + (P.N + 64) ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + P.N ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + (P.so + 48) ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ iv m, H.Repr iv s.mem (State.addr (s.gpr .r0)) m → H.lenOk m.length →
    count s = BitVec.ofNat 64 m.length → bytesAt s'.mem (State.addr (stackArg s 0)) P.N = H.hash iv m
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end

/-! ## What each hash function's own code must do -/

/-- The length field and the digest: `P.len` stores the length field for the
byte count in `r4:r5` at `r0 + N + 56`, and `P.out` writes the digest of the
hash value at `r0` to `r6`; both write only `r9`. -/
structure Shape {P : Params} (H : Md 64 P.N 8) : Prop where
  len : ∀ s : State, (s.gpr .r0).toNat + (P.N + 64) ≤ 2 ^ 32 →
    InRegions s.wr (State.addr (s.gpr .r0) + BitVec.ofNat 64 (P.N + 56)) 8 →
    WP isa (.block P.len) s fun s' => (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (P.N + 56))
        (H.lenOf (s.gpr .r5 ++ s.gpr .r4))
  out : ∀ s : State, (s.gpr .r0).toNat + P.N ≤ 2 ^ 32 → (s.gpr .r6).toNat + P.N ≤ 2 ^ 32 →
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0)) P.N → InRegions s.wr (State.addr (s.gpr .r6)) P.N →
    Region.Disjoint ⟨State.addr (s.gpr .r0), P.N⟩ ⟨State.addr (s.gpr .r6), P.N⟩ →
    WP isa (.block P.out) s fun s' => (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (State.addr (s.gpr .r6)) (H.digest (H.stateAt s.mem (State.addr (s.gpr .r0))))

/-- What `compressAt` needs of the compression function it calls: that it is
correct, makes no calls, and never writes `r0` or `r3`. -/
structure CalleeOk {P : Params} (H : Md 64 P.N 8) (code : Prog isa) : Prop where
  verified : ∀ s, (compressK H).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (compressK H).post s s'
  noCalls : code.noCalls = true
  keeps : ((instrs code).all fun i => dstOf i != some .r0 && dstOf i != some .r3) = true

/-! ## The compression function -/

/-- `n` sets `r2` to `v`. -/
def SetsN (n : Instr) (s : State) (v : BitVec 32) : Prop :=
  ∀ (is : List Instr) (Q : State → Prop), (∀ s', Upd s s' .r2 v → WP isa (.block is) s' Q) →
    WP isa (.block (n :: is)) s Q

theorem setsN_one (s : State) : SetsN (.mov .r2 (.imm 1)) s 1 := fun _ _ k => wp_mov (op2_imm (by decide)) k

theorem setsN_r7 (s : State) : SetsN (.mov .r2 (.reg .r7)) s (s.gpr .r7) := fun _ _ k => wp_mov (op2_reg _ _) k

/-- Compressing the `k` blocks at `r1` (their number set in `r2` by `n`) into
the hash value at `r0`, with scratch space at `r3`. -/
theorem compressWith_ok {P : Params} {H : Md 64 P.N 8} {n : Instr} {s : State} {v : BitVec 32}
    (hn : SetsN n s v) {k : Nat} (hkv : v.toNat = k) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {st scr src : BitVec 32}
    (h0 : s.gpr .r0 = st) (h3 : s.gpr .r3 = scr) (h1 : s.gpr .r1 = src)
    (f₀ : st.toNat + P.N ≤ 2 ^ 32) (f₁ : src.toNat + 64 * k ≤ 2 ^ 32) (f₃ : scr.toNat + P.so ≤ 2 ^ 32)
    (d₁ : Region.Disjoint ⟨State.addr st, P.N⟩ ⟨State.addr scr, P.so⟩)
    (d₂ : Region.Disjoint ⟨State.addr src, 64 * k⟩ ⟨State.addr st, P.N⟩)
    (d₃ : Region.Disjoint ⟨State.addr src, 64 * k⟩ ⟨State.addr scr, P.so⟩)
    (hc : Covers [⟨State.addr src, 64 * k⟩, ⟨State.addr st, P.N⟩, ⟨State.addr scr, P.so⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr st, P.N⟩, ⟨State.addr scr, P.so⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      s'.gpr .r0 = st → s'.gpr .r3 = scr → s'.sp = s.sp →
      Frame [⟨State.addr st, P.N⟩, ⟨State.addr scr, P.so⟩] s.mem s'.mem →
      H.stateAt s'.mem (State.addr st) =
        H.compressBlocks (H.stateAt s.mem (State.addr st)) s.mem (State.addr src) k → Q s') :
    WP isa (compressWith n name code) s Q := by
  have hk : ∀ i ∈ instrs code, dstOf i ≠ some .r0 ∧ dstOf i ≠ some .r3 := by
    intro i hi
    have := List.all_eq_true.mp hf.keeps i hi
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact this
  unfold compressWith
  refine WP.seq (hn _ _ fun s₁ u₁ => WP.block_nil ?_)
  have e0 : s₁.gpr .r0 = st := by rw [u₁.other _ (by decide), h0]
  have e1 : s₁.gpr .r1 = src := by rw [u₁.other _ (by decide), h1]
  have e2 : s₁.gpr .r2 = v := u₁.gpr
  have e3 : s₁.gpr .r3 = scr := by rw [u₁.other _ (by decide), h3]
  have c : ∀ r, r ∉ linkRegs → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr s₁ h
  refine WP.call (k := compressK H) hf.verified
    (rd := [⟨State.addr src, 64 * k⟩]) (wr := [⟨State.addr st, P.N⟩, ⟨State.addr scr, P.so⟩]) ?_ ?_ ?_ ?_
    hf.noCalls
  · simp only [compressK, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c _ (show Reg.r0 ∉ linkRegs by decide), c _ (show Reg.r1 ∉ linkRegs by decide),
      c _ (show Reg.r2 ∉ linkRegs by decide), c _ (show Reg.r3 ∉ linkRegs by decide), e0, e1, e2, e3, hkv]
    exact ⟨trivial, trivial, d₁, d₂, d₃, f₀, f₁, f₃⟩
  · rw [u₁.rd, u₁.wr]; simpa using hc
  · rw [u₁.wr]; exact hw
  · intro s' hrd hwr hsp hf' hcs hg hpost
    simp only [compressK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      c _ (show Reg.r0 ∉ linkRegs by decide), c _ (show Reg.r1 ∉ linkRegs by decide),
      c _ (show Reg.r2 ∉ linkRegs by decide), e0, e1, e2, u₁.mem, hkv] at hpost
    refine hQ s' (hrd.trans u₁.rd) (hwr.trans u₁.wr) (fun r hr hlr => ?_)
      (by rw [hg _ (fun i hi => (hk i hi).1) (by decide), e0])
      (by rw [hg _ (fun i hi => (hk i hi).2) (by decide), e3]) (hsp.trans u₁.sp) (u₁.mem ▸ hf') hpost
    have : r ≠ .r2 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hcs r hr hlr, u₁.other r this]

/-- Compressing the block at `r1` into the hash value at `r0`, with scratch
space at `r3`. -/
theorem compressAt_ok {P : Params} {H : Md 64 P.N 8} {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s : State} {st scr src : BitVec 32}
    (h0 : s.gpr .r0 = st) (h3 : s.gpr .r3 = scr) (h1 : s.gpr .r1 = src)
    (f₀ : st.toNat + P.N ≤ 2 ^ 32) (f₁ : src.toNat + 64 ≤ 2 ^ 32) (f₃ : scr.toNat + P.so ≤ 2 ^ 32)
    (d₁ : Region.Disjoint ⟨State.addr st, P.N⟩ ⟨State.addr scr, P.so⟩)
    (d₂ : Region.Disjoint ⟨State.addr src, 64⟩ ⟨State.addr st, P.N⟩)
    (d₃ : Region.Disjoint ⟨State.addr src, 64⟩ ⟨State.addr scr, P.so⟩)
    (hc : Covers [⟨State.addr src, 64⟩, ⟨State.addr st, P.N⟩, ⟨State.addr scr, P.so⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr st, P.N⟩, ⟨State.addr scr, P.so⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      s'.gpr .r0 = st → s'.gpr .r3 = scr → s'.sp = s.sp →
      Frame [⟨State.addr st, P.N⟩, ⟨State.addr scr, P.so⟩] s.mem s'.mem →
      H.stateAt s'.mem (State.addr st) =
        H.compress (H.stateAt s.mem (State.addr st)) (H.blockAt s.mem (State.addr src)) → Q s') :
    WP isa (compressAt name code) s Q :=
  compressWith_ok (setsN_one s) (k := 1) rfl hf h0 h3 h1 f₀ f₁ f₃ d₁ d₂ d₃ hc hw
    fun s' hrd hwr hcs h0' h3' hsp hf' hs => hQ s' hrd hwr hcs h0' h3' hsp hf' (by rw [hs, Md.compressBlocks_one])

end VG.Proof.MdStream.Arm
