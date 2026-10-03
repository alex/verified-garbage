import VerifiedGarbage.Proof.Ed448.X86_64.ScalarLoop
import VerifiedGarbage.Proof.X448.X86_64.Finish

/-!
# Ed448 scalar arithmetic on x86-64: entry and exit

Saving the callee-saved registers, storing `K`, the remainders the loops
start from (the top bytes of an input), and the result: seven words and a
zero byte at the output's address, then the registers restored.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Keeps Scr rv mv wv word off Outside ofs Saved saved_lt writeW_outside
  word_writeW_self contains_sc ea_sc)
open VG.Impl.X448.X86_64 (W w sc at_ saved)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-- `saveAt b`: the callee-saved registers at `[b]`. -/
theorem saveAt_ok (b : Reg) {s : State} {base : Addr} (hc : s.gpr b = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block (saveAt b)) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Outside base 0 48 s.mem s'.mem ∧
      Saved base s.gpr s'.mem := by
  refine WP.mono (Spill.save_ok b saved s fun p hp => ?_) fun s' ⟨hg, hrd, hwr, hm⟩ =>
    ⟨hg, hrd, hwr, ?_, ?_⟩
  · have := saved_lt p hp; rw [hc]; exact ⟨_, hw, contains_sc (by omega)⟩
  · rw [hm, hc]
    intro x hx
    refine Spill.saveMem_frame_base _ _ _ _ saved_lt (by decide) x fun r hr hx' => ?_
    rw [List.mem_singleton.mp hr] at hx'
    simp only [Region.Contains, ofs] at hx hx'
    omega
  · rw [hm, hc]; exact Spill.saveMem_saved _ _ _ _ (by decide)

theorem loadK_ok (s : State) :
    WP isa (.block loadK) s fun t => rem t = wv kWords ∧ Keeps W s t := by
  apply WP.of_runBlock
  simp only [loadK, W, kWords, List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
    runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [rem, rv, W, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2, ite_false]

/-- `storeK`: `K` at `KC`. -/
theorem storeK_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block storeK) s fun t =>
      mv t.mem base KC 7 = wv kWords ∧ Outside base KC 56 s.mem t.mem ∧
      (∀ r, r ∉ W → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [storeK, WP.block_append_iff]
  refine WP.mono (loadK_ok s) fun a ⟨va, ka⟩ => ?_
  refine WP.mono (Proof.X448.X86_64.stores_ok (hs.of_keeps ka (by decide)) KC W (by decide))
    fun t ⟨vt, ot, gt, rdt, wrt⟩ => ⟨by rw [Proof.X448.X86_64.W_len] at vt; rw [vt]; exact va,
      by rw [ka.2.1] at ot; exact ot, fun r hr => (gt r).trans (ka.1 r hr), rdt.trans ka.2.2.1,
      wrt.trans ka.2.2.2⟩

/-! ## The remainders the loops start from -/

theorem load8_ok {s : State} {p : Addr} (hr : InRegions (s.rd ++ s.wr) p 1) :
    s.load8 p = some (s.mem p) := by
  simp only [State.load8, hr, ite_true]

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_, BitVec.ofInt_natCast]

theorem rotr56 (x : BitVec 64) (h : x.toNat < 2 ^ 8) : (x.rotateRight 56).toNat = 256 * x.toNat := by
  rw [BitVec.toNat_rotateRight]
  simp only [Nat.reduceMod, Nat.reduceSub, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.div_eq_of_lt (by omega), Nat.zero_or, Nat.mod_eq_of_lt (by omega)]
  omega

theorem toNat_byte (b : Byte) : (b.setWidth 64).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

/-- The remainder of the top byte of a 57-byte input. -/
theorem init57_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 56) 1) :
    WP isa (.block init57) s fun t =>
      rem t = decodeLE (bytesAt s.mem (s.gpr .rsi + BitVec.ofNat 64 56) 1) ∧
      t.gpr .rbx = BitVec.ofNat 64 56 ∧ Keeps (.rbx :: W) s t := by
  apply WP.of_runBlock
  simp only [init57, zeroHigh, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, ea_at, load8_ok hr,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [rem, rv, W, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq, bytesAt,
      List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, decodeLE,
      BitVec.add_zero, toNat_byte]
    rfl
  · simp only [W, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]

theorem decode_two (m : Mem) (p : Addr) :
    decodeLE (bytesAt m p 2) = (m p).toNat + 256 * (m (p + 1)).toNat := by
  simp only [bytesAt, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, decodeLE, BitVec.add_zero, Nat.mul_zero, Nat.add_zero]
  rfl

/-- The remainder of the top two bytes of a 114-byte input. -/
theorem init114_ok (s : State)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 112) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 113) 1) :
    WP isa (.block init114) s fun t => rem t = decodeLE (bytesAt s.mem (s.gpr .rsi + BitVec.ofNat 64 112) 2) ∧
        t.gpr .rbx = BitVec.ofNat 64 112 ∧ Keeps (.rax :: .rbx :: W) s t := by
  apply WP.of_runBlock
  simp only [init114, zeroHigh, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execShift, execAlu,
    State.setReg32, ea_at, State.load8, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, h0,
    h1, show 1 ≤ 56 ∧ 56 ≤ 63 by decide, and_self,
    ite_true, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, ite_false,
    reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [decode_two, show s.gpr .rsi + BitVec.ofNat 64 112 + 1 = s.gpr .rsi + BitVec.ofNat 64 113 by
      rw [BitVec.add_assoc]; rfl]
    simp only [rem, rv, W, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, ite_false,
      reduceCtorEq]
    have b0 := (s.mem (s.gpr .rsi + BitVec.ofNat 64 112)).isLt
    have b1 := (s.mem (s.gpr .rsi + BitVec.ofNat 64 113)).isLt
    rw [BitVec.toNat_add, toNat_byte, rotr56 _ (by rw [toNat_byte]; exact b1), toNat_byte]
    simp only [BitVec.toNat_setWidth, Nat.mul_zero, Nat.add_zero]
    have z : (0 : BitVec 32).toNat = 0 := rfl
    omega
  · simp only [W, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2, ite_false]

/-! ## The result -/

/-- Stores relative to a register `b`, as a list. -/
theorem storesR_ok (b : Reg) {q : Addr} {R : Region} :
    ∀ (s : State) (o : Nat) (rs : List Reg), s.gpr b = q → R ∈ s.wr →
      (∀ d, o ≤ d → d + 8 ≤ o + 8 * rs.length → R.Contains (off q d) 8) →
      o + 8 * rs.length < 2 ^ 64 →
      WP isa (.block (Proof.X448.X86_64.storesR b o rs)) s fun s' =>
        mv s'.mem q o rs.length = rv s rs ∧ Outside q o (8 * rs.length) s.mem s'.mem ∧
        Frame [R] s.mem s'.mem ∧ (∀ r, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | s, _, [], _, _, _, _ =>
    WP.block_nil ⟨rfl, Outside.refl _ _ _ _, Frame.refl _ _, fun _ => rfl, rfl, rfl⟩
  | s, o, r :: rs, hq, hR, hc, hn => by
    rw [Proof.X448.X86_64.storesR, WP.block_cons_iff]
    let s1 : State := { s with mem := s.mem.writeW (off q o) (s.gpr r) }
    have hw : InRegions s.wr (off q o) 8 := ⟨R, hR, hc o (Nat.le_refl _) (by simp; omega)⟩
    refine ⟨s1, by simp only [exec, ea_at, hq, State.store64, hw, ite_true]; rfl, ?_⟩
    refine WP.mono (storesR_ok b s1 (o + 8) rs hq hR (fun d h₁ h₂ => hc d (by omega)
      (by simp; omega)) (by simp at hn; omega)) fun s' ⟨hv, ho', hf, hg, hrd, hwr⟩ => ?_
    have o1 : Outside q o 8 s.mem s1.mem := writeW_outside _ _ _ (by simp at hn; omega)
    refine ⟨?_, (o1.mono (by omega) (by simp; omega)).trans (ho'.mono (by omega) (by simp; omega)),
      ?_, fun r' => hg r', hrd, hwr⟩
    · rw [List.length_cons, mv, hv, rv, ho'.word (by omega) (by simp at hn; omega)]
      simp only [s1, word_writeW_self]
      rw [Proof.X448.X86_64.rv_congr (s := s) (s' := s1) fun _ _ => rfl]
    · exact (Frame.refl _ _ |>.writeW (List.mem_singleton_self R) _
        (hc o (Nat.le_refl _) (by simp; omega))).trans hf

theorem finish_eq : finish = ([.mov .rax (.mem (sc OUT))] : List Instr) ++
    (Proof.X448.X86_64.storesR .rax 0 W ++ (([.mov32 .rcx (.imm 0), .store8 (at_ .rax 56) .rcx] :
      List Instr) ++ Impl.X448.X86_64.restore)) := by
  simp only [finish, List.append_assoc]; rfl

theorem loadOut_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block ([.mov .rax (.mem (sc OUT))] : List Instr)) s fun t =>
      t.gpr .rax = word s.mem base OUT ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    Proof.X448.X86_64.readSrc_sc hs (show OUT + 8 ≤ 8192 by decide), Option.map_some,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [RegUpd.gpr_setReg_of_ne _ _ hr]

theorem zeroByte_ok (s : State) {q : Addr} (hq : s.gpr .rax = q)
    (hw : InRegions s.wr (q + BitVec.ofNat 64 56) 1) :
    WP isa (.block ([.mov32 .rcx (.imm 0), .store8 (at_ .rax 56) .rcx] : List Instr)) s fun t =>
      t.mem = s.mem.writeW (q + BitVec.ofNat 64 56) (0 : Byte) ∧
      (∀ r, r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, ea_at,
    State.store8, RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, hq, hw, ite_true,
    ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, trivial⟩
  simp only [hr, ite_false]

theorem leBytes_57 {x : Nat} (hx : x < L) :
    Proof.X25519.leBytes 57 x = Proof.X25519.leBytes 56 x ++ [0] := by
  have h : x / 256 ^ 56 = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx (by decide +kernel))
  rw [show 57 = 56 + 1 from rfl, Proof.X25519.leBytes_add, h]
  rfl

/-- A word of the working space, after writes to a region disjoint from it. -/
theorem word_frame {base : Addr} {m m' : Mem} {R : Region} (hF : Frame [R] m m')
    (hd : R.Disjoint ⟨base, 8192⟩) {d : Nat} (hd8 : d + 8 ≤ 8192) :
    word m' base d = word m base d := by
  refine (Mem.readW_congr fun i hi => (hF _ fun r hr hc => ?_).symm).symm
  rw [List.mem_singleton.mp hr] at hc
  refine hd _ hc ?_
  rw [Offset.add_add]
  exact Offset.contains_base base (d := d + i) (n := 1) (by omega) (by omega)

theorem bytesAt_57 (m : Mem) (q : Addr) :
    bytesAt m q 57 = bytesAt m q 56 ++ [m (q + BitVec.ofNat 64 56)] := by
  rw [show 57 = 56 + 1 from rfl, bytesAt_eq, Proof.X25519.bytesAt_add]
  simp only [bytesAt, Spec.X25519.bytesAt, List.range_one, List.map_cons, List.map_nil,
    BitVec.add_zero]

/-- `finish`: the remainder (below `L`) to the 57 bytes at the output's
address `q`, saved at `OUT`, and the callee-saved registers restored. -/
theorem finish_ok {s : State} {base q : Addr} (hs : Scr s base) (hq : word s.mem base OUT = q)
    (hwo : (⟨q, 57⟩ : Region) ∈ s.wr) (hd : (⟨q, 57⟩ : Region).Disjoint ⟨base, 8192⟩)
    {g : Reg → BitVec 64} (hsv : Saved base g s.mem) (hlt : rem s < L) :
    WP isa (.block finish) s fun t =>
      bytesAt t.mem q 57 = Spec.Ed448.encodeLE 57 (rem s) ∧ (∀ rd ∈ saved, t.gpr rd.1 = g rd.1) ∧
      (∀ r, r ∉ [Reg.rax, .rcx, .rbx, .rbp, .r12, .r13, .r14, .r15] → t.gpr r = s.gpr r) ∧
      Frame [⟨q, 57⟩] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (loadOut_ok hs) fun a ⟨ra, ka⟩ => ?_
  rw [WP.block_append_iff]
  have hc8 : ∀ d, 0 ≤ d → d + 8 ≤ 0 + 8 * W.length → (⟨q, 57⟩ : Region).Contains (off q d) 8 :=
    fun d _ hd' => by
      rw [Proof.X448.X86_64.W_len] at hd'; exact Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (storesR_ok .rax (R := ⟨q, 57⟩) a 0 W (ra.trans hq) (ka.2.2.2 ▸ hwo) hc8
    (by decide)) fun b ⟨vb, ob, fb, gb, rdb, wrb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (zeroByte_ok b (q := q) ((gb _).trans (ra.trans hq))
    ⟨_, by rw [wrb, ka.2.2.2]; exact hwo, Offset.contains_base _ (by omega) (by omega)⟩)
    fun c ⟨mc, gc, rdc, wrc⟩ => ?_
  have fc : Frame [⟨q, 57⟩] s.mem c.mem := by
    rw [mc, ← ka.2.1]
    exact fb.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  have hsc : Scr c base :=
    ⟨by rw [gc _ (by decide), gb, ka.1 _ (by decide)]; exact hs.rdi,
      by rw [wrc, wrb, ka.2.2.2]; exact hs.wr, hs.nowrap⟩
  have svc : Saved base g c.mem := fun rd hrd => by
    have := saved_lt rd hrd
    rw [← hsv rd hrd]
    exact word_frame fc hd (by omega)
  refine WP.mono (Proof.X448.X86_64.restore_ok hsc svc) fun t ⟨rt, gt, mt, rdt, wrt⟩ => ?_
  refine ⟨?_, rt, fun r hr => ?_, by rw [mt]; exact fc, by rw [rdt, rdc, rdb, ka.2.2.1], by rw [wrt, wrc, wrb, ka.2.2.2]⟩
  swap
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gt r (by simp [hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2]), gc r hr.2.1, gb, ka.1 r (by simp [hr.1])]
  rw [mt, bytesAt_57, mc, encodeLE_eq, leBytes_57 hlt]
  congr 1
  · have e : bytesAt (b.mem.writeW (q + BitVec.ofNat 64 56) (0 : Byte)) q 56 = bytesAt b.mem q 56 := by
      simp only [bytesAt]
      refine List.map_congr_left fun i hi => ?_
      simp only [List.mem_range] at hi
      simp only [Mem.writeW]
      apply Mem.write_apply
      rw [Offset.lt_iff _ q (by omega), Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
      omega
    rw [e]
    change Spec.X448.bytesAt b.mem q 56 = _
    rw [Proof.X448.X86_64.bytesAt_mv]
    rw [Proof.X448.X86_64.W_len] at vb
    rw [vb, ka.rv_eq (by decide)]
  · simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero]
    rfl

end VG.Proof.Ed448.X86_64
