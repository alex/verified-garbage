import VerifiedGarbage.Proof.Ed25519.X86_64.CombSelect

/-!
# The comb's digits

Untrusted. Step `c` reads digit `2c + 1` (`c < 32`) or `2(c - 32)` of the
scalar from its bits, expanded one per byte at byte 768 of the scratch
(`combIdx`), by Horner's rule.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

/-- The digit step `c` reads. -/
def combIdx (c : Nat) : Nat := if c < 32 then 2 * c + 1 else 2 * (c - 32)

theorem combIdx_lt {c : Nat} (hc : c < 64) : combIdx c < 64 := by
  unfold combIdx; split <;> omega

theorem combIndex_ok (s : State) {c : Nat} (hc : c < 64) (hb : s.gpr .rbx = BitVec.ofNat 64 c) :
    WP isa combIndex s fun t => t.gpr .rcx = BitVec.ofNat 64 (4 * combIdx c) ∧ Keeps [.rcx] s t := by
  rw [combIndex]
  have h8 : BitVec.ofNat 64 c + BitVec.ofNat 64 c + (BitVec.ofNat 64 c + BitVec.ofNat 64 c) +
      (BitVec.ofNat 64 c + BitVec.ofNat 64 c + (BitVec.ofNat 64 c + BitVec.ofNat 64 c)) =
      BitVec.ofNat 64 (8 * c) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hcf : decide ((BitVec.ofNat 64 c).toNat < ((32 : BitVec 32).signExtend 64).toNat) =
      decide (c < 32) := by
    rw [show (32 : BitVec 32).signExtend 64 = BitVec.ofNat 64 32 from rfl, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    congr 1; apply propext; omega
  refine WP.seq (WP.mono (show WP isa (.block [.mov .rcx (.reg .rbx), .alu .add .rcx (.reg .rcx),
      .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .cmp .rbx (.imm 32)]) s
      (fun t => t.gpr .rcx = BitVec.ofNat 64 (8 * c) ∧ t.cf = some (decide (c < 32)) ∧
        Keeps [.rcx] s t) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, hb, h8, hcf, ite_true,
      ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun a ⟨ac, af, ka⟩ => ?_)
  refine WP.ite (decide (c < 32)) (by simp only [eval, af]) (fun h => ?_) (fun h => ?_)
  · have hc32 : c < 32 := of_decide_eq_true h
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ac, ite_true, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r hr => ?_, ka.2.1, ka.2.2.1, ka.2.2.2⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [combIdx, hc32, ↓reduceIte, BitVec.toNat_add, BitVec.toNat_ofNat,
        show (4 : BitVec 32).signExtend 64 = BitVec.ofNat 64 4 from rfl]
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]; exact ka.1 r (by simpa using hr)
  · have hc32 : ¬ c < 32 := of_decide_eq_false h
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ac, ite_true, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r hr => ?_, ka.2.1, ka.2.2.1, ka.2.2.2⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [combIdx, hc32, ↓reduceIte, BitVec.toNat_sub, BitVec.toNat_ofNat,
        show (256 : BitVec 32).signExtend 64 = BitVec.ofNat 64 256 from rfl]
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]; exact ka.1 r (by simpa using hr)

theorem digit_bits (S i : Nat) :
    (S / 16 ^ i) % 16 = ((((S / 2 ^ (4 * i + 3)) % 2 * 2 + (S / 2 ^ (4 * i + 2)) % 2) * 2 +
      (S / 2 ^ (4 * i + 1)) % 2) * 2 + (S / 2 ^ (4 * i)) % 2) := by
  have h16 : 16 ^ i = 2 ^ (4 * i) := by rw [pow_mul]; norm_num
  have e : ∀ t, S / 2 ^ (4 * i + t) = S / 16 ^ i / 2 ^ t := fun t => by
    rw [h16, Nat.div_div_eq_div_mul, ← pow_add]
  rw [e 3, e 2, e 1, ← Nat.add_zero (4 * i), e 0]
  simp only [pow_zero, Nat.div_one, Nat.reducePow]
  omega

theorem combBit_ea {s : State} {base : Addr} (hs : Scratch s base) {i : Nat}
    (hrcx : s.gpr .rcx = BitVec.ofNat 64 (4 * i)) (t : Nat) :
    s.ea { base := .rdi, index := some .rcx, disp := 768 + (t : Int) } =
      off base (768 + (4 * i + t)) := by
  simp only [State.ea, hs.rdi, hrcx, BitVec.mul_one]
  rw [show (768 : Int) + (t : Int) = ((768 + t : Nat) : Int) by omega, BitVec.ofInt_natCast,
    BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (off base) (by omega)

theorem loadBit_ok {s : State} {base : Addr} (hs : Scratch s base) {S i : Nat} (hi : i < 64)
    (hrcx : s.gpr .rcx = BitVec.ofNat 64 (4 * i))
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (dst : Reg) (t : Nat) (ht : t < 4) :
    WP isa (.block [combBit dst t]) s fun u =>
      u.gpr dst = BitVec.ofNat 64 ((S / 2 ^ (4 * i + t)) % 2) ∧ Keeps [dst] s u := by
  have hr : InRegions (s.rd ++ s.wr) (off base (768 + (4 * i + t))) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have bit : (s.mem (off base (768 + (4 * i + t)))).setWidth 64 =
      BitVec.ofNat 64 ((S / 2 ^ (4 * i + t)) % 2) := by
    rw [hb _ (by omega)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  apply WP.of_runBlock
  simp only [combBit, runBlock_cons, runStep_some, runBlock_nil, exec, State.load8,
    combBit_ea hs hrcx, hr, bit, ite_true, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem addRax_ok (s : State) (r : Reg) :
    WP isa (.block [.alu .add .rax (.reg r)]) s fun u =>
      u.gpr .rax = s.gpr .rax + s.gpr r ∧ Keeps [.rax] s u := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq, ite_false]

theorem combDigit_ok {s : State} {base : Addr} (hs : Scratch s base) {S i : Nat} (hi : i < 64)
    (hrcx : s.gpr .rcx = BitVec.ofNat 64 (4 * i))
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa (.block combDigit) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 ((S / 16 ^ i) % 16) ∧ Keeps [.rax, .rdx] s t := by
  rw [show combDigit = [combBit .rax 3] ++ ([.alu .add .rax (.reg .rax)] ++ ([combBit .rdx 2] ++
      ([.alu .add .rax (.reg .rdx)] ++ ([.alu .add .rax (.reg .rax)] ++ ([combBit .rdx 1] ++
      ([.alu .add .rax (.reg .rdx)] ++ ([.alu .add .rax (.reg .rax)] ++ ([combBit .rdx 0] ++
      [.alu .add .rax (.reg .rdx)])))))))) from rfl]
  have keep : ∀ {x y : State} {rs : List Reg}, Keeps rs x y → (∀ r ∈ rs, r = .rax ∨ r = .rdx) →
      Keeps [.rax, .rdx] x y := fun k h => ⟨fun r hr => k.1 r (fun hm => by
        rcases h r hm with rfl | rfl <;> simp at hr), k.2⟩
  have tr : ∀ {x y z : State}, Keeps [.rax, .rdx] x y → Keeps [.rax, .rdx] y z →
      Keeps [.rax, .rdx] x z := fun a b => ⟨fun r hr => (b.1 r hr).trans (a.1 r hr),
        b.2.1.trans a.2.1, b.2.2.1.trans a.2.2.1, b.2.2.2.trans a.2.2.2⟩
  have st : ∀ {x : State}, Keeps [.rax, .rdx] s x → Scratch x base ∧
      x.gpr .rcx = BitVec.ofNat 64 (4 * i) ∧
      ∀ q < 256, x.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2) := fun k =>
    ⟨⟨(k.1 _ (by decide)).trans hs.rdi, k.2.2.2 ▸ hs.wr, hs.nowrap⟩,
      (k.1 _ (by decide)).trans hrcx, fun q hq => by rw [k.2.1]; exact hb q hq⟩
  rw [WP.block_append_iff]
  refine WP.mono (loadBit_ok hs hi hrcx hb .rax 3 (by decide)) fun a ⟨a3, ka⟩ => ?_
  have ka' := keep ka (by simp)
  rw [WP.block_append_iff]
  refine WP.mono (addRax_ok a .rax) fun b ⟨bv, kb⟩ => ?_
  have kb' := tr ka' (keep kb (by simp))
  obtain ⟨hsb, hcb, hbb⟩ := st kb'
  rw [WP.block_append_iff]
  refine WP.mono (loadBit_ok hsb hi hcb hbb .rdx 2 (by decide)) fun c ⟨c2, kc⟩ => ?_
  have kc' := tr kb' (keep kc (by simp))
  rw [WP.block_append_iff]
  refine WP.mono (addRax_ok c .rdx) fun d ⟨dv, kd⟩ => ?_
  have kd' := tr kc' (keep kd (by simp))
  rw [WP.block_append_iff]
  refine WP.mono (addRax_ok d .rax) fun e ⟨ev, ke⟩ => ?_
  have ke' := tr kd' (keep ke (by simp))
  obtain ⟨hse, hce, hbe⟩ := st ke'
  rw [WP.block_append_iff]
  refine WP.mono (loadBit_ok hse hi hce hbe .rdx 1 (by decide)) fun f ⟨f1, kf⟩ => ?_
  have kf' := tr ke' (keep kf (by simp))
  rw [WP.block_append_iff]
  refine WP.mono (addRax_ok f .rdx) fun g ⟨gv, kg⟩ => ?_
  have kg' := tr kf' (keep kg (by simp))
  rw [WP.block_append_iff]
  refine WP.mono (addRax_ok g .rax) fun h ⟨hv, kh⟩ => ?_
  have kh' := tr kg' (keep kh (by simp))
  obtain ⟨hsh, hch, hbh⟩ := st kh'
  rw [WP.block_append_iff]
  refine WP.mono (loadBit_ok hsh hi hch hbh .rdx 0 (by decide)) fun u ⟨u0, ku⟩ => ?_
  have ku' := tr kh' (keep ku (by simp))
  refine WP.mono (addRax_ok u .rdx) fun t ⟨tv, kt⟩ => ⟨?_, tr ku' (keep kt (by simp))⟩
  rw [tv, u0, ku.1 _ (by decide), hv, gv, f1, kf.1 _ (by decide), ev, dv, c2, kc.1 _ (by decide), bv,
    a3, digit_bits S i, Nat.add_zero]
  have l0 := Nat.mod_lt (S / 2 ^ (4 * i)) (show 2 > 0 by decide)
  have l1 := Nat.mod_lt (S / 2 ^ (4 * i + 1)) (show 2 > 0 by decide)
  have l2 := Nat.mod_lt (S / 2 ^ (4 * i + 2)) (show 2 > 0 by decide)
  have l3 := Nat.mod_lt (S / 2 ^ (4 * i + 3)) (show 2 > 0 by decide)
  generalize S / 2 ^ (4 * i) % 2 = b0 at *
  generalize S / 2 ^ (4 * i + 1) % 2 = b1 at *
  generalize S / 2 ^ (4 * i + 2) % 2 = b2 at *
  generalize S / 2 ^ (4 * i + 3) % 2 = b3 at *
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end VG.Proof.Ed25519.X86_64
