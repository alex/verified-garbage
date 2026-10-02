import VerifiedGarbage.Proof.Ed25519.X86_64.BitByte
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowersLoop

/-! Expand all scalar bits, without X25519's clamping. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Keeps Outside ea_scalar)

structure BitsKeep (base : Addr) (o n : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.rax, .rdx, .rbx] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base o n s.mem t.mem

theorem BitsKeep.scratch {base : Addr} {o n : Nat} {s t : State}
    (h : BitsKeep base o n s t) (hs : Scratch s base) : Scratch t base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem BitsKeep.trans {base : Addr} {o n : Nat} {s t u : State}
    (h : BitsKeep base o n s t) (k : BitsKeep base o n t u) : BitsKeep base o n s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr, h.mem.trans k.mem⟩

theorem BitsKeep.mono {base : Addr} {o n o' n' : Nat} {s t : State}
    (h : BitsKeep base o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : BitsKeep base o' n' s t :=
  ⟨h.gpr, h.rd, h.wr, h.mem.mono ho hn⟩

theorem scalarByteBits_ok {s : State} {base k : Addr} (hs : Scratch s base)
    (i count : Nat) (hi : i < count) (hn : count ≤ 64)
    (hc : s.gpr .rbx = BitVec.ofNat 64 i) (hp : s.gpr .rsi = k)
    (hr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block (scalarByteBits count)) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (i + 1) ∧ t.zf = some (decide (i + 1 = count)) ∧
      BitsKeep base (768 + 8 * i) 8 s t ∧
      ∀ j < 8, t.mem (off base (768 + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (off k i)).toNat >>> j) &&& 1) := by
  rw [scalarByteBits, List.append_assoc, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.movzx8 .rax { base := .rsi, index := some .rbx }]) s
      (fun t => t.gpr .rax = (s.mem (off k i)).setWidth 64 ∧ Keeps [.rax] s t) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_scalar s hp hc,
      State.load8, hr, ite_true, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun a ⟨av, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (scalarBitPrefix_ok (hs.of_keeps ka (by decide)) i 8 (by omega) (by decide)
    ((ka.1 _ (by decide)).trans hc) _ av) fun b ⟨kb, bv⟩ => ?_
  refine WP.mono (powersNext_ok b i count hi hn
    ((kb.gpr _ (by decide)).trans ((ka.1 _ (by decide)).trans hc))) fun t ⟨tc, tz, kt⟩ => ?_
  refine ⟨tc, tz, ⟨fun r hr => ?_, kt.2.2.1.trans (kb.rd.trans ka.2.2.1),
    kt.2.2.2.trans (kb.wr.trans ka.2.2.2), ?_⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact (kt.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.2⟩)).trans
      ((kb.gpr r hr.2.1).trans (ka.1 r (by simpa using hr.1)))
  · rw [kt.2.1, ← ka.2.1]; exact kb.mem
  · rw [kt.2.1]; exact bv

structure BitsInv (s₀ : State) (base k : Addr) (count i : Nat) (s : State) : Prop where
  scratch : Scratch s base
  ptr : s.gpr .rsi = k
  counter : s.gpr .rbx = BitVec.ofNat 64 i
  keep : BitsKeep base 768 (8 * count) s₀ s
  bits : ∀ t < 8 * i, s.mem (off base (768 + t)) =
    BitVec.ofNat 8 (((s₀.mem (off k (t / 8))).toNat >>> (t % 8)) &&& 1)

theorem scalarBitsLoop_ok {s₀ : State} {base k : Addr} (count : Nat) (hn : count ≤ 64)
    (hr : ∀ q < count, InRegions (s₀.rd ++ s₀.wr) (off k q) 1)
    (hd : ∀ q < count, 8192 ≤ ofs base (off k q)) :
    ∀ i s, i < count → BitsInv s₀ base k count i s →
      WP isa (.loop (.block (scalarByteBits count)) .ne) s fun t => BitsInv s₀ base k count count t := by
  intro i s hi h
  refine WP.loop (M := isa) (body := .block (scalarByteBits count)) (c := .ne)
    (Q := fun t => BitsInv s₀ base k count count t)
    (fun n s => ∃ i, n = count - i ∧ i < count ∧ BitsInv s₀ base k count i s) ?_
    (count - i) s ⟨i, rfl, hi, h⟩
  rintro n s ⟨i, rfl, hi, h⟩
  refine WP.mono (scalarByteBits_ok h.scratch i count hi hn h.counter h.ptr
    (by rw [h.keep.rd, h.keep.wr]; exact hr i hi)) fun t ⟨tc, tz, tk, tb⟩ => ?_
  have hbyte : s.mem (off k i) = s₀.mem (off k i) := h.keep.mem _ (by have := hd i hi; omega)
  have inv : BitsInv s₀ base k count (i + 1) t := by
    refine ⟨tk.scratch h.scratch, (tk.gpr _ (by decide)).trans h.ptr, tc,
      h.keep.trans (tk.mono (by omega) (by omega)), fun j hj => ?_⟩
    by_cases hp : j < 8 * i
    · rw [tk.mem _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega), h.bits j hp]
    · have e := tb (j - 8 * i) (by omega)
      rw [show 8 * i + (j - 8 * i) = j by omega, hbyte] at e
      rw [e, show j / 8 = i by omega, show j % 8 = j - 8 * i by omega]
  by_cases he : i + 1 = count
  · exact Or.inl ⟨by simp only [eval, tz, he, decide_true, Option.map_some, Bool.not_true], he ▸ inv⟩
  · exact Or.inr ⟨by simp only [eval, tz, decide_eq_false he, Option.map_some, Bool.not_false],
      count - (i + 1), by omega, i + 1, rfl, by omega, inv⟩

theorem input_byte (m : Mem) (k : Addr) (count j : Nat) (hj : j < count) :
    (Spec.Ed25519.bytesAt m k count).getD j 0 = m (off k j) := by
  simp only [Spec.Ed25519.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hj, Option.map_some, Option.getD_some]

theorem expandScalarBits_ok {s : State} {base k : Addr} (hs : Scratch s base) (hp : s.gpr .rsi = k)
    (count : Nat) (hn0 : 0 < count) (hn : count ≤ 64)
    (hr : ∀ q < count, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < count, 8192 ≤ ofs base (off k q)) :
    WP isa (scalarBits count) s fun t => BitsKeep base 768 (8 * count) s t ∧
      ∀ j < 8 * count, t.mem (off base (768 + j)) =
        BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k count) / 2 ^ j) % 2) := by
  rw [scalarBits]
  refine WP.seq (WP.mono (powersInit_ok s) fun a ⟨ac, ka⟩ => ?_)
  have init : BitsInv s base k count 0 a := by
    refine ⟨hs.of_keeps ka (by decide), (ka.1 _ (by decide)).trans hp, ac,
      ⟨fun r hr => ka.1 r (fun hm => hr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))), ka.2.2.1, ka.2.2.2, ?_⟩, fun j hj => by omega⟩
    rw [ka.2.1]; exact Outside.refl _ _ _ _
  refine WP.mono (scalarBitsLoop_ok count hn hr hd 0 a hn0 init) fun t h => ?_
  refine ⟨h.keep, fun j hj => ?_⟩
  rw [h.bits j hj]
  have hb := Proof.X25519.leNum_bit (Spec.Ed25519.bytesAt s.mem k count) j
  rw [← decodeLE_eq, input_byte _ _ _ _ (by omega)] at hb
  simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at hb ⊢
  exact congrArg (BitVec.ofNat 8) hb.symm

end VG.Proof.Ed25519.X86_64
