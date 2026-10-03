import VerifiedGarbage.Proof.Argon2.X86.HPrime.Next

/-!
# Argon2 H′ on x86 (32-bit): the state of the body

`Body s₀ s`: between H′'s setup and its restore, `ebx` points to `scratch`,
`esp` is as on entry, memory has changed only in the output, `scratch` and
the stack below `esp`, and the caller's registers and the length prefix are
kept in `scratch`. `Out s₀ s k`: the output pointer and the bytes left, after
`k` output bytes. `copy_ok`: copying digest bytes to the output.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (copy outOff leftOff saved)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_addi wp_movm wp_store contains_addr)
open VG.WriteBytes

theorem bytesAt_writeBytes (m : Mem) (p : Addr) (xs : List Byte) (hn : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p xs.length = xs := by
  apply List.ext_getElem (by simp only [bytesAt, List.length_map, List.length_range])
  intro i _ hi
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes,
    Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
    hi, ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem bytesAt_take (m : Mem) (p : Addr) (n k : Nat) (hn : n ≤ k) :
    (bytesAt m p k).take n = bytesAt m p n := by
  simp only [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left hn]

/-- The state of the body. -/
structure Body (s₀ s : State) : Prop where
  ebx : s.gpr .ebx = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [outR s₀, scrR s₀, stkR s₀] s₀.mem s.mem
  saved : ∀ p ∈ saved, s.mem.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1
  pfx : bytesAt s.mem (P s₀ + 832) 4 = Spec.Argon2.le32 (ol s₀)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem Body.ctx {s : State} (h : Body s₀ s) : Ctx (scr s₀) (esp₀ s₀) s :=
  ⟨h.ebx, h.esp, by have := hp.scr_fits; omega, hp.esp_lo, by have := hp.esp_hi; omega,
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp [h.wr, hp.wr], 0, by simp, by simp⟩),
    hp.stk_scr.sub_right (Region.sub_prefix (by decide))⟩

/-- A word of `scratch` from offset 832 on is kept by the hash macros. -/
theorem keeps_word {s t : State} (k : Keeps (scr s₀) (esp₀ s₀) s t) {d : Nat} (hd : 832 ≤ d)
    (hd' : d + 4 ≤ 16384) : t.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := by
  refine k.frame.readW (r := ⟨addr (scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  have e := scr_addr hp (d := d) (by omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [e]; exact Offset.disjoint_base _ hd (by omega)
  · rw [e]
    exact (hp.stk_scr.sub_right (Offset.sub_base _ (show d + 4 ≤ 16384 from hd'))).symm

theorem Body.keeps {s t : State} (h : Body s₀ s) (k : Keeps (scr s₀) (esp₀ s₀) s t) : Body s₀ t := by
  refine ⟨k.ebx.trans h.ebx, k.esp.trans h.esp, k.rd.trans h.rd, k.wr.trans h.wr,
    h.frame.trans (k.frame.sub fun r hr => ?_), fun q hq => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · have hb : 832 ≤ q.2 ∧ q.2 + 4 ≤ 16384 := by
      simp only [Impl.Argon2.X86.HPrime.saved, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> decide
    rw [keeps_word hp k hb.1 hb.2]; exact h.saved q hq
  · rw [← h.pfx]
    exact k.bytes (R := ⟨P s₀ + 832, 4⟩) (by simp) (Offset.disjoint_base _ (by decide) (by decide))
      (hp.stk_scr.sub_right (Offset.sub_base _ (by decide))).symm

end

/-! ## Copying digest bytes -/

/-- The output pointer after `k` output bytes. -/
def OutPtr (s₀ s : State) (k : Nat) : Prop :=
  s.mem.readW (addr (scr s₀) outOff) 32 = op s₀ + BitVec.ofNat 32 k

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem copy_ok {s : State} (h : Body s₀ s) {k n : Nat} (hk : OutPtr s₀ s k)
    (hn : s.gpr .esi = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) (hkn : k + n ≤ ol s₀) :
    WP isa copy s fun t => Body s₀ t ∧ OutPtr s₀ t (k + n) ∧
      bytesAt t.mem ((op s₀).setWidth 64 + BitVec.ofNat 64 k) n = bytesAt s.mem (P s₀ + 768) n ∧
      t.gpr .ebp = s.gpr .ebp ∧
      Frame [⟨(op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩, ⟨P s₀ + BitVec.ofNat 64 outOff, 4⟩]
        s.mem t.mem := by
  have hs := hp.scr_fits
  have ho := hp.out_fits
  unfold copy
  refine WP.seq (wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_movm
    (VG.Proof.Sha512.X86.ea_of (B := scr s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ebx])
      outOff)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]
        exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩)
    fun s₃ u₃ => WP.block_nil ?_)
  have mem₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have edx₃ : s₃.gpr .edx = scr s₀ + 768 := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, h.ebx]
  have edi₃ : s₃.gpr .edi = op s₀ + BitVec.ofNat 32 k := by
    rw [u₃.gpr, u₂.mem, u₁.mem]; exact hk
  have esi₃ : s₃.gpr .esi = BitVec.ofNat 32 n := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hn]
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
  have e768 : (scr s₀ + 768).setWidth 64 = P s₀ + 768 := setWidth_add (d := 768) (by omega)
  have b768 : (scr s₀ + 768).toNat = (scr s₀).toNat + 768 := by
    rw [BitVec.toNat_add, show (768 : BitVec 32).toNat = 768 from rfl]; omega
  have bk : (op s₀ + BitVec.ofNat 32 k).toNat = (op s₀).toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega)]; omega
  have eOut : addr (op s₀ + BitVec.ofNat 32 k) 0 = (op s₀).setWidth 64 + BitVec.ofNat 64 k := by
    rw [MdStream.X86.addr_add_ofNat (by omega), Nat.add_zero]
  refine WP.seq (Proof.Blake2.X86.Stream.copyLoop_ok (w := 0) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (k := n) hn₁ (by omega) (by rw [b768]; omega)
    (by simp only [Proof.Blake2.bufOff, Nat.reduceDiv, Nat.mul_zero, Nat.add_zero]; rw [bk]; omega)
    edx₃ edi₃ esi₃ (fun i hi => ?_) (fun i hi => ?_) ?_ fun t ht => ?_)
  · have : i < 64 := by omega
    rw [rd₃, wr₃, e768, show P s₀ + 768 + BitVec.ofNat 64 i = P s₀ + BitVec.ofNat 64 (768 + i) by
      rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl]
    refine ⟨scrR s₀, by simp [hp.wr], ?_⟩
    exact Offset.contains_base _ (d := 768 + i) (n := 1) (k := 16384) (by omega) (by omega)
  · rw [wr₃]
    simp only [Proof.Blake2.bufOff, Nat.reduceDiv, Nat.mul_zero, eOut]
    refine ⟨outR s₀, by simp [hp.wr], ?_⟩
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.contains_base _ (d := k + i) (n := 1) (k := ol s₀) (by omega) (by omega)
  · rw [e768]
    simp only [Proof.Blake2.bufOff, Nat.reduceDiv, Nat.mul_zero, eOut]
    exact (hp.out_scr.sub_left (Offset.sub_base _ (d := k) (n := n) (k := ol s₀) (by omega))).sub_right
      (Offset.sub_base (P s₀) (d := 768) (n := n) (k := 16384) (by omega)) |>.symm
  -- The store of the output pointer.
  have o : ∀ x, x ≠ .edx → x ≠ .edi → x ≠ .esi → x ≠ .eax → t.gpr x = s.gpr x := fun x a b c d => by
    rw [ht.other x a b c d, u₃.other _ b, u₂.other _ a, u₁.other _ a]
  have ebxT : t.gpr .ebx = scr s₀ := by rw [o _ (by decide) (by decide) (by decide) (by decide), h.ebx]
  have wrT : t.wr = s₀.wr := ht.wr.trans wr₃
  have dstE : addr (op s₀ + BitVec.ofNat 32 k) (Proof.Blake2.bufOff 0) =
      (op s₀).setWidth 64 + BitVec.ofNat 64 k := eOut
  have lenL : (bytesAt s.mem (P s₀ + 768) n).length = n := by simp [bytesAt]
  have memT : t.mem = writeBytes s.mem ((op s₀).setWidth 64 + BitVec.ofNat 64 k)
      (bytesAt s.mem (P s₀ + 768) n) := by
    rw [ht.mem, dstE, e768, mem₃, List.take_of_length_le (by rw [lenL])]
  refine wp_store (VG.Proof.Sha512.X86.ea_of ebxT outOff)
    (by rw [wrT]; exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩)
    fun t' u => WP.block_nil ?_
  have eslot : addr (scr s₀) outOff = P s₀ + BitVec.ofNat 64 outOff := scr_addr hp (by decide)
  have F : Frame [⟨(op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩, ⟨P s₀ + BitVec.ofNat 64 outOff, 4⟩]
      s.mem t'.mem := by
    rw [u.mem, memT, eslot]
    refine ((writeBytes_frame s.mem _ _ (R := ⟨(op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩)
      (by rw [lenL]; exact Region.contains_self _ _)).mono (by simp)).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
  have outSub : Region.Sub ⟨(op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩ (outR s₀) :=
    Offset.sub_base _ (by omega)
  have slotSub : Region.Sub ⟨P s₀ + BitVec.ofNat 64 outOff, 4⟩ (scrR s₀) :=
    Offset.sub_base _ (by decide)
  have keep : ∀ d, d + 4 ≤ 16384 → (d + 4 ≤ outOff ∨ outOff + 4 ≤ d) →
      t'.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := fun d hd hd' => by
    refine F.readW (r := ⟨addr (scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    rw [scr_addr hp (by omega)]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hp.out_scr.sub_left outSub).sub_right (Offset.sub_base _ hd)).symm
    · exact Offset.disjoint _ hd' (by omega) (by simp only [outOff]; omega)
  refine ⟨⟨by rw [u.gpr, ebxT], by rw [u.gpr, o _ (by decide) (by decide) (by decide) (by decide), h.esp],
      by rw [u.rd, ht.rd, rd₃], by rw [u.wr, wrT], ?_, fun q hq => ?_, ?_⟩, ?_, ?_,
    by rw [u.gpr, o _ (by decide) (by decide) (by decide) (by decide)], F⟩
  · exact h.frame.trans (F.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨outR s₀, by simp, outSub⟩
      · exact ⟨scrR s₀, by simp, slotSub⟩)
  · have hb : 832 ≤ q.2 ∧ q.2 + 4 ≤ outOff := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> decide
    rw [keep _ (by simp only [outOff] at hb; omega) (.inl hb.2)]; exact h.saved q hq
  · rw [← h.pfx]
    refine Proof.Blake2.bytesAt_congr fun i hi => F.bytes (R := ⟨P s₀ + 832, 4⟩) (fun r hr => ?_)
      (by simp) hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hp.out_scr.sub_left outSub).sub_right
        (Offset.sub_base (P s₀) (d := 832) (n := 4) (k := 16384) (by decide))).symm
    · exact Offset.disjoint (P s₀) (d := 832) (n := 4) (e := outOff) (k := 4) (by decide) (by decide)
        (by decide)
  · show _ = _
    rw [u.mem, Mem.readW_writeW_self32, ht.dstV, BitVec.add_assoc, BitVec.ofNat_add]
  · have wb : bytesAt t.mem ((op s₀).setWidth 64 + BitVec.ofNat 64 k) n = bytesAt s.mem (P s₀ + 768) n := by
      rw [memT]
      have := bytesAt_writeBytes s.mem ((op s₀).setWidth 64 + BitVec.ofNat 64 k)
        (bytesAt s.mem (P s₀ + 768) n) (by rw [lenL]; omega)
      rwa [lenL] at this
    rw [← wb, u.mem]
    refine Proof.Blake2.bytesAt_congr fun i hi =>
      ((Frame.refl [⟨addr (scr s₀) outOff, 4⟩] t.mem).writeW (List.mem_singleton_self _) _
        (Region.contains_self _ _)).bytes (R := ⟨(op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩) ?_ (by simp; omega) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    rw [eslot]
    exact (hp.out_scr.sub_left outSub).sub_right slotSub

end

end VG.Proof.Argon2.X86.HPrime
