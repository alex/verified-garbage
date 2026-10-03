import VerifiedGarbage.Proof.Argon2.X86.Derive.HCall

/-!
# Argon2 on x86 (32-bit): clearing the memory matrix

`clear_ok`: `clear` zeroes the `blocks · 1024` bytes of the memory matrix,
one word per iteration, and writes nothing else. Its loop counts the words
left in `ecx` (`blocks · 256`, by eight doublings), with `edi` the next
word's address.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd wp_movi wp_mov wp_add wp_addi wp_subi)
open VG.Spec.Blake2 (bytesAt)

/-- The memory matrix, as an address. -/
abbrev memB (s₀ : State) : Addr := (memP s₀).setWidth 64

/-- A byte after a zero word is stored at `a`. -/
theorem writeW_zero (m : Mem) (a x : Addr) :
    (m.writeW a (0 : BitVec 32)) x = if (x - a).toNat < 4 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

/-- `[x + d + k]`, at a 32-bit address that does not wrap. -/
theorem addr32 {x : BitVec 32} {d k : Nat} (h : x.toNat + d + k < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 d) k = x.setWidth 64 + BitVec.ofNat 64 (d + k) := by
  rw [addr_eq (by rw [add_nat (by omega)]; omega), HPrime.setWidth_add (by omega), BitVec.add_assoc,
    BitVec.ofNat_add_ofNat]

/-- A store to a region the body may write keeps the invariant. -/
theorem Inv.store {s₀ s t : State} (h : Inv s₀ s) {R : Region} (hR : R ∈ bodyW s₀) {a : Addr}
    {v : BitVec 32} (hc : R.Contains a 4) (u : Mupd s t (s.mem.writeW a v)) : Inv s₀ t :=
  h.step (by rw [u.gpr]) (by rw [u.gpr]) u.rd u.wr (by rw [u.mem]; exact (Frame.refl _ _).writeW hR v hc)

/-- `cmp d, [b + o]`, and the borrow. -/
theorem wp_cmpm {s : State} {is : List Instr} {Q : State → Prop} {d b : Reg} {B : BitVec 32} {o : Nat}
    (hb : s.gpr b = B) (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Wp.Fupd s s' → s'.cf = some (decide ((s.gpr d).toNat < (s.mem.readW (addr B o) 32).toNat)) →
      s'.zf = some (s.gpr d - s.mem.readW (addr B o) 32 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.mem ⟨b, o⟩) :: is)) s Q :=
  Wp.cons (s' := arithFlags s (s.gpr d - s.mem.readW (addr B o) 32)
      (decide ((s.gpr d).toNat < (s.mem.readW (addr B o) 32).toNat))
      (subOverflow (s.gpr d) (s.mem.readW (addr B o) 32) (s.gpr d - s.mem.readW (addr B o) 32)))
    (by simp only [exec, execAlu, Wp.readSrc_mem hb hin, Option.bind_some])
    (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl rfl)

/-- The loop's state after `j` words. -/
structure CI (s₀ s₁ : State) (j : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  edi : s.gpr .edi = memP s₀ + BitVec.ofNat 32 (4 * j)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (blocksN s₀ * 256 - j)
  eax : s.gpr .eax = 0
  zero : ∀ i < 4 * j, s.mem (memB s₀ + BitVec.ofNat 64 i) = 0
  frame : Frame [memR s₀] s₁.mem s.mem

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem blocks_pos : 1 ≤ blocksN s₀ := by
  rw [hp.blocks_eq, hp.laneLen_eq]
  have := Nat.mul_le_mul hp.lanes_pos (show 1 ≤ 4 * (prm s₀).segmentLen by have := hp.segLen_two; omega)
  omega

theorem clearLoop_ok {s₁ : State} (h : CI s₀ s₁ 0 s₁) :
    WP isa (.loop (.block Impl.Argon2.X86.Derive.clearWord) .ne) s₁ (CI s₀ s₁ (blocksN s₀ * 256)) := by
  have hm := hp.mem_fits
  have hb := hp.blocks_lt
  have b1 := blocks_pos hp
  refine WP.loop (M := isa) (fun n s => ∃ j, n = blocksN s₀ * 256 - j ∧ j < blocksN s₀ * 256 ∧ CI s₀ s₁ j s)
    ?_ (blocksN s₀ * 256) s₁ ⟨0, by omega, by omega, h⟩
  rintro n s ⟨j, rfl, hj, c⟩
  have ea : addr (s.gpr .edi) 0 = memB s₀ + BitVec.ofNat 64 (4 * j) := by
    rw [c.edi, addr32 (by omega), Nat.add_zero]
  have hc : (memR s₀).Contains (addr (s.gpr .edi) 0) 4 := by
    rw [ea]; exact Offset.contains_base _ (by omega) (by omega)
  simp only [Impl.Argon2.X86.Derive.clearWord]
  refine Wp.wp_stm rfl (by rw [c.inv.wr]; exact ⟨_, mem_mem hp, hc⟩) fun t₁ u₁ => ?_
  have i₁ := c.inv.store (R := memR s₀) (by simp) hc u₁
  refine wp_addi fun t₂ u₂ => wp_subi fun t u _ zf => WP.block_nil ?_
  have i₃ := (i₁.upd u₂ (by decide) (by decide)).upd u (by decide) (by decide)
  have e₁ : t.gpr .ecx = BitVec.ofNat 32 (blocksN s₀ * 256 - (j + 1)) := by
    rw [u.gpr, u₂.other _ (by decide), u₁.gpr, c.ecx, Wp.ofNat_pred (by omega)]; rfl
  have next : CI s₀ s₁ (j + 1) t := by
    refine ⟨i₃, ?_, e₁, ?_, fun i hi => ?_, ?_⟩
    · rw [u.other _ (by decide), u₂.gpr, u₁.gpr, c.edi, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl
    · rw [u.other _ (by decide), u₂.other _ (by decide), u₁.gpr, c.eax]
    · rw [u.mem, u₂.mem, u₁.mem, c.eax, ea, writeW_zero]
      by_cases hi' : i < 4 * j
      · split
        · rfl
        · exact c.zero i hi'
      · rw [show memB s₀ + BitVec.ofNat 64 i = memB s₀ + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 (i - 4 * j) by
          rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' (by omega)],
          Offset.add_sub_cancel_left]
        split
        · rfl
        · rename_i hn; rw [BitVec.toNat_ofNat] at hn; omega
    · rw [u.mem, u₂.mem, u₁.mem]
      exact c.frame.writeW (List.mem_singleton_self _) _ hc
  have z : t.zf = some (decide (blocksN s₀ * 256 - (j + 1) = 0)) := by
    rw [zf, u₂.other _ (by decide), u₁.gpr, c.ecx, Wp.ofNat_pred (by omega), Wp.ofNat_beq_zero (by omega)]
    rfl
  by_cases done : j + 1 = blocksN s₀ * 256
  · refine .inl ⟨?_, done ▸ next⟩
    simp only [eval, z, show blocksN s₀ * 256 - (j + 1) = 0 by omega, decide_true, Option.map_some,
      Bool.not_true]
  · refine .inr ⟨?_, blocksN s₀ * 256 - (j + 1), by omega, j + 1, rfl, by omega, next⟩
    simp only [eval, z, show blocksN s₀ * 256 - (j + 1) ≠ 0 by omega, decide_false, Option.map_some,
      Bool.not_false]

theorem clear_ok {s : State} (h : Inv s₀ s) :
    WP isa Impl.Argon2.X86.Derive.clear s fun t => Inv s₀ t ∧ Frame [memR s₀] s.mem t.mem ∧
      ∀ i < blocksN s₀ * 1024, t.mem (memB s₀ + BitVec.ofNat 64 i) = 0 := by
  have hb := hp.blocks_lt
  have eb : blocksN s₀ = (arg s₀ 14).toNat := rfl
  unfold Impl.Argon2.X86.Derive.clear Impl.Argon2.X86.Derive.clearSetup
  simp only [List.cons_append]
  refine WP.seq (wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ =>
    wp_ldarg hp (h.upd u₁ (by decide) (by decide)) (i := 14) (by decide) fun s₂ u₂ => ?_)
  have i₂ := (h.upd u₁ (by decide) (by decide)).upd u₂ (by decide) (by decide)
  refine dbl_ok 8 (by rw [u₂.gpr]; omega) fun s₃ e₃ k₃ => wp_movi fun s₄ u₄ => WP.block_nil ?_
  have i₄ := (i₂.keep k₃).upd u₄ (by decide) (by decide)
  refine (clearLoop_ok hp ⟨i₄, ?_, ?_, u₄.gpr, fun i hi => absurd hi (by omega), Frame.refl _ _⟩).mono
    fun t c => ⟨c.inv, ?_, fun i hi => c.zero i (by omega)⟩
  · rw [u₄.other _ (by decide), k₃.other _ (by decide) (by decide) (by decide), u₂.other _ (by decide), u₁.gpr]
    simp
  · rw [u₄.other _ (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [e₃, u₂.gpr, Wp.toNat_ofNat_lt (by omega)]
    omega
  · rw [show s.mem = s₄.mem by rw [u₄.mem, k₃.mem, u₂.mem, u₁.mem]]
    exact c.frame

end

end VG.Proof.Argon2.X86.Derive
