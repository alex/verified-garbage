import VerifiedGarbage.Proof.AesGcm.X86.Absorb
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Cmac.Block32

/-!
# AES-GCM on x86: padding the buffer (`flush`) and the lengths block (`lens`)

Untrusted: everything here is checked by Lean. `flush yo` pads the `bO`
buffered bytes with zeros in `T` and absorbs them (`flush_pc`); `lens yo`
stores the lengths block of the 64-bit lengths kept in `W` in `T` and
absorbs it (`lens_pc`). Both are correct and constant time.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ghash blocks zeros padLen)
open VG.Proof.Gcm (Absorbed lensBlock)

/-- The regions `flush` and `lens` write. -/
abbrev tFrame (St W SP : BitVec 32) (K yo : Nat) : List Region :=
  [⟨w64 St + BitVec.ofNat 64 yo, 16⟩, ⟨w64 W + BitVec.ofNat 64 96, 16⟩, wsR W, below SP K]

theorem gh_tFrame {St W SP : BitVec 32} {K yo : Nat} {m m' : Mem}
    (h : Frame [⟨w64 St + BitVec.ofNat 64 yo, 16⟩, ⟨w64 W + BitVec.ofNat 64 512, 256⟩, below SP K] m m') :
    Frame (tFrame St W SP K yo) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨wsR W, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP K, by simp, fun _ h => h⟩

theorem t_tFrame {St W SP : BitVec 32} {K yo : Nat} {m m' : Mem}
    (h : Frame [⟨w64 W + BitVec.ofNat 64 96, 16⟩] m m') : Frame (tFrame St W SP K yo) m m' :=
  h.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp

/-- The bytes at `p` after writing `xs` there: `xs`, then what was there. -/
theorem bytesAt_writeBytes_prefix (m : Mem) (p : Addr) (xs : List Byte) {n : Nat} (hn : xs.length ≤ n)
    (h : n < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p n = xs ++ bytesAt m (p + BitVec.ofNat 64 xs.length) (n - xs.length) := by
  rw [show n = xs.length + (n - xs.length) by omega, bytesAt_add, bytesAt_writeBytes_self _ _ _ (by omega),
    Nat.add_sub_cancel_left]
  congr 1
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [writeBytes, BitVec.add_assoc, Offset.add_sub_cancel_left, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := xs.length) (by omega), Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  simp [show ¬xs.length + i < xs.length by omega]

theorem zeros_eq (n : Nat) : Spec.Cmac.zeros n = zeros n := rfl

theorem zero4_bytes' (m : Mem) (p : Addr) : bytesAt (Cmac.zero4 m p) p 16 = zeros 16 := Cmac.zero4_bytes m p

theorem store4_eq (m : Mem) (W : BitVec 32) (o : Nat) (a b c d : BitVec 32) :
    (((m.writeW (w64 W + BitVec.ofNat 64 o) a).writeW (w64 W + BitVec.ofNat 64 (o + 4)) b).writeW
      (w64 W + BitVec.ofNat 64 (o + 8)) c).writeW (w64 W + BitVec.ofNat 64 (o + 12)) d =
      Cmac.store4 m (w64 W + BitVec.ofNat 64 o) a b c d := by
  simp only [Cmac.store4, add_ofNat_assoc]

/-! ## `flush` -/

/-- After `flush yo`: GHASH has absorbed the padding too, from `m₀`. -/
structure FlOut (Ctx St W SP : BitVec 32) (K yo b : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  abs : ∀ x : List Byte, x.length % 16 = b →
    Absorbed m₀ (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) (Hk m₀ Ctx) x →
    Absorbed s.mem (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) (Hk m₀ Ctx)
      (x ++ zeros (padLen x.length))
  frame : Frame (tFrame St W SP K yo) m₀ s.mem

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay Ctx St W SP K) {yo : Nat}
include L

theorem ctx_tFrame (hyo : yo = 0 ∨ yo = 16) :
    ∀ r ∈ tFrame St W SP K yo, (⟨w64 Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega)
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

theorem slot_tFrame (hyo : yo = 0 ∨ yo = 16) {o : Nat} (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 240) :
    ∀ r ∈ tFrame St W SP K yo, (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by omega) (.inr ⟨by omega, by omega⟩)).symm
  · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w (by omega)).symm

theorem env_tFrame (hyo : yo = 0 ∨ yo = 16) {s s' : State} (he : Env Ctx St W SP s)
    (hf : Frame (tFrame St W SP K yo) s.mem s'.mem)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Env Ctx St W SP s' :=
  he.keep hbp hsi hsp hrd hwr (slot_frame hf (slot_tFrame L hyo (by decide) (by decide)))

/-- `T` zeroed, and the pointers of the copy into it. -/
theorem zeroT_ok {s : State} (he : Env Ctx St W SP s) :
    ∃ s', runBlock isa (zero4 tO ++ ([.mov .edi (.reg .esi), .alu .add .edi (imm 32), .mov .edx (.reg .ebp),
        .alu .add .edx (imm tO)] : List Instr)) s = some s' ∧
      s'.mem = Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 96) ∧ s'.gpr .edi = St + BitVec.ofNat 32 32 ∧
      s'.gpr .edx = W + BitVec.ofNat 32 96 ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by xrun [zero4, he.ebp, he.esi, L.aW, he.wIn], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mems []; simp only [Proof.Cmac.zero4, Proof.Cmac.store4, add_ofNat_assoc]; rfl
  · regs [he.esi]
  · regs [he.ebp]
  · intro r h₁ h₂ h₃
    simp only [gpr_setMem, gpr_arithFlags, gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂,
      gpr_setReg_of_ne _ _ h₃]
  all_goals rfl

theorem flush_pc (hyo : yo = 0 ∨ yo = 16) {b : Nat} (hb : b < 16) :
    Pc (fun (m₀ : Mem) s => (Env Ctx St W SP s ∧ slotv s.mem W bO = BitVec.ofNat 32 b) ∧ s.mem = m₀) (flush vg.callees yo)
      (FlOut Ctx St W SP K yo b ·) := by
  refine Pc.seq (Q := fun m₀ s => ((Env Ctx St W SP s ∧ slotv s.mem W bO = BitVec.ofNat 32 b) ∧ s.mem = m₀) ∧
      s.zf = some (decide (b = 0)) ∧ s.gpr .ecx = BitVec.ofNat 32 b)
    (Pc.taint [.ebp] (fun m₀ s ⟨⟨he, hb'⟩, hm⟩ => WP.mono (test_ok L he .ecx bO (by decide) hb' (by omega))
        fun s' ⟨zf, cx, g, m, rd, wr⟩ => ⟨⟨⟨he.keep (g _ (by decide)) (g _ (by decide)) (g _ (by decide)) rd wr
          (by rw [m]), by rw [m]; exact hb'⟩, by rw [m, hm]⟩, zf, cx⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.ebp, h₂.1.1.ebp]) (by taint_decide)) ?_
  refine Pc.ite (decide (b = 0)) (fun _ _ h => h.2.1) (fun ht => ?_) (fun hf => ?_)
  · have h0 : b = 0 := by simpa using ht
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨⟨⟨he, _⟩, hm⟩, _⟩ => ⟨he, fun x hx ha => ?_, by rw [hm]; exact Frame.refl _ _⟩
    rw [Proof.Gcm.padLen_of_mod (by omega), hm]; simpa [zeros] using ha
  · have h0 : b ≠ 0 := by simpa using hf
    -- `T` zeroed.
    refine Pc.seq (Q := fun m₀ s => Env Ctx St W SP s ∧ s.mem = Cmac.zero4 m₀ (w64 W + BitVec.ofNat 64 96) ∧
        s.gpr .edi = St + BitVec.ofNat 32 32 ∧ s.gpr .edx = W + BitVec.ofNat 32 96 ∧
        s.gpr .ecx = BitVec.ofNat 32 b)
      (Pc.taint [.ebp, .esi] (fun m₀ s ⟨⟨⟨he, _⟩, hm⟩, _, cx⟩ => ?_)
        (fun _ _ s₁ s₂ h₁ h₂ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h₁.1.1.1.ebp, h₂.1.1.1.ebp]
          · rw [h₁.1.1.1.esi, h₂.1.1.1.esi]) (by taint_decide)) ?_
    · obtain ⟨s', run, m, di, dx, g, rd, wr⟩ := zeroT_ok L he
      have fz : Frame [⟨w64 W + BitVec.ofNat 64 96, 16⟩] s.mem s'.mem := by rw [m]; exact Cmac.frame_store4 _ _ _ _ _
      refine WP.of_runBlock ⟨s', run, env_tFrame L hyo he (t_tFrame fz) (g _ (by decide) (by decide) (by decide))
        (g _ (by decide) (by decide) (by decide)) (g _ (by decide) (by decide) (by decide)) rd wr, by rw [m, hm], di, dx,
        by rw [g _ (by decide) (by decide) (by decide), cx]⟩
    -- The copy.
    refine Pc.seq (Q := fun m₀ s => Env Ctx St W SP s ∧
        s.mem = writeBytes (Cmac.zero4 m₀ (w64 W + BitVec.ofNat 64 96)) (w64 W + BitVec.ofNat 64 96)
          (bytesAt m₀ (w64 St + BitVec.ofNat 64 32) b))
      (Pc.taint [.edi, .edx, .ecx] (fun m₀ s ⟨he, hm, di, dx, cx⟩ => ?_)
        (fun _ _ s₁ s₂ h₁ h₂ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · rw [h₁.2.2.1, h₂.2.2.1]
          · rw [h₁.2.2.2.1, h₂.2.2.2.1]
          · rw [h₁.2.2.2.2, h₂.2.2.2.2]) (by taint_decide)) ?_
    · have eS := L.aS (o := 32) (by decide)
      have eT := L.aW (o := 96) (by decide)
      have lp : LoopPre s (St + BitVec.ofNat 32 32) (W + BitVec.ofNat 32 96) b := by
        refine ⟨di, dx, cx, by omega, by omega, by rw [L.nS (by decide)]; have := L.fs; omega,
          by rw [L.nW (by decide)]; have := L.fw; omega, by rw [eS]; exact covers_left (he.stC (by omega)),
          by rw [eT]; exact he.wC (by omega), by rw [eS, eT]; exact L.st_w (a := 32) (n := b) (d := 96) (k := b) (by omega) (.inr ⟨by decide, by omega⟩)⟩
      refine WP.mono (copyLoop_ok s lp) fun s' c => ?_
      have cm := c.mem
      rw [eS, eT] at cm
      have hS : bytesAt s.mem (w64 St + BitVec.ofNat 64 32) b = bytesAt m₀ (w64 St + BitVec.ofNat 64 32) b := by
        rw [hm]; exact bytesAt_frame (Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩))
          (by omega)
      have hlen := length_bytesAt s.mem (w64 St + BitVec.ofNat 64 32) b
      have fw : Frame [⟨w64 W + BitVec.ofNat 64 96, b⟩] s.mem s'.mem := by
        rw [cm]; exact writeBytes_frame' _ hlen
      refine ⟨env_tFrame L hyo he (t_tFrame (fw.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩))
        (c.other _ (by decide) (by decide) (by decide) (by decide)) (c.other _ (by decide) (by decide) (by decide)
        (by decide)) (c.other _ (by decide) (by decide) (by decide) (by decide)) c.rd c.wr, ?_⟩
      rw [cm, hS, hm]
    -- The block absorbed.
    have hP : ∀ s, Env Ctx St W SP s → s.gpr .ebp + BitVec.ofNat 32 96 = W + BitVec.ofNat 32 96 ∧
        (W + BitVec.ofNat 32 96).toNat + 16 ≤ 2 ^ 32 ∧ Covers [⟨w64 (W + BitVec.ofNat 32 96), 16⟩] (s.rd ++ s.wr) ∧
        (⟨w64 St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨w64 (W + BitVec.ofNat 32 96), 16⟩ ∧
        (⟨w64 (W + BitVec.ofNat 32 96), 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, 256⟩ ∧
        (below SP K).Disjoint ⟨w64 (W + BitVec.ofNat 32 96), 16⟩ := fun s he => by
      rw [L.aW (by decide)]
      exact ⟨by rw [he.ebp], by rw [L.nW (by decide)]; have := L.fw; omega, covers_left (he.wC (by decide)),
        L.st_w (by omega) (.inr ⟨by decide, by decide⟩), Lay.w_w (.inl (by decide)) (by decide) (by decide),
        L.stk_w (by decide)⟩
    refine Pc.mono (Pc.of (I := Env Ctx St W SP) (fun s he => ghash1_ok L hyo he .ebp 96 (.inr rfl)
        (hP s he).1 (hP s he).2.1 (hP s he).2.2.1 (hP s he).2.2.2.1 (hP s he).2.2.2.2.1 (hP s he).2.2.2.2.2)
      (ghash1_ct L hyo .ebp 96 (.inr ⟨rfl, rfl⟩) fun s he => ⟨he, hP s he⟩) _ fun _ _ h => h.1)
      (fun _ _ h => h) fun m₀ s₂ ⟨s₁, ⟨_, hm⟩, g⟩ => ?_
    have go := g.out
    rw [L.aW (by decide)] at go
    have fT : Frame [⟨w64 W + BitVec.ofNat 64 96, 16⟩] m₀ s₁.mem := by
      rw [hm]
      exact (Cmac.frame_store4 _ _ _ _ _).trans (writeBytes_frame _ _ _ (by
        rw [length_bytesAt]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega))
    have hT : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 96) 16 =
        bytesAt m₀ (w64 St + BitVec.ofNat 64 32) b ++ zeros (16 - b) := by
      rw [hm, bytesAt_writeBytes_prefix _ _ _ (by rw [length_bytesAt]; omega) (by decide), length_bytesAt]
      congr 1
      have z := zero4_bytes' m₀ (w64 W + BitVec.ofNat 64 96)
      rw [show (16 : Nat) = b + (16 - b) by omega, bytesAt_add] at z
      have := congrArg (List.drop b) z
      rwa [List.drop_left' (length_bytesAt _ _ _), show b + (16 - b) = 16 by omega, zeros, List.drop_replicate,
        show 16 - b = 16 - b from rfl] at this
    have hY : blockAt s₁.mem (w64 St + BitVec.ofNat 64 yo) = blockAt m₀ (w64 St + BitVec.ofNat 64 yo) :=
      blockAt_frame fT fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    have hH : blockAt s₁.mem (w64 Ctx + BitVec.ofNat 64 240) = Hk m₀ Ctx :=
      blockAt_frame fT fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
    refine ⟨g.env, fun x hx ha => ?_, (t_tFrame fT).trans (gh_tFrame g.frame)⟩
    refine Proof.Gcm.absorb_pad ha (by omega) (B := bytesAt s₁.mem (w64 W + BitVec.ofNat 64 96) 16) ?_ ?_
    · rw [hT, hx]
    · rw [go, hY, hH]; rfl

end

/-! ## The lengths block -/

section
open VG.Spec.Gcm (be64)

theorem ext32 (w : BitVec 32) (k : Nat) : w.extractLsb' (8 * k) 8 = BitVec.ofNat 8 (w.toNat / 256 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem bswap_eq : VG.X86.bswap = byteRev32 := rfl

theorem le4_bswap (w : BitVec 32) : Proof.Cmac.le4 (VG.X86.bswap w) =
    [w.extractLsb' 24 8, w.extractLsb' 16 8, w.extractLsb' 8 8, w.extractLsb' 0 8] := by
  rw [bswap_eq, Proof.Cmac.le4, byteRev32_extract]

/-- Two byte-reversed words, stored: the big-endian bytes of the 64-bit value. -/
theorem le4_be (u v : BitVec 32) :
    Proof.Cmac.le4 (VG.X86.bswap u) ++ Proof.Cmac.le4 (VG.X86.bswap v) = be64 (u.toNat * 2 ^ 32 + v.toNat) := by
  have hu := u.isLt
  have hv := v.isLt
  rw [le4_bswap, le4_bswap]
  simp only [be64, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append,
    List.cons.injEq, and_true]
  rw [show (24 : Nat) = 8 * 3 from rfl, show (16 : Nat) = 8 * 2 from rfl, show (8 : Nat) = 8 * 1 from rfl,
    show (0 : Nat) = 8 * 0 from rfl, ext32, ext32, ext32, ext32, ext32, ext32, ext32, ext32]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat] <;>
    omega

theorem dbl3 (x : BitVec 32) : (x + x + (x + x) + (x + x + (x + x))).toNat = 8 * x.toNat % 2 ^ 32 := by
  simp only [BitVec.toNat_add]; omega

/-- The two words `be64w` computes: `8 x` modulo 2⁶⁴. -/
theorem be64w_val (hi lo : BitVec 32) :
    (hi + hi + (hi + hi) + (hi + hi + (hi + hi)) + lo >>> 29).toNat * 2 ^ 32 +
      (lo + lo + (lo + lo) + (lo + lo + (lo + lo))).toNat = 8 * (hi.toNat * 2 ^ 32 + lo.toNat) % 2 ^ 64 := by
  have hl := lo.isLt
  rw [BitVec.toNat_add, dbl3, dbl3, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-- The 64-bit value of the words `lo`, `hi`. -/
abbrev val64 (lo hi : BitVec 32) : Nat := hi.toNat * 2 ^ 32 + lo.toNat

theorem lens_bytes (alo ahi tlo thi : BitVec 32) :
    Proof.Cmac.le4 (VG.X86.bswap (ahi + ahi + (ahi + ahi) + (ahi + ahi + (ahi + ahi)) + alo >>> 29)) ++
        Proof.Cmac.le4 (VG.X86.bswap (alo + alo + (alo + alo) + (alo + alo + (alo + alo)))) ++
        Proof.Cmac.le4 (VG.X86.bswap (thi + thi + (thi + thi) + (thi + thi + (thi + thi)) + tlo >>> 29)) ++
        Proof.Cmac.le4 (VG.X86.bswap (tlo + tlo + (tlo + tlo) + (tlo + tlo + (tlo + tlo)))) =
      lensBlock (val64 alo ahi) (val64 tlo thi) := by
  rw [List.append_assoc, le4_be, le4_be, be64w_val, be64w_val, Proof.Gcm.be64_mod, Proof.Gcm.be64_mod]; rfl

end

/-- After `lens yo`: the lengths block absorbed, from `m₀`. -/
structure LensOut (Ctx St W SP : BitVec 32) (K yo : Nat) (aN tN : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  out : blockAt s.mem (w64 St + BitVec.ofNat 64 yo) =
    ghashFrom (Hk m₀ Ctx) (blockAt m₀ (w64 St + BitVec.ofNat 64 yo)) [Spec.Gcm.ofBytes (lensBlock aN tN)]
  frame : Frame (tFrame St W SP K yo) m₀ s.mem

/-- The slots of the lengths. -/
abbrev LensSlots (W : BitVec 32) (al ah tl th : Nat) (alo ahi tlo thi : BitVec 32) (m : Mem) : Prop :=
  slotv m W al = alo ∧ slotv m W ah = ahi ∧ slotv m W tl = tlo ∧ slotv m W th = thi

/-- Where `lens` finds the lengths, in the three uses. -/
abbrev LensAt (yo al ah tl th : Nat) : Prop :=
  (yo = 0 ∧ al = zO ∧ ah = zO ∧ tl = nlO ∧ th = zO) ∨ (yo = 16 ∧ al = alO ∧ ah = ahO ∧ tl = xlO ∧ th = xhO) ∨
    (yo = 16 ∧ al = alO ∧ ah = zO ∧ tl = lenO ∧ th = zO)

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay Ctx St W SP K)
include L

/-- One `be64w`: the words at `W + lo`, `W + hi` shifted and byte-reversed into `W + o`. -/
theorem be64w_ok {lo hi o : Nat} (hlo : lo + 4 ≤ 2560) (hhi : hi + 4 ≤ 2560) (ho : o + 8 ≤ 2560)
    {vlo vhi : BitVec 32} {s : State} (he : Env Ctx St W SP s) (h1 : slotv s.mem W lo = vlo)
    (h2 : slotv s.mem W hi = vhi) :
    ∃ s', runBlock isa (be64w lo hi o) s = some s' ∧
      s'.mem = (s.mem.writeW (w64 W + BitVec.ofNat 64 o)
        (VG.X86.bswap (vhi + vhi + (vhi + vhi) + (vhi + vhi + (vhi + vhi)) + vlo >>> 29))).writeW
        (w64 W + BitVec.ofNat 64 o + BitVec.ofNat 64 4)
        (VG.X86.bswap (vlo + vlo + (vlo + vlo) + (vlo + vlo + (vlo + vlo)))) ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  rw [slotv_eq] at h1 h2
  have a1 := L.aW (o := lo) (by omega)
  have a2 := L.aW (o := hi) (by omega)
  have a3 := L.aW (o := o) (by omega)
  have a4 := L.aW (o := o + 4) (by omega)
  have i1 := he.wIn' (d := lo) (n := 4) hlo
  have i2 := he.wIn' (d := hi) (n := 4) hhi
  have i3 := he.wIn (d := o) (n := 4) (by omega)
  have i4 := he.wIn (d := o + 4) (n := 4) (by omega)
  refine ⟨_, by xrun [be64w, he.ebp, a1, a2, a3, a4, i1, i2, i3, i4, h1, h2], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mems [add_ofNat_assoc]
  · regs []
  · regs []
  · regs []
  all_goals rfl

theorem lensT_ok {yo al ah tl th : Nat} (hc : LensAt yo al ah tl th) {alo ahi tlo thi : BitVec 32} {s : State}
    (he : Env Ctx St W SP s) (hs : LensSlots W al ah tl th alo ahi tlo thi s.mem) :
    ∃ s', runBlock isa (be64w al ah tO ++ be64w tl th (tO + 8)) s = some s' ∧
      s'.mem = Cmac.store4 s.mem (w64 W + BitVec.ofNat 64 96)
        (VG.X86.bswap (ahi + ahi + (ahi + ahi) + (ahi + ahi + (ahi + ahi)) + alo >>> 29))
        (VG.X86.bswap (alo + alo + (alo + alo) + (alo + alo + (alo + alo))))
        (VG.X86.bswap (thi + thi + (thi + thi) + (thi + thi + (thi + thi)) + tlo >>> 29))
        (VG.X86.bswap (tlo + tlo + (tlo + tlo) + (tlo + tlo + (tlo + tlo)))) ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨h1, h2, h3, h4⟩ := hs
  have hb : 144 ≤ al ∧ al + 4 ≤ 240 ∧ 144 ≤ ah ∧ ah + 4 ≤ 240 ∧ 144 ≤ tl ∧ tl + 4 ≤ 240 ∧ 144 ≤ th ∧
      th + 4 ≤ 240 := by
    rcases hc with ⟨_, rfl, rfl, rfl, rfl⟩ | ⟨_, rfl, rfl, rfl, rfl⟩ | ⟨_, rfl, rfl, rfl, rfl⟩ <;> decide
  obtain ⟨s₁, run₁, m₁, bp₁, si₁, sp₁, rd₁, wr₁⟩ := be64w_ok L (o := 96) (by omega) (by omega) (by decide) he h1 h2
  have he₁ : Env Ctx St W SP s₁ := he.keep bp₁ si₁ sp₁ rd₁ wr₁ (by
    rw [m₁, add_ofNat_assoc, readW_writeW_off (b := 100) _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_off (b := 96) _ _ _ (by decide) (by decide) (by decide)])
  have k : ∀ {o}, 144 ≤ o → o + 4 ≤ 240 → slotv s₁.mem W o = slotv s.mem W o := fun h₁ h₂ => by
    rw [slotv_eq, slotv_eq, m₁, add_ofNat_assoc, readW_writeW_off (b := 100) _ _ _ (by omega) (by omega) (by omega),
      readW_writeW_off (b := 96) _ _ _ (by omega) (by omega) (by omega)]
  obtain ⟨s₂, run₂, m₂, bp₂, si₂, sp₂, rd₂, wr₂⟩ := be64w_ok L (lo := tl) (hi := th) (o := 104) (by omega) (by omega) (by decide) he₁
    (k hb.2.2.2.2.1 hb.2.2.2.2.2.1) (k hb.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2)
  refine ⟨s₂, runBlock_app_of run₁ run₂, ?_, by rw [bp₂, bp₁], by rw [si₂, si₁], by rw [sp₂, sp₁], by rw [rd₂, rd₁],
    by rw [wr₂, wr₁]⟩
  rw [m₂, m₁]
  simp only [Proof.Cmac.store4, add_ofNat_assoc, Nat.reduceAdd, h3, h4]


/-- The block at `W + 96`, as a block `ghash1` absorbs. -/
theorem t_gh {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {s : State} (he : Env Ctx St W SP s) :
    Env Ctx St W SP s ∧ s.gpr .ebp + BitVec.ofNat 32 96 = W + BitVec.ofNat 32 96 ∧
      (W + BitVec.ofNat 32 96).toNat + 16 ≤ 2 ^ 32 ∧ Covers [⟨w64 (W + BitVec.ofNat 32 96), 16⟩] (s.rd ++ s.wr) ∧
      (⟨w64 St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨w64 (W + BitVec.ofNat 32 96), 16⟩ ∧
      (⟨w64 (W + BitVec.ofNat 32 96), 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, 256⟩ ∧
      (below SP K).Disjoint ⟨w64 (W + BitVec.ofNat 32 96), 16⟩ := by
  rw [L.aW (by decide)]
  exact ⟨he, by rw [he.ebp], by rw [L.nW (by decide)]; have := L.fw; omega, covers_left (he.wC (by decide)),
    L.st_w (by omega) (.inr ⟨by decide, by decide⟩), Lay.w_w (.inl (by decide)) (by decide) (by decide),
    L.stk_w (by decide)⟩

theorem lens_pc_aux {yo al ah tl th : Nat} (hyo : yo = 0 ∨ yo = 16) (hc : LensAt yo al ah tl th)
    {alo ahi tlo thi : BitVec 32} {hh : Taint.Hint VG.X86.taint.T}
    (ht : (VG.X86.taint.check (τr [.ebp]) (.block (be64w al ah tO ++ be64w tl th (tO + 8))) hh).isSome = true) :
    Pc (fun (m₀ : Mem) s => (Env Ctx St W SP s ∧ LensSlots W al ah tl th alo ahi tlo thi s.mem) ∧ s.mem = m₀)
      (lens vg.callees yo al ah tl th) (LensOut Ctx St W SP K yo (val64 alo ahi) (val64 tlo thi) ·) := by
  refine Pc.seq (Q := fun m₀ s => Env Ctx St W SP s ∧ s.mem = Cmac.store4 m₀ (w64 W + BitVec.ofNat 64 96)
      (VG.X86.bswap (ahi + ahi + (ahi + ahi) + (ahi + ahi + (ahi + ahi)) + alo >>> 29))
      (VG.X86.bswap (alo + alo + (alo + alo) + (alo + alo + (alo + alo))))
      (VG.X86.bswap (thi + thi + (thi + thi) + (thi + thi + (thi + thi)) + tlo >>> 29))
      (VG.X86.bswap (tlo + tlo + (tlo + tlo) + (tlo + tlo + (tlo + tlo)))))
    (Pc.taint [.ebp] (fun m₀ s ⟨⟨he, hs⟩, hm⟩ => by
        obtain ⟨s', run, m, bp, si, sp, rd, wr⟩ := lensT_ok L hc he hs
        have fT : Frame [⟨w64 W + BitVec.ofNat 64 96, 16⟩] s.mem s'.mem := by rw [m]; exact Cmac.frame_store4 _ _ _ _ _
        exact WP.of_runBlock ⟨s', run, env_tFrame L hyo he (t_tFrame fT) bp si sp rd wr, by rw [m, hm]⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.ebp, h₂.1.1.ebp]) ht) ?_
  refine Pc.mono (Pc.of (I := Env Ctx St W SP) (fun s he => ghash1_ok L hyo he .ebp 96 (.inr rfl)
      (t_gh L hyo he).2.1 (t_gh L hyo he).2.2.1 (t_gh L hyo he).2.2.2.1 (t_gh L hyo he).2.2.2.2.1
      (t_gh L hyo he).2.2.2.2.2.1 (t_gh L hyo he).2.2.2.2.2.2)
    (ghash1_ct L hyo .ebp 96 (.inr ⟨rfl, rfl⟩) fun s he => t_gh L hyo he) _ fun _ _ h => h.1)
    (fun _ _ h => h) fun m₀ s₂ ⟨s₁, ⟨_, hm⟩, g⟩ => ?_
  have go := g.out
  rw [L.aW (by decide)] at go
  have fT : Frame [⟨w64 W + BitVec.ofNat 64 96, 16⟩] m₀ s₁.mem := by rw [hm]; exact Cmac.frame_store4 _ _ _ _ _
  have hY : blockAt s₁.mem (w64 St + BitVec.ofNat 64 yo) = blockAt m₀ (w64 St + BitVec.ofNat 64 yo) :=
    blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  have hH : blockAt s₁.mem (w64 Ctx + BitVec.ofNat 64 240) = Hk m₀ Ctx :=
    blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  have hT : blockAt s₁.mem (w64 W + BitVec.ofNat 64 96) =
      Spec.Gcm.ofBytes (lensBlock (val64 alo ahi) (val64 tlo thi)) := by
    rw [blockAt, hm, Cmac.bytesAt_store4, lens_bytes]
  refine ⟨g.env, ?_, (t_tFrame fT).trans (gh_tFrame g.frame)⟩
  rw [go, hY, hH, hT]

theorem lens_pc {yo al ah tl th : Nat} (hc : LensAt yo al ah tl th) {alo ahi tlo thi : BitVec 32} :
    Pc (fun (m₀ : Mem) s => (Env Ctx St W SP s ∧ LensSlots W al ah tl th alo ahi tlo thi s.mem) ∧ s.mem = m₀)
      (lens vg.callees yo al ah tl th) (LensOut Ctx St W SP K yo (val64 alo ahi) (val64 tlo thi) ·) := by
  have hc' := hc
  rcases hc with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact lens_pc_aux L (.inl rfl) hc' (by taint_decide)
  · exact lens_pc_aux L (.inr rfl) hc' (by taint_decide)
  · exact lens_pc_aux L (.inr rfl) hc' (by taint_decide)

end

end VG.Proof.AesGcm.X86
