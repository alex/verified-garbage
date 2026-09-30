import VerifiedGarbage.Proof.X25519.Arm.Pass

/-!
# X25519 on 32-bit ARM: field elements in the working space

Untrusted: everything here is checked by Lean. A field element is 16 words
at an offset `o` of the working space at `B` (`limb`), each below `2¹⁶`
(`Lim`), for the number `V` and its residue `FS`. The carry out of a `pass`
folded in again (`tail_ok`), and `add` and `sub` (`add_ok`, `sub_ok`).
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe)

/-- `r0` holds the working space `b`, 4096 writable bytes. -/
structure Ctx (b : BitVec 32) (s : State) : Prop where
  r0 : s.gpr .r0 = b
  fit : b.toNat + 4096 ≤ 2 ^ 32
  wr : (⟨State.addr b, 4096⟩ : Region) ∈ s.wr

theorem Ctx.of_rest {b : BitVec 32} {s s' : State} {ws : List Reg} (h : Ctx b s) (hr : Rest ws s s')
    (h0 : Reg.r0 ∉ ws) : Ctx b s' :=
  ⟨by rw [hr.gpr _ h0, h.r0], h.fit, by rw [hr.wr]; exact h.wr⟩

theorem Ctx.ea {b : BitVec 32} {s : State} (h : Ctx b s) {d : Nat} (hd : d < 4096) :
    State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = State.addr b + BitVec.ofNat 64 d := by
  rw [h.r0]; exact addr_add (by have := h.fit; omega)

theorem Ctx.inW {b : BitVec 32} {s : State} (h : Ctx b s) {d n : Nat} (hd : d + n ≤ 4096) :
    InRegions s.wr (State.addr b + BitVec.ofNat 64 d) n := in_base h.wr hd (by omega)

theorem Ctx.inR {b : BitVec 32} {s : State} (h : Ctx b s) {d n : Nat} (hd : d + n ≤ 4096) :
    InRegions (s.rd ++ s.wr) (State.addr b + BitVec.ofNat 64 d) n :=
  in_base (List.mem_append_right _ h.wr) hd (by omega)

/-- Limb `k` of the element at `o`. -/
def limb (m : Mem) (B : Addr) (o k : Nat) : Nat := wd m B (o + 4 * k)

/-- Every limb of the element at `o` is below `2¹⁶`. -/
def Lim (m : Mem) (B : Addr) (o : Nat) : Prop := ∀ k < 16, limb m B o k < 65536

/-- The number of the element at `o`. -/
def V (m : Mem) (B : Addr) (o : Nat) : Nat := val16 (limb m B o) 16

/-- The element at `o`. -/
def FS (m : Mem) (B : Addr) (o : Nat) : Fe := Proof.X25519.toFe (V m B o)

theorem V_lt {m : Mem} {B : Addr} {o : Nat} (h : Lim m B o) : V m B o < 2 ^ 256 := val16_lt h

/-- The limbs of an element in a frame that does not overlap it. -/
theorem limb_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {B : Addr} {o : Nat}
    (hd : ∀ r ∈ rs, ∀ k < 16, (⟨B + BitVec.ofNat 64 (o + 4 * k), 4⟩ : Region).Disjoint r) :
    ∀ k < 16, limb m' B o k = limb m B o k := fun k hk => wd_frame hf fun r hr => hd r hr k hk

/-- The words of `[o, o + 64)` are outside the ranges `[p.1, p.1 + p.2)`
of `l`, all within the working space. -/
def Outside (o : Nat) (l : List (Nat × Nat)) : Bool :=
  l.all fun p => o + 64 ≤ p.1 || p.1 + p.2 ≤ o

/-- The ranges `l` of the working space at `B`. -/
def offR (B : Addr) (l : List (Nat × Nat)) : List Region :=
  l.map fun p => ⟨B + BitVec.ofNat 64 p.1, p.2⟩

theorem limb_offR {l : List (Nat × Nat)} {m m' : Mem} {B : Addr} (hf : Frame (offR B l) m m') {o : Nat}
    (ho : Outside o l = true) (hl : (l.all fun p => p.1 + p.2 ≤ 4096) = true) (ho' : o + 64 ≤ 4096) :
    ∀ k < 16, limb m' B o k = limb m B o k := by
  refine limb_frame hf fun r hr k hk => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  have h1 := List.all_eq_true.mp ho p hp
  have h2 := List.all_eq_true.mp hl p hp
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h1 h2
  exact Offset.disjoint B (by omega) (by omega) (by omega)

theorem Lim_offR {l : List (Nat × Nat)} {m m' : Mem} {B : Addr} (hf : Frame (offR B l) m m') {o : Nat}
    (ho : Outside o l = true) (hl : (l.all fun p => p.1 + p.2 ≤ 4096) = true) (ho' : o + 64 ≤ 4096)
    (h : Lim m B o) : Lim m' B o := fun k hk => by rw [limb_offR hf ho hl ho' k hk]; exact h k hk

theorem V_offR {l : List (Nat × Nat)} {m m' : Mem} {B : Addr} (hf : Frame (offR B l) m m') {o : Nat}
    (ho : Outside o l = true) (hl : (l.all fun p => p.1 + p.2 ≤ 4096) = true) (ho' : o + 64 ≤ 4096) :
    V m' B o = V m B o := val16_congr (limb_offR hf ho hl ho')

/-- The clobbered registers of the field operations. -/
abbrev clob : List Reg := [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9]

/-! ## Loading a limb -/

theorem ldr0_ok {b : BitVec 32} {s : State} (hc : Ctx b s) {t : Reg} {d : Nat} (hd : d + 4 ≤ 4096)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t (s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr t .r0 d :: is)) s Q :=
  wp_ldr (by omega) (hc.ea (by omega)) (hc.inR hd) k

theorem str0_ok {b : BitVec 32} {s : State} (hc : Ctx b s) {t : Reg} {d : Nat} (hd : d + 4 ≤ 4096)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Mupd s s' (s.mem.writeW (State.addr b + BitVec.ofNat 64 d) (s.gpr t)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.str t .r0 d :: is)) s Q :=
  wp_str (by omega) (hc.ea (by omega)) (hc.inW hd) k

theorem ldSrc_ok {b : BitVec 32} {o k : Nat} {s : State} (hc : Ctx b s) (hd : o + 4 * k + 4 ≤ 4096) :
    WP isa (.block (ldSrc o k)) s fun s' =>
      (s'.gpr .r3).toNat = wd s.mem (State.addr b) (o + 4 * k) ∧ Rest [.r3] s s' ∧ s'.mem = s.mem :=
  ldr0_ok hc hd fun s1 u1 => WP.block_nil ⟨by rw [u1.gpr]; rfl, u1.rest (by decide), u1.mem⟩

/-! ## The prologue -/

theorem prologue_ok {s : State} :
    WP isa (.block prologue) s fun s' =>
      s'.gpr .r6 = mask16 ∧ s'.gpr .r8 = 38 ∧ s'.gpr .r5 = 0 ∧ Rest [.r5, .r6, .r8] s s' ∧
        s'.mem = s.mem := by
  refine wp_movw fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 =>
    wp_mov (op2_imm (by decide)) fun s3 u3 => WP.block_nil ⟨?_, ?_, u3.gpr, ?_, ?_⟩
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr]
  · rw [u3.other _ (by decide), u2.gpr]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  · rw [u3.mem, u2.mem, u1.mem]

/-! ## The tail -/

section
variable {b : BitVec 32}

theorem tail_ok {o : Nat} (ho : o + 64 ≤ 4096) {s : State} (hc : Ctx b s) (h6 : s.gpr .r6 = mask16)
    (h8 : s.gpr .r8 = 38) {c16 : Nat} (h5 : (s.gpr .r5).toNat = c16) (hc16 : c16 ≤ 38)
    (hl : Lim s.mem (State.addr b) o) :
    WP isa (.block (tail o)) s fun s' =>
      Rest [.r2, .r3, .r4, .r5] s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s.mem s'.mem ∧
      Lim s'.mem (State.addr b) o ∧
      V s'.mem (State.addr b) o % P = (V s.mem (State.addr b) o + 2 ^ 256 * c16) % P := by
  have B0 : State.addr (s.gpr .r0) = State.addr b := by rw [hc.r0]
  have t38 : (38 : BitVec 32).toNat = 38 := rfl
  simp only [tail, List.cons_append, List.nil_append]
  refine wp_mul fun s1 u1 => ?_
  have e1 : (s1.gpr .r5).toNat = 38 * c16 := by
    rw [u1.gpr, h8, toNat_mul_lt (by rw [h5, t38]; omega), h5, t38]; omega
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.r5]) (by decide)) (by decide)
  refine WP.append (pass_ok (s0 := s1) (c := limb s.mem (State.addr b) o) (cin := 38 * c16)
    (by decide) ho (by rw [hc1.r0]; have := hc.fit; omega)
    (fun k hk => by rw [hc1.r0]; exact hc1.inW (by omega))
    (by rw [u1.other _ (by decide), h6]) e1 (fun k hk => by have := hl k hk; omega) (by omega)
    (fun k hk s' hp => WP.mono (ldSrc_ok (hc1.of_rest hp.rest (by decide)) (by omega)) fun s'' h => ?_))
    fun s2 hp => ?_
  · refine ⟨?_, h.2.1.mono (by decide), h.2.2⟩
    rw [h.1, ← u1.mem]
    refine wd_frame hp.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr, hc1.r0]
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · have hc2 : Ctx b s2 := hc1.of_rest hp.rest (by decide)
    have ht := tail_facts hl hc16
    have hpo : ∀ j < 16, wd s2.mem (State.addr b) (o + 4 * j) =
        out (limb s.mem (State.addr b) o) (38 * c16) j := fun j hj => by
      have := hp.outs j hj; rwa [hc1.r0] at this
    have hpf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * 16⟩] s1.mem s2.mem := by
      have := hp.frame; rwa [hc1.r0] at this
    refine wp_mul fun s3 u3 => ?_
    have e3 : (s3.gpr .r5).toNat = 38 * chain (limb s.mem (State.addr b) o) (38 * c16) 16 := by
      rw [u3.gpr, hp.rest.gpr .r8 (by decide), u1.other .r8 (by decide), h8,
        toNat_mul_lt (by rw [hp.r5, t38]; have := ht.1; omega), hp.r5, t38]; omega
    have hc3 : Ctx b s3 := hc2.of_rest (u3.rest (ws := [.r5]) (by decide)) (by decide)
    refine ldr0_ok hc3 (by omega) fun s4 u4 => ?_
    refine wp_dp (op2_reg _ _) fun s5 u5 => ?_
    have hc5 : Ctx b s5 :=
      hc3.of_rest ((u4.rest (ws := [.r3]) (by decide)).trans (u5.rest (by decide))) (by decide)
    refine str0_ok hc5 (by omega) fun s6 u6 => WP.block_nil ?_
    have w0 : s3.mem.readW (State.addr b + BitVec.ofNat 64 o) 32 =
        s2.mem.readW (State.addr b + BitVec.ofNat 64 o) 32 := by
      rw [u3.mem]
    have e5 : (s5.gpr .r3).toNat = tailL (limb s.mem (State.addr b) o) c16 0 := by
      rw [u5.gpr]
      show (s4.gpr .r3 + s4.gpr .r5).toNat = _
      rw [u4.gpr, u4.other .r5 (by decide), w0]
      have o0 := hpo 0 (by decide)
      rw [Nat.mul_zero, Nat.add_zero] at o0
      have h0 := ht.2.1 0 (by decide)
      simp only [tailL, ite_true] at h0 ⊢
      rw [toNat_add_lt (by rw [e3]; unfold wd at o0; rw [o0]; omega), e3]
      unfold wd at o0; rw [o0]
    have hm6 : s6.mem = s2.mem.writeW (State.addr b + BitVec.ofNat 64 o) (s5.gpr .r3) := by
      rw [u6.mem, u5.mem, u4.mem, u3.mem]
    have hlimb : ∀ k < 16, limb s6.mem (State.addr b) o k = tailL (limb s.mem (State.addr b) o) c16 k := by
      intro k hk
      rw [limb, hm6]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [Nat.mul_zero, Nat.add_zero, wd_write_self, e5]
      · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega), hpo k hk]
        simp only [tailL, show k ≠ 0 by omega, ite_false]
    refine ⟨?_, ?_, fun k hk => by rw [hlimb k hk]; exact ht.2.1 k hk, ?_⟩
    · refine (u1.rest (ws := [.r2, .r3, .r4, .r5]) (by decide)).trans (hp.rest.trans ?_)
      refine (u3.rest (by decide)).trans ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ?_))
      exact u6.rest _
    · rw [hm6]
      refine (?_ : Frame _ s.mem s2.mem).writeW (List.mem_singleton_self _) _
        (Offset.contains (State.addr b) (d := o) (n := 4) (e := o) (k := 64) (Nat.le_refl _)
          (by omega) (by omega))
      rw [← u1.mem]
      exact hpf
    · rw [V, val16_congr hlimb, ht.2.2]; rfl

end

end VG.Proof.X25519.Arm
