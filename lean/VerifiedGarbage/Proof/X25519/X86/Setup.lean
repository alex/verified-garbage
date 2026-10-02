import VerifiedGarbage.Proof.X25519.X86.Step
import VerifiedGarbage.Proof.X25519.X86.Freeze
import VerifiedGarbage.Proof.X25519.X86.Contract
import VerifiedGarbage.Proof.X25519.Bytes

/-!
# X25519 on x86 (32-bit): reading the arguments

`save` stores the callee-saved registers in the working space, `loadPoint` the
u-coordinate (its top bit masked) in `X1`, `loadScalar` the bits of the scalar
in `BITS` (clamped), and `initLadder` the ladder's initial state; so the
ladder starts with `LInv 255`.
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

theorem save_eq : save = [.mov .eax (.mem (at_ .esp 16)), .store (at_ .eax 0) .ebx,
    .store (at_ .eax 4) .esi, .store (at_ .eax 8) .edi, .store (at_ .eax 12) .ebp,
    .mov .edi (.reg .eax)] := rfl

/-- What `save` leaves. -/
structure Saved (s₀ s : State) : Prop where
  edi : s.gpr .edi = arg s₀ 3
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [scR 4096 (arg s₀ 3)] s₀.mem s.mem
  saved : ∀ j < 4, wd s.mem (arg s₀ 3) (4 * j) = s₀.gpr (savedReg j)

theorem save_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block save) s₀ (Saved s₀) := by
  have hfit := hp.sc_fit
  rw [save_eq]
  refine Wp.wp_ldm (B := s₀.gpr .esp) (o := 16) rfl (hp.argIn (i := 3) (by decide)) fun s₁ u₁ => ?_
  have ea : s₁.gpr .eax = arg s₀ 3 := u₁.gpr
  have inW : ∀ {s : State} {d : Nat}, s.wr = s₀.wr → d + 4 ≤ 4096 → InRegions s.wr (addr (arg s₀ 3) d) 4 :=
    fun hw hd => ⟨_, hw ▸ hp.sc_in, scR_contains hfit hd (by decide)⟩
  refine Wp.wp_stm ea (inW u₁.wr (by decide)) fun s₂ u₂ => ?_
  refine Wp.wp_stm (by rw [u₂.gpr]; exact ea) (inW (by rw [u₂.wr, u₁.wr]) (by decide)) fun s₃ u₃ => ?_
  refine Wp.wp_stm (by rw [u₃.gpr, u₂.gpr]; exact ea) (inW (by rw [u₃.wr, u₂.wr, u₁.wr]) (by decide))
    fun s₄ u₄ => ?_
  refine Wp.wp_stm (by rw [u₄.gpr, u₃.gpr, u₂.gpr]; exact ea)
    (inW (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (by decide)) fun s₅ u₅ => ?_
  refine Wp.wp_mov fun s₆ u₆ => WP.block_nil ?_
  have g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  have hr : ∀ r, r ≠ .eax → s₁.gpr r = s₀.gpr r := fun r h => u₁.other r h
  have w : ∀ {m : Mem} {d : Nat} (v : BitVec 32), d + 4 ≤ 4096 →
      Frame [scR 4096 (arg s₀ 3)] s₀.mem m → Frame [scR 4096 (arg s₀ 3)] s₀.mem (m.writeW (addr (arg s₀ 3) d) v) :=
    fun v hd hf => hf.writeW (List.mem_singleton_self _) _ (scR_contains hfit hd (by decide))
  refine ⟨by rw [u₆.gpr, g₅, ea], by rw [u₆.other _ (by decide), g₅, hr _ (by decide)],
    by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    ?_, fun j hj => ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact w _ (by decide) (w _ (by decide) (w _ (by decide) (w _ (by decide) (Frame.refl _ _))))
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    have hne : ∀ a b : Nat, a < 4 → b < 4 → a ≠ b → 4 * a + 4 ≤ 4 * b ∨ 4 * b + 4 ≤ 4 * a :=
      fun a b ha hb h => by omega_using [ha, hb, h]
    have ne : ∀ (m : Mem) (v : BitVec 32) (a : Nat), a < 4 → a ≠ j →
        wd (m.writeW (addr (arg s₀ 3) (4 * a)) v) (arg s₀ 3) (4 * j) = wd m (arg s₀ 3) (4 * j) :=
      fun m v a ha h => wd_write_ne m v (by omega_using [hfit, hj]) (by omega_using [hfit, ha])
        (hne j a hj ha (Ne.symm h))
    rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · rw [ne _ _ 3 (by decide) (by decide), ne _ _ 2 (by decide) (by decide),
        ne _ _ 1 (by decide) (by decide), show 4 * 0 = 0 from rfl, wd_write_self, hr _ (by decide)]
      rfl
    · rw [ne _ _ 3 (by decide) (by decide), ne _ _ 2 (by decide) (by decide),
        show 4 * 1 = 4 from rfl, wd_write_self, u₂.gpr, hr _ (by decide)]
      rfl
    · rw [ne _ _ 3 (by decide) (by decide), show 4 * 2 = 8 from rfl, wd_write_self, u₃.gpr, u₂.gpr,
        hr _ (by decide)]
      rfl
    · rw [show 4 * 3 = 12 from rfl, wd_write_self, u₄.gpr, u₃.gpr, u₂.gpr, hr _ (by decide)]
      rfl

/-- A store to the working space above the saved registers keeps `Saved`. -/
theorem Saved.write {s₀ s s' : State} (hp : Pre s₀) (h : Saved s₀ s) {d : Nat} (hd : 16 ≤ d)
    (hd' : d + 4 ≤ 4096) (hg : s'.gpr .edi = s.gpr .edi) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) {v : BitVec 32} (hm : s'.mem = s.mem.writeW (addr (arg s₀ 3) d) v) : Saved s₀ s' := by
  have hfit := hp.sc_fit
  refine ⟨hg.trans h.edi, hesp.trans h.esp, hrd.trans h.rd, hwr.trans h.wr, ?_, fun j hj => ?_⟩
  · rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ (scR_contains hfit hd' (by decide))
  · rw [hm, wd_write_ne _ _ (by omega_using [hfit, hj]) (by omega_using [hfit, hd']) (.inl (by omega_using [hj, hd]))]
    exact h.saved j hj

/-- The words of the u-coordinate, on entry. -/
abbrev pw (s₀ : State) (k : Nat) : BitVec 32 := wd s₀.mem (arg s₀ 2) (4 * k)

/-- The words `X1` receives: those of the u-coordinate, the top bit masked. -/
def pv (s₀ : State) (k : Nat) : BitVec 32 := if k = 7 then pw s₀ 7 &&& low31 else pw s₀ k

/-- A word of the u-coordinate, unchanged. -/
theorem point_contains {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 8) :
    (pointR s₀).Contains (addr (arg s₀ 2) (4 * k)) 4 := by
  have := sub_contains (x := arg s₀ 2) (a := 0) (k := 32) (d := 4 * k) (n := 4)
    (by have := hp.point_fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hk]) (by decide)
  rwa [sub, addr_zero] at this

/-- A word of the u-coordinate, unchanged. -/
theorem Saved.pw {s₀ s : State} (hp : Pre s₀) (h : Saved s₀ s) {k : Nat} (hk : k < 8) :
    wd s.mem (arg s₀ 2) (4 * k) = pw s₀ k :=
  h.frame.readW (point_contains hp hk)
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.point_sc) (by decide)

theorem loadWord_ok {s₀ s : State} (hp : Pre s₀) {n : Nat} (hn : n < 8)
    (h : Saved s₀ s) (hesi : s.gpr .esi = arg s₀ 2) (hw : ∀ j < n, wd s.mem (arg s₀ 3) (X1 + 4 * j) = pv s₀ j) :
    WP isa (.block (([.mov .eax (.mem (at_ .esi (4 * n)))] : List Instr) ++
      (if n = 7 then ([.alu .and .eax (.imm low31)] : List Instr) else []) ++
      ([.store (sc (X1 + 4 * n)) .eax] : List Instr))) s fun s' =>
      Saved s₀ s' ∧ s'.gpr .esi = arg s₀ 2 ∧ ∀ j < n + 1, wd s'.mem (arg s₀ 3) (X1 + 4 * j) = pv s₀ j := by
  have hfit := hp.sc_fit
  have hin : InRegions (s.rd ++ s.wr) (addr (arg s₀ 2) (4 * n)) 4 :=
    ⟨pointR s₀, by rw [h.rd, hp.rd]; simp, point_contains hp hn⟩
  simp only [List.cons_append, List.nil_append]
  refine Wp.wp_ldm hesi hin fun s₁ u₁ => ?_
  -- The rest, from the value `w` in `eax`.
  have fin : ∀ (s₂ : State) (w : BitVec 32), s₂.gpr .eax = w → w = pv s₀ n → s₂.gpr .edi = s.gpr .edi →
      s₂.gpr .esp = s.gpr .esp → s₂.gpr .esi = s.gpr .esi → s₂.rd = s.rd → s₂.wr = s.wr → s₂.mem = s.mem →
      WP isa (.block [.store (sc (X1 + 4 * n)) .eax]) s₂ fun s' =>
        Saved s₀ s' ∧ s'.gpr .esi = arg s₀ 2 ∧ ∀ j < n + 1, wd s'.mem (arg s₀ 3) (X1 + 4 * j) = pv s₀ j := by
    intro s₂ w ew hw' g1 g2 g3 g4 g5 g6
    refine Wp.wp_stm (by rw [g1]; exact h.edi) ⟨_, by rw [g5, h.wr]; exact hp.sc_in,
      scR_contains hfit (by simp only [X1]; omega_using [hn]) (by decide)⟩ fun s₃ u₃ => WP.block_nil ?_
    refine ⟨h.write hp (d := X1 + 4 * n) (by simp only [X1]; omega_using []) (by simp only [X1]; omega_using [hn])
      (by rw [u₃.gpr, g1]) (by rw [u₃.gpr, g2]) (by rw [u₃.rd, g4]) (by rw [u₃.wr, g5]) (by rw [u₃.mem, g6]),
      by rw [u₃.gpr, g3, hesi], fun j hj => ?_⟩
    rw [u₃.mem, g6]
    by_cases e : j = n
    · subst e; rw [wd_write_self, ew, hw']
    · rw [wd_write_ne _ _ (by simp only [X1]; omega_using [hfit, hj, hn]) (by simp only [X1]; omega_using [hfit, hn])
        (by omega_using [e])]
      exact hw j (by omega_using [hj, e])
  have e₁ : s₁.gpr .eax = pw s₀ n := by rw [u₁.gpr]; exact h.pw hp hn
  by_cases h7 : n = 7
  · subst h7
    simp only [ite_true, List.cons_append, List.nil_append]
    refine Wp.wp_andi fun s₂ u₂ => fin s₂ _ u₂.gpr ?_ (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
      (by rw [u₂.mem, u₁.mem])
    rw [e₁]; rfl
  · simp only [h7, ite_false, List.nil_append]
    exact fin s₁ _ rfl (by rw [e₁, pv, ite_eq_right h7]) (u₁.other _ (by decide)) (u₁.other _ (by decide))
      (u₁.other _ (by decide)) u₁.rd u₁.wr u₁.mem

theorem loadWords_ok {s₀ : State} (hp : Pre s₀) : ∀ n ≤ 8, ∀ s, Saved s₀ s → s.gpr .esi = arg s₀ 2 →
    WP isa (.block ((List.range n).flatMap fun k => ([.mov .eax (.mem (at_ .esi (4 * k)))] : List Instr) ++
      (if k = 7 then ([.alu .and .eax (.imm low31)] : List Instr) else []) ++
      ([.store (sc (X1 + 4 * k)) .eax] : List Instr))) s fun s' =>
      Saved s₀ s' ∧ s'.gpr .esi = arg s₀ 2 ∧ ∀ j < n, wd s'.mem (arg s₀ 3) (X1 + 4 * j) = pv s₀ j
  | 0, _, _, h, he => WP.block_nil ⟨h, he, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | n + 1, hn, s, h, he => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (loadWords_ok hp n (by omega_using [hn]) s h he) fun s₁ ⟨h₁, e₁, w₁⟩ =>
      loadWord_ok hp (by omega_using [hn]) h₁ e₁ w₁)

theorem loadPoint_ok {s₀ s : State} (hp : Pre s₀) (h : Saved s₀ s) :
    WP isa (.block loadPoint) s fun s' => Saved s₀ s' ∧ ∀ j < 8, wd s'.mem (arg s₀ 3) (X1 + 4 * j) = pv s₀ j := by
  refine Wp.wp_ldm (B := s.gpr .esp) (o := 12) rfl (by rw [h.esp, h.rd, h.wr]; exact hp.argIn (i := 2) (by decide))
    fun s₁ u₁ => ?_
  have h₁ : Saved s₀ s₁ := ⟨by rw [u₁.other _ (by decide)]; exact h.edi, by rw [u₁.other _ (by decide)]; exact h.esp,
    by rw [u₁.rd]; exact h.rd, by rw [u₁.wr]; exact h.wr, by rw [u₁.mem]; exact h.frame,
    by rw [u₁.mem]; exact h.saved⟩
  have e₁ : s₁.gpr .esi = arg s₀ 2 := by
    rw [u₁.gpr, h.esp]; exact hp.arg_same h.frame (i := 2) (by decide)
  exact WP.mono (loadWords_ok hp 8 (Nat.le_refl _) s₁ h₁ e₁) fun s' ⟨h', _, w'⟩ => ⟨h', w'⟩

/-! ## The scalar's bits -/

theorem wp_store8 {is : List Instr} {s : State} {Q : State → Prop} {b : Reg} {o : Nat} {r : Reg8} {a : Addr}
    (ha : addr (s.gpr b) o = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Wp.Mupd s s' (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 ⟨b, o⟩ r :: is)) s Q := by
  refine Wp.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, State.store8, ea_mk, ha, hout, ↓reduceIte]

theorem byte_write_self (m : Mem) (a : Addr) (v : BitVec 8) : (m.writeW a v) a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero]
  apply BitVec.eq_of_toNat_eq
  simp

theorem byte_write_ne (m : Mem) {x : BitVec 32} (v : BitVec 8) {d e : Nat} (hd : x.toNat + d + 1 ≤ 2 ^ 32)
    (he : x.toNat + e + 1 ≤ 2 ^ 32) (h : d ≠ e) : (m.writeW (addr x e) v) (addr x d) = m (addr x d) := by
  have hdisj := sub_disj (x := x) (n := 1) (k := 1) hd he (by omega_using [h])
  exact Mem.write_apply fun h' => hdisj _ (Region.contains_self _ _) (by
    simp only [Region.Contains]; omega_using [h'])

theorem Saved.of_frame {s₀ sA s : State} (hp : Pre s₀) (h : Saved s₀ sA) {o n : Nat}
    (hf : Frame [sub (arg s₀ 3) o n] sA.mem s.mem) (ho : 16 ≤ o) (hon : o + n ≤ 4096) (hn : o < 4096)
    (hg : s.gpr .edi = sA.gpr .edi) (hesp : s.gpr .esp = sA.gpr .esp) (hrd : s.rd = sA.rd) (hwr : s.wr = sA.wr) :
    Saved s₀ s := by
  have hfit := hp.sc_fit
  refine ⟨hg.trans h.edi, hesp.trans h.esp, hrd.trans h.rd, hwr.trans h.wr, ?_, fun j hj => ?_⟩
  · exact h.frame.trans (hf.sub fun _ hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr, scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by omega_using [hon]) hn⟩)
  · rw [wd_frame1 hf hfit hon (by omega_using [hj]) (.inl (by omega_using [hj, ho]))]; exact h.saved j hj

/-- Byte `i` of the scalar, on entry. -/
abbrev sb (s₀ : State) (i : Nat) : Nat := (s₀.mem (addr (arg s₀ 1) i)).toNat

/-- The bits stored so far. -/
structure BInv (s₀ sA : State) (t : Nat) (s : State) : Prop where
  edi : s.gpr .edi = arg s₀ 3
  esi : s.gpr .esi = arg s₀ 1
  esp : s.gpr .esp = sA.gpr .esp
  rd : s.rd = sA.rd
  wr : s.wr = sA.wr
  frame : Frame [sub (arg s₀ 3) BITS 256] sA.mem s.mem
  bits : ∀ u < t, s.mem (addr (arg s₀ 3) (BITS + u)) = BitVec.ofNat 8 ((sb s₀ (u / 8) >>> (u % 8)) &&& 1)

theorem bit_toNat {b : Nat} (hb : b < 256) (j : Nat) :
    ((BitVec.ofNat 32 b >>> j) &&& 1).toNat = (b >>> j) &&& 1 := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb])]
  rfl

theorem setWidth8_bit (w : BitVec 32) {b : Nat} (h : w.toNat = b) :
    w.setWidth 8 = BitVec.ofNat 8 b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h, BitVec.toNat_ofNat]

theorem and_one_le (n : Nat) : n &&& 1 ≤ 1 := Nat.le_of_lt_succ (Nat.and_lt_two_pow n (by decide : 1 < 2 ^ 1))

theorem bitOf_ok {s₀ sA s : State} (hp : Pre s₀) (hsA : sA.wr = s₀.wr) {i j : Nat} (hi : i < 32) (hj : j < 8)
    (h : BInv s₀ sA (8 * i + j) s) (heax : s.gpr .eax = BitVec.ofNat 32 (sb s₀ i)) :
    WP isa (.block (bitOf i j)) s fun s' => BInv s₀ sA (8 * i + j + 1) s' ∧ s'.gpr .eax = s.gpr .eax := by
  have hfit := hp.sc_fit
  have hbl : sb s₀ i < 256 := BitVec.isLt _
  -- The last two instructions, from `edx = eax >>> j`.
  have fin : ∀ s₁, s₁.gpr .edx = s.gpr .eax >>> j → s₁.gpr .eax = s.gpr .eax → s₁.gpr .edi = s.gpr .edi →
      s₁.gpr .esi = s.gpr .esi → s₁.gpr .esp = s.gpr .esp → s₁.rd = s.rd → s₁.wr = s.wr → s₁.mem = s.mem →
      WP isa (.block [.alu .and .edx (.imm 1), .store8 (sc (BITS + 8 * i + j)) .dl]) s₁ fun s' =>
        BInv s₀ sA (8 * i + j + 1) s' ∧ s'.gpr .eax = s.gpr .eax := by
    intro s₁ e1 a1 g1 g2 g3 g4 g5 g6
    refine Wp.wp_andi fun s₂ u₂ => ?_
    refine wp_store8 (a := addr (arg s₀ 3) (BITS + 8 * i + j)) (by rw [u₂.other _ (by decide), g1, h.edi])
      ⟨_, by rw [u₂.wr, g5, h.wr, hsA]; exact hp.sc_in, scR_contains hfit (by simp only [BITS]; omega_using [hi, hj])
        (by decide)⟩ fun s₃ u₃ => WP.block_nil ?_
    have ev : ((s₂.gpr (Reg8.dl).reg).setWidth 8) = BitVec.ofNat 8 ((sb s₀ i >>> j) &&& 1) := by
      refine setWidth8_bit _ ?_
      show (s₂.gpr .edx).toNat = _
      rw [u₂.gpr, e1, heax, bit_toNat hbl]
    have m₃ : s₃.mem = s.mem.writeW (addr (arg s₀ 3) (BITS + 8 * i + j)) (BitVec.ofNat 8 ((sb s₀ i >>> j) &&& 1)) := by
      rw [u₃.mem, ev, u₂.mem, g6]
    refine ⟨⟨by rw [u₃.gpr, u₂.other _ (by decide), g1, h.edi], by rw [u₃.gpr, u₂.other _ (by decide), g2, h.esi],
      by rw [u₃.gpr, u₂.other _ (by decide), g3, h.esp], by rw [u₃.rd, u₂.rd, g4, h.rd],
      by rw [u₃.wr, u₂.wr, g5, h.wr], ?_, fun u hu => ?_⟩, by rw [u₃.gpr, u₂.other _ (by decide), a1]⟩
    · rw [m₃]
      exact h.frame.writeW (List.mem_singleton_self _) _
        (sub_contains (by simp only [BITS]; omega_using [hfit]) (by simp only [BITS]; omega_using [])
          (by simp only [BITS]; omega_using [hi, hj])
          (by decide))
    · rw [m₃]
      by_cases e : u = 8 * i + j
      · subst e
        rw [show BITS + (8 * i + j) = BITS + 8 * i + j by omega_using [], byte_write_self,
          show (8 * i + j) / 8 = i by omega_using [hj], show (8 * i + j) % 8 = j by omega_using [hj]]
      · rw [byte_write_ne _ _ (by simp only [BITS]; omega_using [hfit, hu, hi, hj])
          (by simp only [BITS]; omega_using [hfit, hi, hj]) (by omega_using [e])]
        exact h.bits u (by omega_using [hu, e])
  simp only [bitOf]
  by_cases h0 : j = 0
  · subst h0
    simp only [ite_true, List.nil_append, List.cons_append]
    refine Wp.wp_mov fun s₁ u₁ => fin s₁ (by rw [u₁.gpr]; exact (BitVec.ushiftRight_zero _).symm)
      (u₁.other _ (by decide)) (u₁.other _ (by decide)) (u₁.other _ (by decide)) (u₁.other _ (by decide))
      u₁.rd u₁.wr u₁.mem
  · simp only [h0, ite_false, List.cons_append, List.nil_append]
    refine Wp.wp_mov fun s₁ u₁ => Wp.wp_shr ⟨by omega_using [h0], by omega_using [hj]⟩ fun s₂ u₂ _ =>
      fin s₂ (by rw [u₂.gpr, u₁.gpr]) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
      (by rw [u₂.mem, u₁.mem])

theorem bitsOf_ok {s₀ sA : State} (hp : Pre s₀) (hsA : sA.wr = s₀.wr) {i : Nat} (hi : i < 32) :
    ∀ n ≤ 8, ∀ s, BInv s₀ sA (8 * i) s → s.gpr .eax = BitVec.ofNat 32 (sb s₀ i) →
    WP isa (.block ((List.range n).flatMap fun j => bitOf i j)) s fun s' =>
      BInv s₀ sA (8 * i + n) s' ∧ s'.gpr .eax = s.gpr .eax
  | 0, _, _, h, _ => WP.block_nil ⟨h, rfl⟩
  | n + 1, hn, s, h, he => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (bitsOf_ok hp hsA hi n (by omega_using [hn]) s h he) fun s₁ ⟨h₁, e₁⟩ => ?_)
    exact WP.mono (bitOf_ok hp hsA hi (by omega_using [hn]) h₁ (by rw [e₁, he])) fun s₂ ⟨h₂, e₂⟩ =>
      ⟨h₂, e₂.trans e₁⟩

theorem scalar_contains {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 32) :
    (scalarR s₀).Contains (addr (arg s₀ 1) i) 1 := by
  have := sub_contains (x := arg s₀ 1) (a := 0) (k := 32) (d := i) (n := 1)
    (by have := hp.scalar_fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hi]) (by decide)
  rwa [sub, addr_zero] at this

theorem bytes_ok {s₀ sA : State} (hp : Pre s₀) (hA : Saved s₀ sA) : ∀ n ≤ 32, ∀ s, BInv s₀ sA 0 s →
    WP isa (.block ((List.range n).flatMap fun i => .movzx8 .eax (at_ .esi i) ::
      (List.range 8).flatMap fun j => bitOf i j)) s (BInv s₀ sA (8 * n))
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ (n := n), List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (bytes_ok hp hA n (by omega_using [hn]) s h) fun s₁ h₁ => ?_)
    have hfit := hp.sc_fit
    -- The byte of the scalar, unchanged.
    have hsame : s₁.mem (addr (arg s₀ 1) n) = s₀.mem (addr (arg s₀ 1) n) := by
      have f : Frame [scR 4096 (arg s₀ 3)] s₀.mem s₁.mem := hA.frame.trans (h₁.frame.sub fun _ hr =>
        ⟨_, List.mem_singleton_self _, by
          rw [List.mem_singleton.mp hr, scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by simp only [BITS]; decide)
            (by simp only [BITS]; decide)⟩)
      exact f _ fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact hp.scalar_sc _ (scalar_contains hp (by omega_using [hn]))
    refine wp_movzx8 (a := addr (arg s₀ 1) n) (by rw [h₁.esi])
      ⟨scalarR s₀, by rw [h₁.rd, hA.rd, hp.rd]; simp, scalar_contains hp (by omega_using [hn])⟩ fun s₂ u₂ => ?_
    have h₂ : BInv s₀ sA (8 * n) s₂ := ⟨by rw [u₂.other _ (by decide)]; exact h₁.edi,
      by rw [u₂.other _ (by decide)]; exact h₁.esi, by rw [u₂.other _ (by decide)]; exact h₁.esp,
      by rw [u₂.rd]; exact h₁.rd, by rw [u₂.wr]; exact h₁.wr, by rw [u₂.mem]; exact h₁.frame,
      by rw [u₂.mem]; exact h₁.bits⟩
    have e₂ : s₂.gpr .eax = BitVec.ofNat 32 (sb s₀ n) := by
      rw [u₂.gpr, hsame]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    exact WP.mono (bitsOf_ok hp (by rw [hA.wr]) (by omega_using [hn]) 8 (Nat.le_refl _) s₂ h₂ e₂)
      fun s₃ ⟨h₃, _⟩ => by rw [show 8 * (n + 1) = 8 * n + 8 by omega_using []]; exact h₃

theorem kb_getD {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 32) :
    (Spec.X25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32).getD i 0 = s₀.mem (addr (arg s₀ 1) i) := by
  simp only [Spec.X25519.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]
  rw [addr_eq (by have := hp.scalar_fit; omega_using [this, hi])]

theorem length_kb (s₀ : State) : (Spec.X25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32).length = 32 := by
  simp [Spec.X25519.bytesAt]

theorem loadScalar_eq : loadScalar = .mov .esi (.mem (at_ .esp 8)) ::
    (((List.range 32).flatMap fun i => .movzx8 .eax (at_ .esi i) :: (List.range 8).flatMap fun j => bitOf i j) ++
    ([.mov .edx (.imm 0), .store8 (sc BITS) .dl, .store8 (sc (BITS + 1)) .dl, .store8 (sc (BITS + 2)) .dl,
      .mov .edx (.imm 1), .store8 (sc (BITS + 254)) .dl] : List Instr)) := rfl

/-- The scalar's bits, clamped: bit `t` of the decoded scalar at `BITS + t`. -/
theorem loadScalar_ok {s₀ sA : State} (hp : Pre s₀) (hA : Saved s₀ sA) :
    WP isa (.block loadScalar) sA fun s' => Saved s₀ s' ∧ Frame [sub (arg s₀ 3) BITS 256] sA.mem s'.mem ∧
      ∀ t < 255, s'.mem (addr (arg s₀ 3) (BITS + t)) = BitVec.ofNat 8
        (bit (decodeScalar25519 (Spec.X25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32)) t) := by
  have hfit := hp.sc_fit
  rw [loadScalar_eq]
  refine Wp.wp_ldm (B := sA.gpr .esp) (o := 8) rfl (by rw [hA.esp, hA.rd, hA.wr]; exact hp.argIn (i := 1) (by decide))
    fun s₁ u₁ => ?_
  have h₁ : BInv s₀ sA 0 s₁ := ⟨by rw [u₁.other _ (by decide)]; exact hA.edi,
    by rw [u₁.gpr, hA.esp]; exact hp.arg_same hA.frame (i := 1) (by decide), u₁.other _ (by decide), u₁.rd,
    u₁.wr, by rw [u₁.mem]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine WP.block_append (WP.mono (bytes_ok hp hA 32 (Nat.le_refl _) s₁ h₁) fun s₂ h₂ => ?_)
  have inb : ∀ {s : State} {d : Nat}, s.wr = sA.wr → d < 256 →
      InRegions s.wr (addr (arg s₀ 3) (BITS + d)) 1 := fun hw hd =>
    ⟨_, by rw [hw, hA.wr]; exact hp.sc_in, scR_contains hfit (by simp only [BITS]; omega_using [hd]) (by decide)⟩
  refine Wp.wp_movi fun s₃ u₃ => ?_
  have edi₃ : s₃.gpr .edi = arg s₀ 3 := by rw [u₃.other _ (by decide)]; exact h₂.edi
  refine wp_store8 (a := addr (arg s₀ 3) (BITS + 0)) (by rw [edi₃]; rfl) (inb (by rw [u₃.wr, h₂.wr]) (by decide))
    fun s₄ u₄ => ?_
  refine wp_store8 (a := addr (arg s₀ 3) (BITS + 1)) (by rw [u₄.gpr, edi₃])
    (inb (by rw [u₄.wr, u₃.wr, h₂.wr]) (by decide)) fun s₅ u₅ => ?_
  refine wp_store8 (a := addr (arg s₀ 3) (BITS + 2)) (by rw [u₅.gpr, u₄.gpr, edi₃])
    (inb (by rw [u₅.wr, u₄.wr, u₃.wr, h₂.wr]) (by decide)) fun s₆ u₆ => ?_
  refine Wp.wp_movi fun s₇ u₇ => ?_
  refine wp_store8 (a := addr (arg s₀ 3) (BITS + 254)) (by rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr, edi₃])
    (inb (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, h₂.wr]) (by decide)) fun s₈ u₈ => WP.block_nil ?_
  have z3 : ((s₃.gpr (Reg8.dl).reg).setWidth 8 : BitVec 8) = 0 := by simp only [Reg8.reg, u₃.gpr]; decide
  have z4 : ((s₄.gpr (Reg8.dl).reg).setWidth 8 : BitVec 8) = 0 := by rw [u₄.gpr]; exact z3
  have z5 : ((s₅.gpr (Reg8.dl).reg).setWidth 8 : BitVec 8) = 0 := by rw [u₅.gpr]; exact z4
  have o : ((s₇.gpr (Reg8.dl).reg).setWidth 8 : BitVec 8) = 1 := by simp only [Reg8.reg, u₇.gpr]; decide
  have m₈ : s₈.mem = ((((s₂.mem.writeW (addr (arg s₀ 3) (BITS + 0)) (0 : BitVec 8)).writeW
      (addr (arg s₀ 3) (BITS + 1)) (0 : BitVec 8)).writeW (addr (arg s₀ 3) (BITS + 2)) (0 : BitVec 8)).writeW
      (addr (arg s₀ 3) (BITS + 254)) (1 : BitVec 8)) := by
    rw [u₈.mem, o, u₇.mem, u₆.mem, z5, u₅.mem, z4, u₄.mem, z3, u₃.mem]
  have g : ∀ r, r ≠ .edx → s₈.gpr r = s₂.gpr r := fun r hr => by
    rw [u₈.gpr, u₇.other _ hr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.other _ hr]
  have hb : ∀ {m : Mem} {d : Nat} (v : BitVec 8), d < 256 → Frame [sub (arg s₀ 3) BITS 256] sA.mem m →
      Frame [sub (arg s₀ 3) BITS 256] sA.mem (m.writeW (addr (arg s₀ 3) (BITS + d)) v) := fun v hd hf =>
    hf.writeW (List.mem_singleton_self _) _ (sub_contains (by simp only [BITS]; omega_using [hfit])
      (by omega_using []) (by omega_using [hd]) (by decide))
  have f₈ : Frame [sub (arg s₀ 3) BITS 256] sA.mem s₈.mem := by
    rw [m₈]; exact hb _ (by decide) (hb _ (by decide) (hb _ (by decide) (hb _ (by decide) h₂.frame)))
  refine ⟨hA.of_frame hp f₈ (by decide) (by decide) (by decide) (by rw [g _ (by decide), h₂.edi, hA.edi])
    (by rw [g _ (by decide), h₂.esp]) (by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, h₂.rd])
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, h₂.wr]), f₈, fun t ht => ?_⟩
  rw [scalar_bit (length_kb s₀) ht, m₈]
  have ne : ∀ (m : Mem) (v : BitVec 8) (e : Nat), e < 256 → t ≠ e →
      (m.writeW (addr (arg s₀ 3) (BITS + e)) v) (addr (arg s₀ 3) (BITS + t)) = m (addr (arg s₀ 3) (BITS + t)) :=
    fun m v e he h => byte_write_ne m v (by simp only [BITS]; omega_using [hfit, ht])
      (by simp only [BITS]; omega_using [hfit, he]) (by omega_using [h])
  by_cases h3 : t < 3
  · rw [ite_eq_left h3, ne _ _ 254 (by decide) (by omega_using [h3])]
    rcases (by omega_using [h3] : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl
    · rw [ne _ _ 2 (by decide) (by decide), ne _ _ 1 (by decide) (by decide), byte_write_self]; rfl
    · rw [ne _ _ 2 (by decide) (by decide), byte_write_self]; rfl
    · rw [byte_write_self]; rfl
  · rw [ite_eq_right h3]
    by_cases h254 : t = 254
    · subst h254; rw [ite_eq_left rfl, byte_write_self]; rfl
    · rw [ite_eq_right h254, ne _ _ 254 (by decide) h254, ne _ _ 2 (by decide) (by omega_using [h3]),
        ne _ _ 1 (by decide) (by omega_using [h3]), ne _ _ 0 (by decide) (by omega_using [h3]),
        h₂.bits t (by omega_using [ht]), kb_getD hp (by omega_using [ht])]

/-! ## The ladder's initial state -/

theorem setSmall_step {x : BitVec 32} {s₀ s : State} (hc : Ctx 4096 x s) {o n : Nat} (ho : Below o) (hn : n < 8)
    (c : BitVec 32) (hk : Keep s₀ s) (hf : Frame [sub x o (4 * n)] s₀.mem s.mem)
    (hw : ∀ j < n, wd s.mem x (o + 4 * j) = if j = 0 then c else 0) :
    WP isa (.block [.mov .eax (.imm (if n = 0 then c else 0)), .store (sc (o + 4 * n)) .eax]) s fun s' =>
      Keep s₀ s' ∧ Frame [sub x o (4 * (n + 1))] s₀.mem s'.mem ∧
        ∀ j < n + 1, wd s'.mem x (o + 4 * j) = if j = 0 then c else 0 := by
  simp only [Below, T] at ho
  have hfit := hc.fit
  refine Wp.wp_movi fun s₁ u₁ => ?_
  have c₁ := (updKeep u₁).ctx hc
  refine Wp.wp_stm c₁.edi (c₁.inW (by omega_using [ho, hn]) (by decide)) fun s₂ u₂ => WP.block_nil ?_
  refine ⟨hk.trans ((updKeep u₁).trans ⟨by rw [u₂.gpr], by rw [u₂.gpr], by rw [u₂.gpr], u₂.rd, u₂.wr⟩),
    ?_, fun j hj => ?_⟩
  · rw [u₂.mem, u₁.mem]
    exact frame_write1 (frameWiden hf hfit (Nat.le_refl _) (by omega_using []) (by omega_using [ho, hn]))
      hfit (by omega_using [ho, hn]) (by omega_using []) (by omega_using []) _
  · rw [u₂.mem, u₁.mem]
    by_cases e : j = n
    · subst e; rw [wd_write_self, u₁.gpr]
    · rw [wd_write_ne _ _ (by omega_using [hfit, ho, hj, hn]) (by omega_using [hfit, ho, hn])
        (by omega_using [hj, e])]
      exact hw j (by omega_using [hj, e])

theorem setSmalls_ok {x : BitVec 32} {s₀ : State} (hc₀ : Ctx 4096 x s₀) {o : Nat} (ho : Below o) (c : BitVec 32) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun k =>
      [.mov .eax (.imm (if k = 0 then c else 0)), .store (sc (o + 4 * k)) .eax])) s₀ fun s' =>
      Keep s₀ s' ∧ Frame [sub x o (4 * n)] s₀.mem s'.mem ∧
        ∀ j < n, wd s'.mem x (o + 4 * j) = if j = 0 then c else 0
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (setSmalls_ok hc₀ ho c n (by omega_using [hn])) fun s₁ ⟨k₁, f₁, w₁⟩ =>
      setSmall_step (k₁.ctx hc₀) ho (by omega_using [hn]) c k₁ f₁ w₁)

/-- `[o] = c`. -/
theorem setSmall_ok {x : BitVec 32} {s : State} (hc : Ctx 4096 x s) {o : Nat} (ho : Below o) (c : BitVec 32) :
    WP isa (.block (setSmall o c)) s fun s' => Keep s s' ∧ Frame [sub x o 32] s.mem s'.mem ∧
      fe s'.mem x o = c.toNat :=
  WP.mono (setSmalls_ok hc ho c 8 (Nat.le_refl _)) fun _ ⟨k, f, w⟩ => ⟨k, f, by
    rw [fe]
    rw [num_congr (g := fun j => if j = 0 then c.toNat else 0) fun j hj => by
      show (wd _ x (o + 4 * j)).toNat = _; rw [w j hj]; split <;> rfl]
    simp only [num, Nat.reduceEqDiff, ↓reduceIte, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul,
      Nat.zero_add]⟩

theorem F_setSmall {x : BitVec 32} {s' : State} {o : Nat} (c : BitVec 32) (h : fe s'.mem x o = c.toNat) :
    F s'.mem x o = toFe c.toNat := by simp only [F, h]

/-- The slots, other than `o`, after a frame of `o`'s. -/
theorem F_frame1 {m m' : Mem} {x : BitVec 32} {o q : Nat} (hx : x.toNat + 4096 ≤ 2 ^ 32)
    (hf : Frame [sub x o 32] m m') (ho : isSlot 288 o = true) (hq : isSlot 288 q = true) (hne : q ≠ o) :
    F m' x q = F m x q := by
  have hob := slot_below ho; have hqb := slot_below hq; simp only [Below, T] at hob hqb
  simp only [F]
  exact congrArg toFe (fe_frame1 hf hx (by omega_using [hob]) (by omega_using [hqb]) (slot_ne ho hq hne))

theorem frame_slot {m m' : Mem} {x : BitVec 32} {o : Nat} (hx : x.toNat + 4096 ≤ 2 ^ 32)
    (hf : Frame [sub x o 32] m m') (ho : isSlot 288 o = true) : Frame [sub x 288 640] m m' := by
  have hob := slot_below ho; have ho' := slot_ge ho; simp only [Below, T] at hob
  exact frameWiden hf hx ho' (by omega_using [hob]) (by omega_using [hob])

/-- The u-coordinate as `X1` holds it: decoded (RFC 7748 §5). -/
theorem fe_X1 {s₀ s : State} (hp : Pre s₀) (hw : ∀ j < 8, wd s.mem (arg s₀ 3) (X1 + 4 * j) = pv s₀ j) :
    fe s.mem (arg s₀ 3) X1 = decodeUCoordinate (Spec.X25519.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 32) := by
  have hpf := hp.point_fit
  have e1 : fe s.mem (arg s₀ 3) X1 = num (fun k => (pv s₀ k).toNat) 8 :=
    num_congr fun j hj => by show (wd _ _ _).toNat = _; rw [hw j hj]
  have e2 : num (fun k => (pv s₀ k).toNat) 8 = num (fun k => (pw s₀ k).toNat) 8 % 2 ^ 255 := by
    rw [(fold_top (f := fun k => (pw s₀ k).toNat) fun _ _ => BitVec.isLt _).1, num_top]
    have n7 : num (fun k => (pv s₀ k).toNat) 7 = num (fun k => (pw s₀ k).toNat) 7 :=
      num_congr fun j hj => by
        show (pv s₀ j).toNat = (pw s₀ j).toNat
        rw [pv, ite_eq_right (show j ≠ 7 by omega_using [hj])]
    rw [n7]
    simp only [pv, ite_true, low31_toNat]
  have e3 : num (fun k => (pw s₀ k).toNat) 8 = leNum (Spec.X25519.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 32) := by
    rw [leNum_bytesAt_words32]
    have r : ∀ k < 8, (pw s₀ k).toNat =
        (s₀.mem.readW ((arg s₀ 2).setWidth 64 + BitVec.ofNat 64 (4 * k)) 32).toNat := fun k hk => by
      simp only [pw, wd]; rw [addr_eq (by omega_using [hpf, hk])]
    simp only [num, r 0 (by decide), r 1 (by decide), r 2 (by decide), r 3 (by decide), r 4 (by decide),
      r 5 (by decide), r 6 (by decide), r 7 (by decide), Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      Nat.reduceMul, Nat.reducePow, Nat.one_mul, Nat.zero_add]
  rw [e1, e2, e3, decodeUCoordinate_eq (length_bytesAt _ _ _)]

/-- The scalar, decoded. -/
abbrev kOf (s₀ : State) : Nat := decodeScalar25519 (Spec.X25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32)

/-- The u-coordinate, decoded. -/
abbrev uOf (s₀ : State) : Fe := toFe (decodeUCoordinate (Spec.X25519.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 32))

theorem setup_eq : setup = save ++ (loadPoint ++ (loadScalar ++ (copy X3 X1 ++ (setSmall X2 1 ++
    (setSmall Z2 0 ++ (setSmall Z3 1 ++ ([.mov .eax (.imm 0), .store (sc SWAP) .eax] : List Instr))))))) := by
  simp only [setup, initLadder, List.append_assoc]

/-- The arguments read: the ladder's initial state, in `LInv 255` but for the counter. -/
theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block setup) s₀ fun s => Base (arg s₀ 3) (kOf s₀) s₀ s ∧ F s.mem (arg s₀ 3) X1 = uOf s₀ ∧
      F s.mem (arg s₀ 3) X2 = 1 ∧ F s.mem (arg s₀ 3) Z2 = 0 ∧ F s.mem (arg s₀ 3) X3 = uOf s₀ ∧
      F s.mem (arg s₀ 3) Z3 = 1 ∧ wd s.mem (arg s₀ 3) SWAP = 0 := by
  have hfit := hp.sc_fit
  rw [setup_eq]
  refine WP.block_append (WP.mono (save_ok hp) fun s₁ h₁ => ?_)
  refine WP.block_append (WP.mono (loadPoint_ok hp h₁) fun s₂ ⟨h₂, w₂⟩ => ?_)
  refine WP.block_append (WP.mono (loadScalar_ok hp h₂) fun s₃ ⟨h₃, f₃, b₃⟩ => ?_)
  have B₃ : Base (arg s₀ 3) (kOf s₀) s₀ s₃ :=
    ⟨⟨h₃.edi, hfit, by rw [h₃.wr]; exact hp.sc_in, by decide⟩, h₃.esp, h₃.rd, h₃.wr, h₃.frame, h₃.saved, b₃⟩
  have x1₃ : F s₃.mem (arg s₀ 3) X1 = uOf s₀ := by
    simp only [F, uOf]
    rw [← fe_X1 hp w₂]
    exact congrArg toFe (fe_frame1 f₃ hfit (by decide) (by decide) (.inr (by decide)))
  have sl : ∀ q, isSlot 288 q = true → Below q := fun q hq => slot_below hq
  refine WP.block_append (WP.mono (copy_ok B₃.ctx (o := X3) (a := X1) (by decide) (by decide) (by decide))
    fun s₄ ⟨k₄, f₄, e₄⟩ => ?_)
  have B₄ := B₃.ops k₄ (frame_slot hfit f₄ (by decide))
  refine WP.block_append (WP.mono (setSmall_ok B₄.ctx (o := X2) (by decide) 1) fun s₅ ⟨k₅, f₅, e₅⟩ => ?_)
  have B₅ := B₄.ops k₅ (frame_slot hfit f₅ (by decide))
  refine WP.block_append (WP.mono (setSmall_ok B₅.ctx (o := Z2) (by decide) 0) fun s₆ ⟨k₆, f₆, e₆⟩ => ?_)
  have B₆ := B₅.ops k₆ (frame_slot hfit f₆ (by decide))
  refine WP.block_append (WP.mono (setSmall_ok B₆.ctx (o := Z3) (by decide) 1) fun s₇ ⟨k₇, f₇, e₇⟩ => ?_)
  have B₇ := B₆.ops k₇ (frame_slot hfit f₇ (by decide))
  refine Wp.wp_movi fun s₈ u₈ => ?_
  have c₈ := (updKeep u₈).ctx B₇.ctx
  refine Wp.wp_stm c₈.edi (c₈.inW (by decide) (by decide)) fun s₉ u₉ => WP.block_nil ?_
  have m₉ : s₉.mem = s₇.mem.writeW (addr (arg s₀ 3) SWAP) (0 : BitVec 32) := by rw [u₉.mem, u₈.gpr, u₈.mem]
  have f₉ : Frame [sub (arg s₀ 3) SWAP 4] s₇.mem s₉.mem := by
    rw [m₉]; exact frame_write1 (Frame.refl _ _) hfit (by decide) (Nat.le_refl _) (Nat.le_refl _) _
  have F₉ : ∀ q, isSlot 288 q = true → F s₉.mem (arg s₀ 3) q = F s₇.mem (arg s₀ 3) q := fun q hq => by
    have hq' := slot_ge hq; have hqb := slot_below hq; simp only [Below, T] at hqb
    simp only [F]
    exact congrArg toFe (fe_frame1 f₉ hfit (by decide) (by omega_using [hqb]) (.inr (by simp only [SWAP]; omega_using [hq'])))
  refine ⟨B₇.of_frame (by rw [u₉.gpr, u₈.other _ (by decide)]) (by rw [u₉.gpr, u₈.other _ (by decide)])
    (by rw [u₉.rd, u₈.rd]) (by rw [u₉.wr, u₈.wr]) f₉ (by decide) (by decide) (.inl (by decide)) (by decide),
    ?_, ?_, ?_, ?_, ?_, by rw [m₉, wd_write_self]⟩
  · rw [F₉ _ (by decide), F_frame1 hfit f₇ (by decide) (by decide) (by decide),
      F_frame1 hfit f₆ (by decide) (by decide) (by decide), F_frame1 hfit f₅ (by decide) (by decide) (by decide),
      F_frame1 hfit f₄ (by decide) (by decide) (by decide), x1₃]
  · rw [F₉ _ (by decide), F_frame1 hfit f₇ (by decide) (by decide) (by decide),
      F_frame1 hfit f₆ (by decide) (by decide) (by decide), F_setSmall _ e₅]; rfl
  · rw [F₉ _ (by decide), F_frame1 hfit f₇ (by decide) (by decide) (by decide), F_setSmall _ e₆]; rfl
  · rw [F₉ _ (by decide), F_frame1 hfit f₇ (by decide) (by decide) (by decide),
      F_frame1 hfit f₆ (by decide) (by decide) (by decide), F_frame1 hfit f₅ (by decide) (by decide) (by decide)]
    simp only [F] at x1₃ ⊢
    rw [e₄]; exact x1₃
  · rw [F₉ _ (by decide), F_setSmall _ e₇]; rfl

end VG.Proof.X25519.X86
