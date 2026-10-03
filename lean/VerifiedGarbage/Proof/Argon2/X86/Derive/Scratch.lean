import VerifiedGarbage.Proof.Argon2.X86.Derive.Parameters

/-!
# Argon2 on x86 (32-bit): the derivation's use of H′'s hash macros

The H₀ code calls the BLAKE2b functions through H′'s macros
(`Impl.Argon2.X86.HPrime`), with `ebx` pointing to `scratch` and the stack
below the locals: `ctx` gives their context (`HPrime.Ctx`), and `Inv.keeps`
the body's invariant and locals after them. `Inv.store_scr` is a store to
`scratch` through `ebx`.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd)
open VG.Proof.Argon2.X86.HPrime (Ctx Keeps)

/-- `n` bytes of `scratch` at offset `d`. -/
theorem scr_sub {s₀ : State} {d n : Nat} (h : d + n ≤ 16384) :
    Region.Sub ⟨(scrP s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩ (scrR s₀) := Offset.sub_base _ h

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem scr_mem : scrR s₀ ∈ (entry s₀).wr := wr_mem s₀ (by rw [hp.wr]; simp)
theorem mem_mem : memR s₀ ∈ (entry s₀).wr := wr_mem s₀ (by rw [hp.wr]; simp)
theorem out_mem : outR s₀ ∈ (entry s₀).wr := wr_mem s₀ (by rw [hp.wr]; simp)


/-- The 60 bytes below the locals that H′'s macros use are outside the body's other regions. -/
theorem below60_call : Region.Sub (VG.X86.below (E s₀) 60) (callR s₀) :=
  VG.X86.below_sub (by decide) (by rw [E_nat hp]; have := hp.esp_lo; omega)

theorem ctx {s : State} (h : Inv s₀ s) (hb : s.gpr .ebx = scrP s₀) : Ctx (scrP s₀) (E s₀) s := by
  have := hp.scr_fits
  refine ⟨hb, h.esp, by omega, by rw [E_nat hp]; have := hp.esp_lo; omega,
    by have := E_hi hp; omega, ?_, ?_⟩
  · rw [h.wr]
    exact (Covers.of_sub (rs' := [scrR s₀]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, List.mem_singleton_self _, 0, by simp, by simp⟩).trans
      (fun a n ⟨r, hr, hc⟩ => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact scr_mem hp, hc⟩)
  · exact ((hp.stk_all (scrR s₀) (by simp)).sub_left fun a ha => call_stk hp a (below60_call hp a ha)).sub_right
      (Region.sub_prefix (by decide))

/-- What H′'s macros keep keeps the body's invariant and the locals. -/
theorem Inv.keeps {s t : State} (h : Inv s₀ s) (k : Keeps (scrP s₀) (E s₀) s t) :
    Inv s₀ t ∧ ∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s d := by
  have sub : ∀ r ∈ [(⟨(scrP s₀).setWidth 64, 832⟩ : Region), VG.X86.below (E s₀) 60],
      ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨callR s₀, by simp, below60_call hp⟩
  refine ⟨h.step k.esp k.ebp k.rd k.wr (k.frame.sub fun r hr => ?_), fun d hd => lw_keep hp k.frame sub hd⟩
  obtain ⟨r', hr', hs⟩ := sub r hr
  refine ⟨r', ?_, hs⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl <;> simp

end

/-! ## The hash macros, with `Keeps` -/

section
open VG.Spec.Blake2

variable {B E : BitVec 32} {s : State} (c : Ctx B E s)
include c

theorem init_k {n : Nat} (hn : s.gpr .edx = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    WP isa Impl.Argon2.X86.HPrime.init s fun t =>
      Repr b (Spec.Blake2.init b n 0) t.mem (B.setWidth 64) [] ∧ Keeps B E s t :=
  (HPrime.init_ok c hn hn₁ hn₂).mono fun t ⟨r, cs, rd, wr, f⟩ =>
    ⟨r, Keeps.of_call (HPrime.of_callee cs) rd wr f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, below_sub (by decide) c.lo⟩⟩

theorem update_k {D : BitVec 32} {L : Nat}
    (hD : s.gpr .esi = D) (hL : (s.gpr .edi).toNat = L) (hDfit : D.toNat + L ≤ 2 ^ 32)
    (hDc : Covers [⟨D.setWidth 64, L⟩] (s.rd ++ s.wr))
    (hDs : Region.Disjoint ⟨D.setWidth 64, L⟩ ⟨B.setWidth 64, 768⟩)
    (hDk : (below E 60).Disjoint ⟨D.setWidth 64, L⟩)
    {h0 : HashValue 64} {d : List Byte} (repr : Repr b h0 s.mem (B.setWidth 64) d)
    (hc : s.gpr .edx ++ s.gpr .ecx = BitVec.ofNat 64 d.length) (hlen : d.length + L < 2 ^ 64) :
    WP isa Impl.Argon2.X86.HPrime.update s fun t =>
      Repr b h0 t.mem (B.setWidth 64) (d ++ bytesAt s.mem (D.setWidth 64) L) ∧ Keeps B E s t :=
  (HPrime.update_ok c hD hL hDfit hDc hDs hDk repr hc hlen).mono fun t ⟨r, cs, rd, wr, f⟩ =>
    ⟨r, Keeps.of_call (HPrime.of_callee cs) rd wr f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩⟩

theorem finalize_k {h0 : HashValue 64} {d : List Byte} (repr : Repr b h0 s.mem (B.setWidth 64) d)
    (hc : s.gpr .edx ++ s.gpr .ecx = BitVec.ofNat 64 d.length) (hlen : d.length < 2 ^ 64) :
    WP isa Impl.Argon2.X86.HPrime.finalize s fun t =>
      bytesAt t.mem (B.setWidth 64 + 768) 64 = finalHash b h0 d ∧ Keeps B E s t :=
  (HPrime.finalize_ok c repr hc hlen).mono fun t ⟨dg, cs, rd, wr, f⟩ =>
    ⟨dg, Keeps.of_call (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> exact cs _ (by decide) (by decide)) rd wr f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩⟩

end

end VG.Proof.Argon2.X86.Derive
