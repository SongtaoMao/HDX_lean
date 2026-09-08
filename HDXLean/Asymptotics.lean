import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Order

/-!
# Elementary asymptotic predicates

The paper only needs asymptotic statements about sequences of natural numbers.  The definitions
in this file deliberately expose all constants and thresholds, so later statements do not depend
on an opaque asymptotics API.

`PolynomiallyBounded f g` means that, eventually, `f r` is at most a constant times a fixed
power of `g r + 1`.  The harmless `+ 1` makes the definition useful even at indices where `g`
vanishes.  `PolylogarithmicallyBounded f N` uses the base-two floor logarithm of `N`, matching
the paper's vertex counts `N = 2^n`.
-/

namespace HDXLean

/-- A predicate on indices holds from some explicit threshold onward. -/
def Eventually (P : ℕ → Prop) : Prop :=
  ∃ r₀, ∀ r, r₀ ≤ r → P r

namespace Eventually

theorem of_forall {P : ℕ → Prop} (h : ∀ r, P r) : Eventually P := by
  exact ⟨0, fun r _ => h r⟩

theorem mono {P Q : ℕ → Prop} (hP : Eventually P) (h : ∀ r, P r → Q r) :
    Eventually Q := by
  rcases hP with ⟨r₀, hP⟩
  exact ⟨r₀, fun r hr => h r (hP r hr)⟩

theorem and {P Q : ℕ → Prop} (hP : Eventually P) (hQ : Eventually Q) :
    Eventually fun r => P r ∧ Q r := by
  rcases hP with ⟨rP, hP⟩
  rcases hQ with ⟨rQ, hQ⟩
  refine ⟨max rP rQ, fun r hr => ?_⟩
  exact ⟨hP r (Nat.le_trans (Nat.le_max_left _ _) hr),
    hQ r (Nat.le_trans (Nat.le_max_right _ _) hr)⟩

theorem or {P Q : ℕ → Prop} (hP : Eventually P) :
    Eventually fun r => P r ∨ Q r :=
  hP.mono fun _ hr => Or.inl hr

end Eventually

/-- A natural-valued sequence eventually exceeds every fixed natural bound. -/
def TendsToInfinity (f : ℕ → ℕ) : Prop :=
  ∀ B, Eventually fun r => B ≤ f r

theorem tendsToInfinity_id : TendsToInfinity (fun r : ℕ => r) := by
  intro B
  exact ⟨B, fun r hr => hr⟩

theorem TendsToInfinity.mono {f g : ℕ → ℕ} (hf : TendsToInfinity f)
    (hfg : Eventually fun r => f r ≤ g r) : TendsToInfinity g := by
  intro B
  exact ((hf B).and hfg).mono fun _ hr => Nat.le_trans hr.1 hr.2

theorem TendsToInfinity.add_const {f : ℕ → ℕ} (hf : TendsToInfinity f) (c : ℕ) :
    TendsToInfinity fun r => f r + c := by
  exact hf.mono <| Eventually.of_forall fun r => Nat.le_add_right (f r) c

/-- `f` is eventually bounded by a constant times `g + 1`. -/
def LinearBounded (f g : ℕ → ℕ) : Prop :=
  ∃ C, Eventually fun r => f r ≤ C * (g r + 1)

/-- Two natural-valued sequences have the same linear order of growth.  The
harmless `+ 1` in `LinearBounded` makes this formulation insensitive to the
finitely many small indices at which one of the sequences may vanish. -/
def ThetaLinear (f g : ℕ → ℕ) : Prop :=
  LinearBounded f g ∧ LinearBounded g f

namespace LinearBounded

theorem zero (g : ℕ → ℕ) : LinearBounded (fun _ => 0) g := by
  exact ⟨0, Eventually.of_forall fun _ => by simp⟩

theorem const (c : ℕ) (g : ℕ → ℕ) : LinearBounded (fun _ => c) g := by
  refine ⟨c, Eventually.of_forall fun r => ?_⟩
  calc
    c = c * 1 := by simp
    _ ≤ c * (g r + 1) := Nat.mul_le_mul_left c (by omega)

theorem refl (f : ℕ → ℕ) : LinearBounded f f := by
  refine ⟨1, Eventually.of_forall fun r => ?_⟩
  simp

theorem of_eventually_le {f g h : ℕ → ℕ} (hfg : Eventually fun r => f r ≤ g r)
    (hgh : LinearBounded g h) : LinearBounded f h := by
  rcases hgh with ⟨C, hgh⟩
  refine ⟨C, (hfg.and hgh).mono fun _ hr => ?_⟩
  exact Nat.le_trans hr.1 hr.2

theorem add {f g h : ℕ → ℕ} (hf : LinearBounded f h) (hg : LinearBounded g h) :
    LinearBounded (fun r => f r + g r) h := by
  rcases hf with ⟨C, hf⟩
  rcases hg with ⟨D, hg⟩
  refine ⟨C + D, (hf.and hg).mono fun r hr => ?_⟩
  calc
    f r + g r ≤ C * (h r + 1) + D * (h r + 1) := Nat.add_le_add hr.1 hr.2
    _ = (C + D) * (h r + 1) := by rw [Nat.add_mul]

end LinearBounded

namespace ThetaLinear

theorem refl (f : ℕ → ℕ) : ThetaLinear f f :=
  ⟨LinearBounded.refl f, LinearBounded.refl f⟩

theorem symm {f g : ℕ → ℕ} (h : ThetaLinear f g) : ThetaLinear g f :=
  ⟨h.2, h.1⟩

end ThetaLinear

/-- `f` is eventually bounded by a constant times a fixed power of `g + 1`. -/
def PolynomiallyBounded (f g : ℕ → ℕ) : Prop :=
  ∃ C k, Eventually fun r => f r ≤ C * (g r + 1) ^ k

namespace PolynomiallyBounded

theorem zero (g : ℕ → ℕ) : PolynomiallyBounded (fun _ => 0) g := by
  exact ⟨0, 0, Eventually.of_forall fun _ => Nat.le_refl 0⟩

theorem const (c : ℕ) (g : ℕ → ℕ) : PolynomiallyBounded (fun _ => c) g := by
  exact ⟨c, 0, Eventually.of_forall fun _ => by simp⟩

theorem refl (f : ℕ → ℕ) : PolynomiallyBounded f f := by
  refine ⟨1, 1, Eventually.of_forall fun r => ?_⟩
  simp

theorem of_eventually_le {f g h : ℕ → ℕ} (hfg : Eventually fun r => f r ≤ g r)
    (hgh : PolynomiallyBounded g h) : PolynomiallyBounded f h := by
  rcases hgh with ⟨C, k, hgh⟩
  refine ⟨C, k, (hfg.and hgh).mono fun _ hr => ?_⟩
  exact Nat.le_trans hr.1 hr.2

theorem of_linear {f g : ℕ → ℕ} (h : LinearBounded f g) : PolynomiallyBounded f g := by
  rcases h with ⟨C, h⟩
  exact ⟨C, 1, by simpa using h⟩

theorem const_mul {f g : ℕ → ℕ} (h : PolynomiallyBounded f g) (a : ℕ) :
    PolynomiallyBounded (fun r => a * f r) g := by
  rcases h with ⟨C, k, h⟩
  refine ⟨a * C, k, h.mono fun r hr => ?_⟩
  calc
    a * f r ≤ a * (C * (g r + 1) ^ k) := Nat.mul_le_mul_left a hr
    _ = (a * C) * (g r + 1) ^ k := by rw [Nat.mul_assoc]

theorem add {f g h : ℕ → ℕ} (hf : PolynomiallyBounded f h)
    (hg : PolynomiallyBounded g h) : PolynomiallyBounded (fun r => f r + g r) h := by
  rcases hf with ⟨C, k, hf⟩
  rcases hg with ⟨D, l, hg⟩
  refine ⟨C + D, k + l, (hf.and hg).mono fun r hr => ?_⟩
  have hbase : 0 < h r + 1 := Nat.zero_lt_succ _
  have hk : (h r + 1) ^ k ≤ (h r + 1) ^ (k + l) :=
    Nat.pow_le_pow_right hbase (Nat.le_add_right k l)
  have hl : (h r + 1) ^ l ≤ (h r + 1) ^ (k + l) :=
    Nat.pow_le_pow_right hbase (Nat.le_add_left l k)
  calc
    f r + g r ≤ C * (h r + 1) ^ k + D * (h r + 1) ^ l :=
      Nat.add_le_add hr.1 hr.2
    _ ≤ C * (h r + 1) ^ (k + l) + D * (h r + 1) ^ (k + l) :=
      Nat.add_le_add (Nat.mul_le_mul_left C hk) (Nat.mul_le_mul_left D hl)
    _ = (C + D) * (h r + 1) ^ (k + l) := by rw [Nat.add_mul]

theorem mul {f g h : ℕ → ℕ} (hf : PolynomiallyBounded f h)
    (hg : PolynomiallyBounded g h) : PolynomiallyBounded (fun r => f r * g r) h := by
  rcases hf with ⟨C, k, hf⟩
  rcases hg with ⟨D, l, hg⟩
  refine ⟨C * D, k + l, (hf.and hg).mono fun r hr => ?_⟩
  calc
    f r * g r ≤ (C * (h r + 1) ^ k) * (D * (h r + 1) ^ l) :=
      Nat.mul_le_mul hr.1 hr.2
    _ = (C * D) * (h r + 1) ^ (k + l) := by
      simp only [Nat.pow_add]
      ac_rfl

end PolynomiallyBounded

namespace ThetaLinear

/-- A `ThetaLinear` bound in particular supplies the polynomial upper bound
used by the older family interface. -/
theorem polynomiallyBounded {f g : ℕ → ℕ} (h : ThetaLinear f g) :
    PolynomiallyBounded f g :=
  PolynomiallyBounded.of_linear h.1

end ThetaLinear

/-- The degree is eventually bounded by a fixed power of the base-two logarithm of the number
of vertices (up to a constant factor). -/
def PolylogarithmicallyBounded (degree vertexCount : ℕ → ℕ) : Prop :=
  PolynomiallyBounded degree fun r => Nat.log2 (vertexCount r)

/-- For binary vector spaces, a polynomial bound in ambient dimension is a polylogarithmic bound
in the number of vertices. -/
theorem PolynomiallyBounded.polylogarithmic_of_vertexCount_pow_two
    {degree ambientDimension vertexCount : ℕ → ℕ}
    (hdegree : PolynomiallyBounded degree ambientDimension)
    (hvertices : ∀ r, vertexCount r = 2 ^ ambientDimension r) :
    PolylogarithmicallyBounded degree vertexCount := by
  rcases hdegree with ⟨C, k, hdegree⟩
  refine ⟨C, k, hdegree.mono fun r hr => ?_⟩
  change degree r ≤ C * (Nat.log2 (vertexCount r) + 1) ^ k
  rw [hvertices r, Nat.log2_two_pow]
  exact hr

namespace PolylogarithmicallyBounded

theorem of_eventually_le {degree₁ degree₂ vertexCount : ℕ → ℕ}
    (h : Eventually fun r => degree₁ r ≤ degree₂ r)
    (hdegree : PolylogarithmicallyBounded degree₂ vertexCount) :
    PolylogarithmicallyBounded degree₁ vertexCount :=
  PolynomiallyBounded.of_eventually_le h hdegree

theorem add {degree₁ degree₂ vertexCount : ℕ → ℕ}
    (h₁ : PolylogarithmicallyBounded degree₁ vertexCount)
    (h₂ : PolylogarithmicallyBounded degree₂ vertexCount) :
    PolylogarithmicallyBounded (fun r => degree₁ r + degree₂ r) vertexCount :=
  PolynomiallyBounded.add h₁ h₂

theorem mul {degree₁ degree₂ vertexCount : ℕ → ℕ}
    (h₁ : PolylogarithmicallyBounded degree₁ vertexCount)
    (h₂ : PolylogarithmicallyBounded degree₂ vertexCount) :
    PolylogarithmicallyBounded (fun r => degree₁ r * degree₂ r) vertexCount :=
  PolynomiallyBounded.mul h₁ h₂

end PolylogarithmicallyBounded

end HDXLean
